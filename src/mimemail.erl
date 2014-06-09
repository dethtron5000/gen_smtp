%%% Copyright 2009 Andrew Thompson <andrew@hijacked.us>. All rights reserved.
%%%
%%% Redistribution and use in source and binary forms, with or without
%%% modification, are permitted provided that the following conditions are met:
%%%
%%%   1. Redistributions of source code must retain the above copyright notice,
%%%      this list of conditions and the following disclaimer.
%%%   2. Redistributions in binary form must reproduce the above copyright
%%%      notice, this list of conditions and the following disclaimer in the
%%%      documentation and/or other materials provided with the distribution.
%%%
%%% THIS SOFTWARE IS PROVIDED BY THE FREEBSD PROJECT ``AS IS'' AND ANY EXPRESS OR
%%% IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
%%% MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO
%%% EVENT SHALL THE FREEBSD PROJECT OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
%%% INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
%%% (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
%%% LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
%%% ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
%%% (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
%%% SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

%% @doc A module for decoding/encoding MIME 1.0 email.
%% The encoder and decoder operate on the same datastructure, which is as follows:
%% A 5-tuple with the following elements: `{Type, SubType, Headers, Parameters, Body}'.
%%
%% `Type' and `SubType' are the MIME type of the email, examples are `text/plain' or
%% `multipart/alternative'. The decoder splits these into 2 fields so you can filter by
%% the main type or by the subtype.
%%
%% `Headers' consists of a list of key/value pairs of binary values eg.
%% `{<<"From">>, <<"Andrew Thompson <andrew@hijacked.us>">>}'. There is no parsing of
%% the header aside from un-wrapping the lines and splitting the header name from the
%% header value.
%%
%% `Parameters' is a list of 3 key/value tuples. The 3 keys are `<<"content-type-params">>',
%% `<<"dispisition">>' and `<<"disposition-params">>'.
%% `content-type-params' is a key/value list of parameters on the content-type header, this
%% usually consists of things like charset and the format parameters. `disposition' indicates
%% how the data wants to be displayed, this is usually 'inline'. `disposition-params' is a list of
%% disposition information, eg. the filename this section should be saved as, the modification
%% date the file should be saved with, etc.
%%
%% Finally, `Body' can be one of several different types, depending on the structure of the email.
%% For a simple email, the body will usually be a binary consisting of the message body, In the
%% case of a multipart email, its a list of these 5-tuple MIME structures. The third possibility,
%% in the case of a message/rfc822 attachment, body can be a single 5-tuple MIME structure.
%% 
%% You should see the relevant RFCs (2045, 2046, 2047, etc.) for more information.
-module(mimemail).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([encode/1, encode/2, decode/2, decode/1, get_header_value/2, get_header_value/3, parse_headers/1]).

-define(DEFAULT_OPTIONS, [
		{encoding, get_default_encoding()}, % default encoding is utf-8 if we can find the iconv module
		{decode_attachments, true} % should we decode any base64/quoted printable attachments?
	]).

-type(mimetuple() :: {binary(), binary(), [{binary(), binary()}], [{binary(), binary()}], binary() | [{binary(), binary(), [{binary(), binary()}], [{binary(), binary()}], binary() | [tuple()]}] | tuple()}).

-type(options() :: [{'encoding', binary()} | {'decode_attachment', boolean()}]).

-spec(decode/1 :: (Email :: binary()) -> mimetuple()).
%% @doc Decode a MIME email from a binary.
decode(All) ->
	{Headers, Body} = parse_headers(All),
	decode(Headers, Body, ?DEFAULT_OPTIONS).

-spec(decode/2 :: (Email :: binary(), Options :: options()) -> mimetuple()).
%% @doc Decode with custom options
decode(All, Options) when is_binary(All), is_list(Options) ->
	{Headers, Body} = parse_headers(All),
	decode(Headers, Body, Options).

decode(OrigHeaders, Body, Options) ->
	%io:format("headers: ~p~n", [Headers]),
	Encoding = proplists:get_value(encoding, Options, none),
	%FixedHeaders = fix_headers(Headers),
	Headers = decode_headers(OrigHeaders, [], Encoding),
	case parse_with_comments(get_header_value(<<"MIME-Version">>, Headers)) of
		undefined ->
			case parse_content_type(get_header_value(<<"Content-Type">>, Headers)) of
				{<<"multipart">>, _SubType, _Parameters} ->
					erlang:error(non_mime_multipart);
				{Type, SubType, Parameters} ->
					NewBody = decode_body(get_header_value(<<"Content-Transfer-Encoding">>, Headers),
						Body, proplists:get_value(<<"charset">>, Parameters), Encoding),
					{Type, SubType, Headers, Parameters, NewBody};
				undefined ->
					Parameters = [{<<"content-type-params">>, [{<<"charset">>, <<"us-ascii">>}]}, {<<"disposition">>, <<"inline">>}, {<<"disposition-params">>, []}],
					{<<"text">>, <<"plain">>, Headers, Parameters, decode_body(get_header_value(<<"Content-Transfer-Encoding">>, Headers), Body)}
			end;
		Other ->
			decode_component(Headers, Body, Other, Options)
	end.

-spec(encode/1 :: (MimeMail :: mimetuple()) -> binary()).
encode(MimeMail) ->
	encode(MimeMail, []).

%% @doc Encode a MIME tuple to a binary.
encode({Type, Subtype, Headers, ContentTypeParams, Parts}, Options) ->
	{FixedParams, FixedHeaders} = ensure_content_headers(Type, Subtype, ContentTypeParams, Headers, Parts, true),
	CheckedHeaders = check_headers(FixedHeaders),
	EncodedBody = binstr:join(
					encode_component(Type, Subtype, CheckedHeaders, FixedParams, Parts),
					"\r\n"),
	EncodedHeaders = encode_headers(CheckedHeaders),
	SignedHeaders = case proplists:get_value(dkim, Options) of
						undefined -> EncodedHeaders;
						DKIM -> dkim_sign_email(EncodedHeaders, EncodedBody, DKIM)
					end,
	list_to_binary([binstr:join(SignedHeaders, "\r\n"),
					"\r\n\r\n",
					EncodedBody]);
encode(_, _) ->
	io:format("Not a mime-decoded DATA~n"),
	erlang:error(non_mime).


decode_headers(Headers, _, none) ->
	Headers;
decode_headers([], Acc, _Charset) ->
	lists:reverse(Acc);
decode_headers([{Key, Value} | Headers], Acc, Charset) ->
	decode_headers(Headers, [{Key, decode_header(Value, Charset)} | Acc], Charset).

decode_header(Value, Charset) ->
	RTokens = tokenize_header(Value, []),
	Tokens = lists:reverse(RTokens),
	Decoded = try decode_header_tokens_strict(Tokens, Charset)
			  catch Type:Reason ->
					  case decode_header_tokens_permissive(Tokens, Charset, []) of
						  {ok, Dec} -> Dec;
						  error ->
							  % re-throw original error
							  % may also use erlang:raise/3 to preserve original traceback
							  erlang:Type(Reason)
					  end
			  end,
	iolist_to_binary(Decoded).

-type hdr_token() :: binary() | {Encoding::binary(), Data::binary()}.
-spec tokenize_header(binary(), [hdr_token()]) -> [hdr_token()].
tokenize_header(<<>>, Acc) ->
    Acc;
tokenize_header(Value, Acc) ->
	%% maybe replace "?([^\s]+)\\?" with "?([^\s]*)\\?"?
	%% see msg lvuvmm593b8s7pqqfhu7cdtqd4g4najh
	%% Subject: =?utf-8?Q??=
	%%	=?utf-8?Q?=D0=9F=D0=BE=D0=B4=D1=82=D0=B2=D0=B5=D1=80=D0=B4=D0=B8=D1=82=D0=B5=20?=
	%%	=?utf-8?Q?=D1=80=D0=B5=D0=B3=D0=B8=D1=81=D1=82=D1=80=D0=B0=D1=86=D0=B8=D1=8E=20?=
	%%	=?utf-8?Q?=D0=B2=20Moy-Rebenok.ru?=

	case re:run(Value, "=\\?([-A-Za-z0-9_]+)\\?([qQbB])\\?([^\s]+)\\?=", [ungreedy]) of
		nomatch ->
			[Value | Acc];
		{match,[{AllStart, AllLen},{EncodingStart, EncodingLen},{TypeStart, _},{DataStart, DataLen}]} ->
			%% RFC 2047 #2 (encoded-word)
			Encoding = binstr:substr(Value, EncodingStart+1, EncodingLen),
			Type = binstr:to_lower(binstr:substr(Value, TypeStart+1, 1)),
			Data = binstr:substr(Value, DataStart+1, DataLen),

			EncodedData =
				case Type of
					<<"q">> ->
						%% RFC 2047 #5. (3)
						decode_quoted_printable(re:replace(Data, "_", " ", [{return, binary}, global]));
					<<"b">> ->
						decode_base64(re:replace(Data, "_", " ", [{return, binary}, global]))
				end,



			Offset = case re:run(binstr:substr(Value, AllStart + AllLen + 1), "^([\s\t\n\r]+)=\\?[-A-Za-z0-9_]+\\?[^\s]\\?[^\s]+\\?=", [ungreedy]) of
				nomatch ->
					% no 2047 block immediately following
					1;
				{match,[{_, _},{_, WhiteSpaceLen}]} ->
					1+ WhiteSpaceLen
			end,

			NewAcc = case binstr:substr(Value, 1, AllStart) of
						 <<>> -> [{fix_encoding(Encoding), EncodedData} | Acc];
						 Other -> [{fix_encoding(Encoding), EncodedData}, Other | Acc]
					 end,
			tokenize_header(binstr:substr(Value, AllStart + AllLen + Offset), NewAcc)
	end.


decode_header_tokens_strict([], _) ->
	[];
decode_header_tokens_strict([{Encoding, Data} | Tokens], Charset) ->
	{ok, S} = convert(Charset, Encoding, Data),
	[S | decode_header_tokens_strict(Tokens, Charset)];
decode_header_tokens_strict([Data | Tokens], Charset) ->
	[Data | decode_header_tokens_strict(Tokens, Charset)].

%% this decoder can handle folded not-by-RFC UTF headers, when somebody split
%% multibyte string not by characters, but by bytes. It first join folded
%% string and only then decode it with iconv.
decode_header_tokens_permissive([], _, [Result]) when is_binary(Result) ->
	{ok, Result};
decode_header_tokens_permissive([], _, Stack) ->
	case lists:all(fun erlang:is_binary/1, Stack) of
		true -> {ok, lists:reverse(Stack)};
		false  -> error
	end;
decode_header_tokens_permissive([{Enc, Data} | Tokens], Charset, [{Enc, PrevData} | Stack]) ->
	NewData = iolist_to_binary([PrevData, Data]),
	case convert(Charset, Enc, NewData) of
		{ok, S} ->
			decode_header_tokens_permissive(Tokens, Charset, [S | Stack]);
		_ ->
			decode_header_tokens_permissive(Tokens, Charset, [{Enc, NewData} | Stack])
	end;
decode_header_tokens_permissive([NextToken | _] = Tokens, Charset, [{_, _} | Stack])
  when is_binary(NextToken) orelse is_tuple(NextToken) ->
	%% practicaly very rare case "=?utf-8?Q?BROKEN?=\r\n\t=?windows-1251?Q?maybe-broken?="
	%% or "=?utf-8?Q?BROKEN?= raw-ascii-string"
	%% drop broken value from stack
	decode_header_tokens_permissive(Tokens, Charset, Stack);
decode_header_tokens_permissive([Data | Tokens], Charset, Stack) ->
	decode_header_tokens_permissive(Tokens, Charset, [Data | Stack]).


convert(To, From, Data) ->
	unicode:characters_to_binary(Data, To, From).
	%CD = case iconv:open(To, From) of
	%		 {ok, Res} -> Res;
	%		 {error, einval} -> throw({bad_charset, From})
	%	 end,
	%Converted = iconv:conv(CD, Data),
	%iconv:close(CD),
	%Converted.


decode_component(Headers, Body, MimeVsn, Options) when MimeVsn =:= <<"1.0">> ->
	case parse_content_disposition(get_header_value(<<"Content-Disposition">>, Headers)) of
		{Disposition, DispositionParams} ->
			ok;
		_ -> % defaults
			Disposition = <<"inline">>,
			DispositionParams = []
	end,

	case parse_content_type(get_header_value(<<"Content-Type">>, Headers)) of
		{<<"multipart">>, SubType, Parameters} ->
			case proplists:get_value(<<"boundary">>, Parameters) of
				undefined ->
					erlang:error(no_boundary);
				Boundary ->
					% io:format("this is a multipart email of type:  ~s and boundary ~s~n", [SubType, Boundary]),
					Parameters2 = [{<<"content-type-params">>, Parameters}, {<<"disposition">>, Disposition}, {<<"disposition-params">>, DispositionParams}],
					{<<"multipart">>, SubType, Headers, Parameters2, split_body_by_boundary(Body, list_to_binary(["--", Boundary]), MimeVsn, Options)}
			end;
		{<<"message">>, <<"rfc822">>, Parameters} ->
			{NewHeaders, NewBody} = parse_headers(Body),
			Parameters2 = [{<<"content-type-params">>, Parameters}, {<<"disposition">>, Disposition}, {<<"disposition-params">>, DispositionParams}],
			{<<"message">>, <<"rfc822">>, Headers, Parameters2, decode(NewHeaders, NewBody, Options)};
		{Type, SubType, Parameters} ->
			%io:format("body is ~s/~s~n", [Type, SubType]),
			Parameters2 = [{<<"content-type-params">>, Parameters}, {<<"disposition">>, Disposition}, {<<"disposition-params">>, DispositionParams}],
			{Type, SubType, Headers, Parameters2, decode_body(get_header_value(<<"Content-Transfer-Encoding">>, Headers), Body, proplists:get_value(<<"charset">>, Parameters), proplists:get_value(encoding, Options, none))};
		undefined -> % defaults
			Type = <<"text">>,
			SubType = <<"plain">>,
			Parameters = [{<<"content-type-params">>, [{<<"charset">>, <<"us-ascii">>}]}, {<<"disposition">>, Disposition}, {<<"disposition-params">>, DispositionParams}],
			{Type, SubType, Headers, Parameters, decode_body(get_header_value(<<"Content-Transfer-Encoding">>, Headers), Body)}
	end;
decode_component(_Headers, _Body, Other, _Options) ->
	erlang:error({mime_version, Other}).

-spec(get_header_value/3 :: (Needle :: binary(), Headers :: [{binary(), binary()}], Default :: any()) -> binary() | any()).
%% @doc Do a case-insensitive header lookup to return that header's value, or the specified default.
get_header_value(Needle, Headers, Default) ->
	%io:format("Headers: ~p~n", [Headers]),
	F =
	fun({Header, _Value}) ->
			binstr:to_lower(Header) =:= binstr:to_lower(Needle)
	end,
	case lists:filter(F, Headers) of
		% TODO if there's duplicate headers, should we use the first or the last?
		[{_Header, Value}|_T] ->
			Value;
		_ ->
			Default
	end.

-spec(get_header_value/2 :: (Needle :: binary(), Headers :: [{binary(), binary()}]) -> binary() | 'undefined').
%% @doc Do a case-insensitive header lookup to return the header's value, or `undefined'.
get_header_value(Needle, Headers) ->
	get_header_value(Needle, Headers, undefined).

-spec parse_with_comments(Value :: binary()) -> binary() | no_return();
	(Value :: atom()) -> atom().
parse_with_comments(Value) when is_binary(Value) ->
	parse_with_comments(Value, [], 0, false);
parse_with_comments(Value) ->
	Value.

-spec parse_with_comments(Value :: binary(), Acc :: list(), Depth :: non_neg_integer(), Quotes :: boolean()) -> binary() | no_return().
parse_with_comments(<<>>, _Acc, _Depth, Quotes) when Quotes ->
	erlang:error(unterminated_quotes);
parse_with_comments(<<>>, _Acc, Depth, _Quotes) when Depth > 0 ->
	erlang:error(unterminated_comment);
parse_with_comments(<<>>, Acc, _Depth, _Quotes) ->
	binstr:strip(list_to_binary(lists:reverse(Acc)));
parse_with_comments(<<$\\, H, Tail/binary>>, Acc, Depth, Quotes) when Depth > 0, H > 32, H < 127 ->
	parse_with_comments(Tail, Acc, Depth, Quotes);
parse_with_comments(<<$\\, Tail/binary>>, Acc, Depth, Quotes) when Depth > 0 ->
	parse_with_comments(Tail, Acc, Depth, Quotes);
parse_with_comments(<<$\\, H, Tail/binary>>, Acc, Depth, Quotes) when H > 32, H < 127 ->
	parse_with_comments(Tail, [H | Acc], Depth, Quotes);
parse_with_comments(<<$\\, Tail/binary>>, Acc, Depth, Quotes) ->
	parse_with_comments(Tail, [$\\ | Acc], Depth, Quotes);
parse_with_comments(<<$(, Tail/binary>>, Acc, Depth, Quotes) when not Quotes ->
	parse_with_comments(Tail, Acc, Depth + 1, Quotes);
parse_with_comments(<<$), Tail/binary>>, Acc, Depth, Quotes) when Depth > 0, not Quotes ->
	parse_with_comments(Tail, Acc, Depth - 1, Quotes);
parse_with_comments(<<_, Tail/binary>>, Acc, Depth, Quotes) when Depth > 0 ->
	parse_with_comments(Tail, Acc, Depth, Quotes);
parse_with_comments(<<$", T/binary>>, Acc, Depth, true) -> %"
	parse_with_comments(T, Acc, Depth, false);
parse_with_comments(<<$", T/binary>>, Acc, Depth, false) -> %"
	parse_with_comments(T, Acc, Depth, true);
parse_with_comments(<<H, Tail/binary>>, Acc, Depth, Quotes) ->
	parse_with_comments(Tail, [H | Acc], Depth, Quotes).

-spec(parse_content_type/1 :: (Value :: 'undefined') -> 'undefined';
	(Value :: binary()) -> {binary(), binary(), [{binary(), binary()}]}).
parse_content_type(undefined) ->
	undefined;
parse_content_type(String) ->
	try parse_content_disposition(String) of
		{RawType, Parameters} ->
			case binstr:strchr(RawType, $/) of
				Index when Index < 2 ->
					throw(bad_content_type);
				Index ->
					Type = binstr:substr(RawType, 1, Index - 1),
					SubType = binstr:substr(RawType, Index + 1),
					{binstr:to_lower(Type), binstr:to_lower(SubType), Parameters}
			end
		catch
			bad_disposition ->
				throw(bad_content_type)
	end.

-spec(parse_content_disposition/1 :: (Value :: 'undefined') -> 'undefined';
	(String :: binary()) -> {binary(), [{binary(), binary()}]}).
parse_content_disposition(undefined) ->
	undefined;
parse_content_disposition(String) ->
	[Disposition | Parameters] = binstr:split(parse_with_comments(String), <<";">>),
	F =
	fun(X) ->
		Y = binstr:strip(binstr:strip(X), both, $\t),
		case binstr:strchr(Y, $=) of
			Index when Index < 2 ->
				throw(bad_disposition);
			Index ->
				Key = binstr:substr(Y, 1, Index - 1),
				Value = binstr:substr(Y, Index + 1),
				{binstr:to_lower(Key), Value}
		end
	end,
	Params = lists:map(F, Parameters),
	{binstr:to_lower(Disposition), Params}.

split_body_by_boundary(Body, Boundary, MimeVsn, Options) ->
	% find the indices of the first and last boundary
	case [binstr:strpos(Body, Boundary), binstr:strpos(Body, list_to_binary([Boundary, "--"]))] of
		[0, _] ->
			erlang:error(missing_boundary);
		[_, 0] ->
			erlang:error(missing_last_boundary);
		[Start, End] ->
			NewBody = binstr:substr(Body, Start + byte_size(Boundary), End - Start),
			% from now on, we can be sure that each boundary is preceeded by a CRLF
			Parts = split_body_by_boundary_(NewBody, list_to_binary(["\r\n", Boundary]), [], Options),
			[decode_component(Headers, Body2, MimeVsn, Options) || {Headers, Body2} <- [V || {_, Body3} = V <- Parts, byte_size(Body3) =/= 0]]
		end.

split_body_by_boundary_(<<>>, _Boundary, Acc, _Options) ->
	lists:reverse(Acc);
split_body_by_boundary_(Body, Boundary, Acc, Options) ->
	% trim the incomplete first line
	TrimmedBody = binstr:substr(Body, binstr:strpos(Body, "\r\n") + 2),
	case binstr:strpos(TrimmedBody, Boundary) of
		0 ->
			lists:reverse([{[], TrimmedBody} | Acc]);
		Index ->
			{ParsedHdrs, BodyRest} = parse_headers(binstr:substr(TrimmedBody, 1, Index - 1)),
			DecodedHdrs = decode_headers(ParsedHdrs, [], proplists:get_value(encoding, Options, none)),
			split_body_by_boundary_(binstr:substr(TrimmedBody, Index + byte_size(Boundary)), Boundary,
									[{DecodedHdrs, BodyRest} | Acc], Options)
	end.

-spec(parse_headers/1 :: (Body :: binary()) -> {[{binary(), binary()}], binary()}).
%% @doc Parse the headers off of a message and return a list of headers and the trailing body.
parse_headers(Body) ->
	case binstr:strpos(Body, "\r\n") of
		0 ->
			{[], Body};
		1 ->
			{[], binstr:substr(Body, 3)};
		Index ->
			parse_headers(binstr:substr(Body, Index+2), binstr:substr(Body, 1, Index - 1), [])
	end.


parse_headers(Body, <<H, Tail/binary>>, []) when H =:= $\s; H =:= $\t ->
	% folded headers
	{[], list_to_binary([H, Tail, "\r\n", Body])};
parse_headers(Body, <<H, T/binary>>, Headers) when H =:= $\s; H =:= $\t ->
	% folded headers
	[{FieldName, OldFieldValue} | OtherHeaders] = Headers,
	FieldValue = list_to_binary([OldFieldValue, T]),
	%io:format("~p = ~p~n", [FieldName, FieldValue]),
	case binstr:strpos(Body, "\r\n") of
		0 ->
			{lists:reverse([{FieldName, FieldValue} | OtherHeaders]), Body};
		1 ->
			{lists:reverse([{FieldName, FieldValue} | OtherHeaders]), binstr:substr(Body, 3)};
		Index2 ->
			parse_headers(binstr:substr(Body, Index2 + 2), binstr:substr(Body, 1, Index2 - 1), [{FieldName, FieldValue} | OtherHeaders])
	end;
parse_headers(Body, Line, Headers) ->
	%io:format("line: ~p, nextpart ~p~n", [Line, binstr:substr(Body, 1, 10)]),
	case binstr:strchr(Line, $:) of
		0 ->
			{lists:reverse(Headers), list_to_binary([Line, "\r\n", Body])};
		Index ->
			FieldName = binstr:substr(Line, 1, Index - 1),
			F = fun(X) -> X > 32 andalso X < 127 end,
			case binstr:all(F, FieldName) of
				true ->
					F2 = fun(X) -> (X > 31 andalso X < 127) orelse X == 9 end,
					FValue = binstr:strip(binstr:substr(Line, Index+1)),
					FieldValue = case binstr:all(F2, FValue) of
						true ->
							FValue;
						_ ->
							% I couldn't figure out how to use a pure binary comprehension here :(
							list_to_binary([ filter_non_ascii(C) || <<C:8>> <= FValue])
					end,
					case binstr:strpos(Body, "\r\n") of
						0 ->
							{lists:reverse([{FieldName, FieldValue} | Headers]), Body};
						1 ->
							{lists:reverse([{FieldName, FieldValue} | Headers]), binstr:substr(Body, 3)};
						Index2 ->
							parse_headers(binstr:substr(Body, Index2 + 2), binstr:substr(Body, 1, Index2 - 1), [{FieldName, FieldValue} | Headers])
					end;
				false ->
					{lists:reverse(Headers), list_to_binary([Line, "\r\n", Body])}
			end
	end.

filter_non_ascii(C) when (C > 31 andalso C < 127); C == 9 ->
	<<C>>;
filter_non_ascii(_C) ->
	<<"?">>.

decode_body(Type, Body, _InEncoding, none) ->
	decode_body(Type, << <<X/integer>> || <<X>> <= Body, X < 128 >>);
decode_body(Type, Body, undefined, _OutEncoding) ->
	decode_body(Type, << <<X/integer>> || <<X>> <= Body, X < 128 >>);
decode_body(Type, Body, InEncoding, OutEncoding) ->
	NewBody = decode_body(Type, Body),
	InEncodingFixed = fix_encoding(InEncoding),
	unicode:characters_to_binary(NewBody, InEncodingFixed, OutEncoding).
	%CD = case iconv:open(OutEncoding, InEncodingFixed) of
	%	{ok, Res} -> Res;
	%	{error, einval} -> throw({bad_charset, InEncodingFixed})
	%end,
	%{ok, Result} = iconv:conv(CD, NewBody),
	%iconv:close(CD),
	%Result.

-spec(decode_body/2 :: (Type :: binary() | 'undefined', Body :: binary()) -> binary()).
decode_body(undefined, Body) ->
	Body;
decode_body(Type, Body) ->
	case binstr:to_lower(Type) of
		<<"quoted-printable">> ->
			decode_quoted_printable(Body);
		<<"base64">> ->
			decode_base64(Body);
		_Other ->
			Body
	end.

decode_base64(Body) ->
	base64:mime_decode(Body).

decode_quoted_printable(Body) ->
	case binstr:strpos(Body, "\r\n") of
		0 ->
			decode_quoted_printable(Body, <<>>, []);
		Index ->
			decode_quoted_printable(binstr:substr(Body, 1, Index +1), binstr:substr(Body, Index + 2), [])
	end.

decode_quoted_printable(<<>>, <<>>, Acc) ->
	list_to_binary(lists:reverse(Acc));
decode_quoted_printable(Line, Rest, Acc) ->
	case binstr:strpos(Rest, "\r\n") of
		0 ->
			decode_quoted_printable(Rest, <<>>, [decode_quoted_printable_line(Line, []) | Acc]);
		Index ->
			%io:format("next line ~p~nnext rest ~p~n", [binstr:substr(Rest, 1, Index +1), binstr:substr(Rest, Index + 2)]),
			decode_quoted_printable(binstr:substr(Rest, 1, Index +1), binstr:substr(Rest, Index + 2),
				[decode_quoted_printable_line(Line, []) | Acc])
	end.

decode_quoted_printable_line(<<>>, Acc) ->
	lists:reverse(Acc);
decode_quoted_printable_line(<<$\r, $\n>>, Acc) ->
	lists:reverse(["\r\n" | Acc]);
decode_quoted_printable_line(<<$=, C, T/binary>>, Acc) when C =:= $\s; C =:= $\t ->
	case binstr:all(fun(X) -> X =:= $\s orelse X =:= $\t end, T) of
		true ->
			lists:reverse(Acc);
		false ->
			throw(badchar)
	end;
decode_quoted_printable_line(<<$=, $\r, $\n>>, Acc) ->
	lists:reverse(Acc);
decode_quoted_printable_line(<<$=, A:2/binary, T/binary>>, Acc) ->
	%<<X:1/binary, Y:1/binary>> = A,
	case binstr:all(fun(C) -> (C >= $0 andalso C =< $9) orelse (C >= $A andalso C =< $F) orelse (C >= $a andalso C =< $f) end, A) of
		true ->
			{ok, [C | []], []} = io_lib:fread("~16u", binary_to_list(A)),
			decode_quoted_printable_line(T, [C | Acc]);
		false ->
			throw(badchar)
	end;
decode_quoted_printable_line(<<$=>>, Acc) ->
	% soft newline
	lists:reverse(Acc);
decode_quoted_printable_line(<<H, T/binary>>, Acc) when H >= $!, H =< $< ->
	decode_quoted_printable_line(T, [H | Acc]);
decode_quoted_printable_line(<<H, T/binary>>, Acc) when H >= $>, H =< $~ ->
	decode_quoted_printable_line(T, [H | Acc]);
decode_quoted_printable_line(<<H, T/binary>>, Acc) when H =:= $\s; H =:= $\t ->
	% if the rest of the line is whitespace, truncate it
	case binstr:all(fun(X) -> X =:= $\s orelse X =:= $\t end, T) of
		true ->
			lists:reverse(Acc);
		false ->
			decode_quoted_printable_line(T, [H | Acc])
	end;
decode_quoted_printable_line(<<H, T/binary>>, Acc) ->
	decode_quoted_printable_line(T, [H| Acc]).

check_headers(Headers) ->
	Checked = [<<"MIME-Version">>, <<"Date">>, <<"From">>, <<"Message-ID">>, <<"References">>, <<"Subject">>],
	check_headers(Checked, lists:reverse(Headers)).

check_headers([], Headers) ->
	lists:reverse(Headers);
check_headers([Header | Tail], Headers) ->
	case get_header_value(Header, Headers) of
		undefined when Header == <<"MIME-Version">> ->
			check_headers(Tail, [{<<"MIME-Version">>, <<"1.0">>} | Headers]);
		undefined when Header == <<"Date">> ->
			check_headers(Tail, [{<<"Date">>, list_to_binary(smtp_util:rfc5322_timestamp())} | Headers]);
		undefined when Header == <<"From">> ->
			erlang:error(missing_from);
		undefined when Header == <<"Message-ID">> ->
			check_headers(Tail, [{<<"Message-ID">>, list_to_binary(smtp_util:generate_message_id())} | Headers]);
		undefined when Header == <<"References">> ->
			case get_header_value(<<"In-Reply-To">>, Headers) of
				undefined ->
					check_headers(Tail, Headers); % ok, whatever
				ReplyID ->
					check_headers(Tail, [{<<"References">>, ReplyID} | Headers])
			end;
		References when Header == <<"References">> ->
			% check if the in-reply-to header, if present, is in references
			case get_header_value(<<"In-Reply-To">>, Headers) of
				undefined ->
					check_headers(Tail, Headers); % ok, whatever
				ReplyID ->
					case binstr:strpos(binstr:to_lower(References), binstr:to_lower(ReplyID)) of
						0 ->
							% okay, tack on the reply-to to the end of References
							check_headers(Tail, [{<<"References">>, list_to_binary([References, " ", ReplyID])} | proplists:delete(<<"References">>, Headers)]);
						_Index ->
							check_headers(Tail, Headers) % nothing to do
					end
				end;
		_ ->
			check_headers(Tail, Headers)
	end.

ensure_content_headers(Type, SubType, Parameters, Headers, Body, Toplevel) ->
	CheckHeaders = [<<"Content-Type">>, <<"Content-Disposition">>, <<"Content-Transfer-Encoding">>],
	ensure_content_headers(CheckHeaders, Type, SubType, Parameters, lists:reverse(Headers), Body, Toplevel).

ensure_content_headers([], _, _, Parameters, Headers, _, _) ->
	{Parameters, lists:reverse(Headers)};
ensure_content_headers([Header | Tail], Type, SubType, Parameters, Headers, Body, Toplevel) ->
	case get_header_value(Header, Headers) of
		undefined when Header == <<"Content-Type">>, ((Type == <<"text">> andalso SubType =/= <<"plain">>) orelse Type =/= <<"text">>) ->
			% no content-type header, and its not text/plain
			CT = io_lib:format("~s/~s", [Type, SubType]),
			CTP = case Type of
				<<"multipart">> ->
					Boundary = case proplists:get_value(<<"boundary">>, proplists:get_value(<<"content-type-params">>, Parameters, [])) of
						undefined ->
							list_to_binary(smtp_util:generate_message_boundary());
						B ->
							B
					end,
					[{<<"boundary">>, Boundary} | proplists:delete(<<"boundary">>, proplists:get_value(<<"content-type-params">>, Parameters, []))];
				<<"text">> ->
					Charset = case proplists:get_value(<<"charset">>, proplists:get_value(<<"content-type-params">>, Parameters, [])) of
						undefined ->
							guess_charset(Body);
						C ->
							C
					end,
					[{<<"charset">>, Charset} | proplists:delete(<<"charset">>, proplists:get_value(<<"content-type-params">>, Parameters, []))];
				_ ->
					proplists:get_value(<<"content-type-params">>, Parameters, [])
			end,

			%CTP = proplists:get_value(<<"content-type-params">>, Parameters, [guess_charset(Body)]),
			CTH = binstr:join([CT | encode_parameters(CTP)], ";"),
			NewParameters = [{<<"content-type-params">>, CTP} | proplists:delete(<<"content-type-params">>, Parameters)],
			ensure_content_headers(Tail, Type, SubType, NewParameters, [{<<"Content-Type">>, CTH} | Headers], Body, Toplevel);
		undefined when Header == <<"Content-Type">> ->
			% no content-type header and its text/plain
			Charset = case proplists:get_value(<<"charset">>, proplists:get_value(<<"content-type-params">>, Parameters, [])) of
				undefined ->
					guess_charset(Body);
				C ->
					C
			end,
			case Charset of
				<<"us-ascii">> ->
					% the default
					ensure_content_headers(Tail, Type, SubType, Parameters, Headers, Body, Toplevel);
				_ ->
					CTP = [{<<"charset">>, Charset} | proplists:delete(<<"charset">>, proplists:get_value(<<"content-type-params">>, Parameters, []))],
					CTH = binstr:join([<<"text/plain">> | encode_parameters(CTP)], ";"),
					NewParameters = [{<<"content-type-params">>, CTP} | proplists:delete(<<"content-type-params">>, Parameters)],
					ensure_content_headers(Tail, Type, SubType, NewParameters, [{<<"Content-Type">>, CTH} | Headers], Body, Toplevel)
			end;
		undefined when Header == <<"Content-Transfer-Encoding">>, Type =/= <<"multipart">> ->
			Enc = case proplists:get_value(<<"transfer-encoding">>, Parameters) of
				undefined ->
					guess_best_encoding(Body);
				Value ->
					Value
			end,
			case Enc of
				<<"7bit">> ->
					ensure_content_headers(Tail, Type, SubType, Parameters, Headers, Body, Toplevel);
				_ ->
					ensure_content_headers(Tail, Type, SubType, Parameters, [{<<"Content-Transfer-Encoding">>, Enc} | Headers], Body, Toplevel)
			end;
		undefined when Header == <<"Content-Disposition">>, Toplevel == false ->
			CD = proplists:get_value(<<"disposition">>, Parameters, <<"inline">>),
			CDP = proplists:get_value(<<"disposition-params">>, Parameters, []),
			CDH = binstr:join([CD | encode_parameters(CDP)], ";"),
			ensure_content_headers(Tail, Type, SubType, Parameters, [{<<"Content-Disposition">>, CDH} | Headers], Body, Toplevel);
		_ ->
			ensure_content_headers(Tail, Type, SubType, Parameters, Headers, Body, Toplevel)
	end.

-spec guess_charset(Body :: binary()) -> atom().
guess_charset(Body) ->
	case binstr:all(fun(X) -> X < 128 end, Body) of
		true -> latin1;
		false -> unicode
	end.

guess_best_encoding(<<Body:200/binary, Rest/binary>>) when Rest =/= <<>> ->
	guess_best_encoding(Body);
guess_best_encoding(Body) ->
	Size = byte_size(Body),
	% get only the allowed ascii characters
	% TODO - this might not be the complete list
	FilteredSize = length([X || <<X>> <= Body, ((X > 31 andalso X < 127) orelse X == $\r orelse X == $\n)]),

	Percent = round((FilteredSize / Size) * 100),

	%based on the % of printable characters, choose an encoding
	if
		Percent == 100 ->
			<<"7bit">>;
		Percent > 80 ->
			<<"quoted-printable">>;
		true ->
			<<"base64">>
	end.

encode_parameters([[]]) ->
	[];
encode_parameters(Parameters) ->
	[encode_parameter(Parameter) || Parameter <- Parameters].

encode_parameter({X, Y}) ->
	case escape_tspecial(Y, false, <<>>) of
		{true, Special} -> [X, $=, $", Special, $"];
		false -> [X, $=, Y]
	end.

% See also: http://www.ietf.org/rfc/rfc2045.txt section 5.1
escape_tspecial(<<>>, false, _Acc) ->
	false;
escape_tspecial(<<>>, IsSpecial, Acc) ->
	{IsSpecial, Acc};
escape_tspecial(<<C, Rest/binary>>, _IsSpecial, Acc) when C =:= $" ->
	escape_tspecial(Rest, true, <<Acc/binary, $\\, $">>);
escape_tspecial(<<C, Rest/binary>>, _IsSpecial, Acc) when C =:= $\\ ->
	escape_tspecial(Rest, true, <<Acc/binary, $\\, $\\>>);
escape_tspecial(<<C, Rest/binary>>, _IsSpecial, Acc)
	when C =:= $(; C =:= $); C =:= $<; C =:= $>; C =:= $@;
		C =:= $,; C =:= $;; C =:= $:; C =:= $/; C =:= $[;
		C =:= $]; C =:= $?; C =:= $=; C =:= $\s ->
	escape_tspecial(Rest, true, <<Acc/binary, C>>);
escape_tspecial(<<C, Rest/binary>>, IsSpecial, Acc) ->
	escape_tspecial(Rest, IsSpecial, <<Acc/binary, C>>).

encode_headers([]) ->
	[];
encode_headers([{Key, Value}|T] = _Headers) ->
    EncodedHeader = encode_folded_header(list_to_binary([Key,": ",encode_header_value(Key, Value)]), <<>>),
	[EncodedHeader | encode_headers(T)].

encode_folded_header(Rest, Acc) ->
	case binstr:split(Rest, <<$;>>, 2) of
		[_] ->
			<<Acc/binary, Rest/binary>>;
		[Before, After] ->
			NewPart = case After of
				<<$\t,_Rest/binary>> ->
					<<Before/binary, ";\r\n">>;
				_ ->
					<<Before/binary, ";\r\n\t">>
			end,
            encode_folded_header(After, <<Acc/binary, NewPart/binary>>)
	end.

encode_header_value(H, Value) when H =:= <<"To">>; H =:= <<"Cc">>; H =:= <<"Bcc">>;
								   H =:= <<"Reply-To">>; H =:= <<"From">> ->
	{ok, Addresses} = smtp_util:parse_rfc822_addresses(Value),
	{Names, Emails} = lists:unzip(Addresses),
	NewNames = lists:map(fun rfc2047_utf8_encode/1, Names),
	smtp_util:combine_rfc822_addresses(lists:zip(NewNames, Emails));

encode_header_value(_, Value) ->
	rfc2047_utf8_encode(Value).

encode_component(_Type, _SubType, Headers, Params, Body) ->
	if
		is_list(Body) -> % is this a multipart component?
			Boundary = proplists:get_value(<<"boundary">>, proplists:get_value(<<"content-type-params">>, Params)),
			[<<>>] ++  % blank line before start of component
			lists:flatmap(
				fun(Part) ->
						[list_to_binary([<<"--">>, Boundary])] ++ % start with the boundary
						encode_component_part(Part)
				end,
				Body
			) ++ [list_to_binary([<<"--">>, Boundary, <<"--">>])] % final boundary (with /--$/)
			  ++ [<<>>]; % blank line at the end of the multipart component
		true -> % or an inline component?
			%encode_component_part({Type, SubType, Headers, Params, Body})
			encode_body(
					get_header_value(<<"Content-Transfer-Encoding">>, Headers),
					[Body]
			 )
	end.

encode_component_part(Part) ->
	case Part of
		{<<"multipart">>, SubType, Headers, PartParams, Body} ->
			{FixedParams, FixedHeaders} = ensure_content_headers(<<"multipart">>, SubType, PartParams, Headers, Body, false),
			encode_headers(FixedHeaders) ++ [<<>>] ++
			encode_component(<<"multipart">>, SubType, FixedHeaders, FixedParams, Body);
		{Type, SubType, Headers, PartParams, Body} ->
			PartData = case Body of
				{_,_,_,_,_} -> encode_component_part(Body);
				String      -> [String]
			end,
			{_FixedParams, FixedHeaders} = ensure_content_headers(Type, SubType, PartParams, Headers, Body, false),
			encode_headers(FixedHeaders) ++ [<<>>] ++
			encode_body(
					get_header_value(<<"Content-Transfer-Encoding">>, FixedHeaders),
					PartData
			 );
		_ ->
			io:format("encode_component_part couldn't match Part to: ~p~n", [Part]),
			[]
	end.

encode_body(undefined, Body) ->
	Body;
encode_body(Type, Body) ->
	case binstr:to_lower(Type) of
		<<"quoted-printable">> ->
			[InnerBody] = Body,
			encode_quoted_printable(InnerBody);
		<<"base64">> ->
			[InnerBody] = Body,
			wrap_to_76(base64:encode(InnerBody));
		_ -> Body
	end.

wrap_to_76(String) ->
	[wrap_to_76(String, [])].

wrap_to_76(<<>>, Acc) ->
	list_to_binary(lists:reverse(Acc));
wrap_to_76(<<Head:76/binary, Tail/binary>>, Acc) ->
	wrap_to_76(Tail, [<<"\r\n">>, Head | Acc]);
wrap_to_76(Head, Acc) ->
	list_to_binary(lists:reverse([<<"\r\n">>, Head | Acc])).

encode_quoted_printable(Body) ->
	[encode_quoted_printable(Body, [], 0)].

encode_quoted_printable(Body, Acc, L) when L >= 75 ->
	LastLine = case string:str(Acc, "\n") of
		0 ->
			Acc;
		Index ->
			string:substr(Acc, 1, Index-1)
	end,
	%Len = length(LastLine),
	case string:str(LastLine, " ") of
		0 when L =:= 75 ->
			% uh-oh, no convienient whitespace, just cram a soft newline in
			encode_quoted_printable(Body, [$\n, $\r, $= | Acc], 0);
		1 when L =:= 75 ->
			% whitespace is the last character we wrote
			encode_quoted_printable(Body, [$\n, $\r, $= | Acc], 0);
		SIndex when (L - 75) < SIndex ->
			% okay, we can safely stick some whitespace in
			Prefix = string:substr(Acc, 1, SIndex-1),
			Suffix = string:substr(Acc, SIndex),
			NewAcc = lists:concat([Prefix, "\n\r=", Suffix]),
			encode_quoted_printable(Body, NewAcc, 0);
		_ ->
			% worst case, we're over 75 characters on the line
			% and there's no obvious break points, just stick one
			% in at position 75 and call it good. However, we have
			% to be very careful not to stick the soft newline in
			% the middle of an existing quoted-printable escape.

			% TODO - fix this to be less stupid
			I = 3, % assume we're at most 3 over our cutoff
			Prefix = string:substr(Acc, 1, I),
			Suffix = string:substr(Acc, I+1),
			NewAcc = lists:concat([Prefix, "\n\r=", Suffix]),
			encode_quoted_printable(Body, NewAcc, 0)
	end;
encode_quoted_printable(<<>>, Acc, _L) ->
	list_to_binary(lists:reverse(Acc));
encode_quoted_printable(<<$=, T/binary>> , Acc, L) ->
	encode_quoted_printable(T, [$D, $3, $= | Acc], L+3);
encode_quoted_printable(<<$\r, $\n, T/binary>> , Acc, _L) ->
	encode_quoted_printable(T, [$\n, $\r | Acc], 0);
encode_quoted_printable(<<H, T/binary>>, Acc, L) when H >= $!, H =< $< ->
	encode_quoted_printable(T, [H | Acc], L+1);
encode_quoted_printable(<<H, T/binary>>, Acc, L) when H >= $>, H =< $~ ->
	encode_quoted_printable(T, [H | Acc], L+1);
encode_quoted_printable(<<H, $\r, $\n, T/binary>>, Acc, _L) when H == $\s; H == $\t ->
	[[A, B]] = io_lib:format("~2.16.0B", [H]),
	encode_quoted_printable(T, [$\n, $\r, B, A, $= | Acc], 0);
encode_quoted_printable(<<H, T/binary>>, Acc, L) when H == $\s; H == $\t ->
	encode_quoted_printable(T, [H | Acc], L+1);
encode_quoted_printable(<<H, T/binary>>, Acc, L) ->
	[[A, B]] = io_lib:format("~2.16.0B", [H]),
	encode_quoted_printable(T, [B, A, $= | Acc], L+3).

get_default_encoding() ->
	unicode.

% convert some common invalid character names into the correct ones
fix_encoding(Encoding) when Encoding == <<"utf8">>; Encoding == <<"UTF8">>; Encoding == <<"utf-8">>; Encoding == <<"UTF-8">> ->
	unicode;
fix_encoding(Encoding) ->
	Encoding.


%% @doc Encode a binary or list according to RFC 2047. Input is
%% assumed to be in UTF-8 encoding.
rfc2047_utf8_encode(undefined) -> undefined;
rfc2047_utf8_encode(B) when is_binary(B) ->
	rfc2047_utf8_encode(binary_to_list(B));
rfc2047_utf8_encode([]) -> 
	[];
rfc2047_utf8_encode(Text) ->
    rfc2047_utf8_encode(Text, Text).

%% Don't escape when all characters are ASCII printable
rfc2047_utf8_encode([], Text) ->
    Text;
rfc2047_utf8_encode([H|T], Text) when H >= 32 andalso H =< 126 ->
    rfc2047_utf8_encode(T, Text);
rfc2047_utf8_encode(_, Text) ->
    "=?UTF-8?Q?" ++ rfc2047_utf8_encode(Text, [], 0) ++ "?=".

rfc2047_utf8_encode([], Acc, _WordLen) ->
    lists:reverse(Acc);
rfc2047_utf8_encode(T, Acc, WordLen) when WordLen >= 55 ->
    %% Make sure that the individual encoded words are not longer than 76 chars (including charset etc)
    rfc2047_utf8_encode(T, [$?,$Q,$?,$8,$-,$F,$T,$U,$?,$=,$\ ,$\n,$\r,$=,$?|Acc], 0);
rfc2047_utf8_encode([C|T], Acc, WordLen) when C > 32 andalso C < 127 andalso C /= 32 
    andalso C /= $? andalso C /= $_ andalso C /= $= andalso C /= $. ->
    rfc2047_utf8_encode(T, [C|Acc], WordLen+1);
rfc2047_utf8_encode([C|T], Acc, WordLen) ->
    rfc2047_utf8_encode(T, [hex(C rem 16), hex(C div 16), $= | Acc], WordLen+3).

hex(N) when N >= 10 -> N + $A - 10;
hex(N) -> N + $0.


%% @doc
%% DKIM sign functions
%% RFC 6376
%% `h' - list of headers to sign (lowercased binary)
%% `c' - {Headers, Body} canonicalization type. Only {simple, simple} and
%% {relaxed, simple} supported for now.
%% `s' `d' - if s = <<"foo.bar">> and d = <<"example.com">>, public key should
%% be located in "foo.bar._domainkey.example.com" (see RFC-6376 #3.6.2.1).
%% `t' - signature timestamp: 'now' or UTC {Date, Time}
%% `x' - signatue expiration time: UTC {Date, Time}
%% `private_key' - private key, to sign emails. May be of 2 types: encrypted and
%% plain in PEM format:
%% `{pem_plain, KeyBinary}' - generated by <code>openssl genrsa -out <out-file.pem> 1024<code>
%% `{pem_encrypted, KeyBinary, Password}' - generated by, eg
%%   <code>openssl genrsa -des3 -out <out-file.pem> 1024<code>. 3'rd paramerter is
%%   password to decrypt the key.
-spec dkim_sign_email([binary()], binary(), Options) -> binary()
																 when
	  Options:: [{h, [binary()]}
				 | {d, binary()}
				 | {s, binary()}
				 | {t, now | calendar:datetime()}
				 | {x, calendar:datetime()}
				 | {c, {simple|relaxed, simple|relaxed}}
				 | {private_key, PrivateKey}],
	  PrivateKey :: {pem_plain, binary()}
					| {pem_encrypted, Key::binary(), Passwd::string()}.
dkim_sign_email(Headers, Body, Opts) ->
	HeadersToSign = proplists:get_value(h, Opts, [<<"from">>, <<"to">>, <<"subject">>, <<"date">>]),
	SDID = proplists:get_value(d, Opts),
	Selector = proplists:get_value(s, Opts),
	%% BodyLength = proplists:get_value(l, Opts),
	OptionalTags = lists:foldl(fun(Key, Acc) ->
									   case proplists:get_value(Key, Opts) of
										   undefined -> Acc;
										   Value -> [{Key, Value} | Acc]
									   end
							   end, [], [t, x]),
	{HdrsCanT, BodyCanT} = Can = proplists:get_value(c, Opts, {relaxed, simple}),
	PrivateKey = proplists:get_value(private_key, Opts),

	%% hash body
	CanBody = dkim_canonicalize_body(Body, BodyCanT),
	BodyHash = dkim_hash_body(CanBody),
	Tags = [%% {b, <<>>},
			{v, 1}, {a, <<"rsa-sha256">>}, {bh, BodyHash}, {c, Can},
			{d, SDID}, {h, HeadersToSign}, {s, Selector} | OptionalTags],
	%% hash headers
	Headers1 = dkim_filter_headers(Headers, HeadersToSign),
	CanHeaders = dkim_canonicalize_headers(Headers1, HdrsCanT),
	[DkimHeaderNoB] = dkim_canonicalize_headers([dkim_make_header([{b, undefined} | Tags])], HdrsCanT),
	DataHash = dkim_hash_data(CanHeaders, DkimHeaderNoB),
	%% io:format("~s~n~n", [base64:encode(DataHash)]),
	%% sign
	Signature = dkim_sign(DataHash, PrivateKey),
	DkimHeader = dkim_make_header([{b, Signature} | Tags]),
	[DkimHeader | Headers].

dkim_filter_headers(Headers, HeadersToSign) ->
	KeyedHeaders = [begin
						[Name, _] = binary:split(Hdr, <<":">>),
						{binstr:strip(binstr:to_lower(Name)), Hdr}
					end || Hdr <- Headers],
	WithUndef = [get_header_value(binstr:to_lower(Name), KeyedHeaders) || Name <- HeadersToSign],
	[Hdr || Hdr <- WithUndef, Hdr =/= undefined].

dkim_canonicalize_headers(Headers, simple) ->
	Headers;
dkim_canonicalize_headers(Headers, relaxed) ->
	dkim_canonic_hdrs_relaxed(Headers).

dkim_canonic_hdrs_relaxed([Hdr | Rest]) ->
	[Name, Value] = binary:split(Hdr, <<":">>),
	LowStripName = binstr:to_lower(binstr:strip(Name)),

	UnfoldedHdrValue = binary:replace(Value, <<"\r\n">>, <<>>, [global]),
	SingleWSValue = re:replace(UnfoldedHdrValue, "[\t ]+", " ", [global, {return, binary}]),
	StrippedWithName = <<LowStripName/binary, ":", (binstr:strip(SingleWSValue))/binary>>,
	[StrippedWithName | dkim_canonic_hdrs_relaxed(Rest)];
dkim_canonic_hdrs_relaxed([]) -> [].


dkim_canonicalize_body(<<>>, simple) ->
	<<"\r\n">>;
dkim_canonicalize_body(Body, simple) ->
	re:replace(Body, "(\r\n)*$", "\r\n", [{return, binary}]);
dkim_canonicalize_body(_Body, relaxed) ->
	throw({not_supported, dkim_body_relaxed}).

dkim_hash_body(CanonicBody) ->
	crypto:hash(sha256, CanonicBody).
	%% crypto:sha256(CanonicBody).

%% RFC 5.5 & 3.7
dkim_hash_data(CanonicHeaders, DkimHeader) ->
	JoinedHeaders = << <<Hdr/binary, "\r\n">> || Hdr <- CanonicHeaders>>,
	crypto:hash(sha256, <<JoinedHeaders/binary, DkimHeader/binary>>).

dkim_sign(DataHash, {pem_plain, PrivBin}) ->
	[PrivEntry] = public_key:pem_decode(PrivBin),
	Key = public_key:pem_entry_decode(PrivEntry),
	public_key:sign({digest, DataHash}, sha256, Key);
dkim_sign(DataHash, {pem_encrypted, EncPrivBin, Passwd}) ->
	[EncPrivEntry] = public_key:pem_decode(EncPrivBin),
	Key = public_key:pem_entry_decode(EncPrivEntry, Passwd),
	public_key:sign({digest, DataHash}, sha256, Key).


dkim_make_header(Tags) ->
	RevTags = lists:reverse(Tags),				%so {b, ...} became last tag
	EncodedTags = binstr:join([dkim_encode_tag(K, V) || {K, V} <- RevTags], <<"; ">>),
	binstr:join(encode_headers([{<<"DKIM-Signature">>, EncodedTags}]), <<"\r\n">>).

%% RFC #3.5
dkim_encode_tag(v, 1) ->
	%% version
	<<"v=1">>;
dkim_encode_tag(a, <<"rsa-sha256">>) ->
	%% algorithm
	<<"a=rsa-sha256">>;
dkim_encode_tag(b, undefined) ->
	%% signature (when hashing with no digest)
	<<"b=">>;
dkim_encode_tag(b, V) ->
	%% signature
	B64Sign = base64:encode(V),
	<<"b=", B64Sign/binary>>;
dkim_encode_tag(bh, V) ->
	%% body hash
	B64Sign = base64:encode(V),
	<<"bh=", B64Sign/binary>>;
dkim_encode_tag(c, {Hdrs, simple}) ->	  % 'relaxed' for body not supported yet
	%% canonicalization type
	<<"c=", (atom_to_binary(Hdrs, utf8))/binary, "/simple">>;
dkim_encode_tag(d, Domain) ->
	%% SDID (domain)
	<<"d=", Domain/binary>>;
dkim_encode_tag(h, Hdrs) ->
	%% headers fields (case-insensitive, ":" separated)
	Joined = binstr:join([binstr:to_lower(H) || H <- Hdrs], <<":">>),
	<<"h=", Joined/binary>>;
dkim_encode_tag(i, V) ->
	%% AUID
	[QPValue] = dkim_qp_tag_value(V),
	<<"i=", QPValue/binary>>;
dkim_encode_tag(l, IntVal) ->
	%% body length count
	BinVal = list_to_binary(integer_to_list(IntVal)),
	<<"l=", (BinVal)/binary>>;
dkim_encode_tag(q, [<<"dns/txt">>]) ->
	%% query methods (':' separated)
	<<"q=dns/txt">>;
dkim_encode_tag(s, Selector) ->
	%% selector
	<<"s=", Selector/binary>>;
dkim_encode_tag(t, now) ->
	dkim_encode_tag(t, calendar:universal_time());
dkim_encode_tag(t, DateTime) ->
	%% timestamp
	BinTs = datetime_to_bin_timestamp(DateTime),
	<<"t=", BinTs/binary>>;
dkim_encode_tag(x, DateTime) ->
	%% signature expiration
	BinTs = datetime_to_bin_timestamp(DateTime),
	<<"x=", BinTs/binary>>;
%% dkim_encode_tag(z, Hdrs) ->
%%	   %% copied header fields
%%	   Joined = dkim_qp_tag_value(binstr:join([(H) || H <- Hdrs], <<"|">>)),
%%	   <<"z=", Joined/binary>>;
dkim_encode_tag(K, V) when is_binary(K), is_binary(V) ->
	<<K/binary, V/binary>>.

dkim_qp_tag_value(Value) ->
    %% XXX: this not fully satisfy #2.11
    [QPValue] = encode_quoted_printable(Value),
    binary:replace(QPValue, <<";">>, <<"=3B">>).

datetime_to_bin_timestamp(DateTime) ->
    EpochStart = 62167219200, % calendar:datetime_to_gregorian_seconds({{1970,1,1}, {0,0,0}})
    UnixTimestamp = calendar:datetime_to_gregorian_seconds(DateTime) - EpochStart,
    list_to_binary(integer_to_list(UnixTimestamp)).

%% /DKIM

