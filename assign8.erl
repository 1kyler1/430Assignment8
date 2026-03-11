%% assign8.erl

-module(assign8).
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").


%% ExprC Forms
%%   {str, Bin}
%%   {id, NameAtom}
%%   {app, FnExpr, ArgsExprs}
%%   {lam, ParamsAtoms, BodyExpr}
%%   {ifc, TestExpr, ThenExpr, ElseExpr}

numC(N) when is_number(N) -> {numC, N}.
strC(S) when is_list(S) -> {strC, unicode:characters_to_binary(S)};
strC(B) when is_binary(B) -> {strC, B}.
idC(A) when is_atom(A) -> {idC, A}.
appC(Fn, Args) when is_tuple(Fn), is_list(Args) -> {appC, Fn, Args}.
lamC(Params, Body) when is_list(Params), is_tuple(Body) -> {lamC, Params, Body}.
ifC(Test, Then, Else) when is_tuple(Test), is_tuple(Then), is_tuple(Else) -> {ifC, Test, Then, Else}.

%% Value Forms
%%   {numv, N}
%%   {boolv, true|false}
%%   {strv, Bin}
%%   {clov, ParamsAtoms, BodyExpr, Env}
%%   {primv, NameAtom, ArityNonNegInt, ImplFun}
%%
%% Env:
%%   [{atom(), Value}]  (association list, first match wins)

numV(N) when is_number(N) -> {numV, N}.
boolV(B) when is_boolean(B) -> {boolV, B}.
strV(S) when is_list(S) -> {strV, unicode:characters_to_binary(S)};
strV(B) when is_binary(B) -> {strV, B}.
cloV(Params, Body, Env) when is_list(Params), is_tuple(Body), is_list(Env) -> {cloV, Params, Body, Env}.
primV(Name, Arity, Impl) when is_atom(Name), is_integer(Arity), Arity >= 0, is_function(Impl) -> {primV, Name, Arity, Impl}.

%% ERRORS

interp_error(Ctx, Msg) -> error({szmx_interp_error, Ctx, Msg}).


%% lookup : atom() * Env -> Value | no_match
%% Look up the value of a variable in the environment.
lookup(Name, Env) when is_atom(Name), is_list(Env) ->
    case lists:keyfind(Name, 1, Env) of
        {Name, Val} -> Val;
        false -> interp_error(Name, io_lib:format("free identifier: ~p", [Name]))
    end.

%% extend-env : atom() * Value * Env -> Env
%% Extend the environment with a new variable binding.
extend_env(Params, Vals, Env)
    when is_list(Params), is_list(Vals), is_list(Env) ->
      case length(Params) =:= length(Vals) of
        true -> lists:zip(Params, Vals) ++ Env;
        false -> interp_error(Params, io_lib:format("Parameter and argument length mismatch: ~p vs ~p", [Params, Vals]))
      end.



%% Small environment unit tests (EUnit)

lookup_finds_test() ->
    Env = [{x, numV(42)}, {y, boolV(true)}],
    ?assertEqual(numV(42), lookup(x, Env)),
    ?assertEqual(boolV(true), lookup(y, Env)).

lookup_free_identifier_test() ->
    Env = [{x, numV(10)}],
    ?assertError({szmx_interp_error, _, _}, lookup(z, Env)).

extend_env_single_into_empty_test() ->
    Env0 = [],
    Env1 = extend_env([x], [numV(10)], Env0),
    ?assertEqual([{x, numV(10)}], Env1).

extend_env_multiple_into_empty_test() ->
    Env0 = [],
    Env1 = extend_env([x,y], [numV(1), numV(2)], Env0),
    ?assertEqual([{x, numV(1)}, {y, numV(2)}], Env1).

extend_env_shadows_old_test() ->
    Env0 = [{x, numV(99)}, {y, numV(3)}],
    Env1 = extend_env([x], [numV(5)], Env0),
    %% new x shadows old x
    ?assertEqual([{x, numV(5)}, {x, numV(99)}, {y, numV(3)}], Env1),
    ?assertEqual(numV(5), lookup(x, Env1)).

extend_env_arity_mismatch_more_params_test() ->
    Env0 = [],
    ?assertError({szmx_interp_error, _, _},
                 extend_env([x,y], [numV(1)], Env0)).

extend_env_arity_mismatch_more_vals_test() ->
    Env0 = [],
    ?assertError({szmx_interp_error, _, _},
                 extend_env([x], [numV(1), numV(2)], Env0)).


manual_ast_construction_test() ->
    NUM = numC(42),
    ?assertEqual({numC, 42}, NUM),

    STR = strC("hello"),
    ?assertEqual({strC, <<"hello">>}, STR),

    STR2 = strC(<<"world">>),
    ?assertEqual({strC, <<"world">>}, STR2),

    ID = idC(x),
    ?assertEqual({idC, x}, ID),

    APP = appC(idC('+'), [numC(1), numC(2)]),
    ?assertEqual({appC, {idC,'+'}, [{numC,1}, {numC,2}]}, APP),

    LAM = lamC([x], appC(idC('+'), [idC(x), numC(1)])),
    ?assertMatch({lamC, [x], _}, LAM),

    IF = ifC(appC(idC('>'), [idC(x), numC(0)]),
          strC("positive"),
          strC("non-positive")),
    ?assertMatch({ifC, _, _, _}, IF).

%%VALUE FORM TESTS
value_construction_test() ->
    NUMV = numV(3.14),
    ?assertEqual({numV, 3.14}, NUMV),

    BOOLV = boolV(false),
    ?assertEqual({boolV, false}, BOOLV),

    STRV = strV("test"),
    ?assertEqual({strV, <<"test">>}, STRV),

    STRV2 = strV(<<"data">>),
    ?assertEqual({strV, <<"data">>}, STRV2),

    CLOV = cloV([x], idC(x), []),
    ?assertMatch({cloV, [x], _, []}, CLOV),

    PRIMV = primV('add', 2, fun(A, B) -> A + B end),
    ?assertMatch({primV, 'add', 2, _}, PRIMV).