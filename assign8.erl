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

%% Part 3: The Interpreter

interp({numC, N}, _Env) when is_number(N) ->
    numV(N);
interp({strC, Bin}, _Env) when is_binary(Bin) ->
    strV(Bin);
interp({idC, Name}, Env) when is_atom(Name), is_list(Env) ->
    lookup(Name, Env);

interp({ifC, TestE, ThenE, ElseE}, Env) ->
    case interp(TestE, Env) of
        {boolV, true}  -> interp(ThenE, Env);
        {boolV, false} -> interp(ElseE, Env);
        V -> interp_error({ifC, TestE, ThenE, ElseE},
                          io_lib:format("if expects a boolean, got ~p", [V]))
    end;

interp({lamC, Params, Body}, Env) when is_list(Params), is_tuple(Body), is_list(Env) ->
    cloV(Params, Body, Env);

interp({appC, FnE, ArgEs}, Env) when is_tuple(FnE), is_list(ArgEs), is_list(Env) ->
    FnV = interp(FnE, Env),
    ArgVs = [interp(A, Env) || A <- ArgEs],
    apply_value(FnV, ArgVs, {appC, FnE, ArgEs});

interp(Expr, _Env) ->
    interp_error(Expr, io_lib:format("unknown expression form: ~p", [Expr])).

apply_value({primV, _Name, Arity, Impl}, Args, Ctx)
  when is_integer(Arity), Arity >= 0, is_function(Impl) ->
    case length(Args) =:= Arity of
        true  -> Impl(Args);
        false -> interp_error(Ctx, "wrong arity")
    end;
apply_value({cloV, Params, Body, CloEnv}, Args, Ctx)
  when is_list(Params), is_tuple(Body), is_list(CloEnv) ->
    case length(Params) =:= length(Args) of
        true  -> interp(Body, extend_env(Params, Args, CloEnv));
        false -> interp_error(Ctx, "wrong arity")
    end;
apply_value(NonFun, _Args, Ctx) ->
    interp_error(Ctx, io_lib:format("attempt to apply non-function: ~p", [NonFun])).

top_interp(Expr) ->
    serialize(interp(Expr, top_env())).

%% END OF PART 3

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

%% Primatives

%% expect_num
expect_num({numV, N}, _) ->
    N;
expect_num(V, Ctx) ->
    interp_error(Ctx,
        io_lib:format("expected a number, got ~p", [V])).

%% checks if nums, bools and stringd are euqal, if yes return true in not return false
value_equal({numV, A}, {numV, B}) -> A =:= B;
value_equal({boolV, A}, {boolV, B}) -> A =:= B;
value_equal({strV, A}, {strV, B}) -> A =:= B;
value_equal(_, _) -> false.

%% applys the primitive operations for each value and errors if the arguments are not correct
apply_prim(add, [A, B]) ->
    {numV, expect_num(A, add) + expect_num(B, add)};
apply_prim(sub, [A, B]) ->
    {numV, expect_num(A, sub) - expect_num(B, sub)};
apply_prim(mul, [A, B]) ->
    {numV, expect_num(A, mul) * expect_num(B, mul)};
apply_prim('div', [A, B]) ->
    Den = expect_num(B, 'div'),
    case Den of
        0 -> interp_error('div', "division by zero");
        _ -> {numV, expect_num(A, 'div') / Den}
    end;
apply_prim(leq, [A, B]) ->
    {boolV, expect_num(A, leq) =< expect_num(B, leq)};
apply_prim(equal, [A, B]) ->
    {boolV, value_equal(A, B)};
apply_prim(error, [{strV, Msg}]) ->
    error({user_error, Msg});
apply_prim(error, _) ->
    error({user_error, "error expects a string"});
apply_prim(Name, Args) ->
    interp_error(Name,
        io_lib:format("wrong arity or bad arguments: ~p", [Args])).

%% make_prim wrapper
make_prim(Name, Arity) ->
    primV(Name, Arity,
        fun(Args) ->
            case length(Args) =:= Arity of
                true -> apply_prim(Name, Args);
                false -> interp_error(Name, "wrong arity")
            end
        end).

%% Top-Level Environment
top_env() ->
    [
        {add,   make_prim(add, 2)},
        {sub,   make_prim(sub, 2)},
        {mul,   make_prim(mul, 2)},
        {'div', make_prim('div', 2)},
        {leq,   make_prim(leq, 2)},
        {equal, make_prim(equal, 2)},
        {error, make_prim(error, 1)},
        {true,  boolV(true)},
        {false, boolV(false)}
    ].

%% Serialization
serialize({numV, N}) ->
    lists:flatten(io_lib:format("~p", [N]));
serialize({boolV, true}) -> "true";
serialize({boolV, false}) -> "false";
serialize({strV, Bin}) when is_binary(Bin) ->
    lists:flatten(io_lib:format("\"~s\"", [binary_to_list(Bin)]));
serialize({cloV, _, _, _}) ->
    "#<procedure>";
serialize({primV, _, _, _}) ->
    "#<primop>".


%% EUnit Tests 

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

%% expect-num tests
expect_num_success_test() ->
    10 = expect_num(numV(10), test_context).

expect_num_failure_test() ->
    ?assertError(_, expect_num(boolV(true), test_context)).

%% value_equal tests
value_equal_numbers_test() ->
    true  = value_equal(numV(3), numV(3)),
    false = value_equal(numV(3), numV(4)).

value_equal_booleans_test() ->
    true  = value_equal(boolV(true), boolV(true)),
    false = value_equal(boolV(true), boolV(false)).

value_equal_strings_test() ->
    true  = value_equal(strV("hello"), strV("hello")),
    false = value_equal(strV("hello"), strV("world")).

value_equal_mixed_types_test() ->
    false = value_equal(numV(3), boolV(true)),
    false = value_equal(strV("3"), numV(3)),
    false = value_equal(cloV([], numC(1), []),
                        cloV([], numC(1), [])).

%% apply_prim tests
apply_prim_add_test() ->
    {numV, 3} = apply_prim(add, [numV(1), numV(2)]).

apply_prim_sub_test() ->
    {numV, 1} = apply_prim(sub, [numV(3), numV(2)]).

apply_prim_mul_test() ->
    {numV, 6} = apply_prim(mul, [numV(2), numV(3)]).

apply_prim_div_test() ->
    {numV, 2.0} = apply_prim('div', [numV(4), numV(2)]).

apply_prim_leq_test() ->
    {boolV, true}  = apply_prim(leq, [numV(2), numV(3)]),
    {boolV, false} = apply_prim(leq, [numV(5), numV(3)]).

apply_prim_equal_test() ->
    {boolV, true}  = apply_prim(equal, [numV(5), numV(5)]),
    {boolV, false} = apply_prim(equal, [numV(5), numV(6)]).

apply_prim_error_test() ->
    ?assertError(_, apply_prim(error, [strV("boom")])),
    ?assertError(_, apply_prim(error, [numV(10)])).

%% make_prim tests
make_prim_correct_arity_test() ->
    {primV, add, 2, Fun} = make_prim(add, 2),
    {numV, 7} = Fun([numV(3), numV(4)]).

make_prim_wrong_arity_test() ->
    {primV, add, 2, Fun} = make_prim(add, 2),
    ?assertError(_, Fun([numV(3)])).

%% top_env tests
top_env_contains_add_test() ->
    Env = top_env(),
    {add, {primV, add, 2, _}} = lists:keyfind(add, 1, Env).

top_env_contains_boolean_test() ->
    Env = top_env(),
    {true,  {boolV, true}}  = lists:keyfind(true, 1, Env),
    {false, {boolV, false}} = lists:keyfind(false, 1, Env).

%% serialize tests
serialize_number_test() ->
    "42" = serialize({numV, 42}).

serialize_boolean_test() ->
    "true"  = serialize({boolV, true}),
    "false" = serialize({boolV, false}).

serialize_string_test() ->
    "\"hello\"" = serialize(strV("hello")).

serialize_closure_test() ->
    "#<procedure>" = serialize(cloV([], numC(1), [])).

serialize_primitive_test() ->
    "#<primop>" = serialize(make_prim(add, 2)).
