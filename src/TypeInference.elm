module TypeInference exposing (inferTypes, inferTypesFreeFriendly, Inferrable, inferrableOne, inferrableBoth, inferrableTypesFreeFriendly)

import Dict exposing (Dict)
import Set exposing (Set)
import Tuple

import Expression exposing (Expression(..))
import Type exposing (Type(..), TypeError(..))
import TypeEnv exposing (TypeEnv)
import Scheme exposing (Scheme(..))
import Substitution exposing (Substitution)
import StateE exposing (StateE)
import Value


type alias Constraint = (Type, Type)


-- Generates a fresh type variable
fresh : StateE Int TypeError Type
fresh =
    StateE.bind (StateE.modify (\i -> i + 1)) <| \() ->
    StateE.map_ StateE.get <| \i ->
    TVariable ("a" ++ String.fromInt i)


-- Takes a list of variable names and associates each one with a fresh type variable
freshList : List String -> StateE Int TypeError (List (String, Type))
freshList list =
    case list of
        [] -> StateE.return []
        (x :: xs) ->
            StateE.bind fresh <| \i ->
            StateE.bind (freshList xs) <| \r ->
            StateE.return ((x, i) :: r)


generalise : TypeEnv -> Type -> Scheme
generalise env t =
    let vs = Set.diff (Type.freeTypeVariables t) (TypeEnv.freeTypeVariables env)
    in ForAll (Set.toList vs) t


instantiate : Scheme -> StateE Int TypeError Type
instantiate (ForAll names t) =
    let namesWithFresh l =
            case l of 
                [] -> StateE.return []
                (x :: xs) ->
                    StateE.bind fresh <| \f ->
                    StateE.map_ (namesWithFresh xs) <| \r ->
                    (x, f) :: r
    in
    (namesWithFresh names)
    |> StateE.map (\l -> Substitution.applyToType (Dict.fromList l) t)


makeConstraints : Expression () -> TypeEnv -> StateE Int TypeError (Expression Type, List Constraint)
makeConstraints expr bindings =
    let typeOf = Expression.getTag in -- TODO: Something better than this
    case expr of
        Constant c () -> StateE.return <| (Constant c (Value.typeOf c), [])
        Variable v () ->
            case Dict.get v bindings of
                Nothing -> StateE.return (Variable v (TInferenceError (UnboundVariable v)), [])
                Just scheme -> StateE.map_ (instantiate scheme) <| \t -> (Variable v t, [])
        FunctionCall f x () ->
            StateE.bind fresh <| \result ->
            StateE.bind (makeConstraints f bindings) <| \(f1, c1) ->
            StateE.map_ (makeConstraints x bindings) <| \(x1, c2) ->
            (FunctionCall f1 x1 result, (typeOf f1, TFunc (typeOf x1) result) :: c1 ++ c2)
        Lambda name () body () ->
            StateE.bind fresh <| \argType ->
            StateE.map_ (makeConstraints body (Dict.insert name (ForAll [] argType) bindings)) <| \(body1, c1) ->
            let ftype = TFunc argType (typeOf body1) in
            (Lambda name argType body1 ftype, c1)
        LetBind name () args x y () ->
            -- At the moment, let bindings aren't recursive
            StateE.bind fresh <| \returnType ->
            StateE.bind (freshList <| List.map Tuple.first args) <| \args1 ->
            let ftype = List.foldr TFunc returnType (List.map Tuple.second args1) in
            let boundArguments = Dict.fromList (List.map (Tuple.mapSecond (ForAll [])) args1) in
            StateE.bind (makeConstraints x (Dict.union boundArguments bindings)) <| \(x1, c1) ->
            case solveConstraints Substitution.empty ((returnType, typeOf x1) :: c1) of
                Err e ->
                    let yUnbound = Expression.mapTags (\() -> TUnbound) y in
                    StateE.return (LetBind name (TInferenceError e) args1 x1 yUnbound TUnbound, [])
                Ok subst ->
                    let scheme = generalise (Substitution.applyToEnv subst bindings) (Substitution.applyToType subst ftype) in
                    StateE.map_ (makeConstraints y (Dict.insert name scheme bindings)) <| \(y1, c2) ->
                    (LetBind name ftype args1 x1 y1 (typeOf y1), (returnType, typeOf x1) :: c1 ++ c2)
        And x y () ->
            StateE.bind (makeConstraints x bindings) <| \(x1, c1) ->
            StateE.map_ (makeConstraints y bindings) <| \(y1, c2) ->
            (And x1 y1 TBool, (typeOf x1, TBool) :: (typeOf y1, TBool) :: c1 ++ c2)
        Or x y () ->
            StateE.bind (makeConstraints x bindings) <| \(x1, c1) ->
            StateE.map_ (makeConstraints y bindings) <| \(y1, c2) ->
            (Or x1 y1 TBool, (typeOf x1, TBool) :: (typeOf y1, TBool) :: c1 ++ c2)
        Not x () ->
            StateE.map_ (makeConstraints x bindings) <| \(x1, c1) ->
            (Not x1 TBool, (typeOf x1, TBool) :: c1)
        Eq x y () ->
            StateE.bind (makeConstraints x bindings) <| \(x1, c1) ->
            StateE.map_ (makeConstraints y bindings) <| \(y1, c2) ->
            (Eq x1 y1 TBool, (typeOf x1, typeOf y1) :: c1 ++ c2)
        IfBranch x y z () ->
            StateE.bind (makeConstraints x bindings) <| \(x1, c1) ->
            StateE.bind (makeConstraints y bindings) <| \(y1, c2) ->
            StateE.map_ (makeConstraints z bindings) <| \(z1, c3) ->
            (IfBranch x1 y1 z1 (typeOf y1), (typeOf x1, TBool) :: (typeOf y1, typeOf z1) :: c1 ++ c2 ++ c3)


-- This seems pretty O(N^2)
solveConstraints : Substitution -> List Constraint -> Result TypeError Substitution
solveConstraints subst constraints =
    case constraints of
        [] -> Ok subst
        ((t1, t2) :: r) ->
            (unify t1 t2)
            |> Result.andThen (\su1 ->
                solveConstraints
                    (Substitution.compose su1 subst)
                    (List.map (\(u1, u2) -> (Substitution.applyToType su1 u1, Substitution.applyToType su1 u2)) r)
            )


inferTypes : Expression () -> Result TypeError (Expression Type)
inferTypes expression =
    StateE.runResult (makeConstraints expression TypeEnv.empty) 0
    |> Result.andThen (\(expressionWithTypeArgs, constraints) ->
        solveConstraints Substitution.empty constraints
        |> Result.map (\subst ->
            Expression.mapTags (\t -> Substitution.applyToType subst t)expressionWithTypeArgs))


inferTypesFreeFriendly : Expression () -> Result TypeError (Expression Type)
inferTypesFreeFriendly expression =
    let freeVars = Set.toList (Expression.freeVariables expression)
    in
    let makeConstraintsFreeFriendly =
            StateE.bind (freshList freeVars) <| \freeBounds ->
                let bounds =
                        freeBounds
                        |> List.map (\(variable, typeVariable) -> (variable, ForAll [] typeVariable))
                        |> Dict.fromList
                in makeConstraints expression bounds
    in
    StateE.runResult makeConstraintsFreeFriendly 0
    |> Result.andThen (\(expressionWithTypeArgs, constraints) ->
        solveConstraints Substitution.empty constraints
        |> Result.map (\subst ->
            Expression.mapTags (\t -> Substitution.applyToType subst t)expressionWithTypeArgs))


-- This is a type class, I think
type alias Inferrable a b =
    { freeVariables : a -> Set String
    , makeConstraints : a -> TypeEnv -> StateE Int TypeError (b, List Constraint)
    , applySubstitutions : b -> Substitution -> b
    }


inferrableOne : Inferrable (Expression ()) (Expression Type)
inferrableOne =
    { freeVariables = Expression.freeVariables
    , makeConstraints = makeConstraints
    , applySubstitutions = (\typedExpr subst -> Expression.mapTags (\t -> Substitution.applyToType subst t) typedExpr)
    }


inferrableBoth : Inferrable a b -> Inferrable x y -> Inferrable (a, x) (b, y)
inferrableBoth infA infX =
    let freeVariables_ (a, x) =
            Set.union
                (infA.freeVariables a)
                (infX.freeVariables x)   
    in  
    let makeConstraints_ (a, x) bindings =
            StateE.bind (infA.makeConstraints a bindings) <| \(b, c1) ->
            StateE.map_ (infX.makeConstraints x bindings) <| \(y, c2) ->
            ((b, y), c1 ++ c2)
    in
    let applySubstitutions_ (b, y) subst =
            ( (infA.applySubstitutions b subst)
            , (infX.applySubstitutions y subst)
            )
    in
    { freeVariables = freeVariables_
    , makeConstraints = makeConstraints_
    , applySubstitutions = applySubstitutions_
    }

inferrableTypesFreeFriendly : Inferrable a b -> a -> Result TypeError b
inferrableTypesFreeFriendly intf a =
    let freeVars = Set.toList (intf.freeVariables a)
    in
    let makeConstraintsFreeFriendly =
            StateE.bind (freshList freeVars) <| \freeBounds ->
                let bounds =
                        freeBounds
                        |> List.map (\(variable, typeVariable) -> (variable, ForAll [] typeVariable))
                        |> Dict.fromList
                in intf.makeConstraints a bounds
    in
    StateE.runResult makeConstraintsFreeFriendly 0
    |> Result.andThen (\(b, constraints) ->
        solveConstraints Substitution.empty constraints
        |> Result.map (\subst ->
            intf.applySubstitutions b subst))


--inferByInferrable : Inferrable a b -> a -> Result TypeError b


unifyBind : String -> Type -> Result TypeError Substitution
unifyBind v t =
    if t == TVariable v then 
        Ok Substitution.empty
    else
        if Type.containsTypeVariable v t then
            Err (InfiniteType v t)
        else
            Ok (Dict.singleton v t)

-- This is O(N^2)
unifyMany : List (Type, Type) -> Result TypeError Substitution
unifyMany list =
    case list of
        [] -> Ok Substitution.empty
        ((t1, t2) :: r) ->
            (unify t1 t2)
            |> Result.andThen (\su1 ->
                unifyMany (List.map (\(u1, u2) -> (Substitution.applyToType su1 u1, Substitution.applyToType su1 u2)) r)
                |> Result.map (\su2 ->
                    Substitution.compose su2 su1
                )
            )

unify : Type -> Type -> Result TypeError Substitution
unify t1 t2 =
    case (t1, t2) of
        (t, (TVariable v)) -> unifyBind v t
        ((TVariable v), t) -> unifyBind v t
        ((TFunc l1 r1), (TFunc l2 r2)) ->
            (unify l1 l2)
            |> Result.andThen (\s1 ->
                (unify (Substitution.applyToType s1 r1) (Substitution.applyToType s1 r2))
                |> Result.andThen (\s2 ->                    
                    Ok (Substitution.compose s2 s1)))
        ((TPair l1 r1), (TPair l2 r2)) ->
            (unify l1 l2)
            |> Result.andThen (\s1 ->
                unify (Substitution.applyToType s1 r1) (Substitution.applyToType s1 r2)
                |> Result.andThen (\s2 ->
                    Ok (Substitution.compose s2 s1)))
        ((TOption a), (TOption b)) ->
            unify a b
        (TInt, TInt) -> Ok Substitution.empty
        (TBool, TBool) -> Ok Substitution.empty
        _ -> Err (UnificationFailure t1 t2)
