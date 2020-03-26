module Substitution exposing (Substitution, empty, compose, applyToType, applyToScheme, applyToEnv)

import Dict exposing (Dict)
import Set exposing (Set)

import Type exposing (Type(..))
import TypeEnv exposing (TypeEnv)
import Scheme exposing (Scheme(..))

type alias Substitution = Dict String Type

empty : Substitution
empty = Dict.empty

-- Dict.union gives preference to the first argument,
-- as does Haskell's Data.Map, as used in Write You A Haskell
compose : Substitution -> Substitution -> Substitution
compose s1 s2 = Dict.union (Dict.map (\_ -> applyToType s1) s2) s1

applyToType : Substitution -> Type -> Type
applyToType s t =
    case t of
        TInt -> TInt
        TBool -> TBool
        TUnbound -> TUnbound
        TVariable v -> Dict.get v s |> Maybe.withDefault t
        TFunc t1 t2 -> TFunc (applyToType s t1) (applyToType s t2)
        TPair t1 t2 -> TPair (applyToType s t1) (applyToType s t2)
        TOption t1 -> TOption (applyToType s t1)
        TInferenceError e -> TInferenceError e

applyToScheme : Substitution -> Scheme -> Scheme
applyToScheme s (ForAll args t) =
    let s2 = List.foldr Dict.remove s args in
    ForAll args (applyToType s2 t)

applyToEnv : Substitution -> TypeEnv -> TypeEnv
applyToEnv s env = Dict.map (\_ -> applyToScheme s) env
