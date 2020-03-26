module TypeEnv exposing (TypeEnv, empty, extend, freeTypeVariables)

import Dict exposing (Dict)
import Set exposing (Set)

import Scheme exposing (Scheme)

import Util

type alias TypeEnv = Dict String Scheme

empty : TypeEnv
empty = Dict.empty

extend : TypeEnv -> String -> Scheme -> TypeEnv
extend env var scheme = Dict.insert var scheme env

freeTypeVariables : TypeEnv -> Set String
freeTypeVariables env =
    Dict.values env |> Util.unionMap Scheme.freeTypeVariables