module StateE exposing (StateE, map, map_, mapE, return, raise, modify, modifyE, get, bind, andThen, run, runResult)

-- TODO: Create a module for the normal "State" and then add a number of functions to promote
-- operations on normal states to this monad

import Result exposing (..)

type StateE s e a = StateE (s -> Result e (s, a))

map : (a -> b) -> StateE s e a -> StateE s e b
map f (StateE g) =
    StateE <| \s -> g s |> Result.map (Tuple.mapSecond f)

flip : (a -> b -> c) -> (b -> a -> c)
flip f a b = f b a

map_ = flip map

-- I'm not sure if "lift" in the correct verb to use here
liftError : StateE s e (Result e a) -> StateE s e a
liftError (StateE f) =
    StateE <| \s ->
        case f s of
            Err e -> Err e
            Ok (t, Err e) -> Err e
            Ok (t, Ok a) -> Ok (t, a)

mapE : (a -> Result e b) -> StateE s e a -> StateE s e b
mapE f s = map f s |> liftError

return : a -> StateE s e a
return a = StateE <| \s -> Ok (s, a)

raise : e -> StateE s e a
raise e = StateE <| \s -> Err e

modify : (s -> s) -> StateE s e ()
modify f = StateE <| \s -> Ok (f s, ())

modifyE : (s -> Result e s) -> StateE s e ()
modifyE f = StateE <| \s ->
    case f s of
        Err e -> Err e
        Ok t -> Ok (t, ())

get : StateE s e s
get = StateE <| \s -> Ok (s, s)

bind : StateE s e a -> (a -> StateE s e b) -> StateE s e b
bind (StateE stateful1) stateful2WithInput =
    StateE <| \s1 ->
        case stateful1 s1 of
            Err e -> Err e
            Ok (s2, r) ->
                let (StateE f) = stateful2WithInput r in f s2

andThen : (a -> StateE s e b) -> StateE s e a -> StateE s e b
andThen x y = bind y x

run : StateE s e a -> s -> Result e (s, a)
run (StateE f) init = f init

runResult: StateE s e a -> s -> Result e a
runResult s init = run s init |> Result.map Tuple.second