module State exposing (..)

type State s a = State (s -> (s, a))

map : (a -> b) -> State s a -> State s b
map f (State g) = State <| g >> Tuple.mapSecond f

map_ : State s a -> (a -> b) -> State s b
map_ s f = map f s

return : a -> State s a
return x = State <| \s -> (s, x)

modify : (s -> s) -> State s ()
modify f = State <| \s -> (f s, ())

get : State s s
get = State <| \s -> (s, s)

bind : State s a -> (a -> State s b) -> State s b
bind (State stateful1) stateful2WithInput =
    State <| \s1 ->
        let (s2, r) = stateful1 s1 in
        let (State f) = stateful2WithInput r in
        f s2

andThen : (a -> State s b) -> State s a -> State s b
andThen x y = bind y x

inc : State Int Int
inc = State <| \s -> (s + 1, s)

runState : State s a -> s -> (s, a)
runState (State f) s = f s

