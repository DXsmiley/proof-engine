module Util exposing (unionMap, foldlMap, listsAreUnique)

import Set exposing (Set)

unionMap : (a -> Set comparable) -> List a -> Set comparable
unionMap f l =
    List.map f l |> List.foldl Set.union Set.empty

foldlMap : (a -> c -> (b, c)) -> c -> List a -> (List b, c)
foldlMap f init list =
    let helper current remaining accumulator =
            case remaining of
                [] -> (List.reverse accumulator, current)
                x :: xs ->
                    let (item, next) = f x current in
                    helper next xs (item :: accumulator)
    in helper init list []

listsAreUnique : List a -> List a -> Bool
listsAreUnique a b = a |> List.all (\i -> not (List.member i b))
