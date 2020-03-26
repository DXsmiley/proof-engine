module Type exposing (Type(..), TypeError(..), freeTypeVariables, containsTypeVariable)

import Set exposing (..)


type Type
    = TInt
    | TBool
    | TFunc Type Type
    | TPair Type Type
    | TOption Type
    | TUnbound -- Might remove this??
    | TVariable String -- Might only be used during inference??
    | TInferenceError TypeError


type TypeError
    = UnificationFailure Type Type
    | InfiniteType String Type
    | UnboundVariable String
    | SecondaryError


freeTypeVariables : Type -> Set String
freeTypeVariables t =
    case t of
        TInt -> Set.empty
        TBool -> Set.empty
        TFunc t1 t2 -> Set.union (freeTypeVariables t1) (freeTypeVariables t2)
        TPair t1 t2 -> Set.union (freeTypeVariables t1) (freeTypeVariables t2)
        TOption t1 -> freeTypeVariables t1
        TUnbound -> Set.empty
        TVariable v -> Set.singleton v
        TInferenceError _ -> Set.empty


containsTypeVariable : String -> Type -> Bool
containsTypeVariable a t =
    case t of
        TInt -> False
        TBool -> False
        TUnbound -> False
        TVariable b -> a == b
        TFunc t1 t2 -> containsTypeVariable a t1 || containsTypeVariable a t2
        TPair t1 t2 -> containsTypeVariable a t1 || containsTypeVariable a t2
        TOption t1 -> containsTypeVariable a t1
        TInferenceError _ -> False