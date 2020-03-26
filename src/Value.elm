module Value exposing (..)

import Type exposing (..)

type Value
    = VInt Int
    | VBool Bool
    | VPair Value Value
    | VOption (Maybe Value)


typeOf : Value -> Type
typeOf value =
    case value of
        VInt _ -> TInt
        VBool _ -> TBool
        VPair a b -> TPair (typeOf a) (typeOf b)
        VOption (Just a) -> TOption (typeOf a)
        VOption Nothing -> TOption TUnbound
