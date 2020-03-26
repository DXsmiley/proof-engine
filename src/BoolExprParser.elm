module BoolExprParser exposing (run)

import Set
import Char
import Parser exposing (Parser, (|.), (|=), succeed, symbol, spaces, lazy, andThen, oneOf, map, variable, end)

import Expression
import Value
import Basics exposing (identity)

withSpaces : Parser a -> Parser a
withSpaces p = succeed identity |. spaces |= p |. spaces

-- Right-recursive sequence parser
mySequence : Parser a -> List String -> (a -> a -> a) -> Parser a
mySequence item seps bindFunc =
    (withSpaces item)
    |> andThen (\firstItem ->
        withSpaces
        <| oneOf
            [ succeed (bindFunc firstItem)
                |. oneOf (List.map symbol seps)
                |. spaces
                |= lazy (\_ -> mySequence item seps bindFunc)
            , succeed firstItem
            ]
    )

bracketedExpression = succeed identity
    |. symbol "("
    |= lazy (\_ -> expression)
    |. symbol ")"

atom = oneOf
    [ variable
        { start = Char.isAlpha
        , inner = Char.isAlpha
        , reserved = Set.empty
        }
      |> map (\s -> Expression.Variable s ())
    , bracketedExpression
    ]

nots = oneOf
    [ succeed (\a -> Expression.Not a ())
        |. oneOf [symbol "!", symbol "¬"]
        |. spaces
        |= lazy (\_ -> nots)
    , atom
    ]

andSeq = mySequence nots ["/\\", "∧"] (\a b -> Expression.And a b ())

orSeq = mySequence andSeq ["\\/", "∨"] (\a b -> Expression.Or a b ())

impSeq = mySequence orSeq ["->", "→"]
    (\a b -> Expression.IfBranch a b (Expression.Constant (Value.VBool False) ()) ())

iffSeq = mySequence impSeq ["<=>", "⇔"] (\a b -> Expression.Eq a b ())

expression = iffSeq

fullExpression =
    succeed identity
        |. spaces
        |= expression
        |. spaces
        |. end

run : String -> Result (List Parser.DeadEnd) (Expression.Expression ())
run string = Parser.run fullExpression string