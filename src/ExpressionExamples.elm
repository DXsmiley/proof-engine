module ExpressionExamples exposing
    ( problem1
    , problem2
    , problem3
    , problem4
    , problem5
    , problem6
    , problem7
    , problem8
    , problem9
    , problem11
    , problem12
    , problem13
    , problem14
    , problem15
    , problem16
    , problem17
    , allProblems
    )

import Expression exposing (..)
import Value exposing (Value(..))

var n = Variable n ()
call a b = FunctionCall a b ()
lambda n a = Lambda n () a ()
const v = Constant v ()
and a b = And a b ()
and3 a b c = and a (and b c)
or a b = Or a b ()
or3 a b c = or a (or b c)
not a = Not a ()
if_ a b c = IfBranch a b c ()
eq a b = Eq a b () -- Same as iff for booleans

true = const (VBool True)
false = const (VBool False)
imp a b = if_ a b false

p = var "p"
q = var "q"
r = var "r"
s = var "s"

excludedMiddle1 = (or p (not p))
excludedMiddle2 = imp (or p (not p)) p

-- Seventy-five problems for testing theoreom provers
-- http://www.sfu.ca/~jeffpell/papers/75ATPproblems86.pdf

problem1 = eq (imp p q) (imp (not q) (not p))

problem2 = eq (not <| not p) p

problem3 = imp (not (imp p q)) (imp q p)

problem4 = eq (imp (not p) q) (imp (not q) p)

problem5 = imp (imp (or p q) (or p r)) (or p (imp q r))

problem6 = or p (not p)

problem7 = or p (not <| not <| not p)

problem8 = imp (imp (imp p q) p) p

problem9 = imp (and3 (or p q) (or (not p) q) (or p (not q))) (not (or (not p) (not q)))

-- not sure how to encode problem10

problem11 = eq p p

problem12 = eq (eq (eq p q) r) (eq p (eq q r))

problem13 = eq (or p (and q r)) (and (or p q) (or p r))

problem14 = eq (eq p q) (and (or q (not p)) (or (not q) p))

problem15 = eq (imp p q) (or (not q) q)

problem16 = or (imp p q) (imp q p)

problem17 = eq
    (imp (and p (imp q r)) s)
    (and (or3 (not p) q s) (or3 (not p) (not r) s))

allProblems =
    [ excludedMiddle1
    , excludedMiddle2
    , problem1
    , problem2
    , problem3
    , problem4
    , problem5
    , problem6
    , problem7
    , problem8
    , problem9
    , problem11
    , problem12
    , problem13
    , problem14
    , problem15
    , problem16
    , problem17
    ]
