module ProofEngine exposing (Proof(..), ProofStep(..), ProofTree(..), proofStepToName, proveByTree, proveBySteps, applyProofSteps)

import Expression exposing (Expression(..))
import Type exposing (Type(..))
import Tee exposing (..)
import Value exposing (..)

import Util exposing (listsAreUnique, foldlMap)


type ProofStep
    = AndFactSplit
    | AndGoalSplit
    | OrFactSplit
    | OrGoalSplit
    | IfFactSplit
    | IfGoalSplit
    | EqBoolFactSplit
    | EqBoolGoalSplit
    | TrivialImplication
    | FalseImpliesAnything
    | DropGoalFalse
    | NotFact
    | NotGoal


type Proof = Proof (List Tee)


type RuleApplicationResult
    = SplitTee (List (Expression Type))
    | AddToTee (List (Expression Type))
    | SplitTeeDiscarding (List (Expression Type))
    | AddToTeeDiscarding (List (Expression Type))
    | RuleNotApplicable



applyToFirstMatchingExpression : (Expression Type -> RuleApplicationResult) -> List (Expression Type) -> List (List (Expression Type))
applyToFirstMatchingExpression f expressions =
    let fFiltered expr =
            let util exprs constructor =
                    (if List.length exprs == 1 && exprs == [ expr ] then RuleNotApplicable else constructor exprs)
            in
            case f expr of
                RuleNotApplicable -> RuleNotApplicable
                AddToTee exprs -> util exprs AddToTee
                SplitTee exprs -> util exprs SplitTee
                AddToTeeDiscarding exprs -> util exprs AddToTeeDiscarding
                SplitTeeDiscarding exprs -> util exprs SplitTeeDiscarding
    in
    let helper unchecked checked =
            case unchecked of
                [] -> [ expressions ]
                x :: xs ->
                    case fFiltered x of
                        RuleNotApplicable -> helper xs (x :: checked)
                        AddToTee exprs -> [ List.reverse checked ++ exprs ++ unchecked ]
                        SplitTee exprs -> List.map (\fact -> List.reverse checked ++ fact :: unchecked) exprs
                        AddToTeeDiscarding exprs -> [ List.reverse checked ++ exprs ++ xs ]
                        SplitTeeDiscarding exprs -> List.map (\fact -> List.reverse checked ++ fact :: xs) exprs
    in helper expressions []


applyToFistMatchingFact : (Expression Type -> RuleApplicationResult) -> Tee -> List Tee
applyToFistMatchingFact f (Tee { facts, goals }) =
    applyToFirstMatchingExpression f facts
    |> List.map (\factList -> Tee { facts = factList, goals = goals})


applyToFirstMatchingGoal : (Expression Type -> RuleApplicationResult) -> Tee -> List Tee
applyToFirstMatchingGoal f (Tee { facts, goals }) =
    applyToFirstMatchingExpression f goals
    |> List.map (\goalList -> Tee { facts = facts, goals = goalList })


splitAndExpression : Expression Type -> List (Expression Type)
splitAndExpression expr =
    case expr of
        And a b TBool -> splitAndExpression a ++ splitAndExpression b
        _ -> [ expr ]


andFactSplit : Tee -> List Tee
andFactSplit = applyToFistMatchingFact (splitAndExpression >> AddToTeeDiscarding)


andGoalSplit : Tee -> List Tee
andGoalSplit = applyToFirstMatchingGoal (splitAndExpression >> SplitTeeDiscarding)


splitOrExpression : Expression Type -> List (Expression Type)
splitOrExpression expr =
    case expr of
        Or a b TBool -> splitOrExpression a ++ splitOrExpression b
        _ -> [ expr ]


orFactSplit : Tee -> List Tee
orFactSplit = applyToFistMatchingFact (splitOrExpression >> SplitTeeDiscarding)


orGoalSplit : Tee -> List Tee
orGoalSplit = applyToFirstMatchingGoal (splitOrExpression >> AddToTeeDiscarding)


extractAndMapFirst : (a -> Maybe b) -> List a -> Maybe (b, List a)
extractAndMapFirst f l =
    let helper unchecked checked =
            case unchecked of
                [] -> Nothing
                x :: xs ->
                    case f x of
                        Nothing -> helper xs (x :: checked)
                        Just r -> Just (r, List.reverse checked ++ xs)
    in helper l []


extractIfExpression : Expression a -> Maybe (Expression a, Expression a, Expression a)
extractIfExpression expr =
    case expr of
        IfBranch c a b _ -> Just (c, a, b)
        _ -> Nothing


-- This might actually be very wrong in the non-boolean case
ifFactSplit : Tee -> List Tee
ifFactSplit (Tee { facts, goals }) =
    case extractAndMapFirst extractIfExpression facts of
        Nothing -> [ Tee {facts = facts, goals = goals} ]
        Just ((c, a, (Constant (VBool False) TBool)), otherFacts) ->
            [ Tee { facts = otherFacts, goals = c :: goals }
            , Tee { facts = a :: otherFacts, goals = goals }
            ]
        Just ((c, a, b), otherFacts) ->
            [ Tee { facts = [c, a] ++ otherFacts, goals = goals }
            , Tee { facts = [Not c TBool, b] ++ otherFacts, goals = goals }
            ]


ifGoalSplit : Tee -> List Tee
ifGoalSplit (Tee {facts, goals}) =
    case extractAndMapFirst extractIfExpression goals of
        Nothing -> [ Tee {facts = facts, goals = goals} ]
        Just ((c, a, (Constant (VBool False) TBool)), otherGoals) ->
            [ Tee { facts = c :: facts, goals = a :: otherGoals} ]
        Just ((c, a, b), otherGoals) ->
            [ Tee { facts = c :: facts, goals = a :: otherGoals}
            , Tee { facts = (Not c TBool) :: facts, goals = b :: otherGoals}
            ]


extractBoolEq : Expression Type -> Maybe (Expression Type, Expression Type)
extractBoolEq expr =
    case expr of
        Eq a b TBool -> Just (a, b)
        _ -> Nothing


eqBoolFactSplit : Tee -> List Tee
eqBoolFactSplit (Tee {facts, goals}) =
    case extractAndMapFirst extractBoolEq facts of
        Nothing -> [ Tee {facts = facts, goals = goals} ]
        Just ((a, b), otherFacts) ->
            [ Tee { facts = a :: b :: otherFacts, goals = goals }
            , Tee { facts = otherFacts, goals = a :: b :: goals }
            ]



eqBoolGoalSplit : Tee -> List Tee
eqBoolGoalSplit (Tee {facts, goals}) =
    case extractAndMapFirst extractBoolEq goals of
        Nothing -> [ Tee {facts = facts, goals = goals} ]
        Just ((a, b), otherGoals) ->
            [ Tee { facts = a :: facts, goals = b :: otherGoals }
            , Tee { facts = b :: facts, goals = a :: otherGoals }
            ]


trivialImplication : Tee -> List Tee
trivialImplication (Tee {facts, goals}) =
    if facts |> List.any (\fact -> List.any ((==) fact) goals) then
        []
    else
        [ Tee { facts = facts, goals = goals} ]


-- Maybe this should remove the whole tee??
dropGoalFalse : Tee -> List Tee
dropGoalFalse =
    let match expr =
            case expr of
                (Constant (VBool False) TBool) -> AddToTeeDiscarding []
                _ -> RuleNotApplicable
    in applyToFirstMatchingGoal match


extractNot expr =
    case expr of
        Not a TBool -> Just a
        _ -> Nothing


notFact : Tee -> List Tee
notFact (Tee {facts, goals}) =
    case extractAndMapFirst extractNot facts of
        Nothing -> [ Tee {facts = facts, goals = goals} ]
        Just (a, otherFacts) -> [ Tee {facts = otherFacts, goals = a :: goals} ]


notGoal : Tee -> List Tee
notGoal (Tee {facts, goals}) =
    case extractAndMapFirst extractNot goals of
        Nothing -> [ Tee {facts = facts, goals = goals} ]
        Just (a, otherGoals) -> [ Tee {facts = a :: facts, goals = otherGoals} ]



falseImpliesAnything : Tee -> List Tee
falseImpliesAnything (Tee {facts, goals}) =
    let isFalseConst expr =
            case expr of
                (Constant (VBool False) TBool) -> True
                _ -> False
    in
    if List.any isFalseConst facts then
        []
    else
        [ Tee { facts = facts, goals = goals }]


proofStepToFunction step =
    case step of
        AndFactSplit -> andFactSplit
        AndGoalSplit -> andGoalSplit
        OrFactSplit -> orFactSplit
        OrGoalSplit -> orGoalSplit
        IfFactSplit -> ifFactSplit
        IfGoalSplit -> ifGoalSplit
        EqBoolFactSplit -> eqBoolFactSplit
        EqBoolGoalSplit -> eqBoolGoalSplit
        TrivialImplication -> trivialImplication
        FalseImpliesAnything -> falseImpliesAnything
        DropGoalFalse -> dropGoalFalse
        NotFact -> notFact
        NotGoal -> notGoal


proofStepToName step =
    case step of
        AndFactSplit -> ("∧", "Left")
        AndGoalSplit -> ("∧", "Right")
        OrFactSplit -> ("∨", "Left")
        OrGoalSplit -> ("∨", "Right")
        IfFactSplit -> ("→", "Left")
        IfGoalSplit -> ("→", "Right")
        EqBoolFactSplit -> ("⇔", "Left")
        EqBoolGoalSplit -> ("⇔", "Right")
        TrivialImplication -> ("", "")
        FalseImpliesAnything -> ("⊥", "Left")
        DropGoalFalse -> ("⊥", "Right")
        NotFact -> ("¬", "Left")
        NotGoal -> ("¬", "Right")


allProofSteps = 
    [ AndFactSplit
    , AndGoalSplit
    , OrFactSplit
    , OrGoalSplit
    , IfFactSplit
    , IfGoalSplit
    , EqBoolFactSplit
    , EqBoolGoalSplit
    , TrivialImplication
    , FalseImpliesAnything
    , DropGoalFalse
    , NotFact
    , NotGoal
    ]

makeRepeatedProgressHelper tees trace maxSteps =
    if maxSteps <= 0 then []
    else case tees of
        [] -> []
        tee :: rest ->
            let sortedOptions =
                    allProofSteps
                    |> List.map (\step -> (step, proofStepToFunction step tee))
                    |> List.filter (\(_, result) -> result /= [ tee ])
                    |> List.filter (\(_, result) -> not <| List.member (result ++ rest) trace)
                    |> List.sortBy (Tuple.second >> List.length)
            in
            case List.head sortedOptions of
                Nothing -> []
                Just (step, result) ->
                    let remaining = result ++ rest in
                    let x = makeRepeatedProgressHelper remaining (remaining :: trace) (maxSteps - 1)
                    in (step, remaining) :: x


makeRepeatedProgress tees maxSteps =
    makeRepeatedProgressHelper tees [ tees ] maxSteps


proveBySteps initial =
    { initial = initial
    , steps = makeRepeatedProgress [ initial ] 30
    }


type ProofTree
    = Node Tee ProofStep (List ProofTree)
    | GiveUp Tee


proveByTreeHelper : Tee -> List Tee -> Int -> ProofTree
proveByTreeHelper tee trace maxSteps =
    if maxSteps <= 0 then
        GiveUp tee
    else
        let sortedOptions =
                allProofSteps
                |> List.map (\step -> (step, proofStepToFunction step tee))
                --|> List.filter (\(_, result) -> result /= [ tee ])
                |> List.filter (\(_, result) -> listsAreUnique result trace)
                |> List.sortBy (Tuple.second >> List.length)
        in
        case List.head sortedOptions of
            Nothing -> GiveUp tee
            Just (step, results) ->
                let children = List.map (\r -> proveByTreeHelper r (r :: trace) (maxSteps - 1)) results
                in Node tee step children



proveByTree : Tee -> ProofTree
proveByTree tee = proveByTreeHelper tee [ tee ] 30


applyProofSteps initial steps =
    let doStep step state =
            case state of
                [] -> ((step, []), [])
                focus :: rest ->
                    let newGoals = proofStepToFunction step focus in
                    ((step, newGoals ++ rest), newGoals ++ rest)
    in
    { initial = initial
    , steps = foldlMap doStep [initial] steps |> Tuple.first
    }