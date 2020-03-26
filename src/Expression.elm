module Expression exposing (Expression(..), mapTags, freeVariables, getTag)

import Set exposing (Set)

import Value exposing (Value)


-- At the moment, a is either () or Type. I'm not sure if it's suitable to be anything else really.
-- Might be OK for (ProofState, Type) pairings??
type Expression a
    = Variable String a
    | FunctionCall (Expression a) (Expression a) a
    | LetBind String a (List (String, a)) (Expression a) (Expression a) a
    | Lambda String a (Expression a) a
    -- TODO: Tuple unpacking
    | Constant Value a
    -- Booleans are baked into the language
    | And (Expression a) (Expression a) a
    | Or (Expression a) (Expression a) a
    | Not (Expression a) a
    | IfBranch (Expression a) (Expression a) (Expression a) a
    -- Structural equality
    | Eq (Expression a) (Expression a) a
    -- Introduce a example into the proof state and assume that it's true
    -- Used for development purposes and for things that are too difficult to prove
    -- Assert (Expression a) (Expression a) a
    
    -- 
    -- Show (Expression a) (Expression a) a
    -- Verify (Expression a) (Expression a) a


mapTags : (a -> b) -> Expression a -> Expression b
mapTags f e =
    let rec x = mapTags f x in
    case e of
        Variable a x -> Variable a (f x)
        FunctionCall a b x ->
            FunctionCall
                (rec a)
                (rec b)
                (f x)
        LetBind a x l b c y ->
            LetBind
                a
                (f x)
                (List.map (Tuple.mapSecond f) l)
                (rec b) 
                (rec c)
                (f y)
        Constant a x -> Constant a (f x)
        Lambda a x b y -> Lambda a (f x) (rec b) (f y)
        And a b x -> And (rec a) (rec b) (f x)
        Or a b x -> Or (rec a) (rec b) (f x)
        Not a x -> Not (rec a) (f x)
        IfBranch a b c x -> IfBranch (rec a) (rec b) (rec c) (f x)
        Eq a b x -> Eq (rec a) (rec b) (f x)


freeVariables : Expression a -> Set String
freeVariables e =
    case e of
        Constant _ _ -> Set.empty
        Variable v _ -> Set.singleton v
        FunctionCall f x _ -> Set.union (freeVariables f) (freeVariables x)
        Lambda var _ body _ -> Set.remove var (freeVariables body)
        And a b _ -> Set.union (freeVariables a) (freeVariables b)
        Or a b _ -> Set.union (freeVariables a) (freeVariables b)
        Not a _ -> freeVariables a
        Eq a b _ -> Set.union (freeVariables a) (freeVariables b)
        IfBranch a b c _ -> Set.union (freeVariables a) (freeVariables b) |> Set.union (freeVariables c)
        LetBind var _ args body final _ ->
            Set.union
                (Set.diff (freeVariables body) (Set.fromList (var :: List.map Tuple.first args)))
                (Set.diff (freeVariables final) (Set.singleton var))


getTag : Expression a -> a
getTag e =
    case e of
        Variable _ a -> a
        FunctionCall _ _ a -> a
        LetBind _ _ _ _ _ a -> a
        Lambda _ _ _ a -> a
        Constant _ a -> a
        And _ _ a -> a
        Or _ _ a -> a
        IfBranch _ _ _ a -> a
        Not _ a -> a
        Eq _ _ a -> a