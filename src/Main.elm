module Main exposing (..)

-- This file is very very big.
-- Most of the stuff in here _should_ be moved to another file.

import Array exposing (Array)
import Browser
import Browser.Navigation as Nav
import Css
import Css.Global
import Debug
import Dict exposing (..)
import Html.Styled exposing (Attribute, Html, button, div, input, p, styled, text, toUnstyled, pre, span, h1, h2, table, td, tr, th)
import Html.Styled.Attributes exposing (id, value)
import Html.Styled.Events exposing (keyCode, on, onClick, onInput)
import Http exposing (Error(..), Response, get)
import Json.Decode as Decode exposing (Decoder)
import Maybe exposing (..)
import Task
import Url
import Set exposing (..)
import StateE exposing (StateE)

import Type exposing (..)
import Expression exposing (..)
import Value exposing (..)

import ExpressionExamples

import BoolExprParser

import Scheme exposing (Scheme(..))
import Substitution exposing (Substitution)
import TypeEnv exposing (TypeEnv)

import TypeInference

import Util exposing (foldlMap)

import Tee exposing (Tee(..), factOnly, goalOnly, makeTee)
import ProofEngine exposing (Proof, ProofStep, ProofTree(..), proofStepToName, proveByTree)


main : Program () Model Msg
main =
    Browser.application
        { view = view
        , init = init
        , update = update
        , subscriptions = subscriptions
        , onUrlChange = UrlChanged
        , onUrlRequest = LinkClicked
        }


subscriptions : Model -> Sub Msg
subscriptions model =
    Sub.none


type Page
    = PageOverview
    | PageInteractive
    | PageExamples
    | PageSource


type alias Model =
    { page : Page
    , expressionInput : String
    , parseResult : Result String (Expression ())
    , compactTree : Bool
    }


init : flags -> Url.Url -> Nav.Key -> ( Model, Cmd Msg )
init flags url key =
    let
        state =
            { page = PageOverview
            , expressionInput = ""
            , parseResult = Err ":("
            , compactTree = False
            }
    in
    ( state, Cmd.none )


type Msg
    = UrlChanged Url.Url
    | LinkClicked Browser.UrlRequest
    | ChangeExpressionInput String
    | ChangePage Page
    | ChangeTreeCompactness Bool


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        UrlChanged url ->
            ( model, Cmd.none )

        LinkClicked urlRequest ->
            case urlRequest of
                --Browser.Internal url  -> ( model, Nav.pushUrl model.key (Url.toString url) )
                Browser.Internal href ->
                    ( model, Nav.load (Url.toString href) )

                Browser.External href ->
                    ( model, Nav.load href )

        ChangeExpressionInput input ->
            ( { model | expressionInput = input}, Cmd.none )

        ChangePage page ->
            ( { model | page = page }, Cmd.none )

        ChangeTreeCompactness compact ->
            ( { model | compactTree = compact}, Cmd.none )


type FormatPeice
    = Text String
    | Indent
    | Deindent
    | Newline


displayValue : Value -> String
displayValue v =
    case v of
        VInt i -> String.fromInt i
        VBool True -> "True"
        VBool False -> "False"
        VPair l r -> "(" ++ displayValue l ++ ", " ++ displayValue r ++ ")"
        VOption Nothing -> "Nothing"
        VOption (Just j) -> "(Some " ++ displayValue j ++ ")"


displayError : TypeError -> String
displayError e =
    case e of
        UnificationFailure a b -> (displayTypeHelper a True) ++ " ~ " ++ (displayTypeHelper b True)
        InfiniteType n t -> "Infinite type, " ++ n ++ " ∈ " ++ (displayTypeHelper t True)
        SecondaryError -> "Ø"
        UnboundVariable v -> "Unbound variable " ++ v


displayTypeHelper : Type -> Bool -> String
displayTypeHelper t bracketFunctions =
    case t of
        TInt -> "Int"
        TBool -> "Bool"
        TOption u -> "(Maybe " ++ displayTypeHelper u True ++ ")"
        TPair a b -> "(" ++ displayTypeHelper a True ++ " * " ++ displayTypeHelper b True ++ ")"
        TUnbound -> "?"
        TVariable v -> "'" ++ v
        TFunc a b ->
            case bracketFunctions of
                True -> "(" ++ displayTypeHelper a True ++ " -> " ++ displayTypeHelper b False ++ ")"
                False -> displayTypeHelper a True ++ " -> " ++ displayTypeHelper b False
        TInferenceError e -> displayError e


displayType : Type -> String
displayType t = displayTypeHelper t False


formatExpression : Expression a -> (a -> List FormatPeice) -> List FormatPeice
formatExpression expression formatTag =
    let nameWithTag n t =
            case formatTag t of
                [] -> [Text n]
                t_ -> [Text "(", Text n] ++ t_ ++ [Text ")"]
    in
    let nameWithTag_ (n, t) = nameWithTag n t
    in
    let rec e =
            case e of
                Variable v t -> nameWithTag v t
                Constant c t -> nameWithTag (displayValue c) t
                LetBind v vt args def expr t ->
                    [Text "let"] ++ nameWithTag v vt ++ (List.concatMap nameWithTag_ args) ++ [Text "=", Newline, Indent] ++ (rec def) ++ [Newline, Deindent, Text "in", Newline, Indent] ++ rec expr ++ [Deindent]
                FunctionCall f x t ->
                    [ Text "(" ] ++ rec f ++ rec x ++ formatTag t ++ [ Text ")" ]
                Lambda v vt def t -> [Text "("] ++ nameWithTag v vt ++ [ Text "->" ] ++ rec def ++ formatTag t ++ [Text ")"]
                And a b t -> [Text "( and"] ++ rec a ++ rec b ++ formatTag t ++ [ Text ")" ]
                Or a b t  -> [Text "( or"]  ++ rec a ++ rec b ++ formatTag t ++ [ Text ")" ]
                Not a t   -> [Text "( not"] ++ rec a ++ formatTag t ++ [ Text ")" ]
                Eq a b t  -> [Text "( eq"]  ++ rec a ++ rec b ++ formatTag t ++ [ Text ")" ]
                IfBranch a b (Constant (VBool False) _) t -> [Text "( imp"] ++ rec a ++ rec b ++ [Text ") "] ++ formatTag t
                IfBranch a b c t -> [Text "( if"] ++ rec a ++ [Text "then"] ++ rec b ++ [Text "else"] ++ rec c ++ [Text ") "] ++ formatTag t
    in rec expression


-- Lots of things here that are "invalid"
-- This is bad
formatExpressionAsMath : Expression a -> String
formatExpressionAsMath expression =
    let rec e =
            case e of
                Variable v _ -> v
                Constant c _ -> displayValue c
                LetBind _ _ _ _ _ _ -> "*"
                FunctionCall f x _ -> rec f ++ " " ++ rec x
                Lambda _ _ _ _ -> "*"
                And a b _ -> "(" ++ rec a ++ " ∧ " ++ rec b ++ ")"
                Or a b _ -> "(" ++ rec a ++ " ∨ " ++ rec b ++ ")"
                Not a _ -> "(¬" ++ rec a ++ ")"
                Eq a b _ -> "(" ++ rec a ++ " ⇔ " ++ rec b ++ ")"
                IfBranch a b (Constant (VBool False) _) _ -> "(" ++ rec a ++ " → " ++ rec b ++ ")"
                IfBranch _ _ _ _ -> "*"
    in rec expression


peicesToSpans : List FormatPeice -> List (Html a)
peicesToSpans ps =
    let (indented, _) = foldlMap (\peice (firstOnLine, indent) ->
            case peice of
                Indent -> (Nothing, (firstOnLine, indent + 1))
                Deindent -> (Nothing, (firstOnLine, indent - 1))
                Text s ->
                    if firstOnLine then
                        (Just ((String.repeat indent "    ") ++ s ++ " "), (False, indent))
                    else (Just (s ++ " "), (False, indent))
                Newline -> (Just "\n", (True, indent))
            )
            (True, 0)
            ps
    in
    List.filterMap (Maybe.map (\s -> span [] [text s])) indented


displayExpressionInlineWithTagFormatter : Expression a -> (a -> List FormatPeice) -> Html b
displayExpressionInlineWithTagFormatter expr formatTag =
    Html.Styled.code [] (formatExpression expr formatTag |> peicesToSpans)


displayExpressionInlineWithoutTags : Expression a -> Html b
displayExpressionInlineWithoutTags expr = displayExpressionInlineWithTagFormatter expr (\_ -> [])


displayExpressionInlineWithTypes : Expression Type -> Html b
displayExpressionInlineWithTypes expr =
    displayExpressionInlineWithTagFormatter expr (\t -> [Text "::", Text <| displayType t])


displayExpressionWithTagFormatter : Expression a -> (a -> List FormatPeice) -> Html b
displayExpressionWithTagFormatter expr formatTag =
    styled div
        [ Css.padding (Css.px 4)
        , Css.borderWidth (Css.px 1)
        ]
        []
        [ pre
            []
            (formatExpression expr formatTag |> peicesToSpans)
        ]

displayExpressionWithoutTags : Expression a -> Html b
displayExpressionWithoutTags expr = displayExpressionWithTagFormatter expr (\_ -> [])

displayExpressionWithTypes : Expression Type -> Html b
displayExpressionWithTypes expr =
    displayExpressionWithTagFormatter expr (\t -> [Text "::", Text <| displayType t])


--exampleExpressionDerived : Expression Type
--exampleExpressionDerived =
--    exampleExpression |> determineTypes


displayTee : Tee -> List (Html Msg)
displayTee (Tee { facts, goals }) =
    let formatSide items = List.intersperse (text "; ") (List.map displayExpressionInlineWithoutTags items)
    in formatSide facts ++ [text " ⊢ "] ++ formatSide goals


formatTeeAsMath : Tee -> String
formatTeeAsMath (Tee { facts, goals} ) =
    let formatSide items = String.join "; " (List.map formatExpressionAsMath items)
    in formatSide facts ++ " ⊢ " ++ formatSide goals


displayTreeProofCompact : ProofTree -> Html Msg
displayTreeProofCompact tree =
    case tree of
        GiveUp tee ->
            styled Html.Styled.code
                [ Css.color (Css.rgb 255 0 0) ]
                []
                [ text <| formatTeeAsMath tee ]
        Node tee rule children ->
            let textLabel =
                    let (label, sub) = proofStepToName rule
                    in styled Html.Styled.span
                        [ Css.color (Css.rgb 0 100 250)
                        , Css.marginLeft (Css.px 8)
                        ]
                        []
                        [ text label
                        , textIn Html.Styled.sub sub
                        ]
            in
            let childNodes =
                    List.map
                        displayTreeProofCompact
                        children
            in
            styled div
                [ Css.borderLeftStyle Css.solid
                , Css.borderLeftWidth (Css.px 1)
                , Css.borderLeftColor (Css.rgb 200 200 200)
                , Css.paddingLeft (Css.px 6)
                ]
                []
                [ span
                    []
                    [ textIn Html.Styled.code <| formatTeeAsMath tee
                    , textLabel
                    ]
                , styled div
                    [ Css.paddingLeft (Css.px 20) ]
                    []
                    childNodes
                ]


displayTreeProof : ProofTree -> Html Msg
displayTreeProof tree =
    case tree of
        GiveUp tee ->
            styled div
                [ Css.flexDirection Css.row
                , Css.flexWrap Css.noWrap
                , Css.flexGrow (Css.num 1)
                --, Css.borderTopWidth (Css.px 1)
                --, Css.borderTopStyle (Css.solid)
                , Css.display Css.inlineFlex
                , Css.color (Css.rgb 255 0 0)
                , Css.alignItems Css.spaceAround
                ]
                []
                [ Html.Styled.code [] [text <| formatTeeAsMath tee] ]
        Node tee rule children ->
            let childNodes =
                    List.intersperse
                        (styled div [Css.minWidth (Css.px 20)] [] [])
                        (List.map (\c -> displayTreeProof c) children)
            in
            let textLabelContents =
                    let (label, sub) = proofStepToName rule
                    in Html.Styled.span
                        []
                        [ text label
                        , textIn Html.Styled.sub sub
                        ]
            in
            let textLabel =
                    styled Html.Styled.span
                        [ Css.color (Css.rgb 0 100 250) ]
                        []
                        [ textLabelContents ]
            in
            let textlabelInvisible =
                    styled Html.Styled.span
                        [ Css.opacity (Css.num 0) ]
                        []
                        [ textLabelContents ]
            in
            styled div
                [ Css.flexDirection Css.column
                , Css.flexWrap Css.noWrap
                , Css.display Css.inlineFlex
                , Css.flexShrink (Css.num 0)
                ]
                []
                [ styled div
                    [ Css.flexDirection Css.row
                    , Css.flexWrap Css.noWrap
                    , Css.alignItems (Css.flexEnd)
                    , Css.display Css.inlineFlex
                    , Css.justifyContent Css.spaceBetween
                    , Css.flexShrink (Css.num 0)
                    ]
                    []
                    (childNodes ++ [textlabelInvisible])
                , styled div
                    [ Css.flexDirection Css.row
                    , Css.flexWrap Css.noWrap
                    , Css.display Css.inlineFlex
                    , Css.alignItems Css.stretch
                    , Css.flexShrink (Css.num 0)
                    ]
                    []
                    [ styled div
                        [ Css.flexShrink (Css.num 1)
                        , Css.flexGrow (Css.num 1)
                        , Css.display Css.inlineFlex
                        , Css.justifyContent Css.flexEnd
                        ]
                        []
                        [ styled div
                            [ Css.borderTopWidth (Css.px 1)
                            , Css.borderTopStyle (Css.solid)
                            , Css.marginTop (Css.px 10)
                            , Css.display Css.inline
                            , Css.flexGrow (Css.num 1)
                            ]
                            []
                            []
                        ]
                    , textLabel
                    ]
                , styled div
                    [ Css.flexDirection Css.row
                    , Css.flexWrap Css.noWrap
                    --, Css.borderTopWidth (Css.px 1)
                    --, Css.borderTopStyle (Css.solid)
                    , Css.display Css.inlineFlex
                    ]
                    []
                    [ styled div
                        [ Css.flexGrow (Css.num 1)
                        , Css.flexShrink (Css.num 0)
                        , Css.display Css.inlineFlex
                        , Css.justifyContent Css.center
                        ]
                        []
                        [ Html.Styled.code [] [text <| formatTeeAsMath tee]
                        ]
                    , textlabelInvisible
                    ]
                ]



displayTeeInDiv tee = div [] (displayTee tee)


displayProofStep (rule, resultGoals) =
    div []
        [ p [] [text <| Debug.toString rule]
        , div [] <| List.map displayTeeInDiv resultGoals
        ]


displayProof { initial, steps } =
    --let isCompelte =
    --    List.reverse steps
    --    |> List.head
    --    |> Maybe.map (Tuple.second >> List.isEmpty)
    --    |> Maybe.withDefault True
    --in
    div
        []
        [ div [] [ Html.Styled.h2 [] (displayTee initial) ]
        , div [] (List.map displayProofStep steps)
        ]


ptext string = p [] [text string]


type Side = Fact | Goal


generateProofRuleFromText string side =
    let toGiveUp tree =
            case tree of
                Node tee _ _ -> GiveUp tee
                GiveUp tee -> GiveUp tee
    in
    case BoolExprParser.run string of
        Err _ -> GiveUp (Tee { facts = [], goals = []})
        Ok expr ->
            case TypeInference.inferTypesFreeFriendly expr of
                Err _ -> GiveUp (Tee { facts = [], goals = []})
                Ok typed ->
                    let otee =
                            case side of
                                Fact -> factOnly typed
                                Goal -> goalOnly typed
                    in
                    case proveByTree otee of
                        -- This is bad
                        GiveUp tee -> GiveUp tee
                        Node tee step children ->
                            Node tee step (List.map toGiveUp children)


ruleExprRows =
    [ ("and", "A /\\ B")
    , ("or", "A \\/ B")
    , ("implication", "A -> B")
    , ("iff", "A <=> B")
    , ("not", "!A")
    ]


rulesTable =
    table
        []
        ([ tr
            []
            [ th [] []
            , th [] [text "Fact"]
            , th [] [text "Goal"]
            ]
        ]
        ++ (List.map
            (\(name, t) ->
                let row x =
                        styled td
                            [ Css.padding (Css.px 10)
                            ]
                            []
                            [ x ]
                in
                tr
                    []
                    [ row (text name)
                    , row (displayTreeProof <| generateProofRuleFromText t Fact)
                    , row (displayTreeProof <| generateProofRuleFromText t Goal)
                    ]
            )
            ruleExprRows
        ))


descriptionPage =
    div
        []
        [ h1 [] [text "Proof"]
        , ptext """This is a small program that can automatically
                   prove statements about propositional logic. It's still in development."""
        , p
            []
            [ text "Most of the work presented here is derived from "
            , Html.Styled.i [] [text "Designing a Theoreom Prover"]
            , text " by Lawrence C Paulson, and "
            , Html.Styled.i [] [text "Write You a Haskell"]
            , text " by Stephen Diehl."
            ]
        , ptext """At the moment, the program can only prove that things are true. Just because it fails to prove something doesn't mean the statement is false."""
        , ptext """If a given statement p is always false, attempting to prove not p might work. However, for statements which are true under some conditions and false under others, the prover will not be able to make any meaningful conclusions."""
        , h1 [] [text "Rules for booleans"]
        , rulesTable
        ]

sourcePage =
    div
        []
        [ h1 [] [ text "Source" ]
        , p [] [ text """Source code isn't available yet because it's an
                         embarassing mess""" ]
        ]

navButtons =
    [ (PageOverview, "About")
    , (PageExamples, "Examples")
    , (PageInteractive, "Proof Machine")
    , (PageSource, "Source")
    ]

navHeader currentPage =
    let makeButton (page, name) =
            styled div
                [ Css.padding (Css.px 20)
                , Css.borderBottomWidth (Css.px 10)
                , Css.borderBottomColor (Css.rgb 40 250 120)
                , if (page == currentPage)
                  then Css.borderBottomStyle Css.solid
                  else Css.borderBottomStyle Css.hidden
                , Css.display Css.inlineBlock
                ]
                [ onClick (ChangePage page) ]
                [ text name ]
    in
    styled div
        [ Css.padding (Css.px 20)
        , Css.backgroundColor (Css.rgb 240 240 240)
        ]
        []
        (List.map makeButton navButtons)


-- Won't show any errors. This is bad.
typedExamples : List (Expression Type)
typedExamples =
    List.filterMap
        (\e -> case TypeInference.inferTypesFreeFriendly e of
            Err _ -> Nothing
            Ok wellTyped -> Just wellTyped
        )
        ExpressionExamples.allProblems


examplesPage : Html Msg
examplesPage =
    div
        []
        (List.map (\e -> div [] [displayTreeProof <| proveByTree <| goalOnly e]) typedExamples)


--tableRow colTag colValues =
--    tr [] <| List.map (\s -> colTag [] [Html.Styled.code [] [text s]]) colValues

--textTable : List (List String) -> Html a
--textTable rows = table [] <| List.map (tableRow td) rows

--textTableWithHeading : List String -> List (List String) -> Html a
--textTableWithHeading headers rows =
--    table [] <| tableRow th headers :: List.map (tableRow td) rows

textIn tag text_ = tag [] [text text_]


syntaxTable =
    let row notation meaning =
            tr
                []
                [ td [] [textIn Html.Styled.code notation]
                , textIn td meaning
                ]
    in
        styled table
            [ Css.margin (Css.px 10)
            ]
            []
            [ tr
                []
                [ textIn td "Notation"
                , textIn td "Meaning"
                ]
            , row "p /\\ q" "p and q"
            , row "p \\/ q" "p or q"
            , row "!p" "not p"
            , row "p -> q" "p implies q"
            , row "p <=> q" "p if and only if q"
            ]


interactivePage : String -> Bool -> Html Msg
interactivePage expressionInput compactTree =
    let parseResult = BoolExprParser.run expressionInput in
    let typeInferenceResult = Maybe.andThen (TypeInference.inferTypesFreeFriendly >> Result.toMaybe) (Result.toMaybe parseResult) in
    let proofResult = Maybe.map (\expr -> proveByTree (goalOnly expr)) typeInferenceResult in
    div
        []
        [ ptext "Write a boolean expression in here and the algorithm will prove it for you"
        , syntaxTable
        , styled Html.Styled.input
            [ Css.fontSize (Css.em 1.2)
            , Css.minWidth (Css.px 400)
            ]
            [ value expressionInput
            , onInput ChangeExpressionInput
            ]
            []
        , if (expressionInput == "") then
            p [] []
          else
            (case parseResult of
                -- TODO: Better error reporting here
                Err err -> textIn p <| "Couldn't parse input"
                Ok expr -> textIn p <| formatExpressionAsMath expr)
        , styled div
            [ Css.marginBottom (Css.px 10) ]
            []
            [ if compactTree then
                button
                    [ onClick <| ChangeTreeCompactness False ]
                    [ text "Normal view" ]
              else
                button
                    [ onClick <| ChangeTreeCompactness True ]
                    [ text "Compact view" ]
            ]
        , case proofResult of
            Nothing -> p [] []
            Just proof ->
                if compactTree then
                    displayTreeProofCompact proof
                else
                    displayTreeProof proof
        ]


view : Model -> Browser.Document Msg
view model =
    let
        body =
            div
                []
                [ navHeader model.page
                , case model.page of
                    PageOverview -> descriptionPage
                    PageExamples -> examplesPage
                    PageSource -> sourcePage
                    PageInteractive ->
                        interactivePage
                            model.expressionInput
                            model.compactTree
                ]
    in
    { title = "proof-things"
    , body =
        [ Css.Global.global
            [ Css.Global.body
                [ Css.margin (Css.px 20)
                ]
            , Css.Global.everything
                [ Css.boxSizing Css.borderBox
                ]
            ]
            |> toUnstyled
        , body |> toUnstyled
        ]
    }
