module Scheme exposing (Scheme(..), freeTypeVariables)

import Set exposing (Set)

import Type exposing (Type(..))

-- Declares that a type is polymorphic across some type variables
type Scheme = ForAll (List String) Type

freeTypeVariables : Scheme -> Set String
freeTypeVariables (ForAll names type_) =
    Set.diff (Type.freeTypeVariables type_) (Set.fromList names)
