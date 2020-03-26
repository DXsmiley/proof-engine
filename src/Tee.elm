module Tee exposing (..)

import Expression exposing (Expression)
import Type exposing (Type)

-- Facts are things we know (expressions that evaluate to true)
-- Goals are things we are trying to prove
type Tee = Tee
    { facts : List (Expression Type)
    , goals : List (Expression Type)
    }

makeTee : Expression Type -> Expression Type -> Tee
makeTee f g = Tee { facts = [f], goals = [g]}

goalOnly : Expression Type -> Tee
goalOnly g = Tee { facts = [], goals = [g]}

factOnly : Expression Type -> Tee
factOnly f = Tee { facts = [f], goals = []}