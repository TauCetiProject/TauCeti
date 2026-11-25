/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.FunctionalCoding
import Mathlib.ModelTheory.Graph

/-!
# The functional coding space for a constant symbol

In the language of one constant symbol, a function table is the value of the constant, and the
graph code of the table with value `3` has unary graph relation `{3}`. The graph codes are not
closed on `ℕ`, while for the relational language of graphs every code is a graph code.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration FunctionalConfiguration

-- In the language of one constant symbol, the graph relation of the constant symbol in the
-- graph code of the table with value `3` holds exactly at `3`.
example (a : (constantsOn Unit).Constants) (y : ℕ) :
    (graphCode (FunctionalConfiguration.mk (fun _ => 3)
        (RelationalConfiguration.mk fun _ => false) :
          FunctionalConfiguration (constantsOn Unit) ℕ)).eval
      (atom (L := (constantsOn Unit).graphLanguage)
        (GraphRelation.graph a) ![y]) = true ↔
      y = 3 := by
  simp [eq_comm]

-- With a function symbol on an infinite carrier, the graph codes are not closed.
example : ¬IsClosed {c : RelationalConfiguration (constantsOn Unit).graphLanguage ℕ |
    IsGraphCode c} :=
  -- The constant symbol is `()`, transported along `constantsOn_constants`.
  not_isClosed_setOf_isGraphCode (cast constantsOn_constants.symm () : (constantsOn Unit).Constants)

-- In the relational language of graphs, every code is a graph code.
example : Set.range (graphCode (L := Language.graph) (V := ℕ)) = Set.univ :=
  range_graphCode_of_isRelational
