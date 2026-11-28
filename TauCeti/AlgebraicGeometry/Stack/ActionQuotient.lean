/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import TauCeti.AlgebraicGeometry.Stack.Stackification
public import TauCeti.CategoryTheory.Sites.Descent.ActionQuotient

/-!
# The fppf quotient stack of an action

`CategoryTheory.Over.actionQuotient` specializes `ModObj.actionQuotient` to the big fppf site.
Its projection is locally essentially surjective by `ModObj.actionQuotient.isLocallyEssSurj_π`.
-/

public noncomputable section

open _root_.AlgebraicGeometry (Scheme)

namespace CategoryTheory.Over

/-- The quotient stack `[X/G]` of an action on the big fppf site of `S`. For a group
scheme `G`, this is the construction of Stacks, Definition 78.20.1 (044Q). -/
abbrev actionQuotient {S : Scheme} (G X : Over S) [MonObj G] [ModObj G X] :=
  ModObj.actionQuotient G X (Scheme.fppfTopology.over S)

end CategoryTheory.Over
