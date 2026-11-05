/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Evaluation of signed words in presented groups

A signed word is a list of pairs `(x, b)`, with `true` denoting a generator and `false` its
inverse. This file gives the product formula for the image of such a word under the quotient map
to a presented group. The corresponding formulas for free groups are in
`TauCeti.GroupTheory.FreeGroup.Basic`.

## Main results

* `PresentedGroup.mk_mk`: the class of a word is the product of its signed generators.
-/

public section

namespace PresentedGroup

/-- The image of a word in a presented group is the product of the images of its signed
letters. -/
theorem mk_mk {α : Type*} (S : Set (FreeGroup α)) (L : List (α × Bool)) :
    mk S (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (of p.1) (of p.1)⁻¹).prod :=
  (mk S).apply_freeGroup_mk L

end PresentedGroup
