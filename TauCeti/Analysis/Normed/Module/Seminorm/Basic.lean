/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Unbounded suprema of seminorms

Mathlib's supremum of a set of seminorms is the pointwise supremum when the set is bounded above
(`Seminorm.sSup_apply`), and the junk value `⊥` otherwise. This file records the junk value:
`Seminorm.sSup_of_not_bddAbove` and `Seminorm.iSup_of_not_bddAbove`, after
`Real.sSup_of_not_bddAbove` and `Real.iSup_of_not_bddAbove`.
-/

public section

namespace Seminorm

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The supremum of a set of seminorms that is not bounded above is the junk value `⊥`. -/
protected theorem sSup_of_not_bddAbove {s : Set (Seminorm 𝕜 E)} (hs : ¬BddAbove s) :
    sSup s = ⊥ :=
  dite_eq_right fun h => (hs (Seminorm.bddAbove_iff.2 h)).elim

/-- The supremum of a family of seminorms that is not bounded above is the junk value `⊥`. -/
protected theorem iSup_of_not_bddAbove {ι : Sort*} {p : ι → Seminorm 𝕜 E}
    (hp : ¬BddAbove (Set.range p)) : ⨆ i, p i = ⊥ :=
  Seminorm.sSup_of_not_bddAbove hp

end Seminorm
