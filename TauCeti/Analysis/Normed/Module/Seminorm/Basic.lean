/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Unbounded suprema of seminorms, and bounds by combinations of seminorms

Mathlib's supremum of a set of seminorms is the pointwise supremum when the set is bounded above
(`Seminorm.sSup_apply`), and the junk value `⊥` otherwise. This file records the junk value:
`Seminorm.sSup_of_not_bddAbove` and `Seminorm.iSup_of_not_bddAbove`, after
`Real.sSup_of_not_bddAbove` and `Real.iSup_of_not_bddAbove`.

It also records how two weighted bounds `w ‖g‖ ≤ K p₁ u` and `w ‖c‖ ≤ p₂ u` combine into a bound
of `w ‖g + c‖` by the single seminorm `K • p₁ + p₂` (`Seminorm.mul_norm_add_le_smul_add_apply`),
the step that turns estimates of the parts of a sum into a continuous seminorm.
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

/-- **Combining two weighted bounds into one seminorm.** If `w ‖g‖ ≤ K p₁ u` and
`w ‖c‖ ≤ p₂ u`, with `w, K ≥ 0`, then `w ‖g + c‖ ≤ (K • p₁ + p₂) u`. -/
theorem mul_norm_add_le_smul_add_apply {G : Type*} [SeminormedAddCommGroup G]
    (p₁ p₂ : Seminorm 𝕜 E) (u : E) {w K : ℝ} (hw : 0 ≤ w) (hK : 0 ≤ K) {g c : G}
    (hg : w * ‖g‖ ≤ K * p₁ u) (hc : w * ‖c‖ ≤ p₂ u) :
    w * ‖g + c‖ ≤ (K.toNNReal • p₁ + p₂) u :=
  calc w * ‖g + c‖ ≤ w * ‖g‖ + w * ‖c‖ := by rw [← mul_add]; gcongr; exact norm_add_le _ _
    _ ≤ K * p₁ u + p₂ u := add_le_add hg hc
    _ = (K.toNNReal • p₁ + p₂) u := by simp [NNReal.smul_def, Real.coe_toNNReal _ hK]

end Seminorm
