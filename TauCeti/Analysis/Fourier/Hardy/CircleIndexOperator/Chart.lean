/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Cayley

/-!
# Cayley coordinates for the circle index symbol

The parametrization sends `w : ℂ` to the circle point `Real.boundaryCayley (w.re / 2)` and the
normalized covector `w.im`. The real coordinate increases with the angle and the origin maps
to the zero covector over `-1`.

The angular and covector coordinates follow `CircleCotangent.lean` of the Lean-Atiyah-Singer
formalization by Alpha Squared Labs and Codex.
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
-/

public section

noncomputable section

open Set Topology
open Real (boundaryCayley boundaryCayleyHomeomorph
  boundaryCayleyHomeomorph_apply boundaryCayley_eq_neg_exp)

namespace TauCeti

/-- Oriented cylinder coordinates for the circle index symbol. The angular displacement from
`-1` is `2 * arctan (w.re / 2)` and `w.im` is the normalized covector. -/
def circleIndexAffineParametrization (w : ℂ) : Circle × ℝ := (boundaryCayley (w.re / 2), w.im)

/-- The circle point and covector of the Cayley parametrization. -/
theorem circleIndexAffineParametrization_apply (w : ℂ) :
    circleIndexAffineParametrization w = (boundaryCayley (w.re / 2), w.im) := (rfl)

/-- The origin maps to the zero covector over `-1`. -/
@[simp] theorem circleIndexAffineParametrization_zero :
    circleIndexAffineParametrization 0 = (-1, 0) := by
  simp [circleIndexAffineParametrization_apply, boundaryCayley_eq_neg_exp]

private def circleIndexAffineHomeomorph : ℂ ≃ₜ ({z : Circle // z ≠ 1} × ℝ) :=
  let scale := (OrderIso.divRight₀ (2 : ℝ) zero_lt_two).toHomeomorph
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((scale.trans boundaryCayleyHomeomorph).prodCongr (Homeomorph.refl ℝ))

private theorem circleIndexAffineParametrization_eq :
    circleIndexAffineParametrization = Prod.map Subtype.val id ∘ circleIndexAffineHomeomorph := by
  funext w
  simp [circleIndexAffineParametrization, circleIndexAffineHomeomorph, Prod.map]

/-- The parametrization is an open embedding into the cylinder. -/
theorem isOpenEmbedding_circleIndexAffineParametrization :
    IsOpenEmbedding circleIndexAffineParametrization := by
  rw [circleIndexAffineParametrization_eq]
  exact (isOpen_compl_singleton.isOpenEmbedding_subtypeVal.prodMap
    (IsOpenEmbedding.id (X := ℝ))).comp circleIndexAffineHomeomorph.isOpenEmbedding

/-- The parametrization covers exactly the covectors based away from `1`. -/
theorem range_circleIndexAffineParametrization :
    range circleIndexAffineParametrization = {p : Circle × ℝ | p.1 ≠ 1} := by
  rw [circleIndexAffineParametrization_eq, EquivLike.range_comp, Set.range_prodMap,
    Subtype.range_val_subtype, Set.range_id, Set.prod_univ]
  rfl

end TauCeti
