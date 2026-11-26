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
normalized covector `w.im`. Its origin maps to the zero covector over `-1`, the affine symbol's
unique zero. The angular displacement `2 * arctan (w.re / 2)` has derivative `1` in the real
coordinate at the origin. This centering and scaling give the punctured coordinates for the
local homotopy to complex inversion.

The angular and covector coordinates follow `CircleCotangent.lean` of the Lean-Atiyah-Singer
formalization by Alpha Squared Labs and Codex.
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
-/

public section

noncomputable section

open Set Topology
open Real (boundaryCayley boundaryCayleyHomeomorph)

namespace TauCeti

/-- Scaled Cayley coordinates on the circle minus `1`, with the imaginary coordinate unchanged. -/
def circleIndexAffineHomeomorph : ℂ ≃ₜ ({z : Circle // z ≠ 1} × ℝ) :=
  let scale := (OrderIso.divRight₀ (2 : ℝ) zero_lt_two).toHomeomorph
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((scale.trans boundaryCayleyHomeomorph).prodCongr (Homeomorph.refl ℝ))

/-- The forward chart uses the boundary Cayley point of half the real coordinate. -/
@[simp] theorem circleIndexAffineHomeomorph_apply (w : ℂ) :
    circleIndexAffineHomeomorph w =
      (⟨boundaryCayley (w.re / 2), Real.boundaryCayley_ne_one _⟩, w.im) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [circleIndexAffineHomeomorph]
  · simp [circleIndexAffineHomeomorph]

/-- The inverse chart doubles the real inverse Cayley coordinate and retains the covector. -/
@[simp] theorem circleIndexAffineHomeomorph_symm_apply (p : {z : Circle // z ≠ 1} × ℝ) :
    circleIndexAffineHomeomorph.symm p = ⟨2 * Complex.inverseCayleyCoord p.1, p.2⟩ := by
  apply circleIndexAffineHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, circleIndexAffineHomeomorph_apply]
  apply Prod.ext
  · apply Subtype.ext
    refine (Real.boundaryCayley_inverseCayleyCoord p.1.property).symm.trans ?_
    exact congrArg boundaryCayley (by ring)
  · rfl

/-- Oriented cylinder coordinates for the circle index symbol. The angular displacement from
`-1` is `2 * arctan (w.re / 2)` and `w.im` is the normalized covector. -/
def circleIndexAffineParametrization : ℂ → Circle × ℝ :=
  Prod.map Subtype.val id ∘ circleIndexAffineHomeomorph

/-- The circle point and covector of the Cayley parametrization. -/
@[simp] theorem circleIndexAffineParametrization_apply (w : ℂ) :
    circleIndexAffineParametrization w = (boundaryCayley (w.re / 2), w.im) := by
  simp only [circleIndexAffineParametrization, Function.comp_apply,
    circleIndexAffineHomeomorph_apply, Prod.map_apply', id_eq]

/-- The parametrization is an open embedding into the cylinder. -/
theorem isOpenEmbedding_circleIndexAffineParametrization :
    IsOpenEmbedding circleIndexAffineParametrization := by
  rw [circleIndexAffineParametrization]
  exact (isOpen_compl_singleton.isOpenEmbedding_subtypeVal.prodMap
    (IsOpenEmbedding.id (X := ℝ))).comp circleIndexAffineHomeomorph.isOpenEmbedding

/-- The parametrization covers exactly the covectors based away from `1`. -/
theorem range_circleIndexAffineParametrization :
    range circleIndexAffineParametrization = {p : Circle × ℝ | p.1 ≠ 1} := by
  rw [circleIndexAffineParametrization, EquivLike.range_comp, Set.range_prodMap,
    Subtype.range_val_subtype, Set.range_id, Set.prod_univ]
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]

end TauCeti
