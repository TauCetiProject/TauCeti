/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The complex plane as the Euclidean product `ℝ × ℝ`

The complex plane is linearly isometric to the `L²` product `WithLp 2 (ℝ × ℝ)`, the model space
`WithLp 2 (ℝ × E)` with `E = ℝ` on which Lipschitz boundary charts, traces and the flat Sobolev
theory are stated. `Complex.equivRealProdL2` reads the coordinates in the order
`(re z, im z)`, while `Complex.equivRealProdL2Swap` reads them in the order `(im z, re z)`,
so that the normal coordinate `im z` of the upper half-plane comes first, as in the model space.

Both are linear isometries between finite-dimensional real inner product spaces, so they and their
inverses preserve the volume measure: `equivRealProdL2.measurePreserving` and
`equivRealProdL2Swap.symm.measurePreserving` are instances of Mathlib's
`LinearIsometryEquiv.measurePreserving`. The volume of `ℂ` is the measure of its real inner
product space structure, so Lebesgue integrals, `Lᵖ` seminorms, weak derivatives and Lipschitz
domains transport through these equivalences with the generic lemmas for measure-preserving maps
and affine isometries.

## Main declarations

* `Complex.equivRealProdL2`: the linear isometry `z ↦ (re z, im z)`.
* `Complex.equivRealProdL2Swap`: the linear isometry `z ↦ (im z, re z)`.
-/

public section

noncomputable section

namespace Complex

/-- The complex plane as the Euclidean product: the linear isometry `z ↦ (re z, im z)` from `ℂ`
to the `L²` product `WithLp 2 (ℝ × ℝ)`. -/
def equivRealProdL2 : ℂ ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toLinearEquiv := equivRealProdLm.trans (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm
  norm_map' z := by
    simp [WithLp.prod_norm_eq_of_L2, Complex.norm_def, Complex.normSq_apply, ← sq]

@[simp]
theorem equivRealProdL2_apply (z : ℂ) : equivRealProdL2 z = WithLp.toLp 2 (z.re, z.im) := (rfl)

@[simp]
theorem equivRealProdL2_symm_apply (x : WithLp 2 (ℝ × ℝ)) :
    equivRealProdL2.symm x = ⟨x.fst, x.snd⟩ := (rfl)

/-- The complex plane as the Euclidean product with the normal coordinate first: the linear
isometry `z ↦ (im z, re z)` from `ℂ` to the `L²` product `WithLp 2 (ℝ × ℝ)`. It takes the upper
half-plane `{0 < im z}` to the region `{0 < x.fst}` above the graph of zero. -/
def equivRealProdL2Swap : ℂ ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) :=
  equivRealProdL2.trans (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ ℝ)

@[simp]
theorem equivRealProdL2Swap_apply (z : ℂ) :
    equivRealProdL2Swap z = WithLp.toLp 2 (z.im, z.re) := (rfl)

@[simp]
theorem equivRealProdL2Swap_symm_apply (x : WithLp 2 (ℝ × ℝ)) :
    equivRealProdL2Swap.symm x = ⟨x.snd, x.fst⟩ := (rfl)

end Complex
