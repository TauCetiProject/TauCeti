/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Complex numbers as a Euclidean product

`Complex.equivRealProdLp` identifies a complex number with its real and imaginary coordinates
in the `L²` product of two real lines, preserving the Euclidean inner product.
-/

public section

namespace Complex

/-- The real-linear isometry sending `z` to `(z.re, z.im)` in the `L²` product. -/
noncomputable def equivRealProdLp : ℂ ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (equivRealProdCLM.trans (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm).toLinearEquiv
    |>.isometryOfInner fun z w ↦ by
      simp [WithLp.prod_inner_apply, Complex.inner]

/-- The coordinate isometry sends a complex number to its real and imaginary parts. -/
@[simp]
theorem equivRealProdLp_apply (z : ℂ) :
    equivRealProdLp z = WithLp.toLp 2 (z.re, z.im) := (rfl)

/-- The inverse coordinate isometry sends `(x, y)` to `x + iy`. -/
@[simp]
theorem equivRealProdLp_symm_apply (p : WithLp 2 (ℝ × ℝ)) :
    equivRealProdLp.symm p = (p.fst : ℂ) + p.snd * I := by
  apply equivRealProdLp.injective
  rw [WithLp.ext_iff]
  simp [Prod.ext_iff]

end Complex
