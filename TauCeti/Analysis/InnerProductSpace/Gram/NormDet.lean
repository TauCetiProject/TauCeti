/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Gram determinants of images of vector families

A linear map multiplies the Gram determinant of a family of size equal to the dimension
of the domain by the square of its norm determinant. The family may be linearly dependent.
For a basis, the ratio of the Gram determinants obtained by applying two maps is independent
of the basis. The codomains can be different and need not be finite-dimensional.

The ratio is the identity used to compare twists in `New.TwistedLattice.covolume_add_index_nonneg`
in `grh/src/New/Reduction/Lattices/TwistedLattice.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
The family formula adapts `New.det_gram_comp` from
`src/Lib/General/LinearAlgebra/GramDeterminant.lean` in the
[Lean RH formalization](https://github.com/leanprover-community/riemann-hypothesis)
(Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace LinearMap

variable {𝕜 U V W ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The Gram determinant of the image of a family of `finrank 𝕜 U` vectors is the
original Gram determinant times the square of the norm determinant of the map. -/
theorem det_gram_comp_eq_normDet_sq_mul (f : U →ₗ[𝕜] V) (v : ι → U)
    (h_card : Module.finrank 𝕜 U = Fintype.card ι) :
    (Matrix.gram 𝕜 (f ∘ v)).det = (↑(f.normDet ^ 2) : 𝕜) * (Matrix.gram 𝕜 v).det := by
  let e := EuclideanSpace.basisFun ι 𝕜
  let A : EuclideanSpace 𝕜 ι →ₗ[𝕜] U := e.toBasis.constr 𝕜 v
  have hA (i : ι) : A (e i) = v i := e.toBasis.constr_basis 𝕜 v i
  have h_gram : (↑(A.normDet ^ 2) : 𝕜) = (Matrix.gram 𝕜 v).det := by
    simpa only [hA] using A.normDet_sq_eq_det_gram e
  have h_comp : (↑((f ∘ₗ A).normDet ^ 2) : 𝕜) = (Matrix.gram 𝕜 (f ∘ v)).det := by
    simpa only [LinearMap.comp_apply, hA, Function.comp_def] using
      (f ∘ₗ A).normDet_sq_eq_det_gram e
  rw [← h_comp, A.normDet_comp_of_finrank_eq f (by simp [h_card]), mul_pow,
    RCLike.ofReal_mul, h_gram]

/-- The ratio of the Gram determinants of the images of a common basis under two maps
is the ratio of the squared norm determinants of the maps. The identity also holds for a
noninjective denominator map, since both denominators then vanish. -/
theorem det_gram_comp_basis_div_det_gram_comp_basis [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] (f : U →ₗ[𝕜] V) (g : U →ₗ[𝕜] W) (b : Module.Basis ι 𝕜 U) :
    (Matrix.gram 𝕜 (f ∘ b)).det / (Matrix.gram 𝕜 (g ∘ b)).det =
      (↑(f.normDet ^ 2) : 𝕜) / ↑(g.normDet ^ 2) := by
  have h_card := Module.finrank_eq_card_basis b
  rw [f.det_gram_comp_eq_normDet_sq_mul b h_card, g.det_gram_comp_eq_normDet_sq_mul b h_card]
  exact mul_div_mul_right _ _
    (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent)

end LinearMap
