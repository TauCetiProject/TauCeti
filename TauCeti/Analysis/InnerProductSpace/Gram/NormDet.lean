/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Gram determinants of images of a basis

A linear map multiplies the Gram determinant of any basis by the square of its norm
determinant. In particular, the ratio of the Gram determinants obtained by applying two maps
to the same basis is independent of the basis. The codomains can be different and need not be
finite-dimensional.

The ratio is the identity used to compare twists in `New.TwistedLattice.covolume_add_index_nonneg`
in `grh/src/New/Reduction/Lattices/TwistedLattice.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
Here it follows from `LinearMap.normDet_comp_of_finrank_eq` in Mathlib.
-/

public section

namespace LinearMap

variable {𝕜 U V W ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The Gram determinant of the image of a basis is the original Gram determinant times
the square of the norm determinant of the map. -/
theorem det_gram_comp_basis_eq_normDet_sq_mul (f : U →ₗ[𝕜] V) (b : Module.Basis ι 𝕜 U) :
    (Matrix.gram 𝕜 (f ∘ b)).det = (↑(f.normDet ^ 2) : 𝕜) * (Matrix.gram 𝕜 b).det := by
  let a₀ := stdOrthonormalBasis 𝕜 U
  let a := a₀.reindex (a₀.toBasis.indexEquiv b)
  let A : U →ₗ[𝕜] U := (a.toBasis.equiv b (Equiv.refl ι)).toLinearMap
  have hA (i : ι) : A (a i) = b i := by
    simp [A, ← OrthonormalBasis.coe_toBasis]
  have h₁ : (↑(A.normDet ^ 2) : 𝕜) = (Matrix.gram 𝕜 b).det := by
    simpa only [hA] using A.normDet_sq_eq_det_gram a
  have h₂ : (↑((f ∘ₗ A).normDet ^ 2) : 𝕜) = (Matrix.gram 𝕜 (f ∘ b)).det := by
    simpa only [LinearMap.comp_apply, hA, Function.comp_def] using
      (f ∘ₗ A).normDet_sq_eq_det_gram a
  rw [← h₂, A.normDet_comp_of_finrank_eq f rfl, mul_pow, RCLike.ofReal_mul, h₁]

/-- The ratio of the Gram determinants of the images of a common basis under two maps
is the ratio of the squared norm determinants of the maps. The identity also holds for a
noninjective denominator map, since both denominators then vanish. -/
theorem det_gram_comp_basis_div_det_gram_comp_basis [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] (f : U →ₗ[𝕜] V) (g : U →ₗ[𝕜] W) (b : Module.Basis ι 𝕜 U) :
    (Matrix.gram 𝕜 (f ∘ b)).det / (Matrix.gram 𝕜 (g ∘ b)).det =
      (↑(f.normDet ^ 2) : 𝕜) / ↑(g.normDet ^ 2) := by
  rw [f.det_gram_comp_basis_eq_normDet_sq_mul b, g.det_gram_comp_basis_eq_normDet_sq_mul b]
  exact mul_div_mul_right _ _
    (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent)

end LinearMap
