/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard

/-!
# Local bounds for Plücker coordinates

The Euclidean norm of the Plücker vector is at most the product of the Euclidean
norms of the original vectors. For a nonarchimedean absolute value, the analogous
statement holds for maximum norms. These are the local estimates underlying the
height bound for a subspace in terms of a spanning family.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.11).
-/

public section

open scoped BigOperators
open Set

namespace TauCeti

/-- The squared Euclidean norm of a real or complex Plücker vector is bounded by the
product of the squared Euclidean row norms, including empty and dependent families. -/
theorem sum_norm_plucker_sq_le {𝕜 ι : Type*} [RCLike 𝕜] [LinearOrder ι] [Fintype ι] {p : ℕ}
    (x : Fin p → ι → 𝕜) :
    ∑ s, ‖plucker x s‖ ^ 2 ≤ ∏ i, ∑ j, ‖x i j‖ ^ 2 := by
  let v : Fin p → EuclideanSpace 𝕜 ι := fun i ↦ WithLp.toLp 2 (x i)
  have hgram : Matrix.gram 𝕜 v = (Matrix.of x * (Matrix.of x).conjTranspose).transpose := by
    ext i j
    simp [Matrix.gram_apply, v, Matrix.mul_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct]
  have h := Matrix.re_det_gram_le_prod_norm_sq (𝕜 := 𝕜) v
  rw [hgram, Matrix.det_transpose, det_mul_conjTranspose_eq_sum_plucker_mul_star] at h
  simpa only [map_sum, RCLike.star_def, RCLike.mul_conj, RCLike.re_ofReal_pow,
    EuclideanSpace.norm_sq_eq, v, WithLp.ofLp_toLp] using h

end TauCeti

namespace AbsoluteValue

open TauCeti

/-- Every Plücker coordinate is bounded by the product of the maximum row norms
for a nonarchimedean real-valued absolute value. -/
theorem plucker_le_prod_iSup {R ι : Type*} [CommRing R] [LinearOrder ι] [Finite ι]
    {p : ℕ} (v : AbsoluteValue R ℝ) (hv : IsNonarchimedean v)
    (x : Fin p → ι → R) (s : powersetCard ι p) :
    v (plucker x s) ≤ ∏ i, ⨆ j, v (x i j) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (plucker x s) 0, map_zero]
    exact Finset.prod_nonneg fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
  rw [plucker_apply, Matrix.det_apply]
  refine (hv.apply_sum_le_sup Finset.univ_nonempty).trans ?_
  refine Finset.sup'_le _ _ fun σ _ ↦ ?_
  have hsign (a : R) : v (σ.sign • a) = v a := by
    rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
  rw [hsign, map_prod]
  calc
    _ ≤ ∏ i, ⨆ j, v (x (σ i) j) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ v.nonneg _) fun i _ ↦
        Finite.le_ciSup_of_le _ le_rfl
    _ = _ := Equiv.prod_comp σ (fun i ↦ ⨆ j, v (x i j))

end AbsoluteValue
