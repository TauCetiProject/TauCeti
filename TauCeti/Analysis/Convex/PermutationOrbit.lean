/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The convex hull of the permutation orbit of a vector

For a vector `w : ι → R`, its *permutation orbit* is the set of rearrangements `w ∘ σ` of its
coordinates, and the convex hull of this orbit is the permutohedron of `w`. This file records two
facts about this convex hull.

By Birkhoff's theorem every doubly stochastic matrix is a convex combination of permutation
matrices, so the image `M *ᵥ w` of `w` under a doubly stochastic matrix `M` lies in the convex hull
of the permutation orbit of `w`. This is how the diagonal of a symmetric operator in an orthonormal
basis enters the permutohedron of its spectrum.

If the coordinates of `w : ι → ℝ` are pairwise at distance at least `γ ≥ 0`, then every point `c`
of the convex hull of its permutation orbit satisfies the displacement estimate

`(γ / √2) ‖w - c‖ ≤ ⟪w - c, w⟫`,

with the Euclidean norm and inner product written as sums. For a single rearrangement `c = w ∘ σ`
the right-hand side is `‖w - w ∘ σ‖² / 2`, and a nontrivial rearrangement moves at least two
coordinates, each by at least `γ`, so `‖w - w ∘ σ‖ ≥ √2 γ`. The left side of the estimate is
convex in `c` and the right side is affine, so the points where it holds form a convex set, and
the estimate passes to the convex hull. The estimate is the convexity input to Davis's lower
bound on the change of the eigenvalues of a symmetric operator.

## Main results

* `Matrix.mulVec_mem_convexHull_range_comp_perm`: if `M` is doubly stochastic, then `M *ᵥ w` lies
  in the convex hull of the permutation orbit of `w`.
* `TauCeti.mul_sqrt_sum_sq_sub_le_sum_sub_mul_of_mem_convexHull`: the separated-coordinate
  displacement estimate `(γ / √2) ‖w - c‖ ≤ ⟪w - c, w⟫`.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl. **6** (1963),
  159–173; the displacement estimate serves the eigenvalue-change bound of Theorem 4.1.
* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), Chapter 2 (doubly stochastic matrices and Birkhoff's
  theorem).
-/

public section

open Finset Matrix

section Birkhoff

variable {R ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype ι]
  [DecidableEq ι]

/-- **Doubly stochastic images lie in the permutohedron.** If `M` is doubly stochastic, then
`M *ᵥ w` lies in the convex hull of the rearrangements `w ∘ σ` of `w`. -/
theorem Matrix.mulVec_mem_convexHull_range_comp_perm {M : Matrix ι ι R}
    (hM : M ∈ doublyStochastic R ι) (w : ι → R) :
    M *ᵥ w ∈ convexHull R (Set.range fun σ : Equiv.Perm ι ↦ w ∘ σ) := by
  rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hM
  have hlin : IsLinearMap R fun A : Matrix ι ι R ↦ A *ᵥ w :=
    ⟨fun A B ↦ add_mulVec A B w, fun c A ↦ smul_mulVec c A w⟩
  have himage : (fun A : Matrix ι ι R ↦ A *ᵥ w) '' {σ.permMatrix R | σ : Equiv.Perm ι} =
      Set.range fun σ : Equiv.Perm ι ↦ w ∘ σ := by
    ext; simp [permMatrix_mulVec, eq_comm]
  rw [← himage, ← hlin.image_convexHull]
  exact Set.mem_image_of_mem _ hM

end Birkhoff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- For a single rearrangement `w ∘ σ` of a vector `w` with `γ`-separated coordinates, the
displacement estimate `(γ / √2) ‖w - w ∘ σ‖ ≤ ⟪w - w ∘ σ, w⟫`. -/
private theorem mul_sqrt_sum_sq_sub_comp_le {w : ι → ℝ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hw : Pairwise fun i j ↦ γ ≤ |w i - w j|) (σ : Equiv.Perm ι) :
    γ / √2 * √(∑ i, (w i - w (σ i)) ^ 2) ≤ ∑ i, (w i - w (σ i)) * w i := by
  classical
  set Q := ∑ i, (w i - w (σ i)) ^ 2 with hQ
  -- The pairing with `w` is half of the squared distance, since `w ∘ σ` and `w` have the same
  -- Euclidean norm.
  have hpair : ∑ i, (w i - w (σ i)) * w i = Q / 2 := by
    have hσ : ∑ i, w (σ i) ^ 2 = ∑ i, w i ^ 2 := Equiv.sum_comp σ fun i ↦ w i ^ 2
    have hsum : Q = ∑ i, (2 * ((w i - w (σ i)) * w i) + (w (σ i) ^ 2 - w i ^ 2)) :=
      sum_congr rfl fun i _ ↦ by ring
    rw [sum_add_distrib, sum_sub_distrib, hσ, sub_self, add_zero, ← mul_sum] at hsum
    linarith
  rw [hpair]
  have hQ0 : 0 ≤ Q := sum_nonneg fun i _ ↦ sq_nonneg _
  by_cases hσ : σ = 1
  · simp [hQ, hσ]
  -- A nontrivial permutation moves some `i`, and then it also moves `σ i`.
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra! h
    exact hσ (Equiv.ext h)
  have hi' : σ (σ i) ≠ σ i := fun h ↦ hi (σ.injective h)
  have h2 : 2 * γ ^ 2 ≤ Q := by
    have hsub : ({i, σ i} : Finset ι) ⊆ univ := subset_univ _
    calc 2 * γ ^ 2 = γ ^ 2 + γ ^ 2 := by ring
      _ ≤ (w i - w (σ i)) ^ 2 + (w (σ i) - w (σ (σ i))) ^ 2 := by
          rw [← sq_abs (w i - _), ← sq_abs (w (σ i) - _)]
          exact add_le_add (pow_le_pow_left₀ hγ (hw hi.symm) 2)
            (pow_le_pow_left₀ hγ (hw hi'.symm) 2)
      _ = ∑ j ∈ {i, σ i}, (w j - w (σ j)) ^ 2 :=
          (sum_pair (f := fun j ↦ (w j - w (σ j)) ^ 2) hi.symm).symm
      _ ≤ Q := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ sq_nonneg _
  -- Hence `√2 γ ≤ √Q`, and `(γ / √2) √Q ≤ √Q * √Q / 2 = Q / 2`.
  have h2' : 0 < √2 := by positivity
  have hγQ : √2 * γ ≤ √Q := by
    rw [← Real.sqrt_sq hγ, ← Real.sqrt_mul zero_le_two]
    exact Real.sqrt_le_sqrt h2
  calc γ / √2 * √Q = √2 * γ * √Q / 2 := by
        field_simp
        rw [Real.sq_sqrt zero_le_two]
        ring
    _ ≤ √Q * √Q / 2 := by gcongr
    _ = Q / 2 := by rw [Real.mul_self_sqrt hQ0]

/-- **Separated-coordinate displacement estimate.** Let `γ ≥ 0` and let the coordinates of
`w : ι → ℝ` be pairwise at distance at least `γ`. If `c` lies in the convex hull of the
rearrangements `w ∘ σ` of `w`, then `(γ / √2) ‖w - c‖ ≤ ⟪w - c, w⟫` for the Euclidean norm and
inner product. -/
theorem mul_sqrt_sum_sq_sub_le_sum_sub_mul_of_mem_convexHull {w c : ι → ℝ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hw : Pairwise fun i j ↦ γ ≤ |w i - w j|)
    (hc : c ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι ↦ w ∘ σ)) :
    γ / √2 * √(∑ i, (w i - c i) ^ 2) ≤ ∑ i, (w i - c i) * w i := by
  -- The Euclidean length of `w - c`, as the norm in `EuclideanSpace ℝ ι`.
  have hnorm (x : ι → ℝ) : √(∑ i, (w i - x i) ^ 2) = ‖WithLp.toLp 2 (w - x)‖ := by
    simp [EuclideanSpace.norm_eq]
  rw [hnorm]
  refine convexHull_min (t := {x | γ / √2 * ‖WithLp.toLp 2 (w - x)‖ ≤ ∑ i, (w i - x i) * w i})
    ?_ ?_ hc
  · rintro _ ⟨σ, rfl⟩
    rw [Set.mem_ofPred_eq, ← hnorm]
    exact mul_sqrt_sum_sq_sub_comp_le hγ hw σ
  -- The set where the estimate holds is convex: the left side is convex in `c` by the triangle
  -- inequality, and the right side is affine in `c`.
  intro x hx y hy a b ha hb hab
  have hw' : w = a • w + b • w := by rw [← add_smul, hab, one_smul]
  have hsplit : w - (a • x + b • y) = a • (w - x) + b • (w - y) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← hw']
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  calc γ / √2 * ‖WithLp.toLp 2 (w - (a • x + b • y))‖
      ≤ γ / √2 * (a * ‖WithLp.toLp 2 (w - x)‖ + b * ‖WithLp.toLp 2 (w - y)‖) := by
        gcongr
        rw [hsplit, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a * (γ / √2 * ‖WithLp.toLp 2 (w - x)‖) + b * (γ / √2 * ‖WithLp.toLp 2 (w - y)‖) := by
        ring
    _ ≤ a * ∑ i, (w i - x i) * w i + b * ∑ i, (w i - y i) * w i := by gcongr
    _ = ∑ i, (w i - (a • x + b • y) i) * w i := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ ↦ ?_
        have : a * w i + b * w i = w i := by rw [← add_mul, hab, one_mul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination w i * this

end TauCeti
