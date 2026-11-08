/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Order.Filter.Extr

/-!
# Positive-semidefinite bilinear forms

This file records a pointwise characterization of positive semidefiniteness for symmetric
bilinear forms. It converts `IsPosSemidef` into diagonal nonnegativity, the form consumed by
quadratic-form signature criteria and other pointwise positivity arguments. Over an ordered ring,
it also bounds the value of a positive-semidefinite form on a sum of `k` vectors by `k` times the
sum of their values, the inequality `‖x₁ + ⋯ + xₖ‖² ≤ k (‖x₁‖² + ⋯ + ‖xₖ‖²)` of inner product
spaces. Over an ordered field, a positive-semidefinite form satisfies the Dirichlet principle: the
solutions of `B(u, ·) = ℓ` are the minimizers of `v ↦ B(v, v) / 2 - ℓ v`.

## Main results

* `LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg`: a symmetric bilinear form is
  positive-semidefinite exactly when its diagonal values are nonnegative.
* `LinearMap.BilinForm.IsPosSemidef.apply_sum_sum_le_card_mul_sum`: the value of a
  positive-semidefinite form on a sum of vectors is at most the number of summands times the sum
  of their values.
* `LinearMap.BilinForm.apply_sq_le_mul_of_apply_le_apply`: Cauchy-Schwarz against a majorant, for
  a symmetric form with nonnegative diagonal.
* `LinearMap.BilinForm.IsPosSemidef.forall_apply_eq_iff_isMinOn`: the **Dirichlet principle**. Over
  an ordered field, `u` solves `B(u, v) = ℓ v` for every `v` exactly when it minimizes the quadratic
  functional `v ↦ B(v, v) / 2 - ℓ v`. This is the variational form of the weak formulation of a
  symmetric elliptic problem.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Corollary
  5.8 (the minimization characterization in the Lax--Milgram theorem for symmetric forms).
-/

open Set

public section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [LE R]

/-- A symmetric bilinear form is positive-semidefinite if and only if its values on all vectors
are nonnegative. -/
@[grind =]
theorem isPosSemidef_iff_forall_nonneg (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ ∀ x, 0 ≤ B x x := by
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [hB, true_and]

section OrderedRing

variable {R M ι : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M]

/-- A positive-semidefinite bilinear form satisfies
`B (x₁ + ⋯ + xₖ) (x₁ + ⋯ + xₖ) ≤ k * (B x₁ x₁ + ⋯ + B xₖ xₖ)`. -/
theorem IsPosSemidef.apply_sum_sum_le_card_mul_sum {B : LinearMap.BilinForm R M}
    (hB : B.IsPosSemidef) (s : Finset ι) (x : ι → M) :
    B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤ s.card * ∑ i ∈ s, B (x i) (x i) := by
  -- Each cross term satisfies `2 B(x, y) ≤ B(x, x) + B(y, y)`, since `B(x - y, x - y) ≥ 0`.
  have hpair (i j : ι) : 2 * B (x i) (x j) ≤ B (x i) (x i) + B (x j) (x j) := by
    have h := hB.isNonneg.nonneg (x i - x j)
    simp only [map_sub, LinearMap.sub_apply, hB.isSymm.eq (x j) (x i)] at h
    linarith
  have hsum : 2 * B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤
      2 * (s.card * ∑ i ∈ s, B (x i) (x i)) := by
    simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
    calc ∑ j ∈ s, ∑ i ∈ s, 2 * B (x i) (x j)
        ≤ ∑ j ∈ s, ∑ i ∈ s, (B (x i) (x i) + B (x j) (x j)) :=
          Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun i _ ↦ hpair i j
      _ = ∑ i ∈ s, 2 * (s.card * B (x i) (x i)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  exact le_of_mul_le_mul_left hsum two_pos

/-- **Cauchy-Schwarz against a majorant.** If `F` is a symmetric positive semidefinite bilinear
form and `F x x ≤ F x z`, then `F x v ^ 2 ≤ F z z * F v v` for every `v`. -/
theorem apply_sq_le_mul_of_apply_le_apply {K V : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]
    (F : LinearMap.BilinForm K V) (hnonneg : ∀ x, 0 ≤ F x x) (hsymm : LinearMap.IsSymm F)
    {x z : V} (hle : F x x ≤ F x z) (v : V) : F x v ^ 2 ≤ F z z * F v v := by
  -- The hypothesis first bounds `F x x` by `F z z`, and then Cauchy-Schwarz bounds `F x v`.
  have hbound : F x x ≤ F z z := by
    rcases eq_or_lt_of_le (hnonneg x) with h0 | h0
    · exact h0 ▸ hnonneg z
    · refine le_of_mul_le_mul_left ?_ h0
      refine (mul_self_le_mul_self h0.le hle).trans ?_
      rw [← pow_two]
      exact F.apply_sq_le_of_symm hnonneg hsymm _ z
  exact (F.apply_sq_le_of_symm hnonneg hsymm x v).trans
    (mul_le_mul_of_nonneg_right hbound (hnonneg v))

end OrderedRing

section OrderedField

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M]
  [Module K M]

/-- **The Dirichlet principle.** For a positive-semidefinite bilinear form `B` and a linear
functional `ℓ` over an ordered field, `u` satisfies `B(u, v) = ℓ v` for every `v` exactly when
it minimizes the quadratic functional `v ↦ B(v, v) / 2 - ℓ v`. -/
theorem IsPosSemidef.forall_apply_eq_iff_isMinOn {B : LinearMap.BilinForm K M}
    (hB : B.IsPosSemidef) (ℓ : Module.Dual K M) (u : M) :
    (∀ v, B u v = ℓ v) ↔ IsMinOn (fun v => B v v / 2 - ℓ v) univ u := by
  -- Along the line `u + t • v` the functional exceeds its value at `u` by
  -- `t (B(u, v) - ℓ v) + t² B(v, v) / 2`.
  have hline (t : K) (v : M) : B (u + t • v) (u + t • v) / 2 - ℓ (u + t • v) =
      B u u / 2 - ℓ u + t * (B u v - ℓ v) + t ^ 2 * (B v v / 2) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.isSymm.eq v u]
    ring
  rw [isMinOn_univ_iff]
  constructor
  · intro h x
    have hx := hline 1 (x - u)
    rw [one_smul, add_sub_cancel] at hx
    linarith [h (x - u), hB.isNonneg.nonneg (x - u)]
  · intro h v
    -- The excess is nonnegative along the whole line, so its linear coefficient `A` vanishes:
    -- at `t = -A / (B(v, v) + 1)` it equals `-A² (B(v, v) + 2) / (2 (B(v, v) + 1)²)`.
    set A := B u v - ℓ v
    have hQ := hB.isNonneg.nonneg v
    have hs : 0 < B v v + 1 := by linarith
    have ht := h (u + (-A / (B v v + 1)) • v)
    rw [hline] at ht
    have hA : A ^ 2 * (B v v + 2) ≤ 0 := by
      have h₂ : 0 ≤ -A / (B v v + 1) * A + (-A / (B v v + 1)) ^ 2 * (B v v / 2) := by linarith
      rw [div_pow, ← sub_nonneg] at h₂
      field_simp at h₂
      nlinarith
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg A]) (sq_nonneg A)))

end OrderedField

end LinearMap.BilinForm
