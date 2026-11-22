/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.LinearAlgebra.Vandermonde

/-!
# Root bounds from bounds on weighted moments

Let `K` be a normed field, `β` a finite family of elements of `K` (the *roots*) and `c` a family of
weights. The weighted moments are the sums `∑ i, c i * β i ^ n`. This file shows that a growth
bound on the moments, such as an eventual bound `‖∑ i, c i * β i ^ n‖ ≤ C * R ^ n`, bounds every
root that the moments can see:

* for pairwise distinct roots, every root with a nonzero weight has norm at most `R`;
* for arbitrary roots, every root whose *total* weight, the sum of the weights of all indices
  carrying that root, is nonzero has norm at most `R`;
* in characteristic zero, the unweighted power sums `∑ i, α i ^ n` are eventually bounded by a
  multiple of `R ^ n` if and only if every root has norm at most `R`;
* if the moments are `o(R ^ n)` for some `R > 0`, every visible root, distinct with nonzero weight
  or of nonzero total weight, has norm strictly less than `R`.

This is the finite-spectrum argument behind deducing the Riemann hypothesis over finite fields from
point-count estimates: the point counts `#X(𝔽_{qⁿ})` are alternating sums of powers of the
Frobenius eigenvalues, and an estimate for all `n` bounds every eigenvalue that does not cancel.

The proof recovers a weighted power `c k * β k ^ n` from the window of moments of orders
`n, n + 1, …, n + d - 1` through the inverse Vandermonde matrix
(`TauCeti.mul_pow_eq_sum_inv_vandermonde_mul_sum_mul_pow_add`), which gives the quantitative
estimate `‖c k‖ * ‖β k‖ ^ n ≤ C * R ^ n * ∑ j, ‖(vandermonde β)⁻¹ j k‖ * R ^ j` with a window
constant independent of `n`. Repeated roots are first grouped, which leaves every moment unchanged.
No completeness and no hypothesis on the characteristic are needed, except to see that a root of
positive multiplicity carries a nonzero total weight in the unweighted case.

## Main results

* `TauCeti.norm_mul_norm_pow_le_of_moment_bound`: the quantitative moment-window bound.
* `TauCeti.norm_le_of_moment_bound`: an eventual moment bound bounds every distinct root of
  nonzero weight.
* `TauCeti.norm_le_of_grouped_moment_bound`: an eventual moment bound bounds every root of nonzero
  total weight.
* `TauCeti.norm_le_of_sum_pow_bound` and `TauCeti.forall_norm_le_iff_exists_sum_pow_bound`: the
  unweighted power-sum criterion in characteristic zero.
* `TauCeti.exists_one_lt_norm_sum_mul_inv_pow`: weighted moments of the inverses of distinct roots
  inside the open unit ball leave the closed unit ball infinitely often.
* `TauCeti.sum_mul_pow_eq_sum_image_mul_pow`: grouping a weighted moment by roots.
* `TauCeti.norm_lt_of_moment_isLittleO` and `TauCeti.norm_lt_of_grouped_moment_isLittleO`: the
  strict root bound from little-o moments, for distinct and for grouped roots.

## References

* Hongjie Yu, *Comptage des systèmes locaux ℓ-adiques sur une courbe*, arXiv:1807.04659,
  Appendix C, the finite-spectrum lemma on p. 81.
* Mircea Mustata, *Zeta functions in algebraic geometry*, §3.3, the root bound from estimates for
  all powers.
* Jeroen van den Bogaart, Bas Edixhoven, *Algebraic stacks whose number of points over finite
  fields is a polynomial*, in: Number fields and function fields, Progr. Math. 239 (2005),
  Lemma 4.1 and its proof, pp. 6–7, the strict bound from little-o moments.
-/

public section

namespace TauCeti

open Asymptotics Filter Finset Matrix

variable {K : Type*} [NormedField K]

/-- **The quantitative moment-window bound.** If the weighted moments of pairwise distinct roots
`β` with weights `c` satisfy `‖∑ i, c i * β i ^ m‖ ≤ C * R ^ m` for all `m ≥ N`, then for `n ≥ N`
the weighted power `c k * β k ^ n` is bounded by `C * R ^ n` times a window constant, which
depends on `β`, `k` and `R` but not on `n`. -/
theorem norm_mul_norm_pow_le_of_moment_bound {d : ℕ} {β : Fin d → K} (hβ : Function.Injective β)
    {c : Fin d → K} {C R : ℝ} {N : ℕ}
    (hbound : ∀ m, N ≤ m → ‖∑ i, c i * β i ^ m‖ ≤ C * R ^ m) (k : Fin d) {n : ℕ} (hn : N ≤ n) :
    ‖c k‖ * ‖β k‖ ^ n ≤ C * R ^ n * ∑ j, ‖(vandermonde β)⁻¹ j k‖ * R ^ (j : ℕ) := by
  rw [← norm_pow, ← norm_mul, mul_pow_eq_sum_inv_vandermonde_mul_sum_mul_pow_add hβ c n k,
    mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul]
  calc ‖(vandermonde β)⁻¹ j k‖ * ‖∑ i, c i * β i ^ (n + j)‖
      ≤ ‖(vandermonde β)⁻¹ j k‖ * (C * R ^ (n + j)) :=
        mul_le_mul_of_nonneg_left (hbound _ (hn.trans (Nat.le_add_right n j))) (norm_nonneg _)
    _ = C * R ^ n * (‖(vandermonde β)⁻¹ j k‖ * R ^ (j : ℕ)) := by ring

/-- **Distinct roots of nonzero weight are bounded by the growth rate of the moments.** If the
weighted moments of pairwise distinct roots `β` with weights `c` are eventually bounded by
`C * R ^ n`, then every root of nonzero weight has norm at most `R`. A root of zero weight is
invisible to the moments and is not bounded. -/
theorem norm_le_of_moment_bound {ι : Type*} [Fintype ι] {β : ι → K} (hβ : Function.Injective β)
    {c : ι → K} {C R : ℝ} (hR : 0 ≤ R) {N : ℕ}
    (hbound : ∀ n, N ≤ n → ‖∑ i, c i * β i ^ n‖ ≤ C * R ^ n) {k : ι} (hk : c k ≠ 0) :
    ‖β k‖ ≤ R := by
  -- Transport the roots to `Fin d`, where the Vandermonde matrix lives.
  let e := Fintype.equivFin ι
  set M := C * ∑ j, ‖(vandermonde (β ∘ e.symm))⁻¹ j (e k)‖ * R ^ (j : ℕ)
  have hwindow : ∀ n, N ≤ n → ‖c k‖ * ‖β k‖ ^ n ≤ M * R ^ n := fun n hn ↦ by
    have h := norm_mul_norm_pow_le_of_moment_bound (hβ.comp e.symm.injective) (c := c ∘ e.symm)
      (fun m hm ↦ by simpa [e.symm.sum_comp fun i ↦ c i * β i ^ m] using hbound m hm) (e k) hn
    simpa [M, mul_right_comm C] using h
  -- If `R < ‖β k‖`, then `‖c k‖ ≤ M * (R / ‖β k‖) ^ n` for large `n`, and the right side tends to
  -- zero.
  by_contra! hlt
  have hpos : 0 < ‖β k‖ := hR.trans_lt hlt
  have htend : Tendsto (fun n : ℕ ↦ M * (R / ‖β k‖) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hpos.le)
      ((div_lt_one hpos).2 hlt)).const_mul M
  refine (norm_pos_iff.2 hk).not_ge (ge_of_tendsto htend ?_)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hpos n)]
  exact hwindow n hn

/-- **Grouping a weighted moment by roots.** The weighted moment of a finite family of roots `α`
with weights `w` is the weighted moment of the distinct roots in the image of `α`, each weighted by
the total weight of the indices carrying it. -/
theorem sum_mul_pow_eq_sum_image_mul_pow {ι : Type*} [Fintype ι] [DecidableEq K] (α w : ι → K)
    (n : ℕ) :
    ∑ i, w i * α i ^ n = ∑ b : univ.image α, (∑ i with α i = b, w i) * (b : K) ^ n := by
  rw [← sum_fiberwise_of_maps_to (g := α) fun i _ ↦ mem_image_of_mem α (mem_univ i),
    ← sum_coe_sort (univ.image α)]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [sum_mul]
  exact sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]

/-- **Roots of nonzero total weight are bounded by the growth rate of the moments.** Let `α` be a
finite family of roots, possibly with repetitions, and `w` a family of weights. If the weighted
moments `∑ i, w i * α i ^ n` are eventually bounded by `C * R ^ n`, then every root whose total
weight, summed over all the indices carrying that root, is nonzero has norm at most `R`.

A nonzero individual weight does not suffice: the weights of a repeated root may cancel. -/
theorem norm_le_of_grouped_moment_bound {ι : Type*} [Fintype ι] [DecidableEq K] {α w : ι → K}
    {C R : ℝ} (hR : 0 ≤ R) {N : ℕ}
    (hbound : ∀ n, N ≤ n → ‖∑ i, w i * α i ^ n‖ ≤ C * R ^ n) {j : ι}
    (hw : ∑ i with α i = α j, w i ≠ 0) : ‖α j‖ ≤ R :=
  norm_le_of_moment_bound (β := fun b : univ.image α ↦ (b : K)) Subtype.val_injective hR
    (fun n hn ↦ sum_mul_pow_eq_sum_image_mul_pow α w n ▸ hbound n hn)
    (k := ⟨α j, mem_image_of_mem α (mem_univ j)⟩) hw

/-- **The power-sum criterion in characteristic zero.** If the power sums `∑ i, α i ^ n` of a
finite family of elements of a normed field of characteristic zero are eventually bounded by
`C * R ^ n`, then every `α i` has norm at most `R`. Neither distinctness nor nonvanishing of the
roots is needed: a repeated root carries its multiplicity as total weight, which is nonzero in
characteristic zero. -/
theorem norm_le_of_sum_pow_bound [CharZero K] {ι : Type*} [Fintype ι] {α : ι → K} {C R : ℝ}
    (hR : 0 ≤ R) {N : ℕ} (hbound : ∀ n, N ≤ n → ‖∑ i, α i ^ n‖ ≤ C * R ^ n) (j : ι) :
    ‖α j‖ ≤ R := by
  classical
  refine norm_le_of_grouped_moment_bound (w := 1) hR (by simpa using hbound) ?_
  simp

/-- **Root bounds are equivalent to power-sum bounds for all positive powers.** In characteristic
zero, every `α i` has norm at most `R` if and only if the power sums `∑ i, α i ^ n` are bounded by
`C * R ^ n` for some `C ≥ 0` and every `n ≥ 1`. In the forward direction `C` is the number of
roots. -/
theorem forall_norm_le_iff_exists_sum_pow_bound [CharZero K] {ι : Type*} [Fintype ι]
    {α : ι → K} {R : ℝ} (hR : 0 ≤ R) :
    (∀ i, ‖α i‖ ≤ R) ↔ ∃ C, 0 ≤ C ∧ ∀ n, 1 ≤ n → ‖∑ i, α i ^ n‖ ≤ C * R ^ n := by
  refine ⟨fun h ↦ ⟨Fintype.card ι, Nat.cast_nonneg _, fun n _ ↦ ?_⟩,
    fun ⟨C, _, hC⟩ ↦ norm_le_of_sum_pow_bound hR hC⟩
  calc ‖∑ i, α i ^ n‖ ≤ ∑ i, ‖α i‖ ^ n := by simpa using norm_sum_le univ fun i ↦ α i ^ n
    _ ≤ ∑ _i : ι, R ^ n := sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h i) n
    _ = Fintype.card ι * R ^ n := by simp

/-- **Moments of inverse roots escape the unit ball.** Let `γ` be pairwise distinct elements of a
normed field and `c` weights. If some `γ k` with `c k ≠ 0` lies in the punctured open unit ball,
then for every `N` there is a positive `n ≥ N` with `1 < ‖∑ i, c i * (γ i)⁻¹ ^ n‖`. -/
theorem exists_one_lt_norm_sum_mul_inv_pow {ι : Type*} [Fintype ι] {γ : ι → K}
    (hγ : Function.Injective γ) {c : ι → K} {k : ι} (hk : c k ≠ 0) (hγk : γ k ≠ 0)
    (hγk' : ‖γ k‖ < 1) (N : ℕ) : ∃ n, N ≤ n ∧ 0 < n ∧ 1 < ‖∑ i, c i * (γ i)⁻¹ ^ n‖ := by
  by_contra! h
  have hle := norm_le_of_moment_bound (β := fun i ↦ (γ i)⁻¹) (inv_injective.comp hγ)
    (C := 1) zero_le_one (N := N + 1) (fun n hn ↦ by simpa using h n (by omega) (by omega)) hk
  rw [norm_inv] at hle
  exact (one_lt_inv₀ (norm_pos_iff.2 hγk)).2 hγk' |>.not_ge hle

/-! ### Strict bounds from little-o moments -/

/-- **Distinct roots of nonzero weight lie strictly inside the radius of little-o moments.** If
the weighted moments of pairwise distinct roots `β` with weights `c` are `o(R ^ n)` for some
`R > 0`, then every root of nonzero weight has norm strictly less than `R`. A root of zero weight
is invisible to the moments and is not bounded. -/
theorem norm_lt_of_moment_isLittleO {ι : Type*} [Fintype ι] {β : ι → K}
    (hβ : Function.Injective β) {c : ι → K} {R : ℝ} (hR : 0 < R)
    (ho : (fun n ↦ ∑ i, c i * β i ^ n) =o[atTop] fun n ↦ R ^ n) {k : ι} (hk : c k ≠ 0) :
    ‖β k‖ < R := by
  -- Transport the roots to `Fin d`, where the Vandermonde matrix lives, and recover the weighted
  -- power `c k * β k ^ n` from the window of moments of orders `n, …, n + d - 1`.
  let e := Fintype.equivFin ι
  have hrec : (fun n ↦ c k * β k ^ n) = fun n ↦ ∑ j, (vandermonde (β ∘ e.symm))⁻¹ j (e k) *
      ∑ i, c i * β i ^ (n + (j : ℕ)) := funext fun n ↦ by
    have h := mul_pow_eq_sum_inv_vandermonde_mul_sum_mul_pow_add (hβ.comp e.symm.injective)
      (c ∘ e.symm) n (e k)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at h
    rw [h]
    exact sum_congr rfl fun j _ ↦ by rw [e.symm.sum_comp fun i ↦ c i * β i ^ (n + (j : ℕ))]
  -- Each shifted moment is `o(R ^ (n + j)) = o(R ^ n)`, hence so is the recovered power.
  have hko : (fun n ↦ c k * β k ^ n) =o[atTop] fun n ↦ R ^ n := by
    rw [hrec]
    refine IsLittleO.fun_sum fun j _ ↦ IsLittleO.const_mul_left ?_ _
    refine (ho.comp_tendsto (tendsto_add_atTop_nat (j : ℕ))).trans_isBigO ?_
    simpa [Function.comp_def, pow_add, mul_comm] using
      isBigO_const_mul_self (R ^ (j : ℕ)) (fun n : ℕ ↦ R ^ n) atTop
  -- If `R ≤ ‖β k‖`, then `‖c k‖ * R ^ n ≤ ‖c k * β k ^ n‖ ≤ ‖c k‖ / 2 * R ^ n` for large `n`.
  by_contra! hle
  have hck : 0 < ‖c k‖ := norm_pos_iff.2 hk
  obtain ⟨n, hn⟩ := (hko.def (half_pos hck)).exists
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hRn.le] at hn
  have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hle n) hck.le
  nlinarith

/-- **Roots of nonzero total weight lie strictly inside the radius of little-o moments.** Let `α`
be a finite family of roots, possibly with repetitions, and `w` a family of weights. If the
weighted moments `∑ i, w i * α i ^ n` are `o(R ^ n)` for some `R > 0`, then every root whose total
weight, summed over all the indices carrying that root, is nonzero has norm strictly less
than `R`. -/
theorem norm_lt_of_grouped_moment_isLittleO {ι : Type*} [Fintype ι] [DecidableEq K]
    {α w : ι → K} {R : ℝ} (hR : 0 < R)
    (ho : (fun n ↦ ∑ i, w i * α i ^ n) =o[atTop] fun n ↦ R ^ n) {j : ι}
    (hw : ∑ i with α i = α j, w i ≠ 0) : ‖α j‖ < R :=
  norm_lt_of_moment_isLittleO (β := fun b : univ.image α ↦ (b : K)) Subtype.val_injective hR
    (by simpa only [sum_mul_pow_eq_sum_image_mul_pow α w] using ho)
    (k := ⟨α j, mem_image_of_mem α (mem_univ j)⟩) hw

end TauCeti
