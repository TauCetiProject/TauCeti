/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.BooleanCube.Plancherel

/-!
# Influences and the Poincaré inequality on the Boolean cube

For a real function `f` on a finite Boolean cube `ι → ZMod 2`, the *influence* of a coordinate `i`
is the mean square of the discrete directional Laplacian `x ↦ (f x - f (x + Pi.single i 1)) / 2`,
and the *total influence* is the sum of the influences over all coordinates. For a sign-valued
function (`f x = ±1`), the influence of `i` is the probability that flipping coordinate `i` changes
the value of `f`.

The directional Laplacian projects the Walsh expansion onto the sets containing `i`. Parseval's
identity therefore gives the spectral formulas for individual and total influences, from which the
Poincaré inequality `variance f ≤ totalInfluence f` and its equality characterization (degree at
most one) follow immediately.

## Main definitions

* `TauCeti.influence i f`: the influence `𝔼 x, ((f x - f (x + Pi.single i 1)) / 2) ^ 2` of
  coordinate `i` on `f`.
* `TauCeti.totalInfluence f`: the sum `∑ i, influence i f` of the influences of all coordinates.

## Main results

* `TauCeti.influence_eq_dens_ne`: for a sign-valued function, `influence i f` is the density of the
  points where flipping coordinate `i` changes `f`.
* `TauCeti.walshCoeff_sub_add_single_div_two`, `TauCeti.expect_mul_sub_add_single_div_two`: the
  Walsh coefficients of the directional Laplacian and its inner product with `f`.
* `TauCeti.influence_eq_sum_sq_walshCoeff`: the spectral formula
  `influence i f = ∑ S with i ∈ S, walshCoeff f S ^ 2`.
* `TauCeti.totalInfluence_eq_sum_card_mul_sq`: the spectral formula
  `totalInfluence f = ∑ S, S.card * walshCoeff f S ^ 2`.
* `TauCeti.influence_le_variance`: every coordinate's influence is at most `variance f`.
* `TauCeti.mul_variance_le_totalInfluence`: if `walshCoeff f S = 0` for all `0 < S.card < k`, then
  `k * variance f ≤ totalInfluence f`.
* `TauCeti.variance_le_totalInfluence`: the Poincaré inequality `variance f ≤ totalInfluence f`,
  with equality if and only if `walshCoeff f S = 0` whenever `2 ≤ S.card`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Chapter 2: Definitions 2.13 and 2.17, Theorems 2.20 and 2.38,
  Proposition 2.26, Section 2.3 (Poincaré Inequality), Exercise 2.8.
* C. Garban and J. E. Steif, *Noise Sensitivity of Boolean Functions and Percolation*,
  Cambridge University Press, 2014 (arXiv:1102.5761), Theorem I.1.
-/

public section

open Finset
open scoped BigOperators

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Influences and total influence -/

/-- The **influence** of coordinate `i` on `f`: the mean square of half the change of `f` when
coordinate `i` is flipped. For a sign-valued function it is the probability that flipping
coordinate `i` changes the value. -/
noncomputable def influence (i : ι) (f : (ι → ZMod 2) → ℝ) : ℝ :=
  𝔼 x, ((f x - f (x + Pi.single i 1)) / 2) ^ 2

lemma influence_def (i : ι) (f : (ι → ZMod 2) → ℝ) :
    influence i f = 𝔼 x, ((f x - f (x + Pi.single i 1)) / 2) ^ 2 := (rfl)

lemma influence_nonneg (i : ι) (f : (ι → ZMod 2) → ℝ) : 0 ≤ influence i f :=
  expect_nonneg fun _ _ ↦ sq_nonneg _

@[simp] lemma influence_zero (i : ι) : influence i (0 : (ι → ZMod 2) → ℝ) = 0 := by
  simp [influence_def]

@[simp] lemma influence_const (i : ι) (c : ℝ) : influence i (fun _ ↦ c) = 0 := by
  simp [influence_def]

@[simp] lemma influence_neg (i : ι) (f : (ι → ZMod 2) → ℝ) : influence i (-f) = influence i f := by
  simp only [influence_def, Pi.neg_apply]
  exact expect_congr rfl fun _ _ ↦ by ring

@[simp] lemma influence_smul (i : ι) (c : ℝ) (f : (ι → ZMod 2) → ℝ) :
    influence i (c • f) = c ^ 2 * influence i f := by
  simp only [influence_def, Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_div_assoc, mul_pow,
    ← mul_expect]

/-- The influence of coordinate `i` on the Walsh character `walsh S` is `1` if `i ∈ S` and `0`
otherwise. -/
@[simp] lemma influence_walsh (i : ι) (S : Finset ι) :
    influence i (walsh S) = if i ∈ S then 1 else 0 := by
  simp only [influence_def, walsh_add, walsh_single_one]
  split_ifs <;> simp [sub_neg_eq_add, ← two_mul]

/-- The **total influence** of `f`: the sum of the influences of all coordinates. -/
noncomputable def totalInfluence (f : (ι → ZMod 2) → ℝ) : ℝ :=
  ∑ i, influence i f

lemma totalInfluence_def (f : (ι → ZMod 2) → ℝ) : totalInfluence f = ∑ i, influence i f := (rfl)

lemma totalInfluence_nonneg (f : (ι → ZMod 2) → ℝ) : 0 ≤ totalInfluence f :=
  sum_nonneg fun i _ ↦ influence_nonneg i f

@[simp] lemma totalInfluence_zero : totalInfluence (0 : (ι → ZMod 2) → ℝ) = 0 := by
  simp [totalInfluence_def]

@[simp] lemma totalInfluence_const (c : ℝ) : totalInfluence (fun _ : ι → ZMod 2 ↦ c) = 0 := by
  simp [totalInfluence_def]

@[simp] lemma totalInfluence_neg (f : (ι → ZMod 2) → ℝ) :
    totalInfluence (-f) = totalInfluence f := by
  simp [totalInfluence_def]

@[simp] lemma totalInfluence_smul (c : ℝ) (f : (ι → ZMod 2) → ℝ) :
    totalInfluence (c • f) = c ^ 2 * totalInfluence f := by
  simp [totalInfluence_def, mul_sum]

/-- The total influence of a Walsh character `walsh S` is `S.card`. -/
@[simp] lemma totalInfluence_walsh (S : Finset ι) : totalInfluence (walsh S) = S.card := by
  simp [totalInfluence_def]

/-- For a sign-valued function, the influence of coordinate `i` is the density of the points where
flipping coordinate `i` changes the value of `f`. -/
theorem influence_eq_dens_ne (i : ι) {f : (ι → ZMod 2) → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1) :
    influence i f = (({x | f x ≠ f (x + Pi.single i 1)} : Finset (ι → ZMod 2)).dens : ℝ) := by
  set s : Finset (ι → ZMod 2) := {x | f x ≠ f (x + Pi.single i 1)}
  rw [influence_def, ← expect_indicator_one s]
  refine expect_congr rfl fun x _ ↦ ?_
  rcases hf x with hx | hx <;> rcases hf (x + Pi.single i 1) with hx' | hx' <;>
    norm_num [s, Set.indicator_apply, hx, hx']

/-! ### Directional Laplacian and spectral formulas -/

/-- The Walsh coefficient at `S` of the directional Laplacian
`x ↦ (f x - f (x + Pi.single i 1)) / 2` is `walshCoeff f S` if `i ∈ S` and `0` otherwise. -/
theorem walshCoeff_sub_add_single_div_two (i : ι) (f : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (fun x ↦ (f x - f (x + Pi.single i 1)) / 2) S =
      if i ∈ S then walshCoeff f S else 0 := by
  have hflip : walshCoeff (fun x ↦ f (x + Pi.single i 1)) S =
      (if i ∈ S then -1 else 1) * walshCoeff f S := by
    rw [walshCoeff_def, walshCoeff_def, mul_expect, ← walsh_single_one]
    refine Fintype.expect_equiv (Equiv.addRight (Pi.single i 1)) _ _ fun x ↦ ?_
    simp only [Equiv.coe_addRight, walsh_add]
    linear_combination -(f (x + Pi.single i 1) * walsh S x) * walsh_mul_self S (Pi.single i 1)
  have hL : (fun x ↦ (f x - f (x + Pi.single i 1)) / 2) =
      (1 / 2 : ℝ) • (f - fun x ↦ f (x + Pi.single i 1)) := by
    ext x
    simp [div_eq_inv_mul]
  rw [hL, walshCoeff_smul, walshCoeff_sub, hflip]
  split_ifs <;> ring

/-- **Spectral formula for the influence:** the influence of coordinate `i` is the sum of the
squared Walsh coefficients on the sets containing `i`. -/
theorem influence_eq_sum_sq_walshCoeff (i : ι) (f : (ι → ZMod 2) → ℝ) :
    influence i f = ∑ S with i ∈ S, walshCoeff f S ^ 2 := by
  rw [influence_def, expect_sq_eq_sum_sq_walshCoeff]
  simp_rw [walshCoeff_sub_add_single_div_two]
  rw [sum_filter]
  exact sum_congr rfl fun S _ ↦ by split_ifs <;> simp

/-- The average of `f` against its directional Laplacian in direction `i` equals `influence i f`. -/
theorem expect_mul_sub_add_single_div_two (i : ι) (f : (ι → ZMod 2) → ℝ) :
    𝔼 x, f x * ((f x - f (x + Pi.single i 1)) / 2) = influence i f := by
  rw [expect_mul_eq_sum_walshCoeff, influence_eq_sum_sq_walshCoeff]
  simp_rw [walshCoeff_sub_add_single_div_two, mul_ite, mul_zero, ← sq, sum_filter]

/-- **Spectral formula for the total influence:** the total influence is the sum of the squared
Walsh coefficients weighted by the sizes of the sets. -/
theorem totalInfluence_eq_sum_card_mul_sq (f : (ι → ZMod 2) → ℝ) :
    totalInfluence f = ∑ S, (S.card : ℝ) * walshCoeff f S ^ 2 := by
  simp_rw [totalInfluence_def, influence_eq_sum_sq_walshCoeff, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [← sum_filter, sum_const, filter_mem_eq_inter, univ_inter, nsmul_eq_mul]

/-- Every coordinate's influence is at most the variance of `f`. -/
theorem influence_le_variance (i : ι) (f : (ι → ZMod 2) → ℝ) :
    influence i f ≤ variance f := by
  rw [influence_eq_sum_sq_walshCoeff, variance_eq_sum_sq_walshCoeff]
  exact sum_le_sum_of_subset_of_nonneg (fun S hS ↦ by
    simp only [mem_filter, mem_univ, true_and] at hS ⊢
    exact ⟨i, hS⟩) (fun _ _ _ ↦ sq_nonneg _)

/-! ### The Poincaré inequality -/

private lemma totalInfluence_eq_sum_nonempty (f : (ι → ZMod 2) → ℝ) :
    totalInfluence f = ∑ S with S.Nonempty, (S.card : ℝ) * walshCoeff f S ^ 2 := by
  rw [totalInfluence_eq_sum_card_mul_sq, ← sum_filter_of_ne (p := Finset.Nonempty)]
  intro S _ hS
  exact ne_empty_iff_nonempty.1 fun h ↦ by simp [h] at hS

/-- If all nonempty Walsh coefficients of `f` on sets of size less than `k` vanish, then
`k * variance f ≤ totalInfluence f`. -/
theorem mul_variance_le_totalInfluence (k : ℕ) {f : (ι → ZMod 2) → ℝ}
    (hf : ∀ S : Finset ι, 0 < S.card → S.card < k → walshCoeff f S = 0) :
    (k : ℝ) * variance f ≤ totalInfluence f := by
  rw [variance_eq_sum_sq_walshCoeff, totalInfluence_eq_sum_nonempty, mul_sum]
  refine sum_le_sum fun S hS ↦ ?_
  have hpos : 0 < S.card := (mem_filter.1 hS).2.card_pos
  by_cases hk : S.card < k
  · simp [hf S hpos hk]
  · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (not_lt.1 hk)) (sq_nonneg _)

/-- **The Poincaré inequality on the Boolean cube**, with its equality case: the variance is at
most the total influence, with equality if and only if `f` has degree at most one. -/
theorem variance_le_totalInfluence (f : (ι → ZMod 2) → ℝ) :
    variance f ≤ totalInfluence f ∧
      (variance f = totalInfluence f ↔ ∀ S : Finset ι, 2 ≤ S.card → walshCoeff f S = 0) := by
  have hdiff : totalInfluence f - variance f =
      ∑ S with S.Nonempty, ((S.card : ℝ) - 1) * walshCoeff f S ^ 2 := by
    rw [totalInfluence_eq_sum_nonempty, variance_eq_sum_sq_walshCoeff, ← sum_sub_distrib]
    exact sum_congr rfl fun S _ ↦ by ring
  have hnonneg : ∀ S ∈ univ.filter Finset.Nonempty,
      0 ≤ ((S.card : ℝ) - 1) * walshCoeff f S ^ 2 := fun S hS ↦ by
    have h1 : (1 : ℝ) ≤ S.card := Nat.one_le_cast.2 (mem_filter.1 hS).2.card_pos
    exact mul_nonneg (sub_nonneg.2 h1) (sq_nonneg _)
  refine ⟨sub_nonneg.1 (hdiff ▸ sum_nonneg hnonneg), ?_⟩
  rw [eq_comm, ← sub_eq_zero, hdiff, sum_eq_zero_iff_of_nonneg hnonneg]
  refine ⟨fun h S hS ↦ ?_, fun h S hS ↦ ?_⟩
  · have hzero := h S (mem_filter.2 ⟨mem_univ _, card_pos.1 (by omega)⟩)
    have hne : (S.card : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
      linarith
    exact sq_eq_zero_iff.1 ((mul_eq_zero.1 hzero).resolve_left hne)
  · have hpos : 1 ≤ S.card := (mem_filter.1 hS).2.card_pos
    by_cases h2 : 2 ≤ S.card
    · simp [h S h2]
    · have h1 : S.card = 1 := by omega
      simp [h1]

end TauCeti
