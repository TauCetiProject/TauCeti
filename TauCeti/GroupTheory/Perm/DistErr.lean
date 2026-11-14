/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin

/-!
# The distance with errors between permutations of different degrees

Chapman and Lubotzky compare permutations of possibly different degrees `n` and `m` by
`Equiv.Perm.distErr σ τ = 1 - #{j < min n m | σ j = τ j} / max n m`, the values `σ j` and
`τ j` being compared as natural numbers. This is the distance used to define their cross-degree
coboundary constant, where the gauge may live in a different symmetric group than the cochain.

Main results:

* `Equiv.Perm.distErr_eq_movedNorm_div`, `Equiv.Perm.mul_distErr_mul_inv_eq_movedNorm`: in equal
  degree, the distance with errors against a gauge quotient `g * h⁻¹` recovers the normalized
  moved-point norm of `g⁻¹ * σ * h`, while `Equiv.Perm.distErr_inv_inv` gives invariance under
  simultaneous inversion across arbitrary degrees;
* `Equiv.Perm.one_div_succ_le_distErr_of_ne`, `Equiv.Perm.distErr_eq_zero_iff`,
  `Equiv.Perm.one_div_four_le_distErr_of_ne_three`, `Equiv.Perm.one_div_three_le_distErr_of_ne`:
  sharp cross-degree separation bounds and degree-3 baselines;
* `Equiv.Perm.three_mul_one_sub_add_movedNorm_div_le_distErr_triangle`: cross-degree triangle
  holonomy lower bound combining the degree-mismatch baseline with the triangle holonomy norm;
* `Equiv.Perm.agreeCount_mul_inv_eq_card_filter`,
  `Equiv.Perm.card_sub_mul_min_div_max_le_sum_distErr`: fiberwise coordinate decomposition of
  cross-degree agreements and resulting pairwise sum lower bounds;
* `Equiv.Perm.ciInf_sum_distErr_eq_six_sub_four_mul_min_div_max`,
  `Equiv.Perm.ciInf_succ_succ_sum_distErr_eq_two`,
  `Equiv.Perm.card_le_four_iff_exists_isSwap_injOn`: on a four-vertex set whose three non-apex
  edges carry the three transpositions of `Perm (Fin 3)` and whose apex edges carry `1` (the
  maximal cardinality admitting such an assignment), the minimum cross-degree gauge cost in degree
  `m` is `6 - 4 * min 3 m / max 3 m`, with global infimum `2`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, equations (2.8)–(2.9).
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Proposition 10.
-/

public section

open Finset

namespace Equiv.Perm

variable {n m : ℕ}

/-- The number of common indices `j < min n m` at which `σ` and `τ` take the same value, the
values compared as natural numbers. -/
def agreeCount (σ : Perm (Fin n)) (τ : Perm (Fin m)) : ℕ :=
  #{j : Fin (min n m) |
    (σ (j.castLE (min_le_left n m)) : ℕ) = τ (j.castLE (min_le_right n m))}

theorem agreeCount_def (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = #{j : Fin (min n m) |
      (σ (j.castLE (min_le_left n m)) : ℕ) = τ (j.castLE (min_le_right n m))} := (rfl)

/-- The distance with errors between a permutation of degree `n` and one of degree `m`:
one minus the proportion, among the `max n m` points of the larger degree, of common indices
where the two permutations agree. -/
noncomputable def distErr (σ : Perm (Fin n)) (τ : Perm (Fin m)) : ℝ :=
  1 - (agreeCount σ τ : ℝ) / max n m

theorem distErr_def (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    distErr σ τ = 1 - (agreeCount σ τ : ℝ) / max n m := (rfl)

/-- Swapping the two permutations does not change the number of agreements. -/
theorem agreeCount_comm (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = agreeCount τ σ := by
  refine card_equiv (finCongr (min_comm n m)) fun j => ?_
  have hj {k : ℕ} (h₁ : min m n ≤ k) (h₂ : min n m ≤ k) :
      (Fin.cast (min_comm n m) j).castLE h₁ = j.castLE h₂ := Fin.ext rfl
  simp [hj, eq_comm]

/-- The number of agreements is at most the smaller degree. -/
theorem agreeCount_le_min (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ ≤ min n m :=
  (card_filter_le _ _).trans (by simp)

/-- The identity permutations agree at every common index. -/
@[simp]
theorem agreeCount_one_one : agreeCount (1 : Perm (Fin n)) (1 : Perm (Fin m)) = min n m := by
  simp [agreeCount_def]

/-- In equal degree, the number of agreements is the number of points where the two permutations
take the same value. -/
theorem agreeCount_eq_card_eq (σ τ : Perm (Fin n)) :
    agreeCount σ τ = #{i : Fin n | σ i = τ i} := by
  refine card_equiv (finCongr (min_self n)) fun j => ?_
  have hj : j.castLE (min_le_left n n) = finCongr (min_self n) j := Fin.ext rfl
  simp [hj, Fin.val_inj]

/-- In equal degree, the agreements and the Hamming distance partition the points. -/
theorem agreeCount_add_hammingDist (σ τ : Perm (Fin n)) :
    agreeCount σ τ + hammingDist ⇑σ ⇑τ = n := by
  rw [agreeCount_eq_card_eq, hammingDist, card_filter_add_card_filter_not, card_univ,
    Fintype.card_fin]

/-- The distance with errors is symmetric. -/
theorem distErr_comm (σ : Perm (Fin n)) (τ : Perm (Fin m)) : distErr σ τ = distErr τ σ := by
  rw [distErr_def, distErr_def, agreeCount_comm, max_comm]

/-- The distance with errors is at least the proportion `1 - min n m / max n m` of points outside
the smaller degree. -/
theorem one_sub_min_div_max_le_distErr (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    1 - (min n m : ℝ) / max n m ≤ distErr σ τ := by
  rw [distErr_def]
  gcongr
  exact_mod_cast agreeCount_le_min σ τ

/-- The identity permutations of degrees `n` and `m` attain the lower bound
`one_sub_min_div_max_le_distErr`. -/
@[simp]
theorem distErr_one_one :
    distErr (1 : Perm (Fin n)) (1 : Perm (Fin m)) = 1 - (min n m : ℝ) / max n m := by
  simp [distErr_def]

/-- The distance with errors is nonnegative. -/
theorem distErr_nonneg (σ : Perm (Fin n)) (τ : Perm (Fin m)) : 0 ≤ distErr σ τ := by
  rw [distErr_def, sub_nonneg]
  refine div_le_one_of_le₀ ?_ (by positivity)
  exact_mod_cast (agreeCount_le_min σ τ).trans (min_le_max)

/-- The distance with errors is at most one. -/
theorem distErr_le_one (σ : Perm (Fin n)) (τ : Perm (Fin m)) : distErr σ τ ≤ 1 := by
  rw [distErr_def]
  linarith [show 0 ≤ (agreeCount σ τ : ℝ) / max n m by positivity]

/-- In equal degree `n ≠ 0`, the distance with errors is the normalized Hamming distance. Degree
`0` is excluded: there the two empty permutations have distance with errors `1`. -/
theorem distErr_eq_hammingDist_div [NeZero n] (σ τ : Perm (Fin n)) :
    distErr σ τ = (hammingDist ⇑σ ⇑τ : ℝ) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h : (agreeCount σ τ : ℝ) + hammingDist ⇑σ ⇑τ = n := by
    exact_mod_cast agreeCount_add_hammingDist σ τ
  rw [distErr_def, max_self]
  field_simp
  linarith

/-- In equal degree `n ≠ 0`, the distance with errors is the moved-point norm of the quotient,
divided by the degree. -/
theorem distErr_eq_movedNorm_div [NeZero n] (σ τ : Perm (Fin n)) :
    distErr σ τ = movedNorm (Fin n) (σ⁻¹ * τ) / n := by
  rw [distErr_eq_hammingDist_div, hammingDist_eq_movedNorm]

/-- A permutation of positive degree has distance with errors `0` from itself. -/
@[simp]
theorem distErr_self [NeZero n] (σ : Perm (Fin n)) : distErr σ σ = 0 := by
  simp [distErr_eq_hammingDist_div]

/-! ### Invariances, identity comparisons, and equal-degree gauge quotients -/

/-- Any common index `j < min n m` at which `σ j = τ j` yields a common index `σ j < min n m` at
which `σ⁻¹` and `τ⁻¹` agree. -/
private theorem agreeCount_le_inv_inv (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ ≤ agreeCount σ⁻¹ τ⁻¹ := by
  rw [agreeCount_def, agreeCount_def]
  refine card_le_card_of_injOn
    (fun j ↦ if h : (σ (j.castLE (min_le_left n m)) : ℕ) < min n m then ⟨_, h⟩ else j)
    (fun j hj ↦ ?_) (fun j₁ hj₁ j₂ hj₂ hEq ↦ ?_)
  · simp only [mem_coe, mem_filter, mem_univ, true_and] at hj ⊢
    have hlt : (σ (j.castLE (min_le_left n m)) : ℕ) < min n m :=
      lt_min (σ (j.castLE (min_le_left n m))).isLt (hj ▸ (τ (j.castLE (min_le_right n m))).isLt)
    simp only [hlt, ↓reduceDIte]
    have hσ : (⟨(σ (j.castLE (min_le_left n m)) : ℕ), hlt⟩ : Fin (min n m)).castLE
        (min_le_left n m) = σ (j.castLE (min_le_left n m)) := Fin.ext rfl
    have hτ : (⟨(σ (j.castLE (min_le_left n m)) : ℕ), hlt⟩ : Fin (min n m)).castLE
        (min_le_right n m) = τ (j.castLE (min_le_right n m)) := Fin.ext hj
    simp [hσ, hτ]
  · simp only [mem_coe, mem_filter, mem_univ, true_and] at hj₁ hj₂
    have hlt₁ : (σ (j₁.castLE (min_le_left n m)) : ℕ) < min n m :=
      lt_min (σ (j₁.castLE (min_le_left n m))).isLt (hj₁ ▸ (τ (j₁.castLE (min_le_right n m))).isLt)
    have hlt₂ : (σ (j₂.castLE (min_le_left n m)) : ℕ) < min n m :=
      lt_min (σ (j₂.castLE (min_le_left n m))).isLt (hj₂ ▸ (τ (j₂.castLE (min_le_right n m))).isLt)
    simp only [hlt₁, hlt₂, ↓reduceDIte, Fin.mk.injEq] at hEq
    exact Fin.castLE_injective (min_le_left n m) (σ.injective (Fin.ext hEq))

/-- Inverting both permutations preserves the number of agreements, even when the degrees differ:
any common index `j < min n m` with `σ j = τ j = k` satisfies `k < min n m` and
`σ⁻¹ k = j = τ⁻¹ k`. -/
@[simp]
theorem agreeCount_inv_inv (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ⁻¹ τ⁻¹ = agreeCount σ τ :=
  le_antisymm (by simpa using agreeCount_le_inv_inv σ⁻¹ τ⁻¹) (agreeCount_le_inv_inv σ τ)

/-- Inverting both permutations preserves the distance with errors across arbitrary degrees. -/
@[simp]
theorem distErr_inv_inv (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    distErr σ⁻¹ τ⁻¹ = distErr σ τ := by
  rw [distErr_def, distErr_def, agreeCount_inv_inv]

/-- In equal positive degree, comparing `σ` with a gauge quotient `g * h⁻¹` gives the normalized
moved-point norm of the gauged element `g⁻¹ * σ * h`. -/
theorem distErr_mul_inv_eq_movedNorm_div [NeZero n] (σ g h : Perm (Fin n)) :
    distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h) / n := by
  rw [distErr_eq_movedNorm_div]
  congr 1
  rw [← map_inv_eq_map, ← movedNorm_conj h⁻¹]
  congr 1
  simp [mul_assoc]

/-- Multiplying the equal-degree distance with errors by the degree recovers the moved-point norm
of the quotient, also at degree `0`. -/
theorem mul_distErr_eq_movedNorm (σ τ : Perm (Fin n)) :
    (n : ℝ) * distErr σ τ = movedNorm (Fin n) (σ⁻¹ * τ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Subsingleton.elim (σ⁻¹ * τ) 1]
  · have : NeZero n := ⟨hn⟩
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [distErr_eq_movedNorm_div, mul_div_cancel₀ _ hn']

/-- Multiplying `distErr σ (g * h⁻¹)` by the degree recovers the moved-point norm of `g⁻¹ * σ * h`,
including at degree `0`. -/
theorem mul_distErr_mul_inv_eq_movedNorm (σ g h : Perm (Fin n)) :
    (n : ℝ) * distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Subsingleton.elim (g⁻¹ * σ * h) 1]
  · have : NeZero n := ⟨hn⟩
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [distErr_mul_inv_eq_movedNorm_div, mul_div_cancel₀ _ hn']

/-- Against the identity of a larger or equal degree, the agreements are the fixed points of `σ`,
so agreements and moved points partition `Fin n`. -/
theorem agreeCount_one_right_add_card_support (hnm : n ≤ m) (σ : Perm (Fin n)) :
    agreeCount σ (1 : Perm (Fin m)) + σ.support.card = n := by
  have hfixed : agreeCount σ (1 : Perm (Fin m)) = #{i : Fin n | σ i = i} := by
    rw [agreeCount_def]
    refine card_equiv (finCongr (min_eq_left hnm)) fun j ↦ ?_
    simp only [mem_filter, mem_univ, true_and]
    have hj : j.castLE (min_le_left n m) = finCongr (min_eq_left hnm) j := Fin.ext rfl
    rw [hj]
    simp [Fin.ext_iff]
  rw [hfixed, support]
  simpa using card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ σ i = i)

/-- Against the identity of a larger or equal degree on the left, agreements and moved points
partition `Fin m`. -/
theorem agreeCount_one_left_add_card_support (hmn : m ≤ n) (τ : Perm (Fin m)) :
    agreeCount (1 : Perm (Fin n)) τ + τ.support.card = m := by
  rw [agreeCount_comm]
  exact agreeCount_one_right_add_card_support hmn τ

/-- Formula for the distance with errors against the identity of a larger or equal degree. -/
theorem distErr_one_right (hnm : n ≤ m) (σ : Perm (Fin n)) :
    distErr σ (1 : Perm (Fin m)) = 1 - ((n - σ.support.card : ℕ) : ℝ) / m := by
  have hcard : agreeCount σ (1 : Perm (Fin m)) = n - σ.support.card := by
    have := agreeCount_one_right_add_card_support hnm σ
    omega
  rw [distErr_def, hcard, max_eq_right hnm]

/-- Formula for the distance with errors of the identity against a permutation of smaller or equal
degree. -/
theorem distErr_one_left (hmn : m ≤ n) (τ : Perm (Fin m)) :
    distErr (1 : Perm (Fin n)) τ = 1 - ((m - τ.support.card : ℕ) : ℝ) / n := by
  rw [distErr_comm, distErr_one_right hmn]

/-! ### Cross-degree baselines and separation -/

/-- One minus the degree ratio `n / m` bounds `distErr σ τ` from below for all `n` and `m`. -/
theorem one_sub_div_le_distErr (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    1 - (n : ℝ) / m ≤ distErr σ τ := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [distErr_def, agreeCount_def]
  · rcases le_or_gt m n with hmn | hnm
    · have hle : (1 : ℝ) ≤ (n : ℝ) / m :=
        (one_le_div (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))).mpr (by exact_mod_cast hmn)
      linarith [distErr_nonneg σ τ]
    · have h := one_sub_min_div_max_le_distErr σ τ
      rwa [min_eq_left (by exact_mod_cast hnm.le), max_eq_right hnm.le] at h

/-- Whenever the two degrees differ, the distance with errors is at least `1 / (n + 1)`. Equality
holds for the identity permutations at `m = n + 1`. -/
theorem one_div_succ_le_distErr_of_ne (hnm : n ≠ m) (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    1 / ((n : ℝ) + 1) ≤ distErr σ τ := by
  rcases hnm.lt_or_gt with hlt | hgt
  · have h1 : 1 - (n : ℝ) / m ≤ distErr σ τ := one_sub_div_le_distErr σ τ
    have hm : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hdiv : (n : ℝ) / m ≤ n / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg n) hn1 hm
    have hsub : 1 / ((n : ℝ) + 1) = 1 - (n : ℝ) / ((n : ℝ) + 1) := by field_simp; ring
    linarith
  · have h1 : 1 - (m : ℝ) / n ≤ distErr σ τ := by
      rw [distErr_comm]
      exact one_sub_div_le_distErr τ σ
    have hm : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
    have hnpos : 0 < n := Nat.zero_lt_of_lt hgt
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hle1 : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
      one_div_le_one_div_of_le hn0 (by linarith)
    have hle2 : 1 / (n : ℝ) ≤ 1 - (m : ℝ) / n := by
      rw [le_sub_iff_add_le, ← add_div, div_le_one hn0]
      linarith
    exact hle1.trans (hle2.trans h1)

/-- Permutations of different degrees lie at strictly positive distance with errors. -/
theorem distErr_pos_of_ne_degree (hnm : n ≠ m) (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    0 < distErr σ τ :=
  (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).trans_le (one_div_succ_le_distErr_of_ne hnm σ τ)

/-- In equal positive degree, the distance with errors vanishes precisely on the diagonal. -/
@[simp]
theorem distErr_eq_zero_iff_eq [NeZero n] (σ τ : Perm (Fin n)) :
    distErr σ τ = 0 ↔ σ = τ := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [distErr_eq_hammingDist_div, div_eq_zero_iff, or_iff_left hn.ne', Nat.cast_eq_zero,
    hammingDist_eq_zero, DFunLike.coe_fn_eq]

/-- In equal positive degree, the distance with errors is positive precisely off the diagonal. -/
theorem distErr_pos_iff_ne [NeZero n] (σ τ : Perm (Fin n)) :
    0 < distErr σ τ ↔ σ ≠ τ :=
  (distErr_nonneg σ τ).lt_iff_ne'.trans (distErr_eq_zero_iff_eq σ τ).not

/-- Across arbitrary degrees, `distErr σ τ = 0` holds if and only if the degrees are equal and
positive and the two permutations coincide. -/
theorem distErr_eq_zero_iff (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    distErr σ τ = 0 ↔ ∃ h : n = m, 0 < n ∧ h ▸ σ = τ := by
  constructor
  · intro h0
    have hnm : n = m := by
      by_contra hne
      exact (distErr_pos_of_ne_degree hne σ τ).ne' h0
    subst hnm
    rcases eq_or_ne n 0 with rfl | hn
    · simp [distErr_def, agreeCount_def] at h0
    · have : NeZero n := ⟨hn⟩
      exact ⟨rfl, Nat.pos_of_ne_zero hn, (distErr_eq_zero_iff_eq σ τ).mp h0⟩
  · rintro ⟨rfl, hn, rfl⟩
    have : NeZero n := ⟨hn.ne'⟩
    exact distErr_self σ

/-- A degree-3 permutation and a permutation of any degree other than `3` have distance with
errors at least `1 / 4`. -/
theorem one_div_four_le_distErr_of_ne_three (hm : m ≠ 3) (σ : Perm (Fin 3)) (τ : Perm (Fin m)) :
    (1 : ℝ) / 4 ≤ distErr σ τ :=
  (by norm_num : (1 : ℝ) / 4 ≤ 1 / ((3 : ℝ) + 1)).trans
    (one_div_succ_le_distErr_of_ne hm.symm σ τ)

/-- A degree-3 permutation and a permutation of any degree other than `3` or `4` have distance
with errors at least `1 / 3`. -/
theorem one_div_three_le_distErr_of_ne (hm3 : m ≠ 3) (hm4 : m ≠ 4)
    (σ : Perm (Fin 3)) (τ : Perm (Fin m)) : (1 : ℝ) / 3 ≤ distErr σ τ := by
  rcases lt_or_ge m 3 with hlt | hge
  · have h1 := one_sub_min_div_max_le_distErr σ τ
    rw [min_eq_right (by exact_mod_cast hlt.le), max_eq_left hlt.le] at h1
    have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast Nat.le_sub_one_of_lt hlt
    linarith
  · have hm5 : 5 ≤ m := by omega
    have h1 : 1 - (3 : ℝ) / m ≤ distErr σ τ := one_sub_div_le_distErr σ τ
    have hdiv : (3 : ℝ) / m ≤ 3 / 5 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast hm5)
    linarith

/-- A degree-3 permutation and a degree-2 permutation have distance with errors at least `1 / 3`. -/
theorem one_div_three_le_distErr (σ : Perm (Fin 3)) (τ : Perm (Fin 2)) :
    (1 : ℝ) / 3 ≤ distErr σ τ :=
  one_div_three_le_distErr_of_ne (by decide) (by decide) σ τ

/-- A degree-3 permutation and a permutation of degree at least `5` have distance with errors at
least `2 / 5`. -/
theorem two_div_five_le_distErr_of_five_le (hm : 5 ≤ m) (σ : Perm (Fin 3)) (τ : Perm (Fin m)) :
    (2 : ℝ) / 5 ≤ distErr σ τ := by
  have h1 : 1 - (3 : ℝ) / m ≤ distErr σ τ := one_sub_div_le_distErr σ τ
  have hdiv : (3 : ℝ) / m ≤ 3 / 5 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast hm)
  linarith

/-- Every agreement occurs at an index whose image under `σ` lies below `m`. -/
theorem agreeCount_le_card_lt (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ ≤ #{j : Fin (min n m) | (σ (j.castLE (min_le_left n m)) : ℕ) < m} := by
  rw [agreeCount_def]
  refine card_le_card fun j hj ↦ ?_
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  rw [hj]
  exact (τ (j.castLE (min_le_right n m))).isLt

/-- If `σ` maps a point below `m` to an index `i` with `m ≤ i`, then `σ` agrees with any
degree-`m` permutation at most `m - 1` times. -/
theorem agreeCount_le_sub_one_of_le_of_inv_lt {σ : Perm (Fin n)} {i : Fin n}
    (hi : m ≤ (i : ℕ)) (hσi : (σ⁻¹ i : ℕ) < m) (τ : Perm (Fin m)) :
    agreeCount σ τ ≤ m - 1 := by
  have hmn : m < n := hi.trans_lt i.isLt
  let j₀ : Fin (min n m) := ⟨(σ⁻¹ i : ℕ), lt_min (σ⁻¹ i).isLt hσi⟩
  have hj₀ : ¬ (σ (j₀.castLE (min_le_left n m)) : ℕ) < m := by
    have hcast : j₀.castLE (min_le_left n m) = σ⁻¹ i := Fin.ext rfl
    rw [hcast]
    simp [not_lt.mpr hi]
  have hsub : univ.filter (fun j : Fin (min n m) ↦ (σ (j.castLE (min_le_left n m)) : ℕ) < m) ⊆
      univ.erase j₀ := fun j hj ↦
    mem_erase.mpr ⟨fun hEq ↦ hj₀ (hEq ▸ (mem_filter.mp hj).2), mem_univ j⟩
  calc
    agreeCount σ τ ≤ #{j : Fin (min n m) | (σ (j.castLE (min_le_left n m)) : ℕ) < m} :=
      agreeCount_le_card_lt σ τ
    _ ≤ #(univ.erase j₀) := card_le_card hsub
    _ = min n m - 1 := by rw [card_erase_of_mem (mem_univ j₀), card_univ, Fintype.card_fin]
    _ = m - 1 := by rw [min_eq_right hmn.le]

/-! ### Triangle holonomy bounds across degrees -/

/-- The number of agreements of `σ` and `τ` equals the number of indices `i : Fin n` below `m`
at which `σ i` and `τ i` coincide as natural numbers. -/
theorem agreeCount_eq_card_filter_lt (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = #{i : Fin n | ∃ hi : (i : ℕ) < m, (σ i : ℕ) = τ ⟨i, hi⟩} := by
  rw [agreeCount_def]
  refine card_bij (fun j _ ↦ j.castLE (min_le_left n m))
    (fun j hj ↦ ?_) (fun _ _ _ _ h ↦ Fin.castLE_injective (min_le_left n m) h) (fun i hi ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact ⟨(j.castLE (min_le_right n m)).isLt, hj⟩
  · simp only [mem_filter, mem_univ, true_and] at hi
    rcases hi with ⟨him, hEq⟩
    exact ⟨⟨i, lt_min i.isLt him⟩, by simp [hEq], Fin.ext rfl⟩

/-- Around a triangle, the cross-degree agreements of `σ₁₂, σ₂₃, σ₁₃` with the gauge quotients of
`g₁, g₂, g₃` plus the moved-point count of the holonomy `σ₁₂ * σ₂₃ * σ₁₃⁻¹` cannot exceed `3 * n`:
any index `j : Fin n` at which all three edges agree with the gauge is fixed by the holonomy. -/
theorem agreeCount_mul_inv_triangle_add_card_support_le
    (σ₁₂ σ₂₃ σ₁₃ : Perm (Fin n)) (g₁ g₂ g₃ : Perm (Fin m)) :
    agreeCount σ₁₂ (g₁ * g₂⁻¹) + agreeCount σ₂₃ (g₂ * g₃⁻¹) + agreeCount σ₁₃ (g₁ * g₃⁻¹) +
      (σ₁₂ * σ₂₃ * σ₁₃⁻¹).support.card ≤ 3 * n := by
  have h12 : agreeCount σ₁₂ (g₁ * g₂⁻¹) =
      #{j : Fin n | ∃ hi : (σ₂₃ j : ℕ) < m, (σ₁₂ (σ₂₃ j) : ℕ) = (g₁ * g₂⁻¹) ⟨σ₂₃ j, hi⟩} := by
    rw [agreeCount_eq_card_filter_lt]
    refine card_equiv σ₂₃⁻¹ fun i ↦ ?_
    have hEq : σ₂₃ (σ₂₃⁻¹ i) = i := by simp
    simp only [mem_filter, mem_univ, true_and, hEq]
  have hsup : (σ₁₂ * σ₂₃ * σ₁₃⁻¹).support.card = #{j : Fin n | (σ₁₃⁻¹ * σ₁₂ * σ₂₃) j ≠ j} := by
    have hprod : σ₁₃ * (σ₁₃⁻¹ * σ₁₂ * σ₂₃) * σ₁₃⁻¹ = σ₁₂ * σ₂₃ * σ₁₃⁻¹ := by simp [mul_assoc]
    rw [← hprod, card_support_conj, support]
  rw [h12, agreeCount_eq_card_filter_lt σ₂₃, agreeCount_eq_card_filter_lt σ₁₃, hsup]
  simp only [card_filter, ← sum_add_distrib]
  refine (sum_le_sum (s := (univ : Finset (Fin n))) (g := fun _ ↦ 3) fun j _ ↦ ?_).trans
    (by simp [mul_comm])
  split_ifs with hA hB hC hD <;> try omega
  exfalso
  rcases hA with ⟨h₂₃, hEq12⟩
  rcases hB with ⟨hj, hEq23⟩
  rcases hC with ⟨_, hEq13⟩
  have hfin : (⟨(σ₂₃ j : ℕ), h₂₃⟩ : Fin m) = (g₂ * g₃⁻¹) ⟨j, hj⟩ := Fin.ext hEq23
  have hval : (σ₁₂ (σ₂₃ j) : ℕ) = (σ₁₃ j : ℕ) := by
    rw [hEq12, hfin, hEq13]
    simp [mul_apply]
  exact hD (by simp [mul_apply, Fin.ext hval])

/-- Cross-degree triangle holonomy inequality: around a triangle, the sum of the three `distErr`
values against any degree-`m` gauge is bounded below by the degree-mismatch baseline
`3 * (1 - n / max n m)` plus the normalized holonomy `movedNorm (σ₁₂ * σ₂₃ * σ₁₃⁻¹) / max n m`. -/
theorem three_mul_one_sub_add_movedNorm_div_le_distErr_triangle
    (σ₁₂ σ₂₃ σ₁₃ : Perm (Fin n)) (g₁ g₂ g₃ : Perm (Fin m)) :
    3 * (1 - (n : ℝ) / max n m) + movedNorm (Fin n) (σ₁₂ * σ₂₃ * σ₁₃⁻¹) / max n m ≤
      distErr σ₁₂ (g₁ * g₂⁻¹) + distErr σ₂₃ (g₂ * g₃⁻¹) + distErr σ₁₃ (g₁ * g₃⁻¹) := by
  rcases eq_or_ne (max n m) 0 with hmax | hmax
  · simp [distErr_def, hmax]
    norm_num
  · have hM : (0 : ℝ) < (max n m : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmax)
    have htri : (agreeCount σ₁₂ (g₁ * g₂⁻¹) : ℝ) + agreeCount σ₂₃ (g₂ * g₃⁻¹) +
        agreeCount σ₁₃ (g₁ * g₃⁻¹) + movedNorm (Fin n) (σ₁₂ * σ₂₃ * σ₁₃⁻¹) ≤ 3 * n := by
      rw [movedNorm_apply]
      exact_mod_cast agreeCount_mul_inv_triangle_add_card_support_le σ₁₂ σ₂₃ σ₁₃ g₁ g₂ g₃
    have hdiv := (div_le_div_iff_of_pos_right hM).mpr htri
    simp only [distErr_def]
    linarith [show ((agreeCount σ₁₂ (g₁ * g₂⁻¹) : ℝ) + agreeCount σ₂₃ (g₂ * g₃⁻¹) +
        agreeCount σ₁₃ (g₁ * g₃⁻¹) + movedNorm (Fin n) (σ₁₂ * σ₂₃ * σ₁₃⁻¹)) / (max n m : ℕ) =
      (agreeCount σ₁₂ (g₁ * g₂⁻¹) : ℝ) / (max n m : ℕ) +
        (agreeCount σ₂₃ (g₂ * g₃⁻¹) : ℝ) / (max n m : ℕ) +
        (agreeCount σ₁₃ (g₁ * g₃⁻¹) : ℝ) / (max n m : ℕ) +
        movedNorm (Fin n) (σ₁₂ * σ₂₃ * σ₁₃⁻¹) / (max n m : ℕ) by ring,
      show (3 * (n : ℝ)) / (max n m : ℕ) = 3 * ((n : ℝ) / (max n m : ℕ)) by ring]

/-! ### Fiber decomposition and pairwise sum bounds -/

/-- Reindexing by `h` identifies the agreements of `σ` with `g * h⁻¹` with the coordinates
`k : Fin m` whose images under both `g` and `h` lie below `n` and satisfy `g k = σ (h k)`. -/
theorem agreeCount_mul_inv_eq_card_filter (σ : Perm (Fin n)) (g h : Perm (Fin m)) :
    agreeCount σ (g * h⁻¹) =
      #{k : Fin m | ∃ (hg : (g k : ℕ) < n) (hh : (h k : ℕ) < n),
        (⟨g k, hg⟩ : Fin n) = σ ⟨h k, hh⟩} := by
  rw [agreeCount_def]
  refine card_bij (fun j _ ↦ h⁻¹ (j.castLE (min_le_right n m)))
    (fun j hj ↦ ?_)
    (fun _ _ _ _ hEq ↦ Fin.castLE_injective (min_le_right n m) (h⁻¹.injective hEq))
    (fun k hk ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and] at hj ⊢
    have hh : (h (h⁻¹ (j.castLE (min_le_right n m))) : ℕ) < n := by
      simpa using (j.castLE (min_le_left n m)).isLt
    have hg : (g (h⁻¹ (j.castLE (min_le_right n m))) : ℕ) < n := by
      have hmul : (g (h⁻¹ (j.castLE (min_le_right n m))) : ℕ) =
          (σ (j.castLE (min_le_left n m)) : ℕ) := by simpa [mul_apply] using hj.symm
      exact hmul ▸ (σ (j.castLE (min_le_left n m))).isLt
    refine ⟨hg, hh, Fin.ext ?_⟩
    have hcast : (⟨h (h⁻¹ (j.castLE (min_le_right n m))), hh⟩ : Fin n) =
        j.castLE (min_le_left n m) := by
      apply Fin.ext
      simp
    rw [hcast]
    simpa [mul_apply] using hj.symm
  · simp only [mem_filter, mem_univ, true_and] at hk
    rcases hk with ⟨hg, hh, hEq⟩
    refine ⟨⟨(h k : ℕ), lt_min hh (h k).isLt⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have hL : (⟨(h k : ℕ), lt_min hh (h k).isLt⟩ : Fin (min n m)).castLE (min_le_left n m) =
          ⟨h k, hh⟩ := Fin.ext rfl
      have hR : (⟨(h k : ℕ), lt_min hh (h k).isLt⟩ : Fin (min n m)).castLE (min_le_right n m) =
          h k := Fin.ext rfl
      rw [hL, hR, ← hEq]
      simp [mul_apply]
    · have hR : (⟨(h k : ℕ), lt_min hh (h k).isLt⟩ : Fin (min n m)).castLE (min_le_right n m) =
          h k := Fin.ext rfl
      simp [hR]

/-- Double counting active vertices across fibers: for any degree-`m` gauge `β` on `V`, summing
over `k : Fin m` the number of vertices with `β v k < n` gives `Fintype.card V * min n m`. -/
theorem sum_card_filter_apply_lt {V : Type*} [Fintype V] (n : ℕ) (β : V → Perm (Fin m)) :
    (∑ k : Fin m, #{v : V | (β v k : ℕ) < n}) = Fintype.card V * min n m := by
  have hv (v : V) : #{k : Fin m | (β v k : ℕ) < n} = min n m := by
    rw [min_comm, ← Fin.card_filter_val_lt]
    exact card_equiv (β v) fun k ↦ by simp
  simp only [card_filter]
  rw [sum_comm]
  simp only [← card_filter, hv, sum_const, card_univ, smul_eq_mul]

/-- If every induced vertex set `s` and `Fin n`-assignment `f` satisfies at most `c * #s` edges of
`E`, then against any degree-`m` gauge `β` the total agreements over `E` are at most
`c * Fintype.card V * min n m`. -/
theorem sum_agreeCount_mul_inv_le_of_forall_card_filter_le {V : Type*} [Fintype V] [DecidableEq V]
    {E : Finset (V × V)} {α : V → V → Perm (Fin n)} {c : ℝ}
    (hc : ∀ (s : Finset V) (f : V → Fin n),
      (#{e ∈ E | e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)} : ℝ) ≤ c * #s)
    (β : V → Perm (Fin m)) :
    (∑ e ∈ E, (agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹) : ℝ)) ≤
      c * Fintype.card V * (min n m : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero (e : V × V) : agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹) = 0 :=
      Nat.eq_zero_of_le_zero ((agreeCount_le_min _ _).trans (by simp))
    simp [hzero]
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    let s (k : Fin m) : Finset V := {v : V | (β v k : ℕ) < n}
    let f (k : Fin m) (v : V) : Fin n := if hv : (β v k : ℕ) < n then ⟨β v k, hv⟩ else ⟨0, hn0⟩
    have hfiber (k : Fin m) (e : V × V) :
        (∃ (hg : (β e.1 k : ℕ) < n) (hh : (β e.2 k : ℕ) < n),
          (⟨β e.1 k, hg⟩ : Fin n) = α e.1 e.2 ⟨β e.2 k, hh⟩) ↔
          e.1 ∈ s k ∧ e.2 ∈ s k ∧ f k e.1 = α e.1 e.2 (f k e.2) := by
      constructor
      · rintro ⟨hg, hh, hEq⟩
        exact ⟨mem_filter.mpr ⟨mem_univ _, hg⟩, mem_filter.mpr ⟨mem_univ _, hh⟩,
          by simp [f, hg, hh, hEq]⟩
      · rintro ⟨h1, h2, hEq⟩
        have hg : (β e.1 k : ℕ) < n := (mem_filter.mp h1).2
        have hh : (β e.2 k : ℕ) < n := (mem_filter.mp h2).2
        exact ⟨hg, hh, by simpa [f, hg, hh] using hEq⟩
    have hswap_sum : (∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
        ∑ k : Fin m, #{e ∈ E | e.1 ∈ s k ∧ e.2 ∈ s k ∧ f k e.1 = α e.1 e.2 (f k e.2)} := by
      simp only [agreeCount_mul_inv_eq_card_filter, hfiber, card_filter]
      exact sum_comm
    calc
      (∑ e ∈ E, (agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹) : ℝ))
          = ∑ k : Fin m,
              (#{e ∈ E | e.1 ∈ s k ∧ e.2 ∈ s k ∧ f k e.1 = α e.1 e.2 (f k e.2)} : ℝ) := by
            exact_mod_cast hswap_sum
      _ ≤ ∑ k : Fin m, c * #(s k) := sum_le_sum fun k _ ↦ hc (s k) (f k)
      _ = c * ∑ k : Fin m, (#(s k) : ℝ) := by rw [← mul_sum]
      _ = c * Fintype.card V * (min n m : ℕ) := by
            have hsum : (∑ k : Fin m, (#(s k) : ℝ)) = Fintype.card V * (min n m : ℕ) := by
              exact_mod_cast sum_card_filter_apply_lt n β
            rw [hsum, mul_assoc]
      _ = c * Fintype.card V * (min n m : ℝ) := by rw [Nat.cast_min]

/-- Lower bound on the sum of `distErr` over `E` against any degree-`m` gauge `β` when every
induced subset `s` and `Fin n`-assignment `f` satisfies at most `c * #s` edges of `E`. -/
theorem card_sub_mul_min_div_max_le_sum_distErr {V : Type*} [Fintype V] [DecidableEq V]
    {E : Finset (V × V)} {α : V → V → Perm (Fin n)} {c : ℝ}
    (hc : ∀ (s : Finset V) (f : V → Fin n),
      (#{e ∈ E | e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)} : ℝ) ≤ c * #s)
    (β : V → Perm (Fin m)) :
    (#E : ℝ) - c * Fintype.card V * (min n m : ℝ) / max n m ≤
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hdiv : (∑ e ∈ E, (agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹) : ℝ)) / max n m ≤
      c * Fintype.card V * (min n m : ℝ) / max n m :=
    div_le_div_of_nonneg_right
      (sum_agreeCount_mul_inv_le_of_forall_card_filter_le hc β) (by positivity)
  have hsum : (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (#E : ℝ) - (∑ e ∈ E, (agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹) : ℝ)) / max n m := by
    simp [distErr_def, sum_sub_distrib, div_eq_mul_inv, ← sum_mul]
  linarith

/-! ### Exact cross-degree gauge minima on four vertices -/

/-- On a finite linearly ordered vertex set `V` with an apex `v₀`, if the strictly ordered pairs
outside `v₀` carry pairwise distinct transpositions of `Fin 3`, then `V` has at most four
vertices. -/
theorem card_le_four_of_isSwap_injOn {V : Type*} [Fintype V] [LinearOrder V] {v₀ : V}
    {α : V → V → Perm (Fin 3)}
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀}) :
    Fintype.card V ≤ 4 := by
  let B : Finset V := univ.erase v₀
  let P : Finset (V × V) := (B ×ˢ B).filter fun e ↦ e.1 < e.2
  let S₃ : Finset (Perm (Fin 3)) := univ.filter fun σ : Perm (Fin 3) ↦ σ.support.card = 2
  have hmaps : ∀ e ∈ P, α e.1 e.2 ∈ S₃ := fun e he ↦ by
    simp only [P, B, mem_filter, mem_product, mem_erase, mem_univ, and_true] at he
    exact mem_filter.mpr ⟨mem_univ _, card_support_eq_two.mpr (hswap e.1 e.2 he.2 he.1.1 he.1.2)⟩
  have hinjP : Set.InjOn (fun e : V × V ↦ α e.1 e.2) P := hinj.mono fun e he ↦ by
    simp only [P, B, mem_coe, mem_filter, mem_product, mem_erase, mem_univ, and_true] at he
    exact ⟨he.2, he.1.1, he.1.2⟩
  have hP : #P ≤ 3 := (card_le_card_of_injOn _ hmaps hinjP).trans (by decide : #S₃ ≤ 3)
  rw [card_product_filter_lt, Nat.choose_two_right, card_erase_of_mem (mem_univ v₀),
    card_univ] at hP
  have _ : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v₀⟩
  by_contra! hgt
  have hB : 4 * 3 ≤ (Fintype.card V - 1) * (Fintype.card V - 1 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Evaluating a transposition on a satisfied ordered pair `{u, w}` outside `v₀` maps `f w` to
`f u` regardless of how `u` and `w` compare. -/
private theorem isSwap_apply_eq {V : Type*} [LinearOrder V] {v₀ u w : V}
    {α : V → V → Perm (Fin 3)}
    (hswap : ∀ a b : V, a < b → a ≠ v₀ → b ≠ v₀ → (α a b).IsSwap)
    (hu : u ≠ v₀) (hw : w ≠ v₀) {f : V → Fin 3}
    (hsat : f (if u < w then (u, w) else (w, u)).1 =
      α (if u < w then (u, w) else (w, u)).1 (if u < w then (u, w) else (w, u)).2
        (f (if u < w then (u, w) else (w, u)).2)) :
    α (if u < w then (u, w) else (w, u)).1 (if u < w then (u, w) else (w, u)).2 (f w) = f u := by
  rcases lt_trichotomy u w with hlt | rfl | hgt
  · simp only [hlt, ↓reduceIte] at hsat ⊢
    exact hsat.symm
  · simp only [lt_irrefl, ↓reduceIte] at hsat ⊢
    exact hsat.symm
  · simp only [not_lt_of_gt hgt, ↓reduceIte] at hsat ⊢
    rcases hswap w u hgt hw hu with ⟨x, y, _, hEq⟩
    rw [hEq, hsat, hEq]
    simp

/-- The satisfied strictly ordered pairs incident to `v₀` inject into `{w ≠ v₀ | f w = f v₀}` by
taking the non-`v₀` endpoint. -/
private theorem card_filter_apex_le {V : Type*} [Fintype V] [LinearOrder V] {v₀ : V}
    {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1) (f : V → Fin 3) :
    #{e : V × V | (e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)) ∧ (e.1 = v₀ ∨ e.2 = v₀)} ≤
      #{w ∈ univ.erase v₀ | f w = f v₀} := by
  refine card_le_card_of_injOn (fun e ↦ if e.1 = v₀ then e.2 else e.1) (fun e he ↦ ?_)
    (fun e₁ he₁ e₂ he₂ hEq ↦ ?_)
  · simp only [mem_coe, mem_filter, mem_erase, mem_univ, true_and, and_true] at he ⊢
    rcases he with ⟨⟨hlt, hsat⟩, h1 | h2⟩
    · simp only [h1, ↓reduceIte]
      rw [h1, h₀ _ _ (h1 ▸ hlt) (Or.inl rfl), one_apply] at hsat
      exact ⟨(h1 ▸ hlt).ne', hsat.symm⟩
    · have hne1 : e.1 ≠ v₀ := h2 ▸ hlt.ne
      simp only [hne1, ↓reduceIte]
      rw [h2, h₀ _ _ (h2 ▸ hlt) (Or.inr rfl), one_apply] at hsat
      exact ⟨hne1, hsat⟩
  · simp only [mem_coe, mem_filter, mem_univ, true_and] at he₁ he₂
    dsimp only at hEq
    split_ifs at hEq with h1 h2 h2
    · exact Prod.ext (h1.trans h2.symm) hEq
    · rcases he₂.2 with h2' | rfl
      · exact absurd h2' h2
      · exact False.elim (lt_asymm (h1 ▸ he₁.1.1) (hEq ▸ he₂.1.1))
    · rcases he₁.2 with h1' | rfl
      · exact absurd h1' h1
      · exact False.elim (lt_asymm he₁.1.1 (hEq.symm ▸ h2 ▸ he₂.1.1))
    · rcases he₁.2 with h1' | h1'
      · exact absurd h1' h1
      · rcases he₂.2 with h2' | h2'
        · exact absurd h2' h2
        · exact Prod.ext hEq (h1'.trans h2'.symm)

/-- When `f` is constant on `univ.erase v₀`, at most one non-apex ordered pair is satisfied,
since distinct transpositions of `Fin 3` disagree everywhere. -/
private theorem card_filter_base_le_one_of_eq_erase {V : Type*} [Fintype V] [LinearOrder V]
    {v₀ : V} {α : V → V → Perm (Fin 3)}
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀})
    {f : V → Fin 3} (hG : (univ.erase v₀).filter (fun w ↦ f w = f v₀) = univ.erase v₀) :
    #{e : V × V | (e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)) ∧ ¬ (e.1 = v₀ ∨ e.2 = v₀)} ≤ 1 := by
  refine card_le_one.mpr fun e₁ he₁ e₂ he₂ ↦ ?_
  by_contra hne
  simp only [mem_filter, mem_univ, true_and, not_or] at he₁ he₂
  have hf (w : V) (hw : w ≠ v₀) : f w = f v₀ := by
    have hw' : w ∈ (univ.erase v₀).filter (fun w ↦ f w = f v₀) := by
      rw [hG]; exact mem_erase.mpr ⟨hw, mem_univ w⟩
    exact (mem_filter.mp hw').2
  have hs₁ : α e₁.1 e₁.2 (f v₀) = f v₀ := by
    have h := he₁.1.2; rw [hf e₁.1 he₁.2.1, hf e₁.2 he₁.2.2] at h; exact h.symm
  have hs₂ : α e₂.1 e₂.2 (f v₀) = f v₀ := by
    have h := he₂.1.2; rw [hf e₂.1 he₂.2.1, hf e₂.2 he₂.2.2] at h; exact h.symm
  exact (hswap _ _ he₁.1.1 he₁.2.1 he₁.2.2).apply_ne_apply_of_ne
    (hswap _ _ he₂.1.1 he₂.2.1 he₂.2.2) (by simp)
    (fun hα ↦ hne (hinj ⟨he₁.1.1, he₁.2.1, he₁.2.2⟩ ⟨he₂.1.1, he₂.2.1, he₂.2.2⟩ hα)) (f v₀)
    (hs₁.trans hs₂.symm)

/-- When exactly two vertices outside `v₀` agree with `f v₀`, at most two non-apex ordered pairs
can be satisfied simultaneously. -/
private theorem card_filter_base_le_two_of_card_eq_two {V : Type*} [Fintype V] [LinearOrder V]
    {v₀ : V} {α : V → V → Perm (Fin 3)}
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀})
    {f : V → Fin 3} (hG2 : #{w ∈ univ.erase v₀ | f w = f v₀} = 2) :
    #{e : V × V | (e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)) ∧ ¬ (e.1 = v₀ ∨ e.2 = v₀)} ≤ 2 := by
  let G : Finset V := (univ.erase v₀).filter fun w ↦ f w = f v₀
  let P : Finset (V × V) := ((univ.erase v₀) ×ˢ (univ.erase v₀)).filter fun e ↦ e.1 < e.2
  let Sb : Finset (V × V) :=
    univ.filter fun e : V × V ↦ (e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)) ∧ ¬ (e.1 = v₀ ∨ e.2 = v₀)
  change #Sb ≤ 2
  have hsub : Sb ⊆ P := fun e he ↦ by
    simp only [Sb, P, mem_filter, mem_product, mem_erase, mem_univ, true_and, and_true,
      not_or] at he ⊢
    exact ⟨he.2, he.1.1⟩
  have hcard4 := card_le_four_of_isSwap_injOn hswap hinj
  have hBge : 2 ≤ #(univ.erase v₀) := hG2 ▸ card_le_card (filter_subset _ _)
  rw [card_erase_of_mem (mem_univ v₀), card_univ] at hBge
  rcases (by omega : Fintype.card V = 3 ∨ Fintype.card V = 4) with hcard3 | hcard
  · exact (card_le_card hsub).trans (by
      rw [card_product_filter_lt, card_erase_of_mem (mem_univ v₀), card_univ, hcard3]; decide)
  · have hPcard : #P = 3 := by
      rw [card_product_filter_lt, card_erase_of_mem (mem_univ v₀), card_univ, hcard]; decide
    by_contra! hgt2
    have hSeq : Sb = P := eq_of_subset_of_card_le hsub (by omega)
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by dsimp [G]; omega : 1 < #G)
    have hdiff : 0 < #((univ.erase v₀) \ G) := by
      rw [card_sdiff_of_subset (filter_subset _ _), card_erase_of_mem (mem_univ v₀),
        card_univ, hcard, show #G = 2 from hG2]; decide
    obtain ⟨u, hu⟩ := card_pos.mp hdiff
    obtain ⟨huB, huG⟩ := mem_sdiff.mp hu
    have haB : a ∈ univ.erase v₀ := filter_subset _ _ ha
    have hbB : b ∈ univ.erase v₀ := filter_subset _ _ hb
    let mk (x y : V) : V × V := if x < y then (x, y) else (y, x)
    have hmkP {w : V} (hwB : w ∈ univ.erase v₀) (huw : u ≠ w) : mk u w ∈ P := by
      dsimp [mk]; split_ifs with h
      · exact mem_filter.mpr ⟨mem_product.mpr ⟨huB, hwB⟩, h⟩
      · exact mem_filter.mpr ⟨mem_product.mpr ⟨hwB, huB⟩, lt_of_le_of_ne (not_lt.mp h) huw.symm⟩
    have heaP := hmkP haB (fun h ↦ huG (h ▸ ha))
    have hebP := hmkP hbB (fun h ↦ huG (h ▸ hb))
    have heab : mk u a ≠ mk u b := by
      dsimp [mk]; split_ifs <;> intro h <;> cases h <;> exact hab rfl
    have hfa : α (mk u a).1 (mk u a).2 (f v₀) = f u :=
      (mem_filter.mp ha).2 ▸ isSwap_apply_eq hswap (mem_erase.mp huB).1 (mem_erase.mp haB).1
        (mem_filter.mp (hSeq ▸ heaP)).2.1.2
    have hfb : α (mk u b).1 (mk u b).2 (f v₀) = f u :=
      (mem_filter.mp hb).2 ▸ isSwap_apply_eq hswap (mem_erase.mp huB).1 (mem_erase.mp hbB).1
        (mem_filter.mp (hSeq ▸ hebP)).2.1.2
    simp only [P, mem_filter, mem_product, mem_erase, mem_univ, and_true] at heaP hebP
    exact (hswap _ _ heaP.2 heaP.1.1 heaP.1.2).apply_ne_apply_of_ne
      (hswap _ _ hebP.2 hebP.1.1 hebP.1.2) (by simp)
      (fun hα ↦ heab (hinj ⟨heaP.2, heaP.1.1, heaP.1.2⟩ ⟨hebP.2, hebP.1.1, hebP.1.2⟩ hα))
      (f v₀) (hfa.trans hfb.symm)

/-- Any `Fin 3`-assignment satisfies at most four edges of an apex-trivial three-transposition
configuration. -/
private theorem card_satisfied_le_four {V : Type*} [Fintype V] [LinearOrder V]
    {v₀ : V} {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀})
    (f : V → Fin 3) :
    #{e : V × V | e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)} ≤ 4 := by
  have hcard4 : Fintype.card V ≤ 4 := card_le_four_of_isSwap_injOn hswap hinj
  let S : Finset (V × V) := {e : V × V | e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)}
  change #S ≤ 4
  rcases lt_or_eq_of_le hcard4 with hlt | hcard
  · have hsub : S ⊆ (univ ×ˢ univ).filter fun e : V × V ↦ e.1 < e.2 :=
      fun e he ↦ mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2.1⟩
    refine (card_le_card hsub).trans ?_
    rw [card_product_filter_lt, card_univ]
    rcases (by omega : Fintype.card V = 0 ∨ Fintype.card V = 1 ∨
      Fintype.card V = 2 ∨ Fintype.card V = 3) with h | h | h | h <;> simp [h]
  · let p (e : V × V) : Prop := e.1 = v₀ ∨ e.2 = v₀
    let G : Finset V := (univ.erase v₀).filter fun w ↦ f w = f v₀
    let P : Finset (V × V) := ((univ.erase v₀) ×ˢ (univ.erase v₀)).filter fun e ↦ e.1 < e.2
    have hpart : #S = #(S.filter p) + #(S.filter fun e ↦ ¬ p e) :=
      (card_filter_add_card_filter_not p).symm
    have hAf : S.filter p =
        univ.filter fun e : V × V ↦ (e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)) ∧ p e := by
      ext e; simp [S, p]
    have hBf : S.filter (fun e ↦ ¬ p e) =
        univ.filter fun e : V × V ↦ (e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2)) ∧ ¬ p e := by
      ext e; simp [S, p]
    have hSapex : #(S.filter p) ≤ #G := hAf ▸ card_filter_apex_le h₀ f
    have hGle : #G ≤ 3 := (card_filter_le _ _).trans (by
      rw [card_erase_of_mem (mem_univ v₀), card_univ, hcard])
    rcases le_or_gt #G 1 with hG1 | hGgt1
    · have hsub : S.filter (fun e ↦ ¬ p e) ⊆ P := fun e he ↦ by
        simp only [S, P, p, mem_filter, mem_product, mem_erase, mem_univ, true_and, and_true,
          not_or] at he ⊢
        exact ⟨he.2, he.1.1⟩
      have hB3 : #(S.filter fun e ↦ ¬ p e) ≤ 3 := (card_le_card hsub).trans (by
        rw [card_product_filter_lt, card_erase_of_mem (mem_univ v₀), card_univ, hcard]; decide)
      omega
    · rcases eq_or_ne #G 3 with hG3 | hGne3
      · have hGeq : G = univ.erase v₀ := eq_of_subset_of_card_le (filter_subset _ _)
          (by rw [card_erase_of_mem (mem_univ v₀), card_univ, hcard, hG3])
        have hB1 : #(S.filter fun e ↦ ¬ p e) ≤ 1 :=
          hBf ▸ card_filter_base_le_one_of_eq_erase hswap hinj hGeq
        omega
      · have hG2 : #G = 2 := by omega
        have hB2 : #(S.filter fun e ↦ ¬ p e) ≤ 2 :=
          hBf ▸ card_filter_base_le_two_of_card_eq_two hswap hinj hG2
        omega

/-- For an apex-trivial three-transposition configuration on `V`, every subset `s : Finset V` and
every `Fin 3`-assignment `f` satisfies at most `#s` strictly ordered pairs in `s`. -/
theorem card_filter_lt_eq_apply_le_card {V : Type*} [Fintype V] [LinearOrder V] {v₀ : V}
    {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀})
    (s : Finset V) (f : V → Fin 3) :
    #{e : V × V | e.1 < e.2 ∧ e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)} ≤ #s := by
  have hs4 : #s ≤ 4 := (card_le_univ s).trans (card_le_four_of_isSwap_injOn hswap hinj)
  rcases le_or_gt #s 3 with hs3 | hsgt
  · have hsub : (univ.filter fun e : V × V ↦
        e.1 < e.2 ∧ e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)) ⊆
        (s ×ˢ s).filter fun e ↦ e.1 < e.2 := fun e he ↦ by
      simp only [mem_filter, mem_product, mem_univ, true_and] at he ⊢
      exact ⟨⟨he.2.1, he.2.2.1⟩, he.1⟩
    refine (card_le_card hsub).trans ?_
    rw [card_product_filter_lt]
    rcases (by omega : #s = 0 ∨ #s = 1 ∨ #s = 2 ∨ #s = 3) with h | h | h | h <;> simp [h]
  · have hs_eq : #s = 4 := by omega
    have hsub : (univ.filter fun e : V × V ↦
        e.1 < e.2 ∧ e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)) ⊆
        univ.filter fun e : V × V ↦ e.1 < e.2 ∧ f e.1 = α e.1 e.2 (f e.2) := fun e he ↦ by
      simp only [mem_filter, mem_univ, true_and] at he ⊢
      exact ⟨he.1, he.2.2.2⟩
    exact ((card_le_card hsub).trans (card_satisfied_le_four h₀ hswap hinj f)).trans hs_eq.symm.le

/-- Sum of agreements with `1 : Perm (Fin m)` across the three transpositions of `Fin 3`. -/
private theorem sum_agreeCount_one_card_support_eq_two (m : ℕ) :
    (∑ σ ∈ univ.filter (fun σ : Perm (Fin 3) ↦ σ.support.card = 2),
      agreeCount σ (1 : Perm (Fin m))) = min 3 m := by
  rcases lt_or_ge m 3 with hlt | hge
  · have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hm_cases with rfl | rfl | rfl <;> decide
  · have h1 : ∀ σ ∈ univ.filter (fun σ : Perm (Fin 3) ↦ σ.support.card = 2),
        agreeCount σ (1 : Perm (Fin m)) = 1 := fun σ hσ ↦ by
      have hsup : σ.support.card = 2 := (mem_filter.mp hσ).2
      have := agreeCount_one_right_add_card_support hge σ; omega
    rw [sum_congr rfl h1, sum_const, smul_eq_mul, mul_one, min_eq_left hge]; decide

/-- Exact cross-degree cost of the identity gauge on a four-vertex apex-trivial three-transposition
configuration: in every degree `m : ℕ` it equals `6 - 4 * min 3 m / max 3 m`. -/
theorem sum_distErr_const_one_of_isSwap_injOn {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V = 4) {v₀ : V} {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀}) (m : ℕ) :
    (∑ e ∈ univ.filter (fun e : V × V ↦ e.1 < e.2),
      distErr (α e.1 e.2) (1 : Perm (Fin m))) = 6 - 4 * (min 3 m : ℝ) / max 3 m := by
  let E : Finset (V × V) := univ.filter fun e : V × V ↦ e.1 < e.2
  let p (e : V × V) : Prop := e.1 = v₀ ∨ e.2 = v₀
  let P : Finset (V × V) := ((univ.erase v₀) ×ˢ (univ.erase v₀)).filter fun e ↦ e.1 < e.2
  let S₃ : Finset (Perm (Fin 3)) := univ.filter fun σ : Perm (Fin 3) ↦ σ.support.card = 2
  have hE : #E = 6 := by
    rw [show E = (univ ×ˢ univ).filter _ from rfl, card_product_filter_lt, card_univ, hcard]; decide
  have hPeq : E.filter (fun e ↦ ¬ p e) = P := by
    ext e; simp [E, P, p, not_or, and_comm]
  have hPcard : #P = 3 := by
    rw [card_product_filter_lt, card_erase_of_mem (mem_univ v₀), card_univ, hcard]; decide
  have hAcard : #(E.filter p) = 3 := by
    have := card_filter_add_card_filter_not (s := E) p; rw [hPeq, hPcard, hE] at this; omega
  have hinjP : Set.InjOn (fun e : V × V ↦ α e.1 e.2) P := hinj.mono fun e he ↦ by
    simp only [P, mem_coe, mem_filter, mem_product, mem_erase, mem_univ, and_true] at he
    exact ⟨he.2, he.1.1, he.1.2⟩
  have himg : P.image (fun e ↦ α e.1 e.2) = S₃ := by
    refine eq_of_subset_of_card_le (fun σ hσ ↦ ?_) ?_
    · rcases mem_image.mp hσ with ⟨e, he, rfl⟩
      simp only [P, mem_filter, mem_product, mem_erase, mem_univ, and_true] at he
      exact mem_filter.mpr ⟨mem_univ _, card_support_eq_two.mpr (hswap _ _ he.2 he.1.1 he.1.2)⟩
    · rw [card_image_of_injOn hinjP, hPcard]; decide
  have hPsum : (∑ e ∈ P, agreeCount (α e.1 e.2) (1 : Perm (Fin m))) = min 3 m := by
    have h := sum_image (f := fun σ ↦ agreeCount σ (1 : Perm (Fin m))) hinjP
    rw [himg, sum_agreeCount_one_card_support_eq_two] at h; exact h.symm
  have hagree : (∑ e ∈ E, agreeCount (α e.1 e.2) (1 : Perm (Fin m))) = 4 * min 3 m := by
    rw [← sum_filter_add_sum_filter_not E p, hPeq, hPsum]
    have hapex : ∀ e ∈ E.filter p, agreeCount (α e.1 e.2) (1 : Perm (Fin m)) = min 3 m :=
      fun e he ↦ by
        rw [h₀ _ _ (mem_filter.mp (mem_filter.mp he).1).2 (mem_filter.mp he).2, agreeCount_one_one]
    rw [sum_congr rfl hapex, sum_const, hAcard, smul_eq_mul]; omega
  calc
    (∑ e ∈ E, distErr (α e.1 e.2) (1 : Perm (Fin m)))
        = (#E : ℝ) - (∑ e ∈ E, (agreeCount (α e.1 e.2) (1 : Perm (Fin m)) : ℝ)) / max 3 m := by
          simp [distErr_def, sum_sub_distrib, div_eq_mul_inv, ← sum_mul]
    _ = 6 - 4 * (min 3 m : ℝ) / max 3 m := by
          have hagreeR : (∑ e ∈ E, (agreeCount (α e.1 e.2) (1 : Perm (Fin m)) : ℝ)) =
              4 * (min 3 m : ℝ) := by
            have h1 : (∑ e ∈ E, (agreeCount (α e.1 e.2) (1 : Perm (Fin m)) : ℝ)) =
                ((4 * min 3 m : ℕ) : ℝ) := by exact_mod_cast hagree
            rw [h1]; push_cast; rfl
          rw [hE, hagreeR]
          norm_num

/-- Lower bound on the cross-degree gauge cost of a four-vertex apex-trivial three-transposition
configuration: in every degree `m : ℕ` and for every gauge `β : V → Perm (Fin m)`, the sum of
`distErr` over strictly ordered pairs is at least `6 - 4 * min 3 m / max 3 m`. -/
theorem six_sub_four_mul_min_div_max_le_sum_distErr {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V = 4) {v₀ : V} {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀})
    (β : V → Perm (Fin m)) :
    6 - 4 * (min 3 m : ℝ) / max 3 m ≤
      ∑ e ∈ univ.filter (fun e : V × V ↦ e.1 < e.2),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  let E : Finset (V × V) := univ.filter fun e : V × V ↦ e.1 < e.2
  have hE : #E = 6 := by
    rw [show E = (univ ×ˢ univ).filter _ from rfl, card_product_filter_lt, card_univ, hcard]; decide
  have hc : ∀ (s : Finset V) (f : V → Fin 3),
      (#{e ∈ E | e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)} : ℝ) ≤ 1 * #s := fun s f ↦ by
    have heq : E.filter (fun e ↦ e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2)) =
        univ.filter fun e : V × V ↦
          e.1 < e.2 ∧ e.1 ∈ s ∧ e.2 ∈ s ∧ f e.1 = α e.1 e.2 (f e.2) := by
      ext e; simp [E]
    rw [heq, one_mul]
    exact_mod_cast card_filter_lt_eq_apply_le_card h₀ hswap hinj s f
  have hbound := card_sub_mul_min_div_max_le_sum_distErr hc β
  rw [hE, hcard] at hbound
  linarith

/-- Exact degree-`m` gauge minimum for a four-vertex apex-trivial three-transposition
configuration: in every degree `m : ℕ`, the infimum over gauges `β : V → Perm (Fin m)` equals
`6 - 4 * min 3 m / max 3 m` (giving `14/3`, `10/3`, `2`, `3`, and `6 - 12/m` at `m = 1, 2, 3, 4`
and `m ≥ 3`). -/
theorem ciInf_sum_distErr_eq_six_sub_four_mul_min_div_max {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V = 4) {v₀ : V} {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀}) (m : ℕ) :
    (⨅ β : V → Perm (Fin m),
      ∑ e ∈ univ.filter (fun e : V × V ↦ e.1 < e.2),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      6 - 4 * (min 3 m : ℝ) / max 3 m := by
  refine le_antisymm ?_ (le_ciInf fun β ↦
    six_sub_four_mul_min_div_max_le_sum_distErr hcard h₀ hswap hinj β)
  have hbdd : BddBelow (Set.range fun β : V → Perm (Fin m) ↦
      ∑ e ∈ univ.filter (fun e : V × V ↦ e.1 < e.2),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) :=
    ⟨0, Set.forall_mem_range.mpr fun _ ↦ sum_nonneg fun _ _ ↦ distErr_nonneg _ _⟩
  refine (ciInf_le hbdd (fun _ ↦ (1 : Perm (Fin m)))).trans_eq ?_
  simpa using sum_distErr_const_one_of_isSwap_injOn hcard h₀ hswap hinj m

/-- Uniform cross-degree lower bound on four vertices: against any gauge `β : V → Perm (Fin m)`
of any degree `m : ℕ`, the sum of `distErr` over strictly ordered pairs is at least `2`. -/
theorem two_le_sum_distErr_of_isSwap_injOn {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V = 4) {v₀ : V} {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀})
    (β : V → Perm (Fin m)) :
    2 ≤ ∑ e ∈ univ.filter (fun e : V × V ↦ e.1 < e.2),
      distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hle1 : (min 3 m : ℝ) / max 3 m ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast min_le_max) (by positivity)
  have hle4 : 4 * (min 3 m : ℝ) / max 3 m ≤ 4 := by rw [mul_div_assoc]; linarith
  linarith [six_sub_four_mul_min_div_max_le_sum_distErr hcard h₀ hswap hinj β]

/-- The infimum over all degrees `m ≥ 2` and gauges `β : V → Perm (Fin (m + 2))` of the
cross-degree cost of a four-vertex apex-trivial three-transposition configuration is `2`. -/
theorem ciInf_succ_succ_sum_distErr_eq_two {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V = 4) {v₀ : V} {α : V → V → Perm (Fin 3)}
    (h₀ : ∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1)
    (hswap : ∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap)
    (hinj : Set.InjOn (fun e : V × V ↦ α e.1 e.2)
      {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀}) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∑ e ∈ univ.filter (fun e : V × V ↦ e.1 < e.2),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 2 := by
  have hmin (m : ℕ) : 2 ≤ 6 - 4 * min (3 : ℝ) ((m + 2 : ℕ) : ℝ) / (max 3 (m + 2) : ℕ) := by
    have hle1 : min (3 : ℝ) ((m + 2 : ℕ) : ℝ) / (max 3 (m + 2) : ℕ) ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast min_le_max) (by positivity)
    have hle4 : 4 * min (3 : ℝ) ((m + 2 : ℕ) : ℝ) / (max 3 (m + 2) : ℕ) ≤ 4 := by
      rw [mul_div_assoc]; linarith
    linarith
  simp_rw [ciInf_sum_distErr_eq_six_sub_four_mul_min_div_max hcard h₀ hswap hinj]
  refine le_antisymm ?_ (le_ciInf hmin)
  have hbdd : BddBelow (Set.range fun m : ℕ ↦
      6 - 4 * min (3 : ℝ) ((m + 2 : ℕ) : ℝ) / (max 3 (m + 2) : ℕ)) :=
    ⟨2, Set.forall_mem_range.mpr hmin⟩
  refine (ciInf_le hbdd 1).trans_eq ?_
  norm_num

/-- Every linearly ordered vertex set `V` of at most four elements and apex `v₀ : V` admits an
apex-trivial three-transposition assignment `α : V → V → Perm (Fin 3)`, witnessing in particular
that the hypotheses of `ciInf_succ_succ_sum_distErr_eq_two` are satisfiable. -/
theorem exists_isSwap_injOn_of_card_le_four {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V ≤ 4) (v₀ : V) :
    ∃ α : V → V → Perm (Fin 3),
      (∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1) ∧
      (∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap) ∧
      Set.InjOn (fun e : V × V ↦ α e.1 e.2)
        {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀} := by
  let P : Finset (V × V) := ((univ.erase v₀) ×ˢ (univ.erase v₀)).filter fun e ↦ e.1 < e.2
  let S₃ : Finset (Perm (Fin 3)) := univ.filter fun σ : Perm (Fin 3) ↦ σ.support.card = 2
  have hPle : #P ≤ #S₃ := by
    rw [card_product_filter_lt, card_erase_of_mem (mem_univ v₀), card_univ,
      show #S₃ = 3 by decide]
    rcases (by omega : Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ Fintype.card V = 2 ∨
      Fintype.card V = 3 ∨ Fintype.card V = 4) with h | h | h | h | h <;> simp [h]
  obtain ⟨T, hTS, hTcard⟩ := exists_subset_card_eq hPle
  have hEq : Fintype.card P = Fintype.card T := by
    rw [Fintype.card_coe, Fintype.card_coe, hTcard]
  let φ : P ≃ T := Fintype.equivOfCardEq hEq
  refine ⟨fun u v ↦ if hp : (u, v) ∈ P then (φ ⟨(u, v), hp⟩ : Perm (Fin 3)) else 1,
    fun u v _ huv ↦ ?_, fun u v hlt hu hv ↦ ?_, fun e₁ he₁ e₂ he₂ hα ↦ ?_⟩
  · have hnot : (u, v) ∉ P := fun hp ↦ by
      simp only [P, mem_filter, mem_product, mem_erase, mem_univ, and_true] at hp
      exact huv.elim hp.1.1 hp.1.2
    simp [hnot]
  · have hp : (u, v) ∈ P :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_erase.mpr ⟨hu, mem_univ _⟩,
        mem_erase.mpr ⟨hv, mem_univ _⟩⟩, hlt⟩
    simp only [hp, ↓reduceDIte]
    exact card_support_eq_two.mp (mem_filter.mp (hTS (φ ⟨(u, v), hp⟩).2)).2
  · have hp₁ : e₁ ∈ P :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_erase.mpr ⟨he₁.2.1, mem_univ _⟩,
        mem_erase.mpr ⟨he₁.2.2, mem_univ _⟩⟩, he₁.1⟩
    have hp₂ : e₂ ∈ P :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_erase.mpr ⟨he₂.2.1, mem_univ _⟩,
        mem_erase.mpr ⟨he₂.2.2, mem_univ _⟩⟩, he₂.1⟩
    have hφ : φ ⟨e₁, hp₁⟩ = φ ⟨e₂, hp₂⟩ :=
      Subtype.ext (by simpa [hp₁, hp₂] using hα)
    exact congrArg Subtype.val (φ.injective hφ)

/-- A finite linearly ordered vertex set `V` with apex `v₀` admits an apex-trivial
three-transposition assignment on its non-apex edges if and only if `Fintype.card V ≤ 4`. -/
theorem card_le_four_iff_exists_isSwap_injOn {V : Type*} [Fintype V] [LinearOrder V] (v₀ : V) :
    Fintype.card V ≤ 4 ↔
      ∃ α : V → V → Perm (Fin 3),
        (∀ u v : V, u < v → (u = v₀ ∨ v = v₀) → α u v = 1) ∧
        (∀ u v : V, u < v → u ≠ v₀ → v ≠ v₀ → (α u v).IsSwap) ∧
        Set.InjOn (fun e : V × V ↦ α e.1 e.2)
          {e : V × V | e.1 < e.2 ∧ e.1 ≠ v₀ ∧ e.2 ≠ v₀} :=
  ⟨fun h ↦ exists_isSwap_injOn_of_card_le_four h v₀,
   fun ⟨_, _, hswap, hinj⟩ ↦ card_le_four_of_isSwap_injOn hswap hinj⟩

end Equiv.Perm

end
