/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.MovedNorm

/-!
# The distance with errors between permutations of different degrees

Chapman and Lubotzky compare permutations of possibly different degrees `n` and `m` by
`Equiv.Perm.distErr σ τ = 1 - #{j < min n m | σ j = τ j} / max n m`, the values `σ j` and
`τ j` being compared as natural numbers. This is the distance used to define their cross-degree
coboundary constant, where the gauge may live in a different symmetric group than the cochain.

Main results:

* `Equiv.Perm.distErr_eq_movedNorm_div` and `Equiv.Perm.mul_distErr_eq_movedNorm`: in equal degree
  `n ≠ 0`, the distance with errors is the normalized Hamming distance
  `movedNorm (Fin n) (σ⁻¹ * τ) / n`, and `(n : ℝ) * distErr σ τ = movedNorm (Fin n) (σ⁻¹ * τ)` holds
  for every `n : ℕ`;
* `Equiv.Perm.agreeCount_one_right`, `Equiv.Perm.distErr_one_right_of_le`,
  `Equiv.Perm.distErr_one_right`, and `Equiv.Perm.agreeCount_mul_inv_eq_card_filter`: agreements
  and distances with errors against the identity permutation and against a degree-`m` quotient
  `g * h⁻¹`;
* `Equiv.Perm.distErr_comm`, `Equiv.Perm.distErr_eq_zero_iff`, and `Equiv.Perm.distErr_pos_iff`:
  symmetry, vanishing only on equal permutations of equal nonzero degree, and positivity;
* `Equiv.Perm.one_sub_min_div_max_le_distErr` and `Equiv.Perm.one_div_add_one_le_distErr_of_ne`:
  lower bounds `1 - min n m / max n m` (attained by `Equiv.Perm.distErr_one_one`) and
  `1 / (n + 1)` whenever `n ≠ m`, together with finite-sum consequences in `Finset`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, equation (2.9).
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

/-- A permutation of degree `n` agrees with itself at all `n` indices, including `n = 0`. -/
@[simp]
theorem agreeCount_self (σ : Perm (Fin n)) : agreeCount σ σ = n := by
  simpa using agreeCount_add_hammingDist σ σ

/-- A permutation of degree `0` has `0` agreements with any permutation. -/
@[simp]
theorem agreeCount_zero_left (σ : Perm (Fin 0)) (τ : Perm (Fin m)) : agreeCount σ τ = 0 := by
  simp [agreeCount_def]

/-- Any permutation has `0` agreements with a permutation of degree `0`. -/
@[simp]
theorem agreeCount_zero_right (σ : Perm (Fin n)) (τ : Perm (Fin 0)) : agreeCount σ τ = 0 := by
  simp [agreeCount_def]

/-- A permutation of degree `0` has distance with errors `1` from any permutation. -/
@[simp]
theorem distErr_zero_left (σ : Perm (Fin 0)) (τ : Perm (Fin m)) : distErr σ τ = 1 := by
  simp [distErr_def]

/-- Any permutation has distance with errors `1` from a permutation of degree `0`. -/
@[simp]
theorem distErr_zero_right (σ : Perm (Fin n)) (τ : Perm (Fin 0)) : distErr σ τ = 1 := by
  simp [distErr_def]

/-- Agreements between `σ : Perm (Fin n)` and the identity permutation of degree `m` are the fixed
points of `σ` lying below `m`. -/
theorem agreeCount_one_right (σ : Perm (Fin n)) (m : ℕ) :
    agreeCount σ (1 : Perm (Fin m)) = #{i : Fin n | (i : ℕ) < m ∧ σ i = i} := by
  rw [agreeCount_def]
  refine card_bij (fun j _ => j.castLE (min_le_left n m)) (fun j hj => ?_)
    (fun _ _ _ _ h => Fin.castLE_injective _ h) (fun i hi => ?_)
  · rw [mem_filter] at hj ⊢
    simp only [coe_one, id_eq, Fin.val_castLE] at hj
    exact ⟨mem_univ _, lt_of_lt_of_le j.isLt (min_le_right n m), Fin.ext hj.2⟩
  · rw [mem_filter] at hi
    refine ⟨⟨i, lt_min i.isLt hi.2.1⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, Fin.ext rfl⟩
    simpa using congrArg Fin.val hi.2.2

/-- Agreements between the identity permutation of degree `n` and `τ : Perm (Fin m)` are the fixed
points of `τ` lying below `n`. -/
theorem agreeCount_one_left (τ : Perm (Fin m)) (n : ℕ) :
    agreeCount (1 : Perm (Fin n)) τ = #{i : Fin m | (i : ℕ) < n ∧ τ i = i} :=
  (agreeCount_comm 1 τ).trans (agreeCount_one_right τ n)

/-- When `n ≤ m`, the number of agreements between `σ : Perm (Fin n)` and `1 : Perm (Fin m)` is the
number `n - #σ.support` of fixed points of `σ`. -/
theorem agreeCount_one_right_of_le (σ : Perm (Fin n)) {m : ℕ} (hnm : n ≤ m) :
    agreeCount σ (1 : Perm (Fin m)) = n - #σ.support := by
  have h1 : agreeCount σ (1 : Perm (Fin m)) = agreeCount σ (1 : Perm (Fin n)) := by
    rw [agreeCount_one_right, agreeCount_eq_card_eq]
    exact congrArg card (filter_congr fun i _ => by simp [i.isLt.trans_le hnm])
  have h2 : agreeCount σ (1 : Perm (Fin n)) + #σ.support = n := by
    simpa [hammingDist, support, eq_comm] using agreeCount_add_hammingDist σ 1
  omega

/-- When `m ≤ n`, the number of agreements between `1 : Perm (Fin n)` and `τ : Perm (Fin m)` is the
number `m - #τ.support` of fixed points of `τ`. -/
theorem agreeCount_one_left_of_ge {n : ℕ} (τ : Perm (Fin m)) (hmn : m ≤ n) :
    agreeCount (1 : Perm (Fin n)) τ = m - #τ.support :=
  (agreeCount_comm 1 τ).trans (agreeCount_one_right_of_le τ hmn)

/-- When `n ≤ m`, the distance with errors from `σ : Perm (Fin n)` to `1 : Perm (Fin m)` equals
`1 - n / m + movedNorm (Fin n) σ / m`. -/
theorem distErr_one_right_of_le (σ : Perm (Fin n)) {m : ℕ} (hnm : n ≤ m) :
    distErr σ (1 : Perm (Fin m)) = 1 - (n : ℝ) / m + movedNorm (Fin n) σ / m := by
  have hle : #σ.support ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
  rw [distErr_def, agreeCount_one_right_of_le σ hnm, Nat.max_eq_right hnm, Nat.cast_sub hle,
    movedNorm_apply]
  ring

/-- When `m ≤ n`, the distance with errors from `1 : Perm (Fin n)` to `τ : Perm (Fin m)` equals
`1 - m / n + movedNorm (Fin m) τ / n`. -/
theorem distErr_one_left_of_ge {n : ℕ} (τ : Perm (Fin m)) (hmn : m ≤ n) :
    distErr (1 : Perm (Fin n)) τ = 1 - (m : ℝ) / n + movedNorm (Fin m) τ / n :=
  (distErr_comm 1 τ).trans (distErr_one_right_of_le τ hmn)

/-- In equal nonzero degree, the distance with errors from `σ` to `1` is `movedNorm (Fin n) σ / n`.
-/
theorem distErr_one_right [NeZero n] (σ : Perm (Fin n)) :
    distErr σ (1 : Perm (Fin n)) = movedNorm (Fin n) σ / n := by
  rw [distErr_comm, distErr_eq_movedNorm_div, inv_one, one_mul]

/-- In equal nonzero degree, the distance with errors from `1` to `σ` is `movedNorm (Fin n) σ / n`.
-/
theorem distErr_one_left [NeZero n] (σ : Perm (Fin n)) :
    distErr (1 : Perm (Fin n)) σ = movedNorm (Fin n) σ / n := by
  rw [distErr_eq_movedNorm_div, inv_one, one_mul]

/-- Rescaling the equal-degree distance with errors by the degree recovers the moved-point norm of
the quotient `σ⁻¹ * τ` for every `n : ℕ`, including `n = 0`. -/
theorem mul_distErr_eq_movedNorm (σ τ : Perm (Fin n)) :
    (n : ℝ) * distErr σ τ = movedNorm (Fin n) (σ⁻¹ * τ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Subsingleton.elim (σ⁻¹ * τ) 1]
  · have : NeZero n := ⟨hn⟩
    rw [distErr_eq_movedNorm_div, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]

/-- Agreements between `σ : Perm (Fin n)` and a degree-`m` quotient `g * h⁻¹` correspond
bijectively to fibers `y : Fin m` at which `h y` lies below `n` and `g y` matches `σ (h y)`. -/
theorem agreeCount_mul_inv_eq_card_filter (σ : Perm (Fin n)) (g h : Perm (Fin m)) :
    agreeCount σ (g * h⁻¹) =
      #{y : Fin m | ∃ i : Fin n, (h y : ℕ) = i ∧ (g y : ℕ) = σ i} := by
  rw [agreeCount_def]
  set h₁ := min_le_left n m
  set h₂ := min_le_right n m
  refine card_bij (fun j _ => h⁻¹ (j.castLE h₂)) (fun j hj => ?_)
    (fun _ _ _ _ heq => Fin.castLE_injective h₂ (h⁻¹.injective heq)) (fun y hy => ?_)
  · rw [mem_filter] at hj ⊢
    refine ⟨mem_univ _, j.castLE h₁, by simp, ?_⟩
    simpa [mul_apply] using hj.2.symm
  · rw [mem_filter] at hy
    rcases hy.2 with ⟨i, hh, hg⟩
    let j : Fin (min n m) := ⟨h y, lt_min (hh ▸ i.isLt) (h y).isLt⟩
    have hc₁ : j.castLE h₁ = i := Fin.ext hh
    have hc₂ : j.castLE h₂ = h y := Fin.ext rfl
    refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [mul_apply, hc₁, hc₂]
      simp [hg]
    · rw [hc₂]
      simp

/-! ### Separation and positivity -/

/-- Two permutations of equal degree agree at all `n` indices if and only if they are equal. -/
@[simp]
theorem agreeCount_eq_iff {σ τ : Perm (Fin n)} : agreeCount σ τ = n ↔ σ = τ := by
  constructor
  · intro h
    have hdist : hammingDist ⇑σ ⇑τ = 0 := by
      have hsum := agreeCount_add_hammingDist σ τ
      omega
    exact DFunLike.coe_injective (hammingDist_eq_zero.mp hdist)
  · rintro rfl
    exact agreeCount_self σ

/-- The number of agreements reaches `max n m` if and only if the degrees coincide and the two
permutations are equal. -/
theorem agreeCount_eq_max_iff (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = max n m ↔ n = m ∧ HEq σ τ := by
  constructor
  · intro h
    have hle := agreeCount_le_min σ τ
    have hnm : n = m := by omega
    subst hnm
    rw [max_self, agreeCount_eq_iff] at h
    exact ⟨rfl, heq_of_eq h⟩
  · rintro ⟨rfl, h⟩
    rcases eq_of_heq h with rfl
    simp

/-- The distance with errors vanishes if and only if the degrees are equal and nonzero and the two
permutations coincide. -/
theorem distErr_eq_zero_iff (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    distErr σ τ = 0 ↔ n ≠ 0 ∧ n = m ∧ HEq σ τ := by
  by_cases hmax : max n m = 0
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    simp
  · have hmax' : ((max n m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmax
    rw [distErr_def, sub_eq_zero, eq_comm, div_eq_one_iff_eq hmax']
    norm_cast
    rw [agreeCount_eq_max_iff]
    exact ⟨fun ⟨hnm, h⟩ => ⟨by omega, hnm, h⟩, fun ⟨_, hnm, h⟩ => ⟨hnm, h⟩⟩

/-- In nonzero equal degree, the distance with errors vanishes if and only if the two permutations
are equal. -/
@[simp]
theorem distErr_eq_zero [NeZero n] {σ τ : Perm (Fin n)} : distErr σ τ = 0 ↔ σ = τ := by
  simp [distErr_eq_zero_iff, NeZero.ne n]

/-- The distance with errors is strictly positive if and only if `n = 0`, the degrees differ, or the
two permutations are distinct. -/
theorem distErr_pos_iff (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    0 < distErr σ τ ↔ n = 0 ∨ n ≠ m ∨ ¬ HEq σ τ := by
  rw [(distErr_nonneg σ τ).lt_iff_ne', ne_eq, distErr_eq_zero_iff]
  tauto

/-- In nonzero equal degree, the distance with errors is strictly positive if and only if the two
permutations are distinct. -/
@[simp]
theorem distErr_pos [NeZero n] {σ τ : Perm (Fin n)} : 0 < distErr σ τ ↔ σ ≠ τ := by
  simp [distErr_pos_iff, NeZero.ne n]

/-- Permutations of distinct degrees have strictly positive distance with errors. -/
theorem distErr_pos_of_ne' (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≠ m) :
    0 < distErr σ τ :=
  (distErr_pos_iff σ τ).mpr (Or.inr (Or.inl hnm))

/-- Distinct permutations of the same degree have strictly positive distance with errors. -/
theorem distErr_pos_of_ne {σ τ : Perm (Fin n)} (h : σ ≠ τ) : 0 < distErr σ τ :=
  (distErr_pos_iff σ τ).mpr (Or.inr (Or.inr (h ∘ eq_of_heq)))

/-! ### General degree-mismatch lower bounds -/

/-- When `n ≤ m`, the distance with errors is at least `1 - n / m`. -/
theorem one_sub_div_le_distErr_of_le (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    1 - (n : ℝ) / m ≤ distErr σ τ := by
  have h := one_sub_min_div_max_le_distErr σ τ
  rwa [← Nat.cast_min, Nat.min_eq_left hnm, Nat.max_eq_right hnm] at h

/-- When `m ≤ n`, the distance with errors is at least `1 - m / n`. -/
theorem one_sub_div_le_distErr_of_ge (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hmn : m ≤ n) :
    1 - (m : ℝ) / n ≤ distErr σ τ := by
  have h := one_sub_min_div_max_le_distErr σ τ
  rwa [← Nat.cast_min, Nat.min_eq_right hmn, Nat.max_eq_left hmn] at h

/-- When `n ≤ k` and `k ≤ m`, the distance with errors between `σ : Perm (Fin n)` and
`τ : Perm (Fin m)` is at least `1 - n / k`. -/
theorem one_sub_div_le_distErr_of_le_of_le (σ : Perm (Fin n)) (τ : Perm (Fin m)) {k : ℕ}
    (hnk : n ≤ k) (hkm : k ≤ m) : 1 - (n : ℝ) / k ≤ distErr σ τ := by
  rcases eq_or_ne k 0 with rfl | hk
  · obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hnk
    simp
  · refine (sub_le_sub_left ?_ 1).trans (one_sub_div_le_distErr_of_le σ τ (hnk.trans hkm))
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))
      (Nat.cast_le.mpr hkm)

/-- Whenever `n ≠ m`, a permutation of degree `n` and a permutation of degree `m` have distance with
errors at least `1 / (n + 1)`. -/
theorem one_div_add_one_le_distErr_of_ne (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≠ m) :
    1 / ((n : ℝ) + 1) ≤ distErr σ τ := by
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hlt)
    have hm1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
      one_div_le_one_div_of_le hn (by linarith)
    have h2 : 1 / (n : ℝ) ≤ 1 - (m : ℝ) / n := by
      rw [div_le_iff₀ hn, sub_mul, div_mul_cancel₀ _ hn.ne']
      linarith
    exact (h1.trans h2).trans (one_sub_div_le_distErr_of_ge σ τ hlt.le)
  · exact absurd rfl hnm
  · have h := one_sub_div_le_distErr_of_le_of_le σ τ (Nat.le_succ n) hgt
    have h1 : 1 / ((n : ℝ) + 1) = 1 - (n : ℝ) / (n + 1 : ℕ) := by
      push_cast
      field_simp
      ring
    exact h1 ▸ h

end Equiv.Perm

namespace Finset

open Equiv Equiv.Perm

variable {ι : Type*} {n m : ℕ}

/-- Summing `distErr` over a finite set expresses the total cost in terms of `#s` minus the
normalized total agreement count. -/
theorem sum_distErr_eq_card_sub_div (s : Finset ι) (f : ι → Perm (Fin n)) (g : ι → Perm (Fin m)) :
    (∑ x ∈ s, distErr (f x) (g x)) =
      (#s : ℝ) - ((∑ x ∈ s, agreeCount (f x) (g x) : ℕ) : ℝ) / max n m := by
  simp only [distErr_def, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, div_eq_mul_inv,
    ← sum_mul, Nat.cast_sum]

/-- Every sum of `distErr` over `s` is at least `#s * (1 - min n m / max n m)`. -/
theorem card_mul_one_sub_min_div_max_le_sum_distErr (s : Finset ι) (f : ι → Perm (Fin n))
    (g : ι → Perm (Fin m)) :
    (#s : ℝ) * (1 - (min n m : ℝ) / max n m) ≤ ∑ x ∈ s, distErr (f x) (g x) := by
  simpa [nsmul_eq_mul] using
    s.card_nsmul_le_sum _ _ fun x _ => one_sub_min_div_max_le_distErr (f x) (g x)

/-- Comparing degree-`n` permutations against degree-`m` permutations with `n ≠ m` over a finite set
`s` has total distance with errors at least `#s / (n + 1)`. -/
theorem card_div_add_one_le_sum_distErr_of_ne (s : Finset ι) (f : ι → Perm (Fin n))
    (g : ι → Perm (Fin m)) (hnm : n ≠ m) :
    (#s : ℝ) / ((n : ℝ) + 1) ≤ ∑ x ∈ s, distErr (f x) (g x) := by
  have h := s.card_nsmul_le_sum _ _ fun x _ => one_div_add_one_le_distErr_of_ne (f x) (g x) hnm
  simpa [nsmul_eq_mul, div_eq_mul_inv] using h

end Finset

end
