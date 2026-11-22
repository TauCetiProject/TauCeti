/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoxeterNumber
import Mathlib.Data.Nat.Prime.Basic

/-!
# Exponents and fundamental degrees of Dynkin types

Defines the exponents `TauCeti.DynkinType.exponents` (`m₁, …, mᵣ`) and fundamental invariant degrees
`TauCeti.DynkinType.degrees` (`dᵢ = mᵢ + 1`) of any Dynkin type (`1, …, n` for `Aₙ`; `1, 3, …, 2n-1`
for `Bₙ`/`Cₙ`; `1, 3, …, 2n-3, n-1` for `Dₙ`; standard lists for `E₆`–`G₂`).

## Main definitions & results

* `TauCeti.DynkinType.exponents`, `degrees`, `two_mul_sum_exponents`, `sum_exponents`,
  `sum_degrees`, `mem_exponents_of_coprime`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§ 3.7, 3.16–3.20.
-/

public section

namespace TauCeti.DynkinType

/-- The **exponents** `m₁, …, mᵣ` of a Dynkin type: for a valid Dynkin type, the complex eigenvalues
of every Coxeter element on the root space, counted with multiplicity, are `exp (2πi e / h)` as `e`
runs over `t.exponents` (`TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`). -/
def exponents : DynkinType → List ℕ
  | .A n => (List.range n).map (· + 1)
  | .B n | .C n => (List.range n).map (2 * · + 1)
  | .D n => if n = 0 then [] else (List.range (n - 1)).map (2 * · + 1) ++ [n - 1]
  | .E6 => [1, 4, 5, 7, 8, 11]
  | .E7 => [1, 5, 7, 9, 11, 13, 17]
  | .E8 => [1, 7, 11, 13, 17, 19, 23, 29]
  | .F4 => [1, 5, 7, 11]
  | .G2 => [1, 5]

@[simp] lemma exponents_A (n : ℕ) : (A n).exponents = (List.range n).map (· + 1) := (rfl)
@[simp] lemma exponents_B (n : ℕ) : (B n).exponents = (List.range n).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_C (n : ℕ) : (C n).exponents = (List.range n).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_D_zero : (D 0).exponents = [] := (rfl)
@[simp] lemma exponents_D_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (D n).exponents = (List.range (n - 1)).map (2 * · + 1) ++ [n - 1] := by
  simp [exponents, hn]
@[simp] lemma exponents_E6 : E6.exponents = [1, 4, 5, 7, 8, 11] := (rfl)
@[simp] lemma exponents_E7 : E7.exponents = [1, 5, 7, 9, 11, 13, 17] := (rfl)
@[simp] lemma exponents_E8 : E8.exponents = [1, 7, 11, 13, 17, 19, 23, 29] := (rfl)
@[simp] lemma exponents_F4 : F4.exponents = [1, 5, 7, 11] := (rfl)
@[simp] lemma exponents_G2 : G2.exponents = [1, 5] := (rfl)

/-- The exponents of `E₈` are the residues modulo `30` coprime to `30`. -/
theorem exponents_E8_eq_filter : E8.exponents = (List.range 30).filter (Nat.Coprime · 30) := by
  decide

/-- The exponents of `F₄` are the residues modulo `12` coprime to `12`. -/
theorem exponents_F4_eq_filter : F4.exponents = (List.range 12).filter (Nat.Coprime · 12) := by
  decide

/-- The exponents of `G₂` are the residues modulo `6` coprime to `6`. -/
theorem exponents_G2_eq_filter : G2.exponents = (List.range 6).filter (Nat.Coprime · 6) := by
  decide

/-- The **fundamental invariant degrees** `dᵢ = mᵢ + 1` of a Dynkin type. -/
def degrees (t : DynkinType) : List ℕ :=
  t.exponents.map (· + 1)

/-- Unfolded characterization of `TauCeti.DynkinType.degrees` as `t.exponents.map (· + 1)`. -/
lemma degrees_def (t : DynkinType) : t.degrees = t.exponents.map (· + 1) := (rfl)

/-- Membership in `t.degrees` in terms of `t.exponents`. -/
@[simp] lemma mem_degrees_iff {t : DynkinType} {d : ℕ} :
    d ∈ t.degrees ↔ ∃ e ∈ t.exponents, e + 1 = d := by
  rw [degrees_def, List.mem_map]

@[simp] lemma length_exponents (t : DynkinType) : t.exponents.length = t.rank := by
  cases t with
  | A n | B n | C n => simp
  | D n =>
    rcases eq_or_ne n 0 with rfl | hn
    · rfl
    · simp [exponents, hn]; omega
  | E6 | E7 | E8 | F4 | G2 => rfl

@[simp] lemma length_degrees (t : DynkinType) : t.degrees.length = t.rank := by
  simp [degrees_def]

/-- **Twice the sum of the exponents of any Dynkin type equals its number of roots**:
`2 ∑ mᵢ = |Φ|`. -/
theorem two_mul_sum_exponents (t : DynkinType) : 2 * t.exponents.sum = t.numRoots := by
  have hsum : ∀ (m : ℕ) (f : ℕ → ℕ),
      ((List.range m).map f).sum = ∑ k ∈ Finset.range m, f k := fun m f => by
    simpa only [List.toFinset_range] using (List.sum_toFinset f List.nodup_range).symm
  have hodd : ∀ m : ℕ, ∑ k ∈ Finset.range m, (2 * k + 1) = m ^ 2 := fun m => by
    have h2 := Finset.sum_range_id_mul_two m
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h2
      nlinarith
  cases t with
  | A n =>
    have h2 := Finset.sum_range_id_mul_two n
    rw [exponents_A, hsum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one, numRoots_A]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h2
      nlinarith
  | B n | C n =>
    simp only [exponents_B, exponents_C, hsum, hodd, numRoots_B, numRoots_C]
  | D n =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [exponents_D_of_ne_zero hn, List.sum_append, hsum, hodd,
        List.sum_singleton, numRoots_D]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
  | E6 | E7 | E8 | F4 | G2 => decide

/-- The sum of the exponents of any Dynkin type is half its number of roots (`|Φ| / 2`, equal to
`|Φ⁺|` for valid types). -/
@[simp] theorem sum_exponents (t : DynkinType) : t.exponents.sum = t.numRoots / 2 := by
  rw [← two_mul_sum_exponents, Nat.mul_div_right _ (by norm_num)]

/-- The sum of the fundamental degrees of any Dynkin type is `|Φ| / 2 + r` (`|Φ⁺| + r` for valid
types). -/
@[simp] theorem sum_degrees (t : DynkinType) : t.degrees.sum = t.numRoots / 2 + t.rank := by
  simp [degrees_def, List.sum_map_add]

/-- Every exponent of a valid Dynkin type is strictly positive. -/
lemma pos_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ} (he : e ∈ t.exponents) :
    0 < e := by
  cases t with
  | A n | B n | C n =>
    simp only [exponents_A, exponents_B, exponents_C, List.mem_map, List.mem_range] at he
    obtain ⟨k, _, rfl⟩ := he
    omega
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    rw [exponents_D_of_ne_zero (by omega), List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨k, _, rfl⟩ | rfl <;> omega
  | E6 | E7 | E8 | F4 | G2 =>
    revert e he
    decide

/-- Every exponent of a valid Dynkin type is strictly less than its Coxeter number. -/
lemma lt_coxeterNumber_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e ∈ t.exponents) : e < t.coxeterNumber := by
  cases t with
  | A n | B n | C n =>
    simp only [exponents_A, exponents_B, exponents_C, coxeterNumber_A, coxeterNumber_B,
      coxeterNumber_C, List.mem_map, List.mem_range] at he ⊢
    obtain ⟨k, hk, rfl⟩ := he
    omega
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    rw [exponents_D_of_ne_zero (by omega), List.mem_append, List.mem_map, List.mem_singleton] at he
    simp only [coxeterNumber_D]
    rcases he with ⟨k, hk, rfl⟩ | rfl
    · rw [List.mem_range] at hk; omega
    · omega
  | E6 | E7 | E8 | F4 | G2 =>
    simp only [coxeterNumber_E6, coxeterNumber_E7, coxeterNumber_E8, coxeterNumber_F4,
      coxeterNumber_G2]
    revert e he
    decide

/-- **Every residue `< h` coprime to the Coxeter number `h` is an exponent of `t`.** -/
theorem mem_exponents_of_coprime {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e < t.coxeterNumber) (hcop : e.Coprime t.coxeterNumber) : e ∈ t.exponents := by
  cases t with
  | A n =>
    have hn : 1 ≤ n := valid_A.mp ht
    simp only [coxeterNumber_A] at he hcop
    have he0 : e ≠ 0 := fun h0 => by rw [h0, Nat.coprime_zero_left] at hcop; omega
    simp only [exponents_A, List.mem_map, List.mem_range]
    exact ⟨e - 1, by omega, by omega⟩
  | B n | C n =>
    simp only [coxeterNumber_B, coxeterNumber_C] at he hcop
    have hmod : e % 2 = 1 := Nat.odd_iff.mp hcop.coprime_mul_right_right.odd_of_right
    simp only [exponents_B, exponents_C, List.mem_map, List.mem_range]
    exact ⟨e / 2, by omega, by omega⟩
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    simp only [coxeterNumber_D] at he hcop
    have hmod : e % 2 = 1 := Nat.odd_iff.mp hcop.coprime_mul_right_right.odd_of_right
    rw [exponents_D_of_ne_zero (by omega), List.mem_append, List.mem_map]
    exact Or.inl ⟨e / 2, List.mem_range.mpr (by omega), by omega⟩
  | E6 =>
    simp only [coxeterNumber_E6] at he hcop
    have hsub : ∀ x ∈ (List.range 12).filter (Nat.Coprime · 12), x ∈ E6.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)
  | E7 =>
    simp only [coxeterNumber_E7] at he hcop
    have hsub : ∀ x ∈ (List.range 18).filter (Nat.Coprime · 18), x ∈ E7.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)
  | E8 =>
    simp only [coxeterNumber_E8] at he hcop
    have hsub : ∀ x ∈ (List.range 30).filter (Nat.Coprime · 30), x ∈ E8.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)
  | F4 =>
    simp only [coxeterNumber_F4] at he hcop
    have hsub : ∀ x ∈ (List.range 12).filter (Nat.Coprime · 12), x ∈ F4.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)
  | G2 =>
    simp only [coxeterNumber_G2] at he hcop
    have hsub : ∀ x ∈ (List.range 6).filter (Nat.Coprime · 6), x ∈ G2.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)

/-- `1` is always an exponent of a valid Dynkin type. -/
lemma one_mem_exponents {t : DynkinType} (ht : t.Valid) : 1 ∈ t.exponents :=
  mem_exponents_of_coprime ht (two_le_coxeterNumber ht) (Nat.coprime_one_left _)

/-- `h - 1` is always an exponent of a valid Dynkin type. -/
lemma coxeterNumber_sub_one_mem_exponents {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber - 1 ∈ t.exponents := by
  have h2 := two_le_coxeterNumber ht
  refine mem_exponents_of_coprime ht (by omega) ?_
  have hcop : (t.coxeterNumber - 1).Coprime (t.coxeterNumber - 1 + 1) := by simp
  rwa [Nat.sub_add_cancel (by omega)] at hcop

/-- Every fundamental degree of a valid Dynkin type is at least `2`. -/
lemma two_le_of_mem_degrees {t : DynkinType} (ht : t.Valid) {d : ℕ} (hd : d ∈ t.degrees) :
    2 ≤ d := by
  obtain ⟨e, he, rfl⟩ := mem_degrees_iff.mp hd
  have := pos_of_mem_exponents ht he
  omega

/-- Every fundamental degree of a valid Dynkin type is at most its Coxeter number. -/
lemma le_coxeterNumber_of_mem_degrees {t : DynkinType} (ht : t.Valid) {d : ℕ}
    (hd : d ∈ t.degrees) : d ≤ t.coxeterNumber := by
  obtain ⟨e, he, rfl⟩ := mem_degrees_iff.mp hd
  exact lt_coxeterNumber_of_mem_exponents ht he

/-- `2` is always a fundamental degree of a valid Dynkin type (corresponding to the invariant
quadratic form). -/
lemma two_mem_degrees {t : DynkinType} (ht : t.Valid) : 2 ∈ t.degrees :=
  mem_degrees_iff.mpr ⟨1, one_mem_exponents ht, rfl⟩

/-- The Coxeter number `h` is always a fundamental degree of a valid Dynkin type. -/
lemma coxeterNumber_mem_degrees {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber ∈ t.degrees := by
  have h2 := two_le_coxeterNumber ht
  exact mem_degrees_iff.mpr ⟨t.coxeterNumber - 1, coxeterNumber_sub_one_mem_exponents ht, by omega⟩

end TauCeti.DynkinType
