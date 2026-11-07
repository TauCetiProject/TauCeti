/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Numerical semigroups and their finite-gap invariants

A numerical semigroup is an additive submonoid of `ℕ` with finite complement.
We characterize this condition by gcd one, and define its gaps, genus, conductor,
integer-valued Frobenius number, and multiplicity. The conductor is the least threshold
above which every integer belongs to the semigroup; subtracting one gives Frobenius
number `-1` for `⊤`, without excluding this case from the API.

These invariants provide the basic interface for counting gaps using Apéry sets.
The comparison with Mathlib's `FrobeniusNumber` allows results about generators,
including the two-generator formula, to be used without constructing a new carrier.

## References

* A. Assi and P. A. García-Sánchez, *Numerical semigroups and applications* (2014),
  §1, Proposition 1 and the definitions of gaps, genus, Frobenius number and conductor.
-/

public section

namespace AddSubmonoid

variable (S : AddSubmonoid ℕ)

/-- An additive submonoid of `ℕ` is a numerical semigroup if its complement is finite. -/
def IsNumericalSemigroup : Prop := (S : Set ℕ)ᶜ.Finite

/-- The defining finite-complement condition for a numerical semigroup. -/
theorem isNumericalSemigroup_def : S.IsNumericalSemigroup ↔ (S : Set ℕ)ᶜ.Finite := Iff.rfl

/-- The gaps are the natural numbers outside the submonoid. -/
def numericalGaps : Set ℕ := (S : Set ℕ)ᶜ

/-- A gap is exactly a natural number outside the submonoid. -/
@[simp]
theorem mem_numericalGaps {n : ℕ} : n ∈ S.numericalGaps ↔ n ∉ S := Iff.rfl

/-- The genus counts the gaps. Its value is zero for an infinite complement. -/
noncomputable def numericalGenus : ℕ := S.numericalGaps.ncard

/-- The genus is the cardinality of the set of gaps. -/
theorem numericalGenus_def : S.numericalGenus = S.numericalGaps.ncard := (rfl)

/-- The least threshold above which every natural number belongs to `S`.
It is zero if there is no such threshold. -/
noncomputable def numericalConductor : ℕ := sInf {c : ℕ | ∀ n ≥ c, n ∈ S}

/-- The Frobenius number, with value `-1` for the full semigroup (and for
submonoids that are not numerical semigroups). -/
noncomputable def numericalFrobenius : ℤ := (S.numericalConductor : ℤ) - 1

/-- The least positive element of the submonoid, or zero if there is none. -/
noncomputable def numericalMultiplicity : ℕ := sInf {n : ℕ | n ∈ S ∧ 0 < n}

/-- Finite complement is equivalent to containing every sufficiently large integer. -/
theorem isNumericalSemigroup_iff_exists_bound :
    S.IsNumericalSemigroup ↔ ∃ c : ℕ, ∀ n ≥ c, n ∈ S := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.bddAbove
    exact ⟨b + 1, fun n hn ↦ by
      by_contra hnot
      have := hb hnot
      omega⟩
  · rintro ⟨c, hc⟩
    exact (Set.finite_lt_nat c).subset fun n hn ↦ lt_of_not_ge fun hge ↦ hn (hc n hge)

/-- A submonoid of `ℕ` has finite complement exactly when its elements have gcd one. -/
theorem isNumericalSemigroup_iff_setGcd :
    S.IsNumericalSemigroup ↔ Nat.setGcd S = 1 := by
  rw [isNumericalSemigroup_iff_exists_bound]
  constructor
  · rintro ⟨c, hc⟩
    have h₁ := Nat.setGcd_dvd_of_mem (hc c le_rfl)
    have h₂ := Nat.setGcd_dvd_of_mem (hc (c + 1) (by omega))
    exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right h₁).mpr h₂)
  · intro hg
    obtain ⟨c, hc⟩ := Nat.exists_mem_closure_of_ge (S : Set ℕ)
    exact ⟨c, fun n hn ↦ by simpa using hc n hn (hg ▸ one_dvd n)⟩

/-- The full submonoid is a numerical semigroup. -/
@[simp]
theorem isNumericalSemigroup_top : (⊤ : AddSubmonoid ℕ).IsNumericalSemigroup := by
  simp [IsNumericalSemigroup]

variable {S}

/-- A numerical semigroup has finitely many gaps. -/
theorem IsNumericalSemigroup.finite_numericalGaps (h : S.IsNumericalSemigroup) :
    S.numericalGaps.Finite := h

/-- Every number at least the conductor belongs to a numerical semigroup. -/
theorem mem_of_numericalConductor_le (h : S.IsNumericalSemigroup) {n : ℕ}
    (hn : S.numericalConductor ≤ n) : n ∈ S :=
  Nat.sInf_mem (s := {c : ℕ | ∀ n ≥ c, n ∈ S})
    ((isNumericalSemigroup_iff_exists_bound S).mp h) n hn

/-- A threshold bounds the conductor exactly when it contains the whole tail. -/
theorem numericalConductor_le_iff (h : S.IsNumericalSemigroup) {c : ℕ} :
    S.numericalConductor ≤ c ↔ ∀ n ≥ c, n ∈ S := by
  exact ⟨fun hc n hn ↦ mem_of_numericalConductor_le h (hc.trans hn),
    fun hc ↦ Nat.sInf_le (s := {c : ℕ | ∀ n ≥ c, n ∈ S}) hc⟩

/-- The conductor vanishes precisely for the full semigroup. -/
@[simp]
theorem numericalConductor_eq_zero_iff (h : S.IsNumericalSemigroup) :
    S.numericalConductor = 0 ↔ S = ⊤ := by
  constructor
  · intro hc
    exact top_unique fun n _ ↦ mem_of_numericalConductor_le h (by omega)
  · rintro rfl
    exact Nat.le_zero.mp (Nat.sInf_le (by simp))

/-- The genus vanishes precisely for the full semigroup. -/
@[simp]
theorem numericalGenus_eq_zero_iff (h : S.IsNumericalSemigroup) :
    S.numericalGenus = 0 ↔ S = ⊤ := by
  rw [numericalGenus, Set.ncard_eq_zero h.finite_numericalGaps]
  simp [numericalGaps, SetLike.ext'_iff]

/-- The only numerical semigroup with Frobenius number `-1` is the full semigroup. -/
@[simp]
theorem numericalFrobenius_eq_neg_one_iff (h : S.IsNumericalSemigroup) :
    S.numericalFrobenius = -1 ↔ S = ⊤ := by
  rw [← numericalConductor_eq_zero_iff h, numericalFrobenius]
  omega

/-- The conductor is one more than the integer-valued Frobenius number. -/
theorem numericalFrobenius_add_one (S : AddSubmonoid ℕ) :
    S.numericalFrobenius + 1 = S.numericalConductor := by
  simp [numericalFrobenius]

/-- Every natural number strictly above the Frobenius number belongs to the semigroup. -/
theorem mem_of_numericalFrobenius_lt (h : S.IsNumericalSemigroup) {n : ℕ}
    (hn : S.numericalFrobenius < n) : n ∈ S := by
  apply mem_of_numericalConductor_le h
  unfold numericalFrobenius at hn
  omega

/-- A proper numerical semigroup has nonnegative Frobenius number. -/
theorem numericalFrobenius_nonneg (h : S.IsNumericalSemigroup) (hS : S ≠ ⊤) :
    0 ≤ S.numericalFrobenius := by
  have := (numericalConductor_eq_zero_iff h).not.mpr hS
  unfold numericalFrobenius
  omega

/-- A natural number is the Frobenius number precisely when it is the last gap.
This also characterizes when the integer-valued invariant is nonnegative. -/
theorem numericalFrobenius_eq_natCast_iff (S : AddSubmonoid ℕ) (n : ℕ) :
    S.numericalFrobenius = n ↔ n ∉ S ∧ ∀ k > n, k ∈ S := by
  have hcast : S.numericalFrobenius = n ↔ S.numericalConductor = n + 1 := by
    unfold numericalFrobenius
    omega
  rw [hcast, numericalConductor]
  rw [Nat.sInf_upward_closed_eq_succ_iff (s := {c : ℕ | ∀ n ≥ c, n ∈ S})
    (fun _ _ hle hc k hk ↦ hc k (hle.trans hk)) n]
  constructor
  · rintro ⟨htail, hnot⟩
    refine ⟨fun hn ↦ hnot fun k hk ↦ ?_, fun k hk ↦ htail k (by omega)⟩
    rcases hk.eq_or_lt with rfl | hk
    · exact hn
    · exact htail k (by omega)
  · rintro ⟨hnot, htail⟩
    exact ⟨fun k hk ↦ htail k (by omega), fun hc ↦ hnot (hc n le_rfl)⟩

/-- The Frobenius number of a proper numerical semigroup is itself a gap. -/
theorem numericalFrobenius_toNat_notMem (h : S.IsNumericalSemigroup) (hS : S ≠ ⊤) :
    S.numericalFrobenius.toNat ∉ S :=
  ((numericalFrobenius_eq_natCast_iff S _).mp
    (Int.toNat_of_nonneg (numericalFrobenius_nonneg h hS)).symm).1

/-- Comparison with Mathlib's Frobenius-number predicate on any set of generators. -/
theorem frobeniusNumber_numericalFrobenius {s : Set ℕ}
    (h : (closure s).IsNumericalSemigroup) (hS : closure s ≠ ⊤) :
    FrobeniusNumber (closure s).numericalFrobenius.toNat s := by
  refine frobeniusNumber_iff.mpr ⟨numericalFrobenius_toNat_notMem h hS, fun n hn ↦ ?_⟩
  exact mem_of_numericalFrobenius_lt h (by omega)

/-- A numerical semigroup has a positive element. -/
theorem IsNumericalSemigroup.exists_pos (h : S.IsNumericalSemigroup) :
    ∃ n : ℕ, n ∈ S ∧ 0 < n :=
  ⟨S.numericalConductor + 1, mem_of_numericalConductor_le h (by omega), by omega⟩

/-- The multiplicity is a member of the numerical semigroup. -/
theorem numericalMultiplicity_mem (h : S.IsNumericalSemigroup) :
    S.numericalMultiplicity ∈ S :=
  (Nat.sInf_mem (s := {n : ℕ | n ∈ S ∧ 0 < n}) h.exists_pos).1

/-- The multiplicity of a numerical semigroup is positive. -/
theorem numericalMultiplicity_pos (h : S.IsNumericalSemigroup) :
    0 < S.numericalMultiplicity :=
  (Nat.sInf_mem (s := {n : ℕ | n ∈ S ∧ 0 < n}) h.exists_pos).2

/-- The multiplicity is no larger than any positive member. -/
theorem numericalMultiplicity_le {n : ℕ} (hn : n ∈ S) (hpos : 0 < n) :
    S.numericalMultiplicity ≤ n := Nat.sInf_le ⟨hn, hpos⟩

/-- The submonoid generated by two integers is numerical precisely when they are coprime. -/
theorem isNumericalSemigroup_closure_pair_iff (a b : ℕ) :
    (closure ({a, b} : Set ℕ)).IsNumericalSemigroup ↔ a.Coprime b := by
  rw [isNumericalSemigroup_iff_setGcd, Nat.coprime_iff_gcd_eq_one]
  suffices Nat.setGcd (closure ({a, b} : Set ℕ)) = a.gcd b by rw [this]
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (Nat.setGcd_dvd_of_mem (subset_closure (by simp)))
      (Nat.setGcd_dvd_of_mem (subset_closure (by simp)))
  · apply Nat.dvd_setGcd_iff.mpr
    intro n hn
    induction hn using closure_induction with
    | mem n hn =>
        rcases Set.mem_insert_iff.mp hn with rfl | hn
        · exact Nat.gcd_dvd_left _ _
        · rcases Set.mem_singleton_iff.mp hn with rfl
          exact Nat.gcd_dvd_right _ _
    | zero => exact dvd_zero _
    | add x y _ _ hx hy => exact dvd_add hx hy

/-- The full semigroup has no gaps. -/
@[simp]
theorem numericalGaps_top : (⊤ : AddSubmonoid ℕ).numericalGaps = ∅ := by
  simp [numericalGaps]

/-- The full semigroup has conductor zero. -/
@[simp]
theorem numericalConductor_top : (⊤ : AddSubmonoid ℕ).numericalConductor = 0 :=
  (numericalConductor_eq_zero_iff isNumericalSemigroup_top).mpr rfl

/-- The full semigroup has multiplicity one. -/
@[simp]
theorem numericalMultiplicity_top : (⊤ : AddSubmonoid ℕ).numericalMultiplicity = 1 := by
  apply le_antisymm (numericalMultiplicity_le (by simp) (by omega))
  exact numericalMultiplicity_pos isNumericalSemigroup_top

/-- The full semigroup has genus zero. -/
@[simp]
theorem numericalGenus_top : (⊤ : AddSubmonoid ℕ).numericalGenus = 0 :=
  (numericalGenus_eq_zero_iff isNumericalSemigroup_top).mpr rfl

/-- The full semigroup has integer-valued Frobenius number minus one. -/
@[simp]
theorem numericalFrobenius_top : (⊤ : AddSubmonoid ℕ).numericalFrobenius = -1 :=
  (numericalFrobenius_eq_neg_one_iff isNumericalSemigroup_top).mpr rfl

/-- The gaps of the semigroup generated by `3` and `5`. -/
theorem numericalGaps_closure_three_five :
    (closure ({3, 5} : Set ℕ)).numericalGaps = {1, 2, 4, 7} := by
  ext n
  have hf := frobeniusNumber_iff.mp (frobeniusNumber_pair (m := 3) (n := 5)
    (by decide) (by decide) (by decide))
  by_cases hn : n ≤ 7
  · interval_cases n <;> simp [mem_closure_pair, smul_eq_mul] <;> try omega
    · exact ⟨1, 0, rfl⟩
    · exact ⟨0, 1, rfl⟩
    · exact ⟨2, 0, rfl⟩
  · have hmem := hf.2 n (by norm_num at *; omega)
    simp only [mem_numericalGaps, hmem, not_true, Set.mem_insert_iff, Set.mem_singleton_iff,
      false_iff]
    omega

/-- The semigroup generated by `3` and `5` has genus four. -/
theorem numericalGenus_closure_three_five :
    (closure ({3, 5} : Set ℕ)).numericalGenus = 4 := by
  rw [numericalGenus, numericalGaps_closure_three_five]
  norm_num

/-- The semigroup generated by `3` and `5` has Frobenius number seven. -/
theorem numericalFrobenius_closure_three_five :
    (closure ({3, 5} : Set ℕ)).numericalFrobenius = 7 := by
  apply (numericalFrobenius_eq_natCast_iff _ 7).mpr
  simpa using frobeniusNumber_iff.mp
    (frobeniusNumber_pair (m := 3) (n := 5) (by decide) (by decide) (by decide))

/-- The even integers do not form a numerical semigroup. -/
theorem not_isNumericalSemigroup_closure_two_four :
    ¬ (closure ({2, 4} : Set ℕ)).IsNumericalSemigroup := by
  rw [isNumericalSemigroup_closure_pair_iff]
  decide

end AddSubmonoid
