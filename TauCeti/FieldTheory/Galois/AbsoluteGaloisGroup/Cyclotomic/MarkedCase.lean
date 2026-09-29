/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.OddDegree

/-!
# Arithmetic cases for marked local Galois presentations

The marked classification of maximal pro-`p` local Galois groups separates the dyadic fields
with exactly two `2`-power roots of unity according to the parity of their degree and, in even
degree, according to whether `-1` belongs to the cyclotomic image. This file defines those
arithmetic predicates and proves that every finite extension of `ℚ₂` lies in exactly one of the
four resulting cases.

The partition is purely arithmetic: it does not assume a Demushkin presentation. It is the case
split used when the abstract marked classification is applied to a local Galois group.
-/

public section

namespace TauCeti

section FreeCase

variable (p : ℕ) (K : Type*) [Field K]

/-- The free arithmetic case: `K` does not contain a primitive `p`-th root of unity. -/
def IsFreeCase : Prop :=
  ¬ ∃ ζ : K, IsPrimitiveRoot ζ p

/-- Characterization of the free arithmetic case. -/
theorem isFreeCase_iff : IsFreeCase p K ↔ ¬ ∃ ζ : K, IsPrimitiveRoot ζ p :=
  Iff.rfl

variable {K}

/-- A field in which `2 ≠ 0` (for example, any field of characteristic zero) is never in the
free arithmetic case at `p = 2`, since `-1` is a primitive square root of unity. -/
theorem not_isFreeCase_two [NeZero (2 : K)] : ¬ IsFreeCase 2 K := by
  rw [isFreeCase_iff]
  push Not
  have := ringChar.charP K
  refine ⟨-1, IsPrimitiveRoot.neg_one (ringChar K) fun h => NeZero.ne (2 : K) ?_⟩
  exact_mod_cast h ▸ ringChar.Nat.cast_ringChar

end FreeCase

section QNeTwoCase

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The nonexceptional Demushkin case: `K` contains `μ_p` and its group of `p`-power roots of
unity does not have order two. -/
def IsQNeTwoCase : Prop :=
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  (∃ ζ : K, IsPrimitiveRoot ζ p) ∧
    localRootOfUnityOrder p K
      (finite_pPowerRootsOfUnity (p := p) (K := K)
        (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) ≠ 2

variable {p K}

/-- Characterization of the nonexceptional Demushkin case. -/
theorem isQNeTwoCase_iff : IsQNeTwoCase p K ↔
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
    (∃ ζ : K, IsPrimitiveRoot ζ p) ∧
      localRootOfUnityOrder p K
        (finite_pPowerRootsOfUnity (p := p) (K := K)
          (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) ≠ 2 :=
  Iff.rfl

end QNeTwoCase

section Dyadic

variable (K : Type*) [Field K] [Algebra ℚ_[2] K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The even dyadic case in which the cyclotomic image contains `-1`. -/
def IsDyadicEvenPlusMinusCase : Prop :=
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  localRootOfUnityOrder 2 K
      (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 ∧
    Even (Module.finrank ℚ_[2] K) ∧
      (-1 : ℤ_[2]ˣ) ∈ (localCyclotomicCharacter 2 K).range

/-- The even dyadic case in which the cyclotomic image does not contain `-1`. -/
def IsDyadicEvenPrincipalCase : Prop :=
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  localRootOfUnityOrder 2 K
      (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 ∧
    Even (Module.finrank ℚ_[2] K) ∧
      (-1 : ℤ_[2]ˣ) ∉ (localCyclotomicCharacter 2 K).range

/-- The four arithmetic branches of the dyadic marked classification. -/
inductive DyadicMarkedCase
  | qNeTwo
  | odd
  | evenPlusMinus
  | evenPrincipal
  deriving DecidableEq

/-- The arithmetic predicate represented by a dyadic marked case. -/
def DyadicMarkedCase.Holds : DyadicMarkedCase → Prop
  | .qNeTwo => IsQNeTwoCase 2 K
  | .odd => IsDyadicOddCase K
  | .evenPlusMinus => IsDyadicEvenPlusMinusCase K
  | .evenPrincipal => IsDyadicEvenPrincipalCase K

@[simp]
theorem DyadicMarkedCase.holds_qNeTwo : DyadicMarkedCase.qNeTwo.Holds K ↔
    IsQNeTwoCase 2 K :=
  Iff.rfl

@[simp]
theorem DyadicMarkedCase.holds_odd : DyadicMarkedCase.odd.Holds K ↔ IsDyadicOddCase K :=
  Iff.rfl

@[simp]
theorem DyadicMarkedCase.holds_evenPlusMinus : DyadicMarkedCase.evenPlusMinus.Holds K ↔
    IsDyadicEvenPlusMinusCase K :=
  Iff.rfl

@[simp]
theorem DyadicMarkedCase.holds_evenPrincipal : DyadicMarkedCase.evenPrincipal.Holds K ↔
    IsDyadicEvenPrincipalCase K :=
  Iff.rfl

variable {K}

/-- Characterization of the numerical and cyclotomic conditions in the even plus-minus case. -/
theorem isDyadicEvenPlusMinusCase_iff : IsDyadicEvenPlusMinusCase K ↔
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
    localRootOfUnityOrder 2 K
        (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 ∧
      Even (Module.finrank ℚ_[2] K) ∧
        (-1 : ℤ_[2]ˣ) ∈ (localCyclotomicCharacter 2 K).range :=
  Iff.rfl

/-- Characterization of the numerical and cyclotomic conditions in the even principal case. -/
theorem isDyadicEvenPrincipalCase_iff : IsDyadicEvenPrincipalCase K ↔
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
    localRootOfUnityOrder 2 K
        (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 ∧
      Even (Module.finrank ℚ_[2] K) ∧
        (-1 : ℤ_[2]ˣ) ∉ (localCyclotomicCharacter 2 K).range :=
  Iff.rfl

/-- The even plus-minus case has exactly two `2`-power roots of unity. -/
theorem IsDyadicEvenPlusMinusCase.localRootOfUnityOrder_eq_two
    (hcase : IsDyadicEvenPlusMinusCase K) :
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
    localRootOfUnityOrder 2 K
      (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 :=
  ((isDyadicEvenPlusMinusCase_iff (K := K)).mp hcase).1

/-- The degree in the even plus-minus case is even. -/
theorem IsDyadicEvenPlusMinusCase.even_finrank (hcase : IsDyadicEvenPlusMinusCase K) :
    Even (Module.finrank ℚ_[2] K) :=
  ((isDyadicEvenPlusMinusCase_iff (K := K)).mp hcase).2.1

/-- In the even plus-minus case, the cyclotomic image contains `-1`. -/
theorem IsDyadicEvenPlusMinusCase.neg_one_mem_range (hcase : IsDyadicEvenPlusMinusCase K) :
    (-1 : ℤ_[2]ˣ) ∈ (localCyclotomicCharacter 2 K).range :=
  ((isDyadicEvenPlusMinusCase_iff (K := K)).mp hcase).2.2

/-- The even principal case has exactly two `2`-power roots of unity. -/
theorem IsDyadicEvenPrincipalCase.localRootOfUnityOrder_eq_two
    (hcase : IsDyadicEvenPrincipalCase K) :
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
    localRootOfUnityOrder 2 K
      (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 :=
  ((isDyadicEvenPrincipalCase_iff (K := K)).mp hcase).1

/-- The degree in the even principal case is even. -/
theorem IsDyadicEvenPrincipalCase.even_finrank (hcase : IsDyadicEvenPrincipalCase K) :
    Even (Module.finrank ℚ_[2] K) :=
  ((isDyadicEvenPrincipalCase_iff (K := K)).mp hcase).2.1

/-- In the even principal case, the cyclotomic image does not contain `-1`. -/
theorem IsDyadicEvenPrincipalCase.neg_one_notMem_range
    (hcase : IsDyadicEvenPrincipalCase K) :
    (-1 : ℤ_[2]ˣ) ∉ (localCyclotomicCharacter 2 K).range :=
  ((isDyadicEvenPrincipalCase_iff (K := K)).mp hcase).2.2

/-- Every finite extension of `ℚ₂` belongs to exactly one arithmetic branch of the marked
classification. -/
theorem dyadic_markedCase_exists_unique :
    ∃! c : DyadicMarkedCase, c.Holds K := by
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  let q := localRootOfUnityOrder 2 K
    (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num))
  have hmu : ∃ ζ : K, IsPrimitiveRoot ζ 2 :=
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
  by_cases hq : q = 2
  · rcases Nat.even_or_odd (Module.finrank ℚ_[2] K) with heven | hodd
    · by_cases hneg : (-1 : ℤ_[2]ˣ) ∈ (localCyclotomicCharacter 2 K).range
      · refine ⟨.evenPlusMinus, ⟨hq, heven, hneg⟩, ?_⟩
        intro c hc
        cases c with
        | qNeTwo => exact (hc.2 hq).elim
        | odd => exact (Nat.not_even_iff_odd.mpr hc.odd_finrank heven).elim
        | evenPlusMinus => rfl
        | evenPrincipal => exact (hc.neg_one_notMem_range hneg).elim
      · refine ⟨.evenPrincipal, ⟨hq, heven, hneg⟩, ?_⟩
        intro c hc
        cases c with
        | qNeTwo => exact (hc.2 hq).elim
        | odd => exact (Nat.not_even_iff_odd.mpr hc.odd_finrank heven).elim
        | evenPlusMinus => exact (hneg hc.neg_one_mem_range).elim
        | evenPrincipal => rfl
    · refine ⟨.odd, IsDyadicOddCase.mk (K := K) hq hodd, ?_⟩
      intro c hc
      cases c with
      | qNeTwo => exact (hc.2 hq).elim
      | odd => rfl
      | evenPlusMinus => exact (Nat.not_odd_iff_even.mpr hc.even_finrank hodd).elim
      | evenPrincipal => exact (Nat.not_odd_iff_even.mpr hc.even_finrank hodd).elim
  · refine ⟨.qNeTwo, ⟨hmu, hq⟩, ?_⟩
    intro c hc
    cases c with
    | qNeTwo => rfl
    | odd => exact (hq hc.localRootOfUnityOrder_eq_two).elim
    | evenPlusMinus => exact (hq hc.localRootOfUnityOrder_eq_two).elim
    | evenPrincipal => exact (hq hc.localRootOfUnityOrder_eq_two).elim

end Dyadic

end TauCeti
