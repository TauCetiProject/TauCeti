/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
public import TauCeti.NumberTheory.LocalField.RootsOfUnity

import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# The dyadic cyclotomic character in odd degree

This file shows that the local cyclotomic character of a finite odd-degree extension of `ℚ₂` has
full image in `ℤ₂ˣ`. The base case `Φ₁` is linear, while for positive exponents the translated
`2`-power cyclotomic polynomial over `ℤ₂` is Eisenstein.

The predicate `IsDyadicOddCase` packages the two numerical invariants used by the odd dyadic case
of the local Galois-group classification. See Serre, *Local Fields*, Chapter IV, §4, for the
cyclotomic extensions of local fields.
-/

public section

open Polynomial

namespace TauCeti

section FiniteExtension

variable (K : Type*) [Field K] [Algebra ℚ_[2] K] [FiniteDimensional ℚ_[2] K]

/-- The local dyadic cyclotomic character of an odd-degree extension of `ℚ₂` has full image. -/
theorem range_localCyclotomicCharacter_of_odd_finrank
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    (localCyclotomicCharacter 2 K).range = ⊤ := by
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  rw [MonoidHom.range_eq_top]
  apply localCyclotomicCharacter_surjective_of_irreducible
  intro n
  apply irreducible_cyclotomic_of_coprime_finrank
    (irreducible_cyclotomic_two_pow_ratPadic n)
  cases n with
  | zero => simp
  | succ n =>
      rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos n)]
      simpa using (Nat.coprime_two_left.mpr hodd).pow_left n

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The numerical conditions defining the odd dyadic case: exactly two `2`-power roots of unity,
and odd degree over `ℚ₂`. -/
def IsDyadicOddCase : Prop :=
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  localRootOfUnityOrder 2 K
    (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 ∧
      Odd (Module.finrank ℚ_[2] K)

omit [FiniteDimensional ℚ_[2] K] in
/-- Characterization of the numerical conditions in `IsDyadicOddCase`. -/
theorem isDyadicOddCase_iff : IsDyadicOddCase K ↔
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
    localRootOfUnityOrder 2 K
      (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 ∧
        Odd (Module.finrank ℚ_[2] K) :=
  Iff.rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- Construct the odd dyadic case from its two numerical conditions. -/
theorem IsDyadicOddCase.mk
    (hroots : let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
      localRootOfUnityOrder 2 K
        (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2)
    (hodd : Odd (Module.finrank ℚ_[2] K)) : IsDyadicOddCase K :=
  (isDyadicOddCase_iff (K := K)).mpr ⟨hroots, hodd⟩

omit [FiniteDimensional ℚ_[2] K] in
/-- The odd dyadic case has exactly two `2`-power roots of unity. -/
theorem IsDyadicOddCase.localRootOfUnityOrder_eq_two (hcase : IsDyadicOddCase K) :
    let _ : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
    localRootOfUnityOrder 2 K
      (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) = 2 :=
  ((isDyadicOddCase_iff (K := K)).mp hcase).1

omit [FiniteDimensional ℚ_[2] K] in
/-- The degree over `ℚ₂` in the odd dyadic case is odd. -/
theorem IsDyadicOddCase.odd_finrank (hcase : IsDyadicOddCase K) :
    Odd (Module.finrank ℚ_[2] K) :=
  ((isDyadicOddCase_iff (K := K)).mp hcase).2

/-- In the odd dyadic case, the image of the local cyclotomic character is all of `ℤ₂ˣ`. -/
theorem range_localCyclotomicCharacter_of_degree_odd (hcase : IsDyadicOddCase K) :
    (localCyclotomicCharacter 2 K).range = ⊤ :=
  range_localCyclotomicCharacter_of_odd_finrank K hcase.odd_finrank

end FiniteExtension

end TauCeti
