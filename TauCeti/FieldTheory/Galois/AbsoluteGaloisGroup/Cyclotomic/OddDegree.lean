/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
public import TauCeti.NumberTheory.LocalField.RootsOfUnity

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# The dyadic cyclotomic character in odd degree

Every `2`-power cyclotomic polynomial remains irreducible over a finite odd-degree extension of
`ℚ₂`: after translating by one, the polynomial over `ℤ₂` is Eisenstein, and coprime-degree linear
disjointness handles the base change. Consequently the local cyclotomic character has full image
in `ℤ₂ˣ`.

The predicate `IsDyadicOddCase` packages the two numerical invariants used by the odd dyadic case
of the local Galois-group classification. See Serre, *Local Fields*, Chapter IV, §2, for the
cyclotomic extensions of local fields.
-/

public section

open Polynomial

namespace TauCeti

/-- The `2^n`-th cyclotomic polynomial is irreducible over `ℚ₂`. -/
theorem irreducible_cyclotomic_two_pow_ratPadic (n : ℕ) :
    Irreducible (cyclotomic (2 ^ n) ℚ_[2]) := by
  cases n with
  | zero =>
      simpa only [pow_zero, cyclotomic_one, C_1] using
        (irreducible_X_sub_C (1 : ℚ_[2]))
  | succ k =>
      let fz : ℤ[X] := (cyclotomic (2 ^ (k + 1)) ℤ).comp (X + 1)
      let fi : ℤ_[2][X] := fz.map (Int.castRingHom ℤ_[2])
      have hfz : fz.IsEisensteinAt (Ideal.span {(2 : ℤ)}) :=
        cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt 2 k
      have hfi : fi.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[2]) := by
        apply Monic.isEisensteinAt_of_mem_of_notMem
        · exact (cyclotomic.monic _ ℤ).comp_X_add_C 1 |>.map (Int.castRingHom ℤ_[2])
        · exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        · intro i hi
          have hdeg : fi.natDegree = fz.natDegree := by
            simpa only [fi] using
              Polynomial.natDegree_map_eq_of_injective Int.cast_injective fz
          have hzmem : fz.coeff i ∈ Ideal.span {(2 : ℤ)} := hfz.mem (hdeg ▸ hi)
          rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
          simp only [fi, coeff_map]
          have hzdiv : (2 : ℤ) ∣ fz.coeff i := by rwa [← Ideal.mem_span_singleton]
          obtain ⟨a, ha⟩ := hzdiv
          refine ⟨Int.castRingHom ℤ_[2] a, ?_⟩
          calc
            (Int.castRingHom ℤ_[2]) (fz.coeff i) =
                (Int.castRingHom ℤ_[2]) ((2 : ℤ) * a) :=
              congrArg (Int.castRingHom ℤ_[2]) ha
            _ = (2 : ℤ_[2]) * (Int.castRingHom ℤ_[2]) a := by norm_num
        · have hconst : fi.coeff 0 = 2 := by
            simp [fi, fz, coeff_zero_eq_eval_zero, eval_comp,
              eval_one_cyclotomic_prime_pow]
          rw [hconst, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          intro h
          have := (PadicInt.pow_p_dvd_int_iff (p := 2) 2 2).mp h
          norm_num at this
      have hfimonic : fi.Monic :=
        (cyclotomic.monic _ ℤ).comp_X_add_C 1 |>.map (Int.castRingHom ℤ_[2])
      have hfi_irr : Irreducible fi := hfi.irreducible
        (IsLocalRing.maximalIdeal.isMaximal ℤ_[2]).isPrime
        hfimonic.isPrimitive
        (by
          rw [show fi.natDegree = fz.natDegree by
            simpa only [fi] using
              Polynomial.natDegree_map_eq_of_injective Int.cast_injective fz]
          rw [show fz.natDegree = (2 ^ (k + 1)).totient by
            simp [fz, natDegree_comp, natDegree_cyclotomic]]
          exact Nat.totient_pos.mpr (Nat.pow_pos (by norm_num)))
      have hq_irr : Irreducible (fi.map (algebraMap ℤ_[2] ℚ_[2])) :=
        hfimonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp hfi_irr
      have hcomp : fi.map (algebraMap ℤ_[2] ℚ_[2]) =
          (cyclotomic (2 ^ (k + 1)) ℚ_[2]).comp (X + 1) := by
        simp [fi, fz, map_comp]
      rw [hcomp] at hq_irr
      have hmapped := hq_irr.map (Polynomial.algEquivAevalXAddC (-(1 : ℚ_[2])))
      simpa [Polynomial.algEquivAevalXAddC, ← comp_eq_aeval, comp_assoc] using hmapped

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
  apply IsCyclotomicExtension.irreducible_cyclotomic_of_coprime_finrank
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

/-- In the odd dyadic case, the image of the local cyclotomic character is all of `ℤ₂ˣ`. -/
theorem range_localCyclotomicCharacter_of_degree_odd (hcase : IsDyadicOddCase K) :
    (localCyclotomicCharacter 2 K).range = ⊤ :=
  range_localCyclotomicCharacter_of_odd_finrank K hcase.2

end FiniteExtension

end TauCeti
