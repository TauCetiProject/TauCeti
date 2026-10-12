/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFive.Modular
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver

/-!
# Success of the cyclotomic Dixon solver for A₅

The character values of A₅ lie in the fifth cyclotomic ring, whereas the assembled Dixon
solver uses the group exponent, `30`. Substitution `ζ₅ ↦ ζ₃₀⁶` transports the certified
central and ordinary tables to the solver's coefficient ring. The transported central
coefficients fit in the balanced residue window at `61`, a good Dixon prime. Consequently
the solver succeeds at that prime, and its prime search succeeds with budget `2`.

This proves success of the existing executable search; it does not evaluate its enumeration
of all modular rows and alignments. The returned table is certified by the general solver
soundness theorem.

The construction uses the exact A₅ certificate in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFive.Basic`
and the completeness criterion `TauCeti.ClassData.isSome_dixonCyclotomicCharacterTable_of_spec`.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446–450.
* J.-P. Serre, *Linear Representations of Finite Groups*, §5.2 (the A₅ character table).
-/

public section

namespace TauCeti

open Matrix

/-- The central-character table of A₅ in the exponent-`30` coefficient ring used by the solver.
Substitution sends the fifth root to the sixth power of the thirtieth root. -/
def alternatingGroupFiveExponentCentralCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 30) :=
  fun i j ↦ Cyclotomic.evalCoeffs (Int.castRingHom (Cyclotomic 30)) (Cyclotomic.zeta 30 ^ 6)
    (alternatingGroupFiveCandidateCentralCharacterTable i j)

/-- The ordinary-character table of A₅ in the exponent-`30` coefficient ring used by the solver. -/
def alternatingGroupFiveExponentCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 30) :=
  fun i j ↦ Cyclotomic.evalCoeffs (Int.castRingHom (Cyclotomic 30)) (Cyclotomic.zeta 30 ^ 6)
    (alternatingGroupFiveCandidateCharacterTable i j)

/-- Entrywise substitution describing the exponent-`30` central table. -/
@[simp] theorem alternatingGroupFiveExponentCentralCharacterTable_apply
    (i j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveExponentCentralCharacterTable i j =
      Cyclotomic.evalCoeffs (Int.castRingHom (Cyclotomic 30)) (Cyclotomic.zeta 30 ^ 6)
        (alternatingGroupFiveCandidateCentralCharacterTable i j) := (rfl)

/-- Entrywise substitution describing the exponent-`30` ordinary table. -/
@[simp] theorem alternatingGroupFiveExponentCharacterTable_apply
    (i j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveExponentCharacterTable i j =
      Cyclotomic.evalCoeffs (Int.castRingHom (Cyclotomic 30)) (Cyclotomic.zeta 30 ^ 6)
        (alternatingGroupFiveCandidateCharacterTable i j) := (rfl)

/-- The transported A₅ tables satisfy the exact certificate in the solver's coefficient ring. -/
theorem isCyclotomicCharacterTableSpec_alternatingGroupFive_exponent :
    alternatingGroupFiveClassData.IsCyclotomicCharacterTableSpec 30
      alternatingGroupFiveExponentCentralCharacterTable alternatingGroupFiveExponentCharacterTable
      alternatingGroupFiveCandidateCharacterDegrees := by
  have hroot : (Polynomial.cyclotomic 5 ℤ).eval₂ (Int.castRingHom (Cyclotomic 30))
      (Cyclotomic.zeta 30 ^ 6) = 0 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    norm_num [Polynomial.cyclotomic_prime, Finset.sum_range_succ]
    decide +kernel
  let f := Cyclotomic.evalRingHom (Int.castRingHom (Cyclotomic 30))
    (Cyclotomic.zeta 30 ^ 6) hroot
  have hf (x : Cyclotomic 5) : f (star x) = star (f x) := by
    have hhom : f.comp (starRingEnd (Cyclotomic 5)) =
        (starRingEnd (Cyclotomic 30)).comp f := by
      apply Cyclotomic.ringHom_ext
      simp only [RingHom.comp_apply, starRingEnd_apply, Cyclotomic.star_zeta,
        map_pow, f, Cyclotomic.evalRingHom_zeta]
      decide +kernel
    exact DFunLike.congr_fun hhom x
  have h := isCyclotomicCharacterTableSpec_alternatingGroupFive.map f hf
  simp only [f, Cyclotomic.evalRingHom_apply, ← Cyclotomic.evalCoeffs_eq_eval₂] at h
  simpa only [← alternatingGroupFiveExponentCentralCharacterTable_apply,
    ← alternatingGroupFiveExponentCharacterTable_apply] using h

/-- Every central coefficient in the exponent-`30` table lies in the balanced residue window
at prime `61`. -/
theorem alternatingGroupFiveExponentCentralCharacterTable_two_mul_natAbs_coeff_lt
    (i j : AlternatingGroupFiveClassIndex) (k : Fin (30 : ℕ).totient) :
    2 * ((alternatingGroupFiveExponentCentralCharacterTable i j).coeff k).natAbs < 61 := by
  have hcheck : ((alternatingGroupFiveExponentCentralCharacterTable i j).coeffs.all
      fun z ↦ decide (2 * z.natAbs < 61)) = true := by
    rw [alternatingGroupFiveExponentCentralCharacterTable_apply,
      alternatingGroupFiveCandidateCentralCharacterTable_apply]
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hmem : (alternatingGroupFiveExponentCentralCharacterTable i j).coeff k ∈
      (alternatingGroupFiveExponentCentralCharacterTable i j).coeffs := by
    rw [Cyclotomic.coeff, List.getD_eq_getElem _ _
      (by simpa only [List.length_reverse, Cyclotomic.length_coeffs] using k.isLt)]
    exact List.mem_reverse.mp (List.getElem_mem _)
  have h := List.all_eq_true.mp hcheck
  simpa only [decide_eq_true_eq] using h _ hmem

/-- The cyclotomic Dixon solver finds a certified A₅ table at any Dixon prime data with prime
`61`, independently of the chosen primitive thirtieth root. -/
theorem isSome_dixonCyclotomicCharacterTable_alternatingGroupFive
    (q : DixonPrimeData (alternatingGroup (Fin 5))) (hq : q.p = 61) :
    (alternatingGroupFiveClassData.dixonCyclotomicCharacterTable? 30 q).isSome = true := by
  apply alternatingGroupFiveClassData.isSome_dixonCyclotomicCharacterTable_of_spec 30
    exponent_alternatingGroup_five.symm q
    alternatingGroupFiveExponentCentralCharacterTable alternatingGroupFiveExponentCharacterTable
    alternatingGroupFiveCandidateCharacterDegrees
    isCyclotomicCharacterTableSpec_alternatingGroupFive_exponent
  simpa only [hq] using
    alternatingGroupFiveExponentCentralCharacterTable_two_mul_natAbs_coeff_lt

/-- With budget `2`, the assembled prime search reaches `61` and returns a certified A₅ table. -/
theorem isSome_characterTableDixon_alternatingGroupFive :
    (alternatingGroupFiveClassData.characterTableDixon? 30
      exponent_alternatingGroup_five.symm 2).isSome = true := by
  obtain ⟨q, hmem, hq⟩ := DixonPrimeData.exists_mem_candidates
    (e := 30) (he := exponent_alternatingGroup_five.symm)
    (n := Fintype.card (alternatingGroup (Fin 5))) (hn := Nat.card_eq_fintype_card.symm)
    (fuel := 2) isGoodDixonPrime_alternatingGroup_five_sixtyOne (by norm_num)
  exact (alternatingGroupFiveClassData.isSome_characterTableDixon?_iff 30
    exponent_alternatingGroup_five.symm 2).mpr
      ⟨q, hmem, isSome_dixonCyclotomicCharacterTable_alternatingGroupFive q hq⟩

end TauCeti
