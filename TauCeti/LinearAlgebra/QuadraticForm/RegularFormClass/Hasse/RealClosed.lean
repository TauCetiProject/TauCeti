/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.Quaternion
public import TauCeti.Algebra.Quaternion.RealClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Signature
import Mathlib.FieldTheory.IsRealClosed.Real

/-!
# The Hasse invariant over ordered real closed fields and `ℝ`

Over an ordered real closed field `K`, every regular quadratic form decomposes into `p = sigPos`
copies of `⟨1⟩` and `q = sigNeg` copies of `⟨-1⟩`. Positive unit lines contribute trivial
quaternion symbols, while each unordered pair of negative unit lines contributes `[(-1, -1)]`,
giving the closed formula `s(Q) = [(-1, -1)]^C(q, 2)`. Since `[(-1, -1)]` has order `2`, the Hasse
invariant is trivial precisely when `C(q, 2) = q(q - 1)/2` is even.

Unlike over local fields, `(rank, discr, hasseInvariant)` is **not** a complete system of
invariants over an ordered real closed field: `⟨1, 1, 1, 1⟩` (`q = 0`) and `⟨-1, -1, -1, -1⟩`
(`q = 4`, `C(4, 2) = 6`) both have rank `4`, trivial discriminant, and trivial Hasse invariant,
while their signatures `4` and `-4` distinguish them.

## Main results

* `TauCeti.RegularFormClass.hasseInvariant_eq_pow_choose_sigNeg`: `s(x) = [(-1, -1)]^C(sigNeg x, 2)`
  over an ordered real closed field.
* `TauCeti.RegularFormClass.hasseInvariant_eq_one_iff_even_choose_sigNeg` and
  `TauCeti.RegularFormClass.hasseInvariant_eq_neg_one_neg_one_iff_odd_choose_sigNeg`: parity
  characterizations of the Hasse invariant.
* `QuadraticForm.hasseInvariant_formClass_eq_pow_choose_sigNeg`: the same formula for regular
  quadratic forms on finite-dimensional spaces.
* `TauCeti.RegularFormClass.four_nsmul_one_ne_four_nsmul_neg_one`: `⟨1, 1, 1, 1⟩` and
  `⟨-1, -1, -1, -1⟩` witness that rank, discriminant, and Hasse invariant do not classify regular
  forms over an ordered real closed field.
* `TauCeti.hasseInvariant_formClass_realSignatureForm`: the Hasse invariant of the real normal form
  `p⟨1⟩ ⊥ q⟨-1⟩` is `[ℍ[ℝ]]^C(q, 2)`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, §3, Definition 3.17
  and Proposition 3.18.
-/

public section

open QuadraticMap QuadraticForm TauCeti

namespace TauCeti

section IsRealClosed

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Invertible (2 : K)]
  [IsRealClosed K]

namespace RegularFormClass

/-- **Closed formula for the Hasse invariant over an ordered real closed field**: a regular-form
class with negative index of inertia `q = sigNeg x` has Hasse invariant `[(-1, -1)]^C(q, 2)`. -/
theorem hasseInvariant_eq_pow_choose_sigNeg (x : RegularFormClass K) :
    hasseInvariant x = BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ^ x.sigNeg.choose 2 := by
  conv_lhs => rw [eq_sigPos_nsmul_add_sigNeg_nsmul x]
  rw [hasseInvariant_add, hasseInvariant_nsmul_one, one_mul, hasseInvariant_nsmul_mk_rankOne,
    discr_nsmul, discr_one, smul_zero, BrauerGroup.quaternionClassOnSquareClasses_zero_left,
    mul_one]

/-- Over an ordered real closed field, the Hasse invariant of a regular-form class is trivial if
and only if `C(sigNeg x, 2)` is even. -/
theorem hasseInvariant_eq_one_iff_even_choose_sigNeg (x : RegularFormClass K) :
    hasseInvariant x = 1 ↔ Even (x.sigNeg.choose 2) := by
  rw [hasseInvariant_eq_pow_choose_sigNeg,
    BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_one_iff]

/-- Over an ordered real closed field, the Hasse invariant of a regular-form class equals
`[(-1, -1)]` if and only if `C(sigNeg x, 2)` is odd. -/
theorem hasseInvariant_eq_neg_one_neg_one_iff_odd_choose_sigNeg (x : RegularFormClass K) :
    hasseInvariant x = BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ↔ Odd (x.sigNeg.choose 2) := by
  rw [hasseInvariant_eq_pow_choose_sigNeg,
    BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_self_iff]

omit [IsRealClosed K] in
/-- **Rank, discriminant, and Hasse invariant do not classify regular forms over an ordered
field**: `⟨1, 1, 1, 1⟩` and `⟨-1, -1, -1, -1⟩` both have rank `4`, discriminant `0`, and Hasse
invariant `1` (`[(-1, -1)]` occurs `C(4, 2) = 6` times), yet they have signatures `4` and `-4` and
so are not isometric. -/
theorem four_nsmul_one_ne_four_nsmul_neg_one :
    let posFour : RegularFormClass K := 4 • 1
    let negFour : RegularFormClass K :=
      4 • Quotient.mk (regularFormSetoid K) ⟨1, fun _ => (-1 : Kˣ)⟩
    posFour.rank = 4 ∧ negFour.rank = 4 ∧
      discr posFour = 0 ∧ discr negFour = 0 ∧
      hasseInvariant posFour = 1 ∧ hasseInvariant negFour = 1 ∧
      posFour ≠ negFour := by
  dsimp only
  refine ⟨by rw [rank_nsmul, rank_one, mul_one], by rw [rank_nsmul, rank_mk, mul_one],
    by rw [discr_nsmul, discr_one, smul_zero], ?_,
    hasseInvariant_nsmul_one 4, ?_, ?_⟩
  · rw [discr_nsmul, discr_mk, Fin.prod_univ_one, ← squareClass_pow]
    exact (squareClass_eq_zero_iff _).mpr ⟨(-1 : Kˣ) ^ 2, by group⟩
  · rw [hasseInvariant_nsmul_mk_rankOne,
      (BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_one_iff (Nat.choose 4 2)).mpr (by decide)]
  · intro h
    have hs := congrArg signature h
    rw [signature_nsmul, signature_one, signature_nsmul, signature_mk_rankOne] at hs
    have hneg : ¬(0 : K) < ((-1 : Kˣ) : K) := by simp
    simp only [hneg, ↓reduceIte, nsmul_eq_mul, mul_one, mul_neg] at hs
    omega

end RegularFormClass

end IsRealClosed

end TauCeti

namespace QuadraticForm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Invertible (2 : K)]
  [IsRealClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The Hasse invariant of a regular quadratic form over an ordered real closed field is
`[(-1, -1)]^C(sigNeg Q, 2)`. -/
theorem hasseInvariant_formClass_eq_pow_choose_sigNeg (Q : _root_.QuadraticForm K M)
    (hQ : Q.Nondegenerate) :
    RegularFormClass.hasseInvariant (formClass Q hQ) =
      BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ^ (sigNeg Q).choose 2 := by
  rw [RegularFormClass.hasseInvariant_eq_pow_choose_sigNeg, sigNeg_formClass]

/-- The Hasse invariant of a regular quadratic form over an ordered real closed field is trivial
if and only if `C(sigNeg Q, 2)` is even. -/
theorem hasseInvariant_formClass_eq_one_iff_even_choose_sigNeg (Q : _root_.QuadraticForm K M)
    (hQ : Q.Nondegenerate) :
    RegularFormClass.hasseInvariant (formClass Q hQ) = 1 ↔ Even ((sigNeg Q).choose 2) := by
  rw [RegularFormClass.hasseInvariant_eq_one_iff_even_choose_sigNeg, sigNeg_formClass]

end QuadraticForm

namespace TauCeti

open scoped _root_.Quaternion

/-- Over `ℝ`, the quaternion symbol `[(-1, -1)]` is the Brauer class of Hamilton's quaternions
`ℍ[ℝ]`. -/
theorem BrauerGroup.quaternionClass_neg_one_neg_one_real :
    BrauerGroup.quaternionClass (-1 : ℝˣ) (-1) = BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) := by
  simp [BrauerGroup.quaternionClass_def]

/-- The real normal form `p⟨1⟩ ⊥ q⟨-1⟩` has Hasse invariant `[ℍ[ℝ]]^C(q, 2)`. -/
@[simp]
theorem hasseInvariant_formClass_realSignatureForm (p q : ℕ) :
    RegularFormClass.hasseInvariant
        (formClass (realSignatureForm p q) (nondegenerate_realSignatureForm p q)) =
      BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) ^ q.choose 2 := by
  rw [QuadraticForm.hasseInvariant_formClass_eq_pow_choose_sigNeg, sigNeg_realSignatureForm,
    BrauerGroup.quaternionClass_neg_one_neg_one_real]

/-- Over `ℝ`, the positive definite and negative definite four-dimensional normal forms have the
same dimension `4`, trivial discriminant, and trivial Hasse invariant, yet are not isometric. -/
example :
    Module.finrank ℝ (Fin 4 ⊕ Fin 0 → ℝ) = Module.finrank ℝ (Fin 0 ⊕ Fin 4 → ℝ) ∧
      RegularFormClass.discr (formClass (realSignatureForm 4 0)
        (nondegenerate_realSignatureForm 4 0)) =
        RegularFormClass.discr (formClass (realSignatureForm 0 4)
          (nondegenerate_realSignatureForm 0 4)) ∧
      RegularFormClass.hasseInvariant (formClass (realSignatureForm 4 0)
        (nondegenerate_realSignatureForm 4 0)) = 1 ∧
      RegularFormClass.hasseInvariant (formClass (realSignatureForm 0 4)
        (nondegenerate_realSignatureForm 0 4)) = 1 ∧
      ¬(realSignatureForm 4 0).Equivalent (realSignatureForm 0 4) := by
  refine ⟨by simp, ?_, ?_, ?_, by simp⟩
  · have h0 : RegularFormClass.discr (formClass (realSignatureForm 4 0)
        (nondegenerate_realSignatureForm 4 0)) = 0 := by
      rw [RegularFormClass.discr_eq_sigNeg_nsmul, sigNeg_formClass, sigNeg_realSignatureForm,
        zero_nsmul]
    have h4 : RegularFormClass.discr (formClass (realSignatureForm 0 4)
        (nondegenerate_realSignatureForm 0 4)) = 0 := by
      rw [RegularFormClass.discr_eq_sigNeg_nsmul, sigNeg_formClass, sigNeg_realSignatureForm,
        ← squareClass_pow]
      exact (squareClass_eq_zero_iff _).mpr ⟨(-1 : ℝˣ) ^ 2, by group⟩
    rw [h0, h4]
  · rw [QuadraticForm.hasseInvariant_formClass_eq_one_iff_even_choose_sigNeg,
      sigNeg_realSignatureForm]
    decide
  · rw [QuadraticForm.hasseInvariant_formClass_eq_one_iff_even_choose_sigNeg,
      sigNeg_realSignatureForm]
    decide

end TauCeti
