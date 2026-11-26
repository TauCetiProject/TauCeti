/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.Quaternion
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

Unlike over non-archimedean local fields, `(rank, discr, hasseInvariant)` is **not** a complete
system of invariants over an ordered real closed field (or more generally any semireal field; see
`TauCeti.RegularFormClass.four_nsmul_one_ne_four_nsmul_mk_rankOne_neg_one` in
`TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse.Basic`): `⟨1, 1, 1, 1⟩` (`q = 0`) and
`⟨-1, -1, -1, -1⟩` (`q = 4`, `C(4, 2) = 6`) both have rank `4`, trivial discriminant, and trivial
Hasse invariant, while their signatures `4` and `-4` distinguish them.

## Main results

* `TauCeti.RegularFormClass.hasseInvariant_eq_pow_choose_sigNeg`: `s(x) = [(-1, -1)]^C(sigNeg x, 2)`
  over an ordered real closed field.
* `TauCeti.RegularFormClass.hasseInvariant_eq_one_iff_even_choose_sigNeg` and
  `TauCeti.RegularFormClass.hasseInvariant_eq_neg_one_neg_one_iff_odd_choose_sigNeg`: parity
  characterizations of the Hasse invariant.
* `QuadraticForm.hasseInvariant_formClass_eq_pow_choose_sigNeg`: the same formula for regular
  quadratic forms on finite-dimensional spaces.
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
  conv_lhs => rw [eq_sigPos_nsmul_add_sigNeg_nsmul x, nsmul_one]
  rw [hasseInvariant_add, hasseInvariant_natCast, one_mul, hasseInvariant_nsmul_mk_rankOne,
    discr_natCast, BrauerGroup.quaternionClassOnSquareClasses_zero_left, mul_one]

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

/-- The real normal form `p⟨1⟩ ⊥ q⟨-1⟩` has Hasse invariant `[ℍ[ℝ]]^C(q, 2)`. -/
@[simp]
theorem hasseInvariant_formClass_realSignatureForm (p q : ℕ) :
    RegularFormClass.hasseInvariant
        (formClass (realSignatureForm p q) (nondegenerate_realSignatureForm p q)) =
      BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) ^ q.choose 2 := by
  rw [QuadraticForm.hasseInvariant_formClass_eq_pow_choose_sigNeg, sigNeg_realSignatureForm,
    BrauerGroup.quaternionClass_neg_one_neg_one_real]

end TauCeti
