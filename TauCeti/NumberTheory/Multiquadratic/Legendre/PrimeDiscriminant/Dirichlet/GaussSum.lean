/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Dirichlet.Character

/-!
# Gauss sums of prime-discriminant characters

The Gauss sum of the Dirichlet character `primeDiscriminantChar P hP` of a prime discriminant
`P`, formed with a primitive `|P|`-th root of unity in a field of characteristic zero, squares to
`P`. It is therefore an explicit square root of `P` built out of roots of unity, which is how the
quadratic fields `ℚ(√P)` are located inside cyclotomic fields.

The computation is classical; see K. Ireland and M. Rosen, *A Classical Introduction to Modern
Number Theory*, Chapter 6, and D. A. Cox, *Primes of the Form x² + ny²*, §3.B.

## Main results

* `TauCeti.Multiquadratic.primeDiscriminantChar_neg_one`: the character of `P` takes the value
  `sign P` at `-1`.
* `TauCeti.Multiquadratic.gaussSumOfPrimitiveRoot_primeDiscriminantChar_sq`: the Gauss sum of the
  character of a prime discriminant `P` squares to `P`.
-/

public section

open DirichletCharacter

namespace TauCeti.Multiquadratic

/-- The character of a prime discriminant `P` takes the value `sign P` at `-1`. -/
@[simp]
theorem primeDiscriminantChar_neg_one {P : ℤ} (hP : IsPrimeDiscriminant P) :
    primeDiscriminantChar P hP (-1) = P.sign := by
  simpa [primeDiscriminantCharFun_neg_one hP] using primeDiscriminantChar_apply_int P hP (-1)

/-- **The Gauss sum of a prime discriminant squares to it.** In any field of characteristic zero,
the Gauss sum of the character of the prime discriminant `P`, formed with a primitive `|P|`-th
root of unity, is a square root of `P`. -/
@[simp]
theorem gaussSumOfPrimitiveRoot_primeDiscriminantChar_sq {L : Type*} [Field L] [CharZero L]
    {P : ℤ} (hP : IsPrimeDiscriminant P) [NeZero P.natAbs] {ζ : L}
    (hζ : IsPrimitiveRoot ζ P.natAbs) :
    gaussSumOfPrimitiveRoot (primeDiscriminantChar P hP) hζ ^ 2 = (P : L) := by
  rw [gaussSumOfPrimitiveRoot_sq _ (isPrimitive_primeDiscriminantChar P hP)
    (isQuadratic_primeDiscriminantChar P hP)]
  simpa using congr_arg (Int.cast : ℤ → L) (Int.sign_mul_natAbs P)

end TauCeti.Multiquadratic
