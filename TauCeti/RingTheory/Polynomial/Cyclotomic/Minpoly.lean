/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic factors of a minimal polynomial over `ℚ`

`Φₐ` is irreducible over `ℚ`, so it divides the minimal polynomial of an element `x` of a
`ℚ`-algebra as soon as the minimal polynomial divides `Φₐ q` for some `q` that does not annihilate
`x`.

## Main results

* `Polynomial.cyclotomic_dvd_minpoly`: if `minpoly ℚ x ∣ Φₐ q` and `q` does not annihilate `x`,
  then `Φₐ ∣ minpoly ℚ x`.
-/

public section

namespace Polynomial

/-- If the minimal polynomial of `x` divides `Φₐ q` and `q` does not annihilate `x`, then `Φₐ`
divides the minimal polynomial, since `Φₐ` is irreducible over `ℚ`. -/
theorem cyclotomic_dvd_minpoly {A : Type*} [Ring A] [Algebra ℚ A] {x : A} {a : ℕ} (ha : 0 < a)
    {q : ℚ[X]} (hq : minpoly ℚ x ∣ cyclotomic a ℚ * q) (hn : aeval x q ≠ 0) :
    cyclotomic a ℚ ∣ minpoly ℚ x := by
  by_contra h
  have hcop := ((cyclotomic.irreducible_rat ha).coprime_iff_not_dvd.2 h).symm
  exact hn (minpoly.dvd_iff.1 (hcop.dvd_of_dvd_mul_left hq))

end Polynomial

end
