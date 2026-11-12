/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.Derivation.LocallyNilpotent

/-!
# Local nilpotence of algebra derivations

For a derivation of a possibly noncommutative algebra, the elements annihilated by some power
are closed under multiplication. Consequently, local nilpotence can be checked on algebra
generators. Both facts specialise the corresponding results for linear endomorphisms satisfying
the Leibniz rule in `TauCeti.RingTheory.Derivation.LocallyNilpotent`.

These facts allow nilpotent Lie derivations to act nilpotently on finite stable quotients of
universal enveloping algebras, even though the lifted derivations on the enveloping algebras
need not have a uniform nilpotence bound.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  Proposition E.5, for the use of nilpotent derivations on finite enveloping quotients.
-/

public section

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- If powers `n` and `m` of a derivation kill the two factors, power `n + m` kills their
product. Neither associativity nor commutativity of multiplication is required. -/
theorem pow_apply_mul_eq_zero (D : derivationLieAlgebra R A) {x y : A} {n m : ℕ}
    (hx : ((D : Module.End R A) ^ n) x = 0)
    (hy : ((D : Module.End R A) ^ m) y = 0) :
    ((D : Module.End R A) ^ (n + m)) (x * y) = 0 :=
  Module.End.pow_apply_mul_eq_zero_of_leibniz (leibniz D) hx hy

end TauCeti.derivationLieAlgebra

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Local nilpotence on a set of generators extends to the algebra they generate. -/
theorem exists_pow_apply_eq_zero_of_mem_adjoin (D : derivationLieAlgebra R A) {s : Set A}
    (hs : ∀ x ∈ s, ∃ n : ℕ, ((D : Module.End R A) ^ n) x = 0)
    {a : A} (ha : a ∈ Algebra.adjoin R s) :
    ∃ n : ℕ, ((D : Module.End R A) ^ n) a = 0 :=
  Module.End.exists_pow_apply_eq_zero_of_mem_adjoin_of_leibniz (leibniz D)
    (apply_one_eq_zero D) hs ha

end TauCeti.derivationLieAlgebra
