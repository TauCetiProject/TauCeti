/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Local nilpotence of algebra derivations

For a derivation of a possibly noncommutative algebra, the elements annihilated by some power
are closed under multiplication. Consequently, local nilpotence can be checked on algebra
generators.

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
    ((D : Module.End R A) ^ (n + m)) (x * y) = 0 := by
  induction n generalizing x y m with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ n ih =>
    induction m generalizing y with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hy
      simp [hy]
    | succ m ihm =>
      have hx' : ((D : Module.End R A) ^ n) ((D : Module.End R A) x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      have hy' : ((D : Module.End R A) ^ m) ((D : Module.End R A) y) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hy
      rw [Nat.succ_add, pow_succ, Module.End.mul_apply, leibniz, map_add]
      rw [ih hx' hy, Nat.add_succ, ← Nat.succ_add, ihm hy', add_zero]

end TauCeti.derivationLieAlgebra

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Local nilpotence on a set of generators extends to the algebra they generate. -/
theorem exists_pow_apply_eq_zero_of_mem_adjoin (D : derivationLieAlgebra R A) {s : Set A}
    (hs : ∀ x ∈ s, ∃ n : ℕ, ((D : Module.End R A) ^ n) x = 0)
    {a : A} (ha : a ∈ Algebra.adjoin R s) :
    ∃ n : ℕ, ((D : Module.End R A) ^ n) a = 0 := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hs a ha
  | algebraMap r =>
    refine ⟨1, ?_⟩
    simp only [pow_one, Algebra.algebraMap_eq_smul_one, map_smul,
      apply_one_eq_zero, smul_zero]
  | add a b _ _ ha hb =>
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    exact ⟨max n m, by rw [map_add,
      Module.End.pow_map_zero_of_le (le_max_left _ _) hn,
      Module.End.pow_map_zero_of_le (le_max_right _ _) hm, add_zero]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    exact ⟨n + m, pow_apply_mul_eq_zero D hn hm⟩

end TauCeti.derivationLieAlgebra
