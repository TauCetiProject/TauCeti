/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Frobenius and split nilpotent thickenings

Suppose `f : R →+* S` has a ring section `s` and nilpotent kernel. In positive characteristic
`p > 1`, every sufficiently high Frobenius iterate on `R` is `s ∘ F_S ∘ f`.
An explicit version takes a bound on the nilpotence exponent, and the existence version gives
one bound for all larger iterates. This factorization makes Frobenius base changes of families
over nilpotent thickenings descend to the quotient base when a section is given.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, proof of 5.3.6.
-/

public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [ExpChar R p] [ExpChar S p]

/-- Frobenius factors through a split reduction once its exponent exceeds the nilpotence
bound of the kernel. The formula includes Frobenius on the quotient. -/
theorem iterateFrobenius_eq_of_ker_pow_eq_zero (f : R →+* S) (s : S →+* R)
    (hs : f.comp s = RingHom.id S) {N n : ℕ} (hN : RingHom.ker f ^ N = 0)
    (hn : N ≤ p ^ n) :
    iterateFrobenius R p n = s.comp ((iterateFrobenius S p n).comp f) := by
  ext x
  have hx : x - s (f x) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, hs, RingHom.id_apply, sub_self]
  have hpow := Ideal.pow_eq_zero_of_mem hN hn hx
  rw [sub_pow_expChar_pow, sub_eq_zero] at hpow
  simpa only [RingHom.comp_apply, iterateFrobenius_def, map_pow] using hpow

/-- For a split reduction with nilpotent kernel in positive characteristic, high Frobenius iterates
factor through the quotient, with one bound working for all elements. -/
theorem exists_iterateFrobenius_eq_of_isNilpotent_ker (f : R →+* S) (s : S →+* R)
    (hs : f.comp s = RingHom.id S) (hp : 1 < p) (h : IsNilpotent (RingHom.ker f)) :
    ∃ N : ℕ, ∀ n ≥ N,
      iterateFrobenius R p n = s.comp ((iterateFrobenius S p n).comp f) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn ↦ f.iterateFrobenius_eq_of_ker_pow_eq_zero p s hs hN ?_⟩
  exact hn.trans (Nat.lt_pow_self hp).le

end RingHom
