/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DeltaRing.Quotient

/-!
# Checks for quotients of `δ`-rings

The zero ideal is `δ`-stable and its quotient recovers the given `δ`-structure; the unit ideal is
`δ`-stable with quotient the zero ring. For the `δ`-structure on `ℤ`, the ideal `(p)` is stable
under the Frobenius, which is the identity, but not under `δ`, since `δ p = 1 - p ^ (p - 1)` is
not divisible by `p`. So no `δ`-structure on `ℤ ⧸ (p)` makes the quotient map a `δ`-map.

For `p = 2`, where `δ 2 = -1`, the `δ`-stabilization of `(2)` contains the unit `-1`, so it is
the unit ideal and the universal `δ`-quotient of `ℤ` in which `2` vanishes is the zero ring. In
particular `(2) ≤ (2)` but the `δ`-stabilization of `(2)` does not lie in `(2)`: the minimality
statement `deltaStabilization_le_iff` needs its target to be `δ`-stable.
-/

namespace TauCeti.Examples

open DeltaRing

variable {p : ℕ} {A : Type*} [CommRing A] [DeltaRing p A]

-- The zero ideal is `δ`-stable, and the isomorphism `A ⧸ ⊥ ≃+* A` carries the quotient
-- `δ`-structure to the given one.
example (hI : ∀ x ∈ (⊥ : Ideal A), delta p x ∈ (⊥ : Ideal A)) (x : A ⧸ (⊥ : Ideal A)) :
    RingEquiv.quotientBot A (@delta p _ _ (quotient ⊥ hI) x) =
      delta p (RingEquiv.quotientBot A x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [delta_quotient_mk, RingEquiv.quotientBot_mk]

example : ∀ x ∈ (⊥ : Ideal A), delta p x ∈ (⊥ : Ideal A) := by
  simp

-- The unit ideal is `δ`-stable, with quotient the zero ring and its unique `δ`-structure.
example (hI : ∀ x ∈ (⊤ : Ideal A), delta p x ∈ (⊤ : Ideal A)) :
    quotient ⊤ hI = default :=
  Subsingleton.elim _ _

-- The ideal `(p)` of `ℤ` is stable under the Frobenius but not under `δ`.
example [Fact p.Prime] : ∀ x ∈ Ideal.span {(p : ℤ)}, frobenius p ℤ x ∈ Ideal.span {(p : ℤ)} := by
  simp

-- `(p)` is not `δ`-stable, so no `δ`-structure on `ℤ ⧸ (p)` makes the quotient map a `δ`-map.
example [hp : Fact p.Prime] :
    ¬ ∃ d : DeltaRing p (ℤ ⧸ Ideal.span {(p : ℤ)}),
      @IsDeltaMap p ℤ _ _ _ _ d (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) := by
  have key : ¬ ∀ x ∈ Ideal.span {(p : ℤ)}, delta p x ∈ Ideal.span {(p : ℤ)} := by
    intro h
    have h' := h p (Ideal.mem_span_singleton_self _)
    rw [delta_natCast_self, Ideal.mem_span_singleton] at h'
    have h1 : (p : ℤ) ∣ 1 := by
      simpa using dvd_add h' (dvd_pow_self (p : ℤ) (Nat.sub_ne_zero_of_lt hp.out.one_lt))
    exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
  exact fun ⟨_, hd⟩ => key fun _ hx => delta_mem_of_isDeltaMap_quotient_mk hd hx

-- The `δ`-stabilization of `(2)` is the unit ideal of `ℤ`.
example : deltaStabilization 2 (Ideal.span {(2 : ℤ)}) = ⊤ := by
  have h := iterate_delta_mem_deltaStabilization (p := 2) (Ideal.mem_span_singleton_self (2 : ℤ)) 1
  rw [Function.iterate_one, delta_int_two] at h
  exact Ideal.eq_top_of_isUnit_mem _ h isUnit_one.neg

-- `deltaStabilization_le_iff` needs its target to be `δ`-stable: `(2) ≤ (2)`, but the
-- `δ`-stabilization of `(2)` does not lie in `(2)`, which is not `δ`-stable.
example : ¬ deltaStabilization 2 (Ideal.span {(2 : ℤ)}) ≤ Ideal.span {(2 : ℤ)} := by
  intro h
  have h1 := h (iterate_delta_mem_deltaStabilization (p := 2)
    (Ideal.mem_span_singleton_self (2 : ℤ)) 1)
  rw [Function.iterate_one, delta_int_two, Ideal.mem_span_singleton] at h1
  norm_num at h1

-- The universal `δ`-quotient of `ℤ` in which `2` vanishes is the zero ring.
example : Subsingleton (ℤ ⧸ deltaStabilization 2 (Ideal.span {(2 : ℤ)})) := by
  have h := iterate_delta_mem_deltaStabilization (p := 2) (Ideal.mem_span_singleton_self (2 : ℤ)) 1
  rw [Function.iterate_one, delta_int_two] at h
  exact Ideal.Quotient.subsingleton_iff.mpr (Ideal.eq_top_of_isUnit_mem _ h isUnit_one.neg)

end TauCeti.Examples
