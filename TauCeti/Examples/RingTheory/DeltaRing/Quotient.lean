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
  rw [delta_quotient_mk]
  rfl

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

end TauCeti.Examples
