/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Nilpotence in ring quotients

An element nilpotent modulo a two-sided ideal remains nilpotent modulo every power of that
ideal. This allows a representation kernel to be refined by taking powers without losing
nilpotence of its operators. The ring need not be commutative.

For commutative rings, the quotient by the nilradical is reduced.
-/

public section

namespace TauCeti

/-- The quotient of a commutative ring by its nilradical is reduced. -/
instance isReduced_quotient_nilradical (A : Type*) [CommRing A] :
    IsReduced (A ⧸ nilradical A) := by
  rw [← Ideal.isRadical_iff_quotient_reduced, nilradical]
  exact Ideal.radical_isRadical ⊥

variable {A : Type*} [Ring A]

/-- An element nilpotent modulo a two-sided ideal remains nilpotent modulo every power of it,
including the zeroth power. -/
theorem _root_.Ideal.isNilpotent_quotient_pow_of_isNilpotent_quotient
    (I : Ideal A) [I.IsTwoSided]
    {a : A} (ha : IsNilpotent (Ideal.Quotient.mk I a)) (n : ℕ) :
    IsNilpotent (Ideal.Quotient.mk (I ^ n) a) := by
  obtain ⟨e, he⟩ := ha
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at he
  refine ⟨e * n, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_mul]
  exact Ideal.pow_mem_pow he n

end TauCeti
