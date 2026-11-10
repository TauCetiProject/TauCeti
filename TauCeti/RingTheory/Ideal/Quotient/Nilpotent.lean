/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Nilpotence in ring quotients

For a positive power of a two-sided ideal, nilpotence in the quotient is equivalent to
nilpotence modulo the original ideal. The zeroth-power quotient is the zero ring. This allows a
representation kernel to be refined by taking powers without losing nilpotence of its operators.
The ring need not be commutative.

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

/-- Nilpotence modulo a power of a two-sided ideal is equivalent to nilpotence modulo the ideal,
except that the zeroth-power quotient is the zero ring. -/
@[simp]
theorem _root_.Ideal.isNilpotent_quotient_pow_iff
    (I : Ideal A) [I.IsTwoSided] (n : ℕ) {a : A} :
    IsNilpotent (Ideal.Quotient.mk (I ^ n) a) ↔
      n = 0 ∨ IsNilpotent (Ideal.Quotient.mk I a) := by
  constructor
  · intro ha
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      simpa only [Ideal.Quotient.factor_mk] using
        ha.map (Ideal.Quotient.factor (Ideal.pow_le_self hn))
  · rintro (rfl | ha)
    · refine ⟨1, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      simp [Submodule.pow_zero]
    · obtain ⟨e, he⟩ := ha
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at he
      refine ⟨e * n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_mul]
      exact Ideal.pow_mem_pow he n

end TauCeti
