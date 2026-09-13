/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Nonzero representatives of residue classes

`Ideal.Quotient.mk_surjective` produces *some* representative of a class in `R ⧸ I`, with no
control over it.  Modulo a nonzero two-sided ideal the representative can be chosen nonzero: a
representative that happens to vanish is corrected by a nonzero element of the ideal, which does
not change its class.  This is what a residue class needs before its representative can be
inverted in an appropriate fraction field.

## Main results

* `Ideal.Quotient.exists_ne_zero_mk_eq`: every residue class modulo a nonzero ideal is the class of
  a nonzero element.
-/

public section

namespace Ideal.Quotient

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]

/-- **A nonzero ideal has a nonzero representative for every residue class.**  A representative
that happens to vanish can be corrected by a nonzero element of the ideal. -/
theorem exists_ne_zero_mk_eq (hI : I ≠ ⊥) (y : R ⧸ I) : ∃ a ≠ (0 : R), mk I a = y := by
  obtain ⟨a, rfl⟩ := mk_surjective y
  obtain ⟨m, hm, hm0⟩ := (Submodule.ne_bot_iff I).mp hI
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨m, hm0, by rw [eq_zero_iff_mem.mpr hm, map_zero]⟩
  · exact ⟨a, ha, rfl⟩

end Ideal.Quotient

end
