/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Normed fields of small residue characteristic

A normed field is ultrametric as soon as the image of some algebra's scalars lies in its
closed unit ball, since the natural numbers then lie there too. This is the algebra-map form
of Mathlib's `IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one`.
A nonzero natural-number cast of norm less than one forces characteristic zero, even without
an ultrametricity assumption.
-/

public section

namespace IsUltrametricDist

/-- A normed field is ultrametric if an algebra's scalars lie in its closed unit ball. -/
theorem isUltrametricDist_of_forall_norm_algebraMap_le_one {R C : Type*}
    [CommSemiring R] [NormedField C] [Algebra R C]
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) : IsUltrametricDist C :=
  isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
    simpa using hR (n : R)

end IsUltrametricDist

namespace NormedField

/-- A nonzero natural-number cast of norm less than one forces characteristic zero. -/
theorem charZero_of_norm_natCast_lt_one {C : Type*} [NormedField C] {n : ℕ}
    (hnC : ‖(n : C)‖ < 1) (hn0 : (n : C) ≠ 0) : CharZero C := by
  rcases CharP.exists' C with h | ⟨p, hp, hchar⟩
  · exact h
  · let := hp
    let := hchar
    let f := ZMod.castHom (dvd_refl p) C
    have hn : (n : ZMod p) ≠ 0 := fun h ↦ hn0 (by simpa using congrArg f h)
    have hunit : IsUnit (n : ZMod p) := isUnit_iff_ne_zero.mpr hn
    have horder := f.toMonoidHom.isOfFinOrder hunit.isOfFinOrder
    exact (hnC.ne (by simpa using horder.norm_eq_one)).elim

end NormedField
