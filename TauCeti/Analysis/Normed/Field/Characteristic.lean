/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.Factorial

/-!
# Characteristic detected by a prime of small norm

In an ultrametric field, a prime of norm strictly between zero and one forces
characteristic zero. This separates mixed-characteristic arguments from the degenerate
case in which the prime vanishes in the field.
-/

public section

namespace NormedField

/-- A nonzero prime of norm less than one forces characteristic zero. -/
theorem charZero_of_prime_norm_lt_one {C : Type*} [NormedField C] [IsUltrametricDist C]
    {p : ℕ} (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (hp0 : (p : C) ≠ 0) : CharZero C := by
  apply charZero_of_inj_zero
  intro m hm
  by_contra hm0
  have h := TauCeti.norm_natCast_eq_pow_multiplicity hp hpC hm0
  rw [hm, norm_zero] at h
  exact (pow_ne_zero _ (norm_ne_zero_iff.mpr hp0)) h.symm

end NormedField
