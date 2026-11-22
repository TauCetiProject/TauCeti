/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeltaRing.MonoidAlgebra

/-!
# Checks for the `δ`-structure on a monoid algebra

These examples exercise the `δ`-structure on `ℤ[M]`. For `M = Multiplicative ℕ` the monoid
algebra is the polynomial ring `ℤ[x]` with `x = of ℤ M (ofAdd 1)`; its `δ`-structure has
`δ x = 0` and `φ x = x ^ p`. The coefficients still carry the `δ`-structure of `ℤ`: at `p = 2`,
`δ (2 x) = -x ^ 2`, since `φ (2 x) = 2 x ^ 2` and `(2 x) ^ 2 = 4 x ^ 2`.
-/

public section

open MonoidAlgebra

namespace TauCeti.Examples

open DeltaRing

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `δ`-structure on `ℤ[M]`. -/
noncomputable local instance (M : Type*) [CommMonoid M] : DeltaRing p ℤ[M] :=
  monoidAlgebra M (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero))

-- The variable `x` of `ℤ[x]` has `δ x = 0`.
example : delta p (of ℤ (Multiplicative ℕ) (.ofAdd 1)) = 0 :=
  delta_monoidAlgebra_of (delta_single_monoidAlgebra _) _

-- The Frobenius of `ℤ[x]` sends `x` to `x ^ p`.
example : frobenius p ℤ[Multiplicative ℕ] (of ℤ _ (.ofAdd 1)) = of ℤ _ (.ofAdd 1) ^ p := by
  rw [frobenius_monoidAlgebra_of (delta_single_monoidAlgebra _), map_pow]

-- At `p = 2`, `δ (2 x) = -x ^ 2` in `ℤ[x]`.
example :
    delta 2 (single (.ofAdd 1) 2 : ℤ[Multiplicative ℕ]) = -single (.ofAdd 1) 1 ^ 2 := by
  rw [delta_single_monoidAlgebra, delta_int_two, single_pow, single_neg, one_pow]

-- The augmentation `ℤ[M] → ℤ`, sending every element of `M` to `1`, is a `δ`-map.
example (M : Type*) [CommMonoid M] :
    IsDeltaMap p (liftNCRingHom (RingHom.id ℤ) (1 : M →* ℤ) fun _ _ => .all _ _) :=
  isDeltaMap_liftNCRingHom (delta_single_monoidAlgebra _) (isDeltaMap_id p ℤ) fun _ => delta_one

end TauCeti.Examples
