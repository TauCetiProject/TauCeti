/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DeltaRing.Basic

/-!
# Checks for the `δ`-structure on `ℤ` and on integer scalars

These examples exercise the unique `δ`-structure `δ n = (n - n ^ p) / p` on `ℤ`, whose Frobenius
is the identity, and its image in every `δ`-ring. The division is exact integer division, and
negative integers and `p = 2` are included. In every `δ`-ring `δ p = 1 - p ^ (p - 1)`, so a
nonzero ring in which `p = 0`, such as `ZMod p`, has no `δ`-structure.
-/

namespace TauCeti.Examples

open DeltaRing

-- `D_2 (-1) = -1`.
example : delta 2 (-1 : ℤ) = -1 := by
  rw [delta_int]
  norm_num

-- `D_3 2 = -2`.
example : delta 3 (2 : ℤ) = -2 := by
  rw [delta_int]
  norm_num

-- `D_p 0 = 0`.
example (p : ℕ) [Fact p.Prime] : delta p (0 : ℤ) = 0 :=
  delta_zero

-- The Frobenius of the `δ`-structure on `ℤ` is the identity.
example (p : ℕ) [Fact p.Prime] : frobenius p ℤ = RingHom.id ℤ :=
  frobenius_int

-- `δ p = 1 - p ^ (p - 1)` on `ℤ`; at `p = 2` this is `δ 2 = -1`.
example (p : ℕ) [Fact p.Prime] : delta p (p : ℤ) = 1 - (p : ℤ) ^ (p - 1) :=
  delta_natCast_self

-- In any `2`-`δ`-ring, `δ 2 = -1` and `δ 4 = -6`, without any hypothesis on `2`-torsion.
example {A : Type*} [CommRing A] [DeltaRing 2 A] : delta 2 (2 : A) = -1 := by
  have h := delta_natCast (A := A) (p := 2) 2
  norm_num at h
  exact h

example {A : Type*} [CommRing A] [DeltaRing 2 A] : delta 2 (4 : A) = -6 := by
  have h := delta_natCast (A := A) (p := 2) 4
  norm_num at h
  exact h

-- `ZMod p` has no `δ`-structure.
example (p : ℕ) [Fact p.Prime] : IsEmpty (DeltaRing p (ZMod p)) :=
  isEmpty_of_natCast_eq_zero (ZMod.natCast_self p)

end TauCeti.Examples
