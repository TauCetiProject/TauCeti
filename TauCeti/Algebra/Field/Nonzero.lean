/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Field.Basic

/-!
# Nonzero natural casts in semirings

This file records that every natural divisor of a nonzero natural cast in a semiring also has
nonzero cast.
-/

public section

namespace TauCeti

namespace Nat

/-- A divisor of a nonzero natural cast in a semiring has nonzero cast. -/
theorem cast_ne_zero_of_dvd {K : Type*} [Semiring K] {N d : ℕ} (hN : (N : K) ≠ 0) (hd : d ∣ N) :
    (d : K) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hd
  contrapose! hN
  rw [Nat.cast_mul, hN, zero_mul]

end Nat

end TauCeti

end
