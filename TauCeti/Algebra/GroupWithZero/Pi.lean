/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.GroupWithZero.Pi

/-!
# Products of `MulZeroClass` and `MulZeroOneClass` families

This file supplements `Mathlib.Algebra.GroupWithZero.Pi` with orthogonality and idempotence lemmas
for single-coordinate elements `Pi.single i a` in a dependent product `∀ k, α k`:

* `Pi.single_mul_single_of_ne`: the product of elements supported at distinct coordinates vanishes.
* `IsIdempotentElem.piSingle`, `IsIdempotentElem.piSingle_iff`, `IsIdempotentElem.piSingle_one`:
  `Pi.single i a` is idempotent if and only if `a` is idempotent, and in particular `Pi.single i 1`
  is idempotent in any product of `MulZeroOneClass`es.
-/

public section

namespace Pi

variable {ι : Type*} {α : ι → Type*} [DecidableEq ι]

/-- In a product of `MulZeroClass`es, multiplying two elements supported at distinct coordinates
`i ≠ j` yields zero. -/
@[simp]
theorem single_mul_single_of_ne [∀ k, MulZeroClass (α k)] {i j : ι} (h : i ≠ j)
    (a : α i) (b : α j) :
    (Pi.single i a : ∀ k, α k) * Pi.single j b = 0 := by
  rw [← Pi.single_mul_left, Pi.single_eq_of_ne h, mul_zero, Pi.single_zero]

end Pi

namespace IsIdempotentElem

variable {ι : Type*} {α : ι → Type*} [DecidableEq ι]

/-- In a product of `MulZeroClass`es, `Pi.single i a` is idempotent whenever `a` is idempotent. -/
theorem piSingle [∀ k, MulZeroClass (α k)] (i : ι) {a : α i} (ha : IsIdempotentElem a) :
    IsIdempotentElem (Pi.single i a : ∀ k, α k) :=
  ha.map (MulHom.single i)

/-- In a product of `MulZeroClass`es, `Pi.single i a` is idempotent if and only if `a` is
idempotent. -/
theorem piSingle_iff [∀ k, MulZeroClass (α k)] (i : ι) {a : α i} :
    IsIdempotentElem (Pi.single i a : ∀ k, α k) ↔ IsIdempotentElem a :=
  ⟨fun h ↦ by simpa [IsIdempotentElem] using congrFun h.eq i, fun h ↦ h.piSingle i⟩

/-- In a product of `MulZeroOneClass`es, the single-coordinate unit `Pi.single i 1` is
idempotent. -/
theorem piSingle_one [∀ k, MulZeroOneClass (α k)] (i : ι) :
    IsIdempotentElem (Pi.single i (1 : α i) : ∀ k, α k) :=
  IsIdempotentElem.one.piSingle i

end IsIdempotentElem
