/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import TauCeti.Algebra.Ring.Pi

/-!
# Star-invariant coordinate slices along a product ring equivalence

When `star` fixes every coordinate central idempotent `e.symm (Pi.single i 1)` of
`e : E ≃+* ∀ i, A i`, `star` restricts to each coordinate slice and acts coordinatewise.
-/

public section

namespace RingEquiv

variable {E : Type*} [Semiring E] [StarRing E] {ι : Type*} [DecidableEq ι] {A : ι → Type*}
  [∀ i, Semiring (A i)] (e : E ≃+* ∀ i, A i)

/-- When `star` fixes every coordinate central idempotent `e.symm (Pi.single i 1)`, `star` acts
coordinatewise via `a ↦ e (star (e.symm (Pi.single i a))) i`. -/
theorem apply_star_eq_coord (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (x : E) (i : ι) :
    e (star x) i = e (star (e.symm (Pi.single i (e x i)))) i := by
  have hst : star x * e.symm (Pi.single i 1) = star (e.symm (Pi.single i (e x i))) := by
    rw [← e.symm_single_one_mul i x, star_mul, hδ i]
  simpa using congrFun (congrArg e hst) i

/-- When `star` fixes every coordinate central idempotent, `star` sends each coordinate slice
`e.symm (Pi.single i a)` back into the same coordinate slice. -/
theorem apply_star_single (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (i : ι) (a : A i) :
    e (star (e.symm (Pi.single i a))) =
      Pi.single i (e (star (e.symm (Pi.single i a))) i) := by
  have hmul : e.symm (Pi.single i 1) * e.symm (Pi.single i a) = e.symm (Pi.single i a) := by
    simpa using e.symm_single_one_mul i (e.symm (Pi.single i a))
  have hst : star (e.symm (Pi.single i a)) =
      star (e.symm (Pi.single i a)) * e.symm (Pi.single i 1) := by
    conv_lhs => rw [← hmul, star_mul, hδ i]
  funext j
  by_cases hji : j = i
  · subst hji; simp
  · (conv_lhs => rw [hst]); simp [Pi.single_eq_of_ne hji]

end RingEquiv
