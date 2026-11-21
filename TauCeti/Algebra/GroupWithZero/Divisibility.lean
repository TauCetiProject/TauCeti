/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# `NeZero` passes to divisors

Mathlib's `ne_zero_of_dvd_ne_zero` says that, in a monoid with zero, a divisor of a nonzero
element is nonzero, as the proposition `p ≠ 0`. Instance resolution needs the same fact as the
class `NeZero p`, and a caller holding `[NeZero q]` together with `p ∣ q` has to repackage the
conclusion by hand; Mathlib does exactly that inline in `Mathlib/GroupTheory/Index.lean` and
`Mathlib/GroupTheory/Schreier.lean`. This file names the repackaging once, in any semigroup with
zero, so that a divisibility hypothesis can discharge a `NeZero` side condition in one term.

## Main results

* `NeZero.of_dvd`: a divisor of an element carrying `NeZero` carries `NeZero`.
* `NeZero.of_not_dvd_right`: if `¬ p ∣ q`, then `q` carries `NeZero`.
-/

public section

namespace NeZero

/-- **`NeZero` passes to divisors.** If `q` carries `NeZero` and `p ∣ q`, then so does `p`. This
is `ne_zero_of_dvd_ne_zero` with the conclusion packaged as an instance instead of as `p ≠ 0`, and
it holds in any semigroup with zero, with no unit required. Composed with `dvd_of_mul_right_dvd`
and `dvd_of_mul_left_dvd` it discharges both side conditions carried by a hypothesis of the shape
`d * M ∣ N`. -/
theorem of_dvd {α : Type*} [SemigroupWithZero α] {p q : α} [NeZero q] (h : p ∣ q) : NeZero p :=
  ⟨fun hp ↦ NeZero.ne q <| zero_dvd_iff.mp <| hp ▸ h⟩

/-- **`NeZero` from non-divisibility.** Since every element divides `0`, if `¬ p ∣ q` in a
semigroup with zero then `q` carries `NeZero`. The `_right` suffix distinguishes this from
`NeZero.of_not_dvd`, which concludes `NeZero (n : R)` from `[CharP R p]` and `¬ p ∣ n`. -/
theorem of_not_dvd_right {α : Type*} [SemigroupWithZero α] {p q : α} (h : ¬ p ∣ q) : NeZero q :=
  ⟨fun hq ↦ h (hq ▸ dvd_zero p)⟩

end NeZero
