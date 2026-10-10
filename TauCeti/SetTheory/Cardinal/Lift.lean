/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh,
Claude Opus 5
-/
module

public import Mathlib.SetTheory.Cardinal.Order

/-!
# Cardinal bounds by a natural number are lift-invariant

A cardinal in one universe and a cardinal in another are not directly
comparable, but every *natural-number* bound is: `Cardinal.lift` fixes the
image of `ℕ`.  This module records the resulting cancellation

`Cardinal.lift.{w} c ≤ n ↔ c ≤ n`,

which is what lets rank bounds be compared across the independent source and
target universes of a `ContinuousLinearMap`.

Mathlib has the two ingredients (`Cardinal.lift_natCast` and `Cardinal.lift_le`)
and the analogous cancellations for the `ℵ`, `ℶ`, `ω` families
(`Cardinal.aleph_natCast_le_lift` and friends), but not this one; it is stated
here in the iff shape those use, so it can go upstream to
`Mathlib/SetTheory/Cardinal/Order.lean` on its own.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original declaration: `Cardinal.le_natCast_of_lift_le`, stated as a one-way
  implication inside
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`
  (itself adapted from Mathlib PR #32126).
* Extraction class: **moved and generalized to an iff.**  The signature-polish
  backlog flagged the original as
  a public extension of Mathlib's `Cardinal` namespace living inside an
  operator-ideal file — a placement a reviewer would challenge.  It has four
  call sites in three modules plus one downstream consumer, so privatizing it
  was not an option; giving it its own dependency-closed module, in the shape
  its Mathlib neighbours use, is.
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

namespace Cardinal

universe v w

/-- A natural-number bound on a cardinal is invariant under universe lifting.

Ranks of maps between spaces in different universes are not directly
comparable, but every bound used by the approximation-number API is a natural
number, and natural numbers are fixed by `Cardinal.lift`. -/
@[simp]
theorem lift_le_natCast {c : Cardinal.{v}} {n : ℕ} :
    Cardinal.lift.{w} c ≤ (n : Cardinal.{max v w}) ↔ c ≤ (n : Cardinal.{v}) := by
  conv_lhs => rw [← Cardinal.lift_natCast.{w} n]
  exact Cardinal.lift_le

end Cardinal

end
