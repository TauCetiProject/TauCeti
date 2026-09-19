/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Additive constant weights

Mathlib's `Quiver.Path.addWeight w p` sums the weights `w e` of the arrows along a path `p`. This
file records its evaluation at a constant weight: a constant weight `c` sums to `p.length • c`.
This identifies the path-length grading of a path algebra as the grading by the constant weight
one.

## Main results

* `Quiver.Path.addWeight_const`: the constant weight `c` gives a path the weight `p.length • c`.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V] {M : Type*} [AddMonoid M]

/-- **A constant weight counts arrows**: with every arrow of weight `c`, a path has weight
`p.length • c`. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_const (c : M) {a b : V} (p : Quiver.Path a b) :
    p.addWeight (fun _ => c) = p.length • c := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, succ_nsmul]

end TauCeti
