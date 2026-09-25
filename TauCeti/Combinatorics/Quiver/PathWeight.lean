/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Additive path weights

Mathlib's `Quiver.Path.addWeight w p` sums the weights `w e` of the arrows along a path `p`. This
file records its evaluation at a constant weight: a constant weight `c` sums to `p.length • c`.
This identifies the path-length grading of a path algebra as the grading by the constant weight
one. It also records that pushing a path along a prefunctor sums the pulled-back arrow weight.

## Main results

* `Quiver.Path.addWeight_const`: the constant weight `c` gives a path the weight `p.length • c`.
* `Prefunctor.addWeight_mapPath`: the weight of a pushed path is the pulled-back weight of the
  original path.
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

variable {W : Type*} [Quiver W]

/-- **Pushing a path pulls back its arrow weight**: the weight of the image path is the sum of the
image-arrow weights along the original path. -/
@[simp]
theorem _root_.Prefunctor.addWeight_mapPath (φ : V ⥤q W)
    (wt : ∀ {a b : W}, (a ⟶ b) → M) {a b : V} (p : Quiver.Path a b) :
    (φ.mapPath p).addWeight wt = p.addWeight fun e => wt (φ.map e) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

end TauCeti
