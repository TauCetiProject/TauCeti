/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Reversed quiver paths

Reversing every arrow leaves the number of arrows unchanged. This allows path reversal to
preserve the path-length grading of a path algebra. A prefunctor that preserves reversal of
arrows also preserves reversal of paths.
-/

public section

namespace Quiver.Path

universe u v

variable {V : Type u} [Quiver.{v} V] [HasReverse V]

/-- Reversing a path preserves its length. -/
@[simp]
theorem length_reverse {a b : V} (p : Path a b) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [Path.reverse, Path.length_comp, ih, Nat.add_comm]

end Quiver.Path

namespace Prefunctor

variable {U V : Type*} [Quiver U] [Quiver V] [Quiver.HasReverse U] [Quiver.HasReverse V]

/-- A prefunctor that preserves reversal of arrows maps the reverse of a path to the reverse of
its image. -/
@[simp]
theorem mapPath_reverse (φ : U ⥤q V) [φ.MapReverse] {a b : U} (p : Quiver.Path a b) :
    φ.mapPath p.reverse = (φ.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

end Prefunctor
