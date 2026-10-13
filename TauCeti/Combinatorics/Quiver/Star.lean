/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Covering
public import Mathlib.Data.Fintype.EquivFin

/-!
# Finite quiver stars

The arrows from a fixed source to a fixed target inject into the star at the source. Thus a
finite source star makes each of these arrow types finite, without requiring finite vertices
or a chosen enumeration of the arrows.

## Main results

* `Quiver.finiteHomOfFiniteStar`: finite source stars give finite arrow types.
-/

public section

namespace Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- The arrows from `i` to `j` form a finite type when the star at `i` is finite. -/
instance finiteHomOfFiniteStar (i j : V) [Finite (Star i)] : Finite (i ⟶ j) :=
  Finite.of_injective (fun e : i ⟶ j => (Star.mk e : Star i)) sigma_mk_injective

end Quiver
