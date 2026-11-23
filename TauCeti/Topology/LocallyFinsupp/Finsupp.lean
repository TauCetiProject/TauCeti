/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Topology.LocallyFinsupp

/-!
# Finitely supported functions as functions with locally finite support

A finitely supported function `X →₀ Y` has finite, hence locally finite, support, so it is a
function with locally finite support on `X`. `Function.locallyFinsupp.ofFinsupp` is this inclusion,
as an additive monoid homomorphism. Composed with `Finsupp.embDomain`, it extends a finitely
supported function on a subset of `X` by zero, as for the cycles supported on a given set of points
of a scheme.
-/

public section

open Set Filter

namespace Function.locallyFinsupp

variable {X Y : Type*} [TopologicalSpace X] [AddMonoid Y]

/-- A finitely supported function, regarded as a function with locally finite support. -/
def ofFinsupp : (X →₀ Y) →+ locallyFinsupp X Y where
  toFun f :=
    { toFun := f
      supportWithinDomain' := subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦ ⟨univ, univ_mem, by simp⟩ }
  map_zero' := by
    ext
    simp
  map_add' f g := by
    ext
    simp

/-- A finitely supported function keeps its values as a function with locally finite support. -/
@[simp]
lemma ofFinsupp_apply (f : X →₀ Y) (x : X) : ofFinsupp f x = f x :=
  (rfl)

end Function.locallyFinsupp
