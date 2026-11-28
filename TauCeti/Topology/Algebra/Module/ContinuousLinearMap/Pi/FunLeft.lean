/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Continuous linear precomposition on product modules

Precomposition by a map of index types is continuous and linear for the product topologies.
This supplies coordinate restriction for the implicit function charts of polynomial zero sets.
-/

public section

namespace ContinuousLinearMap

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  {ι κ : Type*}

/-- Precomposition by a map of index types, with the product topologies. -/
def funLeft (f : ι → κ) : (κ → M) →L[R] (ι → M) :=
  pi fun i ↦ proj (f i)

/-- Precomposition evaluates at the image of the index. -/
@[simp]
theorem funLeft_apply (f : ι → κ) (x : κ → M) (i : ι) :
    funLeft R M f x i = x (f i) := (rfl)

/-- The underlying linear map of continuous linear precomposition. -/
@[simp]
theorem toLinearMap_funLeft (f : ι → κ) :
    (funLeft R M f).toLinearMap = LinearMap.funLeft R M f := (rfl)

end ContinuousLinearMap
