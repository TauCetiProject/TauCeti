/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Order.SupIndep

/-!
# Finite families of submodules under an injective linear map

`Submodule.map` preserves arbitrary suprema (`Submodule.map_iSup`), and along an injective map it
also preserves infima (`Submodule.map_inf`) and hence disjointness (`Submodule.disjoint_map`).  This
file records that pushing an independent finite family forward along an injective map leaves it
independent.

The finite-set form is what a decomposition of a module into a `Finset` of submodules needs, as in
`TauCeti/RingTheory/KrullSchmidt/Existence.lean`, when it is transported along an injective map.

## Main results

* `LinearMap.supIndep_image_map`: an injective linear map carries an independent finite
  family of submodules to an independent one.
-/

public section

namespace LinearMap

universe u v v'

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']

/-- **An injective linear map preserves independence of a finite family of submodules**: the images
of the members are again independent. -/
theorem supIndep_image_map [DecidableEq (Submodule R M')] (f : M →ₗ[R] M')
    (hf : Function.Injective f) {s : Finset (Submodule R M)}
    (hs : s.SupIndep _root_.id) :
    (s.image (Submodule.map f)).SupIndep _root_.id := by
  refine Finset.SupIndep.image fun t hts P hP hPt ↦ ?_
  simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup] using
    Submodule.disjoint_map hf (hs hts hP hPt)

end LinearMap
