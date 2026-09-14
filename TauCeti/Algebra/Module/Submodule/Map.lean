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
file records what those give for a *finite set* of submodules: the supremum of the image of a
`Finset` of submodules, and the fact that pushing an independent finite family forward along an
injective linear map leaves it independent.

The finite-set form is what a decomposition of a module into a `Finset` of submodules needs, as in
`TauCeti/RingTheory/KrullSchmidt/Existence.lean`, when it is transported along an injective map.

## Main results

* `TauCeti.Submodule.map_finset_sup`: the image of a finite supremum is the supremum of the images.
* `TauCeti.Submodule.sup_image_map`: the supremum of the image `Finset` is the image of the
  supremum.
* `TauCeti.Submodule.supIndep_image_map`: an injective linear map carries an independent finite
  family of submodules to an independent one.
-/

public section

namespace TauCeti

namespace Submodule

universe u v v'

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']

/-- The image of a finite supremum of submodules is the supremum of the images. -/
theorem map_finset_sup (f : M →ₗ[R] M') (s : Finset (Submodule R M)) :
    Submodule.map f (s.sup id) = s.sup (Submodule.map f) := by
  simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup, id_eq]

/-- The supremum of the image of a finite set of submodules under `Submodule.map` is the image of
the supremum. -/
theorem sup_image_map [DecidableEq (Submodule R M')] (f : M →ₗ[R] M')
    (s : Finset (Submodule R M)) :
    (s.image (Submodule.map f)).sup id = Submodule.map f (s.sup id) := by
  rw [Finset.sup_image]
  simpa only [Function.comp_def, id_eq] using (map_finset_sup f s).symm

/-- **An injective linear map preserves independence of a finite family of submodules**: the images
of the members are again independent. -/
theorem supIndep_image_map [DecidableEq (Submodule R M')] {f : M →ₗ[R] M'}
    (hf : Function.Injective f) {s : Finset (Submodule R M)} (hs : s.SupIndep id) :
    (s.image (Submodule.map f)).SupIndep id := by
  refine Finset.SupIndep.image fun t hts P hP hPt ↦ ?_
  simpa only [Function.comp_def, id_eq, ← map_finset_sup] using
    Submodule.disjoint_map hf (hs hts hP hPt)

end Submodule

end TauCeti
