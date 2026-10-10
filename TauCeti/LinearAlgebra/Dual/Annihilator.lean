/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Pulling back annihilators

Over a field, pulling back functionals that annihilate a subspace gives exactly the
annihilator of its inverse image. This is the extension-of-functionals statement needed
when a Hom cocycle space is computed using an embedding into an injective module.

The proof uses Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker`, applied to
the composite with the quotient by the subspace.
-/

public section

namespace Submodule

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Pullback of functionals annihilating `S` gives all functionals annihilating its
inverse image. Neither the map nor either vector space needs to be finite-dimensional. -/
@[simp]
theorem dualAnnihilator_map_dualMap_eq (S : Submodule k W) (f : V →ₗ[k] W) :
    S.dualAnnihilator.map f.dualMap = (S.comap f).dualAnnihilator := by
  rw [← S.range_dualMap_mkQ_eq, ← LinearMap.range_comp,
    LinearMap.dualMap_comp_dualMap,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.ker_comp,
    Submodule.ker_mkQ]

end Submodule
