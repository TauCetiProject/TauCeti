/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Hom from an exact cokernel sequence

For an exact short complex `S` with an epimorphic second map, precomposition with `S.g`
identifies `Hom(S.X₃, Y)` with `Hom(S.X₂, Y)` whenever every map from `S.X₂` to `Y` kills
`S.f`. In a balanced preadditive category with a linear structure, this identification is linear.
In particular, it gives the degree-zero Hom computation for a projective resolution without any
Ext hypothesis.

## Main definitions

* `TauCeti.homLinearEquivOfExact`: the linear identification induced by
  precomposition with the second map of an exact short complex.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u t

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  {k : Type t} [Ring k] [Linear k C] {S : CategoryTheory.ShortComplex C} {Y : C} [Epi S.g]

/-- Precomposition with an epimorphic second map of an exact short complex identifies the
two Hom modules when every map to the target kills the first map. -/
noncomputable def homLinearEquivOfExact (hS : S.Exact)
    (h : ∀ f : S.X₂ ⟶ Y, S.f ≫ f = 0) : (S.X₃ ⟶ Y) ≃ₗ[k] (S.X₂ ⟶ Y) :=
  LinearEquiv.ofBijective (Linear.leftComp k Y S.g)
    ⟨fun _ _ hfg ↦ (cancel_epi S.g).mp hfg,
      fun f ↦ ⟨hS.desc f (h f), hS.g_desc _ _⟩⟩

/-- The Hom equivalence is precomposition with the second map. -/
-- `ofBijective` preserves the underlying map; `Linear.leftComp` is precomposition.
@[simp]
theorem homLinearEquivOfExact_apply (hS : S.Exact)
    (h : ∀ f : S.X₂ ⟶ Y, S.f ≫ f = 0) (f : S.X₃ ⟶ Y) :
    homLinearEquivOfExact (k := k) hS h f = S.g ≫ f := (rfl)

end TauCeti
