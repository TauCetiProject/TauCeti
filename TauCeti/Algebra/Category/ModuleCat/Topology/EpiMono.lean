/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Monomorphisms in `TopModuleCat`

A morphism of topological modules is a monomorphism exactly when it is injective
(`TopModuleCat.mono_iff_injective`), the counterpart for `TopModuleCat R` of
`ModuleCat.mono_iff_injective`. The forward direction goes through the forgetful functor to
`ModuleCat R`, which preserves monomorphisms because it is a right adjoint; the backward direction
holds in any concrete category. Epimorphisms are not characterised here.
-/

public section

open CategoryTheory

namespace TopModuleCat

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- A morphism of topological modules is a monomorphism exactly when it is injective. The forward
direction goes through the forgetful functor to modules, which preserves monomorphisms because it
is a right adjoint. -/
theorem mono_iff_injective {X Y : TopModuleCat R} (f : X ⟶ Y) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ (TopModuleCat R) (ModuleCat R)).map f)).1
    inferInstance, fun h => ConcreteCategory.mono_of_injective f h⟩

/-- A monomorphism of topological modules is injective. -/
theorem injective_of_mono {X Y : TopModuleCat R} (f : X ⟶ Y) [Mono f] :
    Function.Injective f.hom :=
  (mono_iff_injective f).1 inferInstance

end TopModuleCat
