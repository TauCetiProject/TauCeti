/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.OrzechProperty

/-!
# Epimorphisms onto finite modules in `ModuleCat`

Over a ring with the Orzech property, such as any commutative ring, a surjective endomorphism of a
finitely generated module is injective (`OrzechProperty.injective_of_surjective_endomorphism`).
This file records the categorical form: an epimorphism onto a finitely generated module `M` from
a module isomorphic to `M` is a monomorphism (`ModuleCat.mono_of_epi_of_iso`).
-/

public section

open CategoryTheory

namespace ModuleCat

universe u v

variable {R : Type u} [Ring R] [OrzechProperty R]

/-- Over a ring with the Orzech property, an epimorphism onto a finitely generated module `M` from
a module isomorphic to `M` is a monomorphism. -/
theorem mono_of_epi_of_iso {M Y : ModuleCat.{v} R} [Module.Finite R M] (e : Y ≅ M)
    (g : Y ⟶ M) [Epi g] : Mono g := by
  have : Mono (e.inv ≫ g) := (mono_iff_injective _).2
    (OrzechProperty.injective_of_surjective_endomorphism (e.inv ≫ g).hom
      ((epi_iff_surjective _).1 (epi_comp _ _)))
  simpa using mono_comp e.hom (e.inv ≫ g)

end ModuleCat
