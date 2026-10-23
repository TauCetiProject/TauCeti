/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Simple quotients of modules

A nonzero module with a coatomic submodule lattice has a simple quotient. In particular this
applies to nonzero Noetherian modules. The categorical statement provides an epimorphism to a
simple object, so it can be transported along equivalences of module and representation categories.
-/

public section

namespace ModuleCat

open CategoryTheory

variable {R : Type*} [Ring R]

/-- A nonzero module whose submodule lattice is coatomic admits an epimorphism to a simple
module. -/
theorem exists_epi_simple (M : ModuleCat R) [IsCoatomic (Submodule R M)]
    (hM : ¬ CategoryTheory.Limits.IsZero M) :
    ∃ S : ModuleCat R, Simple S ∧ ∃ f : M ⟶ S, Epi f := by
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp
    (fun h ↦ hM (ModuleCat.isZero_iff_subsingleton.mpr h))
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Submodule R M)
  have : IsSimpleModule R (M ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  refine ⟨ModuleCat.of R (M ⧸ N), inferInstance, ModuleCat.ofHom N.mkQ, ?_⟩
  exact (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective

end ModuleCat
