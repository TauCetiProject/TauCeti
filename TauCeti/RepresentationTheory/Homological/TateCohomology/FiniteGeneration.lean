/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finiteness of low-degree Tate cohomology for integral representations

For a finite group acting on a finitely generated abelian group, Tate cohomology in degrees zero
and minus one is finite. The low-degree descriptions give quotients of finitely generated
subgroups; the group order kills both quotients. These finiteness results allow Herbrand
quotients of arithmetic lattices, in particular the `S`-units, to be used without separate
finiteness assumptions.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.TateCohomology

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) [Module.Finite ℤ M]

/-- Degree-zero Tate cohomology of a finitely generated integral representation of a finite
group is finite. -/
theorem finite_tateCohomology_zero_of_moduleFinite : Finite (tateCohomology M 0) := by
  have : IsNoetherian ℤ M := inferInstance
  let : Module ℤ M.ρ.invariants := M.ρ.invariants.module
  have : Module.Finite ℤ M.ρ.invariants := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hfg : Module.Finite ℤ (tateCohomology M 0) :=
    Module.Finite.of_surjective (H0π M).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  -- The categorical cohomology object and its additive group carry the unique integer module
  -- structure by different instance paths.
  have hmod : (tateCohomology M 0).isModule = (AddCommGroup.toIntModule _) :=
    Subsingleton.elim _ _
  rw [hmod] at hfg
  exact AddCommGroup.finite_of_fg_isAddTorsion _
    (hG' := Module.Finite.iff_addGroup_fg.mp hfg) (isAddTorsion_tateCohomology M _)

/-- Degree-minus-one Tate cohomology of a finitely generated integral representation of a
finite group is finite. -/
theorem finite_tateCohomology_negOne_of_moduleFinite :
    Finite (tateCohomology M (-1)) := by
  have : IsNoetherian ℤ M := inferInstance
  let : Module ℤ (LinearMap.ker M.ρ.norm) := (LinearMap.ker M.ρ.norm).module
  have : Module.Finite ℤ (LinearMap.ker M.ρ.norm) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hfg : Module.Finite ℤ (tateCohomology M (-1)) :=
    Module.Finite.of_surjective (HNegOneπ M).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have hmod : (tateCohomology M (-1)).isModule = (AddCommGroup.toIntModule _) :=
    Subsingleton.elim _ _
  rw [hmod] at hfg
  exact AddCommGroup.finite_of_fg_isAddTorsion _
    (hG' := Module.Finite.iff_addGroup_fg.mp hfg) (isAddTorsion_tateCohomology M _)

end TauCeti.TateCohomology
