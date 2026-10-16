/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
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
  have htor : IsAddTorsion (tateCohomology M 0) := by
    intro x
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨Nat.card G, Nat.card_pos, ?_⟩
    induction x using H0_induction_on with
    | h y =>
      have hnorm : M.ρ.norm y.val = (Nat.card G : ℤ) • y.val := by
        simp [Representation.norm, (Representation.mem_invariants M.ρ y.val).mp y.property,
          Nat.card_eq_fintype_card]
      rw [← map_nsmul]
      apply (H0π_eq_zero_iff (M := M) _).mpr
      exact ⟨y.val, by simpa using hnorm⟩
  -- The categorical cohomology object and its additive group carry the unique integer module
  -- structure by different instance paths.
  have hmod : (tateCohomology M 0).isModule = (AddCommGroup.toIntModule _) :=
    Subsingleton.elim _ _
  rw [hmod] at hfg
  exact AddCommGroup.finite_of_fg_isAddTorsion _
    (hG' := Module.Finite.iff_addGroup_fg.mp hfg) htor

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
  have htor : IsAddTorsion (tateCohomology M (-1)) := by
    intro x
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨Nat.card G, Nat.card_pos, ?_⟩
    induction x using HNegOne_induction_on with
    | h y =>
      rw [← map_nsmul]
      apply (HNegOneπ_eq_zero_iff (M := M) _).mpr
      -- `HNegOneπ_eq_zero_iff` states membership in the kernel restricted to the norm kernel;
      -- here we read that membership in the ambient representation.
      change (↑(Nat.card G • y) : M) ∈ Representation.Coinvariants.ker M.ρ
      have hsum : (∑ g : G, (M.ρ g y.val - y.val)) ∈
          Representation.Coinvariants.ker M.ρ :=
        Submodule.sum_mem _ fun g _ => Representation.Coinvariants.sub_mem_ker g y.val
      have hnorm : (∑ g : G, M.ρ g y.val) = 0 := by
        simpa [Representation.norm] using y.property
      have hsum_neg := (Representation.Coinvariants.ker M.ρ).neg_mem hsum
      simpa [Finset.sum_sub_distrib, hnorm, Nat.card_eq_fintype_card] using hsum_neg
  have hmod : (tateCohomology M (-1)).isModule = (AddCommGroup.toIntModule _) :=
    Subsingleton.elim _ _
  rw [hmod] at hfg
  exact AddCommGroup.finite_of_fg_isAddTorsion _
    (hG' := Module.Finite.iff_addGroup_fg.mp hfg) htor

end TauCeti.TateCohomology
