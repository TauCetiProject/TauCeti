/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.Topology.Algebra.Module.JointContinuity

/-!
# Criteria for jointly continuous representations

A linear representation on a finite module with its module topology is jointly continuous
exactly when each orbit map is continuous. One may check just a finite generating family;
on a finite free carrier, one may instead check matrix entries in any basis. No compactness
of the acting monoid or projectivity of the carrier is required.

The forgetful map from `TauCeti.ContinuousRep` to Mathlib's `ContRepresentation` is injective.
Its image consists exactly of the jointly continuous actions; for finite carriers with their
module topology this is equivalent to continuity of every orbit map. Thus continuity of the
individual operators alone does not suffice to lift a `ContRepresentation`.
-/

public section

namespace Representation

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R] [TopologicalSpace R]
  [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M]

/-- Joint continuity of a representation on a finite module is equivalent to continuity of
every orbit map. The carrier has its module topology. -/
theorem continuous_iff_orbit [Module.Finite R M] (ρ : Representation R Γ M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ m, Continuous (fun g => ρ g m) := by
  have := IsModuleTopology.toContinuousAdd R M
  exact LinearMap.continuous_uncurry_iff ρ

/-- Joint continuity can be checked on a finite generating family of the representation's
carrier with its module topology. -/
theorem continuous_iff_of_span_eq_top (ρ : Representation R Γ M)
    {ι : Type*} [Finite ι] (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ i, Continuous (fun g => ρ g (v i)) := by
  have := IsModuleTopology.toContinuousAdd R M
  exact LinearMap.continuous_uncurry_iff_of_span_eq_top ρ v hv

end Representation

namespace TauCeti.ContinuousRep

section Forgetful

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- Forgetting joint continuity loses no data. -/
theorem toContRepresentation_injective :
    Function.Injective (toContRepresentation : ContinuousRep Γ R M → ContRepresentation R Γ M) := by
  intro ρ σ h
  ext g m
  simpa only [toContRepresentation_apply] using
    congrArg (fun τ : ContRepresentation R Γ M => τ g m) h

end Forgetful

end TauCeti.ContinuousRep

namespace ContRepresentation

open TauCeti

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- A Mathlib continuous representation lifts to a jointly continuous representation exactly
when its action map is jointly continuous. -/
@[simp]
theorem exists_continuousRep_iff (ρ : ContRepresentation R Γ M) :
    (∃ σ : ContinuousRep Γ R M, σ.toContRepresentation = ρ) ↔
      Continuous (fun p : Γ × M => ρ p.1 p.2) := by
  constructor
  · rintro ⟨σ, rfl⟩
    simpa only [ContinuousRep.toContRepresentation_apply, ContinuousRep.coe_toRepresentation]
      using σ.continuous_action
  · intro h
    refine ⟨⟨ρ.toRepresentation, h⟩, ?_⟩
    apply DFunLike.ext
    intro g
    apply ContinuousLinearMap.ext
    intro m
    simp only [ContinuousRep.toContRepresentation_apply]
    -- Mathlib's `toRepresentation` evaluates by forgetting continuity of each operator.
    rfl

section Finite

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R] [TopologicalSpace R]
  [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M] [IsTopologicalAddGroup M] [Module.Finite R M]

/-- On a finite module with its module topology, a Mathlib continuous representation lifts
exactly when every orbit map is continuous. -/
theorem exists_continuousRep_iff_orbit (ρ : ContRepresentation R Γ M) :
    (∃ σ : ContinuousRep Γ R M, σ.toContRepresentation = ρ) ↔
      ∀ m, Continuous (fun g => ρ g m) := by
  rw [exists_continuousRep_iff]
  exact ρ.toRepresentation.continuous_iff_orbit

end Finite

end ContRepresentation
