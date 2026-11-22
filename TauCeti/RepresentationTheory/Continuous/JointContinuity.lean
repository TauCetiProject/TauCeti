/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.Topology.Algebra.Module.JointContinuity
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# Criteria for jointly continuous representations

A linear representation on a finite module with its module topology is jointly continuous
exactly when each orbit map is continuous. One may check just a finite generating family.
No compactness of the acting monoid or projectivity of the carrier is required.

For finite carriers with their module topology, the image of
`TauCeti.ContinuousRep.toContRepresentation` is therefore characterized by continuity of
every orbit map, not just continuity of each individual operator.
-/

public section

namespace Representation

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M]

/-- Joint continuity of a representation on a finite module is equivalent to continuity of
every orbit map. The carrier has its module topology. -/
theorem continuous_iff_orbit [Module.Finite R M] (ρ : Representation R Γ M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ m, Continuous (fun g => ρ g m) := by
  have := IsModuleTopology.toContinuousAdd R M
  exact TauCeti.ModuleTopology.continuous_uncurry_iff_apply ρ

/-- Joint continuity can be checked on a finite generating family of the representation's
carrier with its module topology. -/
theorem continuous_iff_orbit_of_span_eq_top (ρ : Representation R Γ M)
    {ι : Type*} [Finite ι] (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ i, Continuous (fun g => ρ g (v i)) := by
  have := IsModuleTopology.toContinuousAdd R M
  exact TauCeti.ModuleTopology.continuous_uncurry_iff_apply_of_span_eq_top ρ v hv

end Representation

namespace ContRepresentation

open TauCeti

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M] [IsTopologicalAddGroup M] [Module.Finite R M]

/-- On a finite module with its module topology, a Mathlib continuous representation lifts
exactly when every orbit map is continuous. -/
theorem exists_continuousRep_iff_orbit (ρ : ContRepresentation R Γ M) :
    (∃ σ : ContinuousRep Γ R M, σ.toContRepresentation = ρ) ↔
      ∀ m, Continuous (fun g => ρ g m) := by
  rw [exists_continuousRep_iff]
  simpa only [toRepresentation_apply] using ρ.toRepresentation.continuous_iff_orbit

end ContRepresentation
