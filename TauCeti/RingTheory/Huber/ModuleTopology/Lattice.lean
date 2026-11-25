/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.FiniteModule
public import TauCeti.RingTheory.AdicCompletion.ModuleComparison

/-!
# The induced topology on a defining lattice

Let `(A₀, I)` be a pair of definition of a topological ring `A`. If a finitely generated
`A₀`-submodule `L` of a naturally topologised `A`-module spans that module over `A`, its
subspace topology is exactly its `I`-adic module topology, hence its natural `A₀`-module
topology. Neither noetherianity nor completeness is needed for this comparison.

This identifies the topology on the defining lattices used in finite-module completion:
algebraic statements about the quotients `L / IⁿL` then refer to the actual induced topology,
not to an independently chosen topology on `L`. When `A₀` is noetherian,
`latticeCompletionEquiv` identifies the separated completion of the induced uniformity with
`AdicCompletion I L`, sending original lattice elements to their compatible residue classes.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, before Lemma 2.3 and its proof.
-/

public section

open Filter Topology

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  (P : PairOfDefinition A) {L : Submodule P.ringOfDefinition M}

/-- The powers `IⁿL` form a zero-neighbourhood basis in the subspace topology of a finite
spanning defining lattice. -/
theorem hasBasis_nhds_zero_lattice (hL : L.FG)
    (hspan : Submodule.span A (L : Set M) = ⊤) :
    (𝓝 (0 : L)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((P.idealOfDefinition ^ n • ⊤ : Submodule P.ringOfDefinition L) : Set L) := by
  rw [nhds_subtype_eq_comap]
  exact ((P.hasBasis_nhds_zero_idealOfDefinition_pow_smul hL hspan).comap
    (Subtype.val : L → M)).congr (fun _ ↦ Iff.rfl) fun n _ ↦ by
      ext x
      exact (Submodule.mem_smul_top_iff _ L x).symm

/-- The subspace topology on a finite spanning defining lattice is its adic module topology. -/
theorem adicModuleTopology_eq_lattice (hL : L.FG)
    (hspan : Submodule.span A (L : Set M) = ⊤) :
    P.idealOfDefinition.adicModuleTopology L = (inferInstance : TopologicalSpace L) := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  apply IsTopologicalAddGroup.ext
  · infer_instance
  · infer_instance
  exact (P.idealOfDefinition.hasBasis_nhds_zero_adicModule (M := L)).eq_of_same_basis
    (P.hasBasis_nhds_zero_lattice hL hspan)

/-- A finite spanning defining lattice carries its natural module topology over the ring
of definition, with its given subspace topology. -/
theorem isModuleTopology_lattice (hL : L.FG)
    (hspan : Submodule.span A (L : Set M) = ⊤) :
    IsModuleTopology P.ringOfDefinition L := by
  have : Module.Finite P.ringOfDefinition L := Module.Finite.iff_fg.mpr hL
  constructor
  rw [← P.isAdic_idealOfDefinition.adicModuleTopology_eq_moduleTopology (M := L)]
  exact (P.adicModuleTopology_eq_lattice hL hspan).symm

end TauCeti.Huber.PairOfDefinition

open UniformSpace

namespace TauCeti.Huber.PairOfDefinition

universe u

variable {A M : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [AddCommGroup M] [Module A M] [UniformSpace M]
  [IsUniformAddGroup M] [IsModuleTopology A M]
  (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]
  {L : Submodule P.ringOfDefinition M}

local instance : IsUniformAddGroup L := L.toAddSubgroup.isUniformAddGroup

local instance : UniformContinuousConstSMul P.ringOfDefinition L := by
  have := uniformContinuousConstSMul_of_continuousConstSMul A M
  exact ⟨fun r ↦ ((uniformContinuous_const_smul (r : A)).comp
    uniformContinuous_subtypeVal).subtype_mk _⟩

/-- The separated completion of a finite spanning defining lattice, for its induced
uniformity, is its algebraic adic completion. No completeness of the ambient ring is assumed. -/
noncomputable def latticeCompletionEquiv (hL : L.FG)
    (hspan : Submodule.span A (L : Set M) = ⊤) :
    Completion L ≃ₗ[P.ringOfDefinition] AdicCompletion P.idealOfDefinition L := by
  have := P.isModuleTopology_lattice hL hspan
  have : Module.Finite P.ringOfDefinition L := Module.Finite.iff_fg.mpr hL
  exact P.isAdic_idealOfDefinition.completionModuleEquivAdicCompletion

/-- The lattice comparison sends a lattice element to its system of residue classes. -/
@[simp]
theorem latticeCompletionEquiv_coe (hL : L.FG)
    (hspan : Submodule.span A (L : Set M) = ⊤) (m : L) :
    P.latticeCompletionEquiv hL hspan (m : Completion L) =
      AdicCompletion.of P.idealOfDefinition L m := by
  have := P.isModuleTopology_lattice hL hspan
  have : Module.Finite P.ringOfDefinition L := Module.Finite.iff_fg.mpr hL
  exact P.isAdic_idealOfDefinition.completionModuleEquivAdicCompletion_coe m

/-- The inverse lattice comparison sends an original residue-class system to the image
of the lattice element in its separated completion. -/
@[simp]
theorem latticeCompletionEquiv_symm_of (hL : L.FG)
    (hspan : Submodule.span A (L : Set M) = ⊤) (m : L) :
    (P.latticeCompletionEquiv hL hspan).symm (AdicCompletion.of P.idealOfDefinition L m) =
      (m : Completion L) := by
  rw [LinearEquiv.symm_apply_eq, latticeCompletionEquiv_coe]

end TauCeti.Huber.PairOfDefinition
