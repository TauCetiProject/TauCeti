/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Complete
public import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
public import TauCeti.RingTheory.Huber.ModuleTopology.Strict
public import TauCeti.RingTheory.Huber.NoetherianType.Basic
public import TauCeti.RingTheory.Huber.StrictMorphism

/-!
# Finite modules over a Huber ring of noetherian type

Let `A` be a complete Hausdorff Huber ring of noetherian type (`TauCeti.Huber.IsNoetherianType`).
This file unifies the module-topology properties of finitely generated `A`-modules across the two
defining branches of `IsNoetherianType` — existence of a noetherian ring of definition and strong
noetherianness of a Tate ring:

* every finite `A`-module with its natural topology is Hausdorff and naturally complete,
* every `A`-submodule of a finite `A`-module is closed,
* every `A`-linear map between finite `A`-modules with their natural topologies is strict, and
* every finitely generated submodule of a finite `A`-module carries the `A`-module topology as its
  subspace topology.

Note that a Huber ring with a noetherian ring of definition need not be a noetherian ring itself
(for instance an arbitrary discrete commutative ring has its prime subring as a noetherian ring of
definition), so a submodule of a finite `A`-module need not be finitely generated automatically;
`IsNoetherianType.isModuleTopology_submodule` therefore takes `[Module.Finite A L]` explicitly.

## Main results

* `TauCeti.Huber.IsNoetherianType.t2Space_of_isModuleTopology`,
  `TauCeti.Huber.IsNoetherianType.t2Space_moduleTopology`: a finite module over `A` is Hausdorff in
  its natural topology.
* `TauCeti.Huber.IsNoetherianType.isNaturallyComplete`: every finite `A`-module is naturally
  complete.
* `TauCeti.Huber.IsNoetherianType.isClosed_submodule`: every `A`-submodule of a finite `A`-module
  is closed.
* `TauCeti.Huber.IsNoetherianType.isStrictMap`: every `A`-linear map between finite `A`-modules
  with their natural topologies is strict.
* `TauCeti.Huber.IsNoetherianType.isModuleTopology_submodule`: the subspace topology on a finitely
  generated submodule of a finite `A`-module is its `A`-module topology.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and §1.6.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18 and Remark 6.37.
-/

public section

open Topology
open scoped Uniformity

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] [T0Space A] [IsNoetherianType A]

section SingleModule

variable {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **A finite module over a complete Hausdorff Huber ring of noetherian type is Hausdorff** in its
natural topology (Huber 1994, Lemma 2.3(ii); Wedhorn, Proposition 6.18(1)). -/
theorem IsNoetherianType.t2Space_of_isModuleTopology [TopologicalSpace M] [IsModuleTopology A M] :
    T2Space M := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ P.t2Space_of_isNoetherianRing) fun _ _ ↦ ?_
  have : IsNoetherianRing A := isNoetherianRing_of_isStronglyNoetherian <| by
    rwa [IsUniformAddGroup.rightUniformSpace_eq]
  rw [eq_moduleTopology A M]
  exact IsTateRing.t2Space_moduleTopology

/-- **The module topology on a finite module over a complete Hausdorff Huber ring of noetherian
type is Hausdorff.** -/
theorem IsNoetherianType.t2Space_moduleTopology : @T2Space M (moduleTopology A M) :=
  let _ : TopologicalSpace M := moduleTopology A M
  IsNoetherianType.t2Space_of_isModuleTopology (A := A)

/-- **Every finite module over a complete Hausdorff Huber ring of noetherian type is naturally
complete.** Completeness holds by `TauCeti.completeSpace_moduleTopology` since `A` is complete and
first countable, and separatedness by `IsNoetherianType.t2Space_moduleTopology`. -/
theorem IsNoetherianType.isNaturallyComplete : IsNaturallyComplete A M := by
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact isNaturallyComplete_iff_t2Space.mpr (IsNoetherianType.t2Space_moduleTopology (A := A))

/-- **Every submodule of a finite module over a complete Hausdorff Huber ring of noetherian type is
closed** in its natural topology (Huber 1994, Lemma 2.3(ii)). -/
theorem IsNoetherianType.isClosed_submodule [TopologicalSpace M] [IsModuleTopology A M]
    (N : Submodule A M) : IsClosed (N : Set M) := by
  let _ : TopologicalSpace (M ⧸ N) := moduleTopology A (M ⧸ N)
  have : IsModuleTopology A (M ⧸ N) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalAddGroup A (M ⧸ N)
  have : T2Space (M ⧸ N) := IsNoetherianType.t2Space_of_isModuleTopology (A := A)
  convert (isClosed_singleton (x := (0 : M ⧸ N))).preimage
    (IsModuleTopology.continuous_of_linearMap N.mkQ) using 1
  ext x
  simp [Submodule.Quotient.mk_eq_zero]

end SingleModule

section Strict

/-- Helper packaging the uniform and first-countability instances on a finite module with its
natural topology over `A`, used to invoke `LinearMap.isStrictMap_of_module_finite` in the strongly
noetherian Tate branch. -/
private theorem complete_countablyGenerated_t2_of_isModuleTopology
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [TopologicalSpace M] [IsModuleTopology A M] :
    letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    IsUniformAddGroup M ∧ CompleteSpace M ∧ (𝓤 M).IsCountablyGenerated ∧ T2Space M := by
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  obtain ⟨hcomp, ht2⟩ := isNaturallyComplete_iff.mp (IsNoetherianType.isNaturallyComplete (A := A)
    (M := M))
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : FirstCountableTopology M := by
    rw [eq_moduleTopology A M]
    exact firstCountableTopology_moduleTopology (A := A)
  exact ⟨‹_›, hcomp, IsUniformAddGroup.uniformity_countably_generated, ht2⟩

/-- **Every linear map between finite modules over a complete Hausdorff Huber ring of noetherian
type is strict** for their natural topologies (Huber 1994, Lemma 2.3(i); Wedhorn,
Proposition 6.18(2)). -/
theorem IsNoetherianType.isStrictMap
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [TopologicalSpace M] [IsModuleTopology A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [TopologicalSpace N] [IsModuleTopology A N]
    (f : M →ₗ[A] N) : IsStrictMap f := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ P.isStrictMap_of_isNoetherianRing f) fun _ _ ↦ ?_
  have : IsNoetherianRing A := isNoetherianRing_of_isStronglyNoetherian <| by
    rwa [IsUniformAddGroup.rightUniformSpace_eq]
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  obtain ⟨_, _, _, _⟩ := complete_countablyGenerated_t2_of_isModuleTopology (A := A) (M := M)
  let _ : IsTopologicalAddGroup N := IsModuleTopology.isTopologicalAddGroup A N
  let _ : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  obtain ⟨_, _, _, _⟩ := complete_countablyGenerated_t2_of_isModuleTopology (A := A) (M := N)
  have : ContinuousSMul A M := IsModuleTopology.toContinuousSMul A M
  have : ContinuousSMul A N := IsModuleTopology.toContinuousSMul A N
  exact f.isStrictMap_of_module_finite

/-- **The subspace topology on a finitely generated submodule of a finite module over a complete
Hausdorff Huber ring of noetherian type is its natural module topology.** -/
theorem IsNoetherianType.isModuleTopology_submodule
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [TopologicalSpace M] [IsModuleTopology A M]
    (L : Submodule A M) [Module.Finite A L] : IsModuleTopology A L := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A L
  have hf_strict : IsStrictMap f :=
    IsEmbedding.subtypeVal.isStrictMap_iff.mpr (IsNoetherianType.isStrictMap (A := A)
      (L.subtype.comp f))
  have hq : IsQuotientMap f := isQuotientMap_iff_isStrictMap_surjective.mpr ⟨hf_strict, hf⟩
  apply IsModuleTopology.of_continuous_id
  rw [hq.eq_coinduced, continuous_coinduced_dom]
  exact @IsModuleTopology.continuous_of_linearMap A _ _ (Fin n → A) _ _ _ inferInstance
    L _ _ (moduleTopology A L) (ModuleTopology.continuousAdd A L)
    (ModuleTopology.continuousSMul A L) f

end Strict

end TauCeti.Huber
