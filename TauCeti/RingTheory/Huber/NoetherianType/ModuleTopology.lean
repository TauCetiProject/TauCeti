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
`Submodule.isModuleTopology_of_isNoetherianType` therefore takes `[Module.Finite A L]` explicitly.

## Main results

* `TauCeti.Huber.IsNoetherianType.t2Space_of_isModuleTopology`,
  `TauCeti.Huber.IsNoetherianType.t2Space_moduleTopology`: a finite module over `A` is Hausdorff in
  its natural topology.
* `TauCeti.Huber.IsNoetherianType.isNaturallyComplete`: every finite `A`-module is naturally
  complete.
* `TauCeti.Huber.IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology`: the canonical
  right uniformity of a finite module with its natural topology is uniform-additive, complete,
  Hausdorff, and nonarchimedean.
* `Submodule.isClosed_of_isNoetherianType`: every `A`-submodule of a finite `A`-module is closed.
* `LinearMap.isStrictMap_of_isNoetherianType`: every `A`-linear map between finite `A`-modules
  with their natural topologies is strict.
* `Submodule.isModuleTopology_of_isNoetherianType`: the subspace topology on a finitely generated
  submodule of a finite `A`-module is its `A`-module topology.

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
complete** (Huber 1994, Lemma 2.3(ii); Wedhorn, Proposition 6.18(1)). -/
theorem IsNoetherianType.isNaturallyComplete : IsNaturallyComplete A M := by
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact isNaturallyComplete_iff_t2Space.mpr (IsNoetherianType.t2Space_moduleTopology (A := A))

/-- **Uniform-group properties of a finite module with its natural topology**: over a complete
Hausdorff Huber ring `A` of noetherian type, the canonical right uniformity on a finite `A`-module
carrying the `A`-module topology makes it a complete, Hausdorff, nonarchimedean uniform additive
group. -/
theorem IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology
    [TopologicalSpace M] [IsModuleTopology A M] :
    letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    IsUniformAddGroup M ∧ CompleteSpace M ∧ T2Space M ∧ NonarchimedeanAddGroup M := by
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  obtain ⟨hcomp, ht2⟩ := isNaturallyComplete_iff.mp (IsNoetherianType.isNaturallyComplete (A := A)
    (M := M))
  have hna : NonarchimedeanAddGroup M := by
    rw [eq_moduleTopology A M]
    exact TauCeti.nonarchimedeanAddGroup_moduleTopology (A := A)
  exact ⟨‹_›, hcomp, ht2, hna⟩

/-- **Every submodule of a finite module over a complete Hausdorff Huber ring of noetherian type is
closed** in its natural topology (Huber 1994, Lemma 2.3(ii)). -/
theorem _root_.Submodule.isClosed_of_isNoetherianType [TopologicalSpace M] [IsModuleTopology A M]
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

/-- **Every linear map between finite modules over a complete Hausdorff Huber ring of noetherian
type is strict** for their natural topologies (Huber 1994, Lemma 2.3(i); Wedhorn,
Proposition 6.18(2)). -/
theorem _root_.LinearMap.isStrictMap_of_isNoetherianType
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
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := A) (M := M)
  have : FirstCountableTopology M := by
    rw [eq_moduleTopology A M]
    exact firstCountableTopology_moduleTopology (A := A)
  have : (𝓤 M).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let _ : IsTopologicalAddGroup N := IsModuleTopology.isTopologicalAddGroup A N
  let _ : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := A) (M := N)
  have : FirstCountableTopology N := by
    rw [eq_moduleTopology A N]
    exact firstCountableTopology_moduleTopology (A := A)
  have : (𝓤 N).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : ContinuousSMul A M := IsModuleTopology.toContinuousSMul A M
  have : ContinuousSMul A N := IsModuleTopology.toContinuousSMul A N
  exact f.isStrictMap_of_module_finite

/-- **The subspace topology on a finitely generated submodule of a finite module over a complete
Hausdorff Huber ring of noetherian type is its natural module topology.** -/
theorem _root_.Submodule.isModuleTopology_of_isNoetherianType
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [TopologicalSpace M] [IsModuleTopology A M]
    (L : Submodule A M) [Module.Finite A L] : IsModuleTopology A L := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A L
  have hf_strict : IsStrictMap f :=
    IsEmbedding.subtypeVal.isStrictMap_iff.mpr (L.subtype.comp f).isStrictMap_of_isNoetherianType
  have hq : IsQuotientMap f := isQuotientMap_iff_isStrictMap_surjective.mpr ⟨hf_strict, hf⟩
  exact ⟨hq.eq_coinduced.trans (ModuleTopology.eq_coinduced_of_surjective hf).symm⟩

end Strict

end TauCeti.Huber
