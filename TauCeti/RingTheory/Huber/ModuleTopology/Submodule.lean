/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Noetherian.LinearMap
import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Closedness and canonical topology of finite submodules via separating functionals

Over a complete Hausdorff Tate ring `A`, `TauCeti.Huber.isClosed_of_isNoetherian` shows that every
submodule of a complete Hausdorff first-countable Noetherian topological `A`-module `M` is closed.
Infinite-dimensional function and sequence spaces such as `C₀(X, M)` or `ι → M` are not themselves
Noetherian, nor need they be first-countable, yet they admit point-separating families of
continuous `A`-linear maps into `M`.

This file shows that any module-finite submodule `P` of a topological `A`-module `V` on which a
family `φ : ι → V →L[A] M` separates points inherits the canonical `A`-module topology
(`TauCeti.Huber.isModuleTopology_of_forall_apply_eq_zero`), is closed in `V` whenever `V` is
Hausdorff (`TauCeti.Huber.isClosed_of_forall_apply_eq_zero`), and is complete whenever `V` is a
uniform additive group (`TauCeti.Huber.completeSpace_of_forall_apply_eq_zero`), with no
completeness or metrizability assumption on `V`.

The proof follows Buzzard, *Eigenvarieties*, Lemma 2.3, extended to Banach–Tate rings as in
Johansson–Newton, §2.1:

1. By `TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero` (Buzzard, Lemma 2.2), finitely many
   functionals `φ i` (`i ∈ S`) already separate points of `P`, reducing to a single continuous
   linear map `f : V →L[A] (S → M)` injective on `P`.
2. In the finite product `S → M`, the image `Q` of `P` is closed by
   `TauCeti.Huber.isClosed_of_isNoetherian`, hence complete, metrisable, and Baire, so `Q` carries
   the canonical module topology by `TauCeti.Huber.IsTateRing.isModuleTopology`.
3. Every `A`-linear map out of `Q` into a topological `A`-module is therefore continuous
   (`IsModuleTopology.continuous_of_linearMap`). Applied to the algebraic inverse `Q →ₗ[A] P`, this
   identifies `P` topologically with `Q` and exhibits `P` inside the closed preimage `f ⁻¹' Q` as
   the fixed locus of a continuous retraction into the Hausdorff ambient space `V`.

## Main results

* `TauCeti.Huber.isModuleTopology_of_apply_eq_zero`,
  `TauCeti.Huber.isClosed_of_apply_eq_zero`,
  `TauCeti.Huber.completeSpace_of_apply_eq_zero`: module topology, closedness, and completeness of
  a module-finite submodule injected by a single continuous linear map into a complete Hausdorff
  first-countable Noetherian `A`-module.
* `TauCeti.Huber.isModuleTopology_of_forall_apply_eq_zero`,
  `TauCeti.Huber.isClosed_of_forall_apply_eq_zero`,
  `TauCeti.Huber.completeSpace_of_forall_apply_eq_zero`: the corresponding statements for an
  arbitrary family of continuous linear maps separating points of the submodule.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, London Math. Soc.
  Lecture Note Ser. 320 (2007), Lemmas 2.2–2.3.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra
  Number Theory 13 (2019), §2.1.
* T. Wedhorn, *Adic Spaces*, Propositions 6.17–6.18.
-/

public section

open Topology
open scoped Uniformity

namespace TauCeti.Huber

section SingleMap

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T0Space A] [IsTopologicalRing A] [IsTateRing A]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [FirstCountableTopology M] [T0Space M] [Module A M] [ContinuousSMul A M] [IsNoetherian A M]
  {V : Type*} [AddCommGroup V] [Module A V]

/-- Restricting a continuous linear map `f : V →L[A] M` that is injective on a module-finite
submodule `P` identifies `P` topologically with its image in `M`. -/
private noncomputable def continuousLinearEquivRangeDomRestrict [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P]
    (f : V →L[A] M) (hf : ∀ p ∈ P, f p = 0 → p = 0) :
    P ≃L[A] LinearMap.range (f.toLinearMap.domRestrict P) := by
  have : (𝓤 M).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  set g : P →ₗ[A] M := f.toLinearMap.domRestrict P
  have hg : Function.Injective g :=
    (injective_iff_map_eq_zero g).2 fun p hp ↦ Subtype.ext (hf p.1 p.2 hp)
  have hQ_closed : IsClosed (LinearMap.range g : Set M) :=
    isClosed_of_isNoetherian (LinearMap.range g)
  have : CompleteSpace (LinearMap.range g) := hQ_closed.completeSpace_coe
  have : IsModuleTopology A (LinearMap.range g) :=
    IsTateRing.isModuleTopology (A := A) (M := LinearMap.range g)
  let e : P ≃ₗ[A] LinearMap.range g := LinearEquiv.ofInjective g hg
  exact
    { e with
      continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

@[simp]
private theorem continuousLinearEquivRangeDomRestrict_coe [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P]
    (f : V →L[A] M) (hf : ∀ p ∈ P, f p = 0 → p = 0) (p : P) :
    (continuousLinearEquivRangeDomRestrict P f hf p : M) = f p.1 := (rfl)

/-- A module-finite submodule injected by a continuous linear map into a complete Hausdorff
first-countable Noetherian module over a complete Hausdorff Tate ring carries the canonical module
topology. -/
theorem isModuleTopology_of_apply_eq_zero [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P] (f : V →L[A] M)
    (hf : ∀ p ∈ P, f p = 0 → p = 0) : IsModuleTopology A P := by
  have : (𝓤 M).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  set g : P →ₗ[A] M := f.toLinearMap.domRestrict P
  have : CompleteSpace (LinearMap.range g) := (isClosed_of_isNoetherian _).completeSpace_coe
  have : IsModuleTopology A (LinearMap.range g) :=
    IsTateRing.isModuleTopology (A := A) (M := LinearMap.range g)
  exact IsModuleTopology.iso (continuousLinearEquivRangeDomRestrict P f hf).symm

/-- A module-finite submodule of a Hausdorff topological module over a complete Hausdorff Tate ring
is closed whenever some continuous linear map into a complete Hausdorff first-countable Noetherian
module is injective on it. -/
theorem isClosed_of_apply_eq_zero [TopologicalSpace V] [ContinuousAdd V] [T2Space V]
    [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P] (f : V →L[A] M)
    (hf : ∀ p ∈ P, f p = 0 → p = 0) : IsClosed (P : Set V) := by
  have : (𝓤 M).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let e := continuousLinearEquivRangeDomRestrict P f hf
  have he_coe (p : P) : (e p : M) = f p.1 := continuousLinearEquivRangeDomRestrict_coe P f hf p
  let Q : Submodule A M := LinearMap.range (f.toLinearMap.domRestrict P)
  have hQ : IsClosed (Q : Set M) := isClosed_of_isNoetherian Q
  have hW : IsClosed (f ⁻¹' (Q : Set M)) := hQ.preimage f.continuous
  let r : f ⁻¹' (Q : Set M) → V := fun w ↦ (e.symm ⟨f w.1, w.2⟩ : V)
  have hr : Continuous r :=
    continuous_subtype_val.comp <|
      e.symm.continuous.comp ((f.continuous.comp continuous_subtype_val).subtype_mk _)
  have hZ : IsClosed {w : f ⁻¹' (Q : Set M) | r w = w.1} :=
    isClosed_eq hr continuous_subtype_val
  convert hW.isClosedEmbedding_subtypeVal.isClosedMap _ hZ using 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, Set.mem_preimage, SetLike.mem_coe]
  refine ⟨fun hv ↦ ⟨v, ⟨⟨v, hv⟩, rfl⟩, ?_, rfl⟩, ?_⟩
  · have hfe : (⟨f v, ⟨⟨v, hv⟩, rfl⟩⟩ : Q) = e ⟨v, hv⟩ := Subtype.ext (he_coe ⟨v, hv⟩).symm
    exact congrArg Subtype.val (hfe ▸ e.symm_apply_apply ⟨v, hv⟩)
  · rintro ⟨w, hfw, hrw, rfl⟩
    exact hrw ▸ (e.symm ⟨f w, hfw⟩).2

/-- A module-finite submodule of a uniform additive group module over a complete Hausdorff Tate
ring is complete whenever some continuous linear map into a complete Hausdorff first-countable
Noetherian module is injective on it. Completeness of the ambient module is not needed. -/
theorem completeSpace_of_apply_eq_zero [UniformSpace V] [IsUniformAddGroup V]
    [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P] (f : V →L[A] M)
    (hf : ∀ p ∈ P, f p = 0 → p = 0) : CompleteSpace P := by
  have : (𝓤 M).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let e := continuousLinearEquivRangeDomRestrict P f hf
  have : CompleteSpace (LinearMap.range (f.toLinearMap.domRestrict P)) :=
    (isClosed_of_isNoetherian _).completeSpace_coe
  have he : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr he).1 inferInstance

end SingleMap

section Family

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T0Space A] [IsTopologicalRing A] [IsTateRing A]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [FirstCountableTopology M] [T0Space M] [Module A M] [ContinuousSMul A M] [IsNoetherian A M]
  {V : Type*} [AddCommGroup V] [Module A V]

/-- **Canonical module topology from separating functionals** (Buzzard, *Eigenvarieties*,
Lemma 2.3): a module-finite submodule on which a family of continuous linear maps into a complete
Hausdorff first-countable Noetherian module separates points carries the canonical module topology.
-/
theorem isModuleTopology_of_forall_apply_eq_zero [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P] {ι : Type*}
    (φ : ι → V →L[A] M) (hφ : ∀ p ∈ P, (∀ i, φ i p = 0) → p = 0) :
    IsModuleTopology A P := by
  obtain ⟨S, hS⟩ := TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero
    (fun i : ι ↦ (φ i).toLinearMap.domRestrict P) (fun p hp ↦ Subtype.ext (hφ p.1 p.2 hp))
  exact isModuleTopology_of_apply_eq_zero P (ContinuousLinearMap.pi fun i : S ↦ φ i.1)
    fun p hp hpS ↦ congrArg Subtype.val <| hS ⟨p, hp⟩ fun i hi ↦ congrFun hpS ⟨i, hi⟩

/-- **Closedness of finite submodules from separating functionals** (Buzzard, *Eigenvarieties*,
Lemma 2.3): in a Hausdorff topological module over a complete Hausdorff Tate ring, any
module-finite submodule on which a family of continuous linear maps into a complete Hausdorff
first-countable Noetherian module separates points is closed. -/
theorem isClosed_of_forall_apply_eq_zero [TopologicalSpace V] [ContinuousAdd V] [T2Space V]
    [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P] {ι : Type*}
    (φ : ι → V →L[A] M) (hφ : ∀ p ∈ P, (∀ i, φ i p = 0) → p = 0) :
    IsClosed (P : Set V) := by
  obtain ⟨S, hS⟩ := TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero
    (fun i : ι ↦ (φ i).toLinearMap.domRestrict P) (fun p hp ↦ Subtype.ext (hφ p.1 p.2 hp))
  exact isClosed_of_apply_eq_zero P (ContinuousLinearMap.pi fun i : S ↦ φ i.1)
    fun p hp hpS ↦ congrArg Subtype.val <| hS ⟨p, hp⟩ fun i hi ↦ congrFun hpS ⟨i, hi⟩

/-- **Completeness of finite submodules from separating functionals**: in a uniform additive group
module over a complete Hausdorff Tate ring, any module-finite submodule on which a family of
continuous linear maps into a complete Hausdorff first-countable Noetherian module separates points
is complete, without assuming completeness of the ambient module. -/
theorem completeSpace_of_forall_apply_eq_zero [UniformSpace V] [IsUniformAddGroup V]
    [ContinuousSMul A V] (P : Submodule A V) [Module.Finite A P] {ι : Type*}
    (φ : ι → V →L[A] M) (hφ : ∀ p ∈ P, (∀ i, φ i p = 0) → p = 0) :
    CompleteSpace P := by
  obtain ⟨S, hS⟩ := TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero
    (fun i : ι ↦ (φ i).toLinearMap.domRestrict P) (fun p hp ↦ Subtype.ext (hφ p.1 p.2 hp))
  exact completeSpace_of_apply_eq_zero P (ContinuousLinearMap.pi fun i : S ↦ φ i.1)
    fun p hp hpS ↦ congrArg Subtype.val <| hS ⟨p, hp⟩ fun i hi ↦ congrFun hpS ⟨i, hi⟩

end Family

end TauCeti.Huber
