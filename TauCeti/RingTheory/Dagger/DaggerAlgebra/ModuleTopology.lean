/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Continuity
public import TauCeti.Topology.Algebra.Module.ModuleTopology

import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Pi
import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.Analysis.Normed.Module.Finite.QuotientNorm
import TauCeti.LinearAlgebra.TensorProduct.Kernel
import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.Noetherian
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism
import TauCeti.Topology.Algebra.Ring.Basic

/-!
# Canonical module topology over dagger algebras

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra equipped
with its canonical topology (the topology induced by `toCompletion K A : A → completion K A`, or
equivalently by any Monsky–Washnitzer presentation residue norm). Because `A` is in general not
complete, Henkel's open mapping theorem and completeness-based closedness criteria for finite
modules over Tate rings do not apply directly over `A`.

Following Grosse-Klönne (§1.11), we compare a finite `A`-module `M` carrying `moduleTopology A M`
with its scalar extension `completion K A ⊗[A] M` carrying `moduleTopology (completion K A) _`:

* **Faithfully flat dense embedding.** For any `A`-module `M`, the map
  `toCompletionTensor K A M : m ↦ 1 ⊗ₜ m` is injective (`toCompletionTensor_injective`, by faithful
  flatness of `A → completion K A`) and has dense image (`denseRange_toCompletionTensor`). When `M`
  is finitely generated over `A`, a presentation `Aʳ ↠ M` identifies `M` and `completion K A ⊗[A] M`
  with normed additive-group quotients whose kernels satisfy `closure (f '' ker q) = ker q'`, making
  `toCompletionTensor K A M` a topological embedding (`isEmbedding_toCompletionTensor`).
* **Separation, closed submodules, subspace topology, and strictness.** Pulling back the complete
  noetherian Tate module theory on `completion K A ⊗[A] M` along `isEmbedding_toCompletionTensor`
  shows `M` is Hausdorff (`t2Space_of_isModuleTopology`), every submodule with finitely generated
  quotient is closed (`isClosed_submodule_of_isModuleTopology`), every submodule of a finite module
  carries the `A`-module topology as its subspace topology (`isModuleTopology_submodule`), and every
  `A`-linear map from a module with the `A`-module topology into a finite `A`-module is strict
  (`isStrictMap_of_linearMap`).

## Main definitions

* `TauCeti.Dagger.toCompletionTensor`: the canonical `A`-linear map
  `M →ₗ[A] completion K A ⊗[A] M` sending `m` to `1 ⊗ₜ[A] m`.

## Main results

* `TauCeti.Dagger.toCompletionTensor_injective`, `TauCeti.Dagger.denseRange_toCompletionTensor`, and
  `TauCeti.Dagger.isEmbedding_toCompletionTensor`.
* `TauCeti.Dagger.t2Space_of_isModuleTopology`,
  `TauCeti.Dagger.isClosed_submodule_of_isModuleTopology`,
  `TauCeti.Dagger.isModuleTopology_submodule`, and `TauCeti.Dagger.isStrictMap_of_linearMap`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.11.
-/

public section

open scoped TensorProduct

namespace TauCeti.Dagger

section AlgebraAndMap

variable (K A M : Type*) [NormedField K] [IsUltrametricDist K]
  [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [AddCommGroup M] [Module A M]

/-- The canonical `A`-linear map `M →ₗ[A] completion K A ⊗[A] M` sending `m` to `1 ⊗ₜ[A] m`. -/
noncomputable def toCompletionTensor :
    letI := completionAlgebra K A
    M →ₗ[A] completion K A ⊗[A] M :=
  letI := completionAlgebra K A
  TensorProduct.mk A (completion K A) M 1

variable {K A M}

@[simp↓]
theorem toCompletionTensor_apply (m : M) :
    letI := completionAlgebra K A
    toCompletionTensor K A M m = 1 ⊗ₜ[A] m := (rfl)

/-- For any `A`-module `M`, `toCompletionTensor K A M` has dense image in `completion K A ⊗[A] M`
equipped with the `completion K A`-module topology. -/
theorem denseRange_toCompletionTensor :
    letI := completionAlgebra K A
    letI : TopologicalSpace (completion K A ⊗[A] M) :=
      moduleTopology (completion K A) (completion K A ⊗[A] M)
    DenseRange (toCompletionTensor K A M) :=
  letI := completionAlgebra K A
  letI : TopologicalSpace (completion K A ⊗[A] M) :=
    moduleTopology (completion K A) (completion K A ⊗[A] M)
  by
    have : IsModuleTopology (completion K A) (completion K A ⊗[A] M) := ⟨rfl⟩
    have : IsTopologicalAddGroup (completion K A ⊗[A] M) :=
      IsModuleTopology.isTopologicalAddGroup (completion K A) (completion K A ⊗[A] M)
    let H0 := (LinearMap.range (toCompletionTensor K A M)).toAddSubgroup
    let H := H0.topologicalClosure
    intro z
    rw [← LinearMap.coe_range, ← Submodule.coe_toAddSubgroup, ← AddSubgroup.topologicalClosure_coe]
    refine TensorProduct.inductionOn z (fun x m ↦ ?_) fun _ _ ↦ H.add_mem
    let L : completion K A →ₗ[completion K A] completion K A ⊗[A] M :=
      LinearMap.toSpanSingleton (completion K A) (completion K A ⊗[A] M) (1 ⊗ₜ[A] m)
    have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
    have hmem : Set.range (toCompletion K A) ⊆ L ⁻¹' (H : Set (completion K A ⊗[A] M)) := by
      rintro _ ⟨a, rfl⟩
      simp only [Set.mem_preimage, SetLike.mem_coe, L, LinearMap.toSpanSingleton_apply,
        ← algebraMap_completionAlgebra_apply, algebraMap_smul, ← toCompletionTensor_apply,
        ← map_smul]
      exact AddSubgroup.le_topologicalClosure H0 ⟨a • m, rfl⟩
    have hLx : L x = x ⊗ₜ[A] m := by simp [L, TensorProduct.smul_tmul']
    rw [← hLx]
    exact closure_minimal hmem (H0.isClosed_topologicalClosure.preimage hL)
      (denseRange_toCompletion x)

end AlgebraAndMap

section GeneralModule

variable {K A M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [AddCommGroup M] [Module A M]

/-- For any `A`-module `M`, `toCompletionTensor K A M : M → completion K A ⊗[A] M` is injective. -/
theorem toCompletionTensor_injective :
    letI := completionAlgebra K A
    Function.Injective (toCompletionTensor K A M) :=
  letI := completionAlgebra K A
  haveI := faithfullyFlat_completionAlgebra (K := K) (A := A)
  Module.FaithfullyFlat.tensorProduct_mk_injective M

end GeneralModule

section FiniteModule

variable {K A M N : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

private noncomputable def piBaseChange {r : ℕ} (q : (Fin r → A) →ₗ[A] M) :
    letI := completionAlgebra K A
    (Fin r → completion K A) →ₗ[completion K A] completion K A ⊗[A] M :=
  letI := completionAlgebra K A
  q.baseChange (completion K A) ∘ₗ
    (TensorProduct.piScalarRight A (completion K A) (completion K A) (Fin r)).symm.toLinearMap

omit [CompleteSpace K] in
private theorem ker_piBaseChange_eq_span {r : ℕ} (q : (Fin r → A) →ₗ[A] M)
    (hq : Function.Surjective q) :
    letI := completionAlgebra K A
    LinearMap.ker (piBaseChange (K := K) q) =
      Submodule.span (completion K A)
        (algebraMap (Fin r → A) (Fin r → completion K A) '' (LinearMap.ker q : Set _)) :=
  letI := completionAlgebra K A
  by
    have hker := LinearMap.ker_baseChange_of_surjective (completion K A) q hq
    ext v
    rw [piBaseChange, LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, hker,
      Submodule.baseChange_eq_span, LinearEquiv.coe_toLinearMap,
      ← Submodule.mem_map_equiv
        (e := TensorProduct.piScalarRight A (completion K A) (completion K A) (Fin r)),
      Submodule.map_span]
    suffices h : ⇑(TensorProduct.piScalarRight A (completion K A) (completion K A) (Fin r)) ''
          ((LinearMap.ker q).map (TensorProduct.mk A (completion K A) (Fin r → A) 1) : Set _) =
        algebraMap (Fin r → A) (Fin r → completion K A) '' (LinearMap.ker q : Set _) by
      rw [LinearEquiv.coe_coe, h]
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr fun u _ ↦
      (LinearEquiv.eq_symm_apply _).mp
        (TensorProduct.piScalarRight_symm_algebraMap A (completion K A) (Fin r) u).symm

omit [CompleteSpace K] in
private theorem span_image_le_closure_image {r : ℕ} (S : Submodule A (Fin r → A)) :
    letI := completionAlgebra K A
    (Submodule.span (completion K A)
        (algebraMap (Fin r → A) (Fin r → completion K A) '' (S : Set (Fin r → A))) :
        Set (Fin r → completion K A)) ⊆
      closure (algebraMap (Fin r → A) (Fin r → completion K A) '' (S : Set (Fin r → A))) :=
  letI := completionAlgebra K A
  by
    let f := algebraMap (Fin r → A) (Fin r → completion K A)
    let H0 := S.toAddSubgroup.map f.toAddMonoidHom
    let H := H0.topologicalClosure
    have hH_cl : IsClosed (H : Set (Fin r → completion K A)) := H0.isClosed_topologicalClosure
    have hH0_eq : (H0 : Set (Fin r → completion K A)) = f '' (S : Set (Fin r → A)) := by
      rw [AddSubgroup.coe_map, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
        Submodule.coe_toAddSubgroup]
    have hH_eq : (H : Set (Fin r → completion K A)) = closure (f '' (S : Set (Fin r → A))) := by
      rw [AddSubgroup.topologicalClosure_coe, hH0_eq]
    rw [← hH_eq]
    intro x hx
    refine Submodule.span_induction
      (fun y hy ↦ AddSubgroup.le_topologicalClosure H0 (SetLike.mem_coe.mp (hH0_eq.symm ▸ hy)))
      H.zero_mem (fun _ _ _ _ ↦ H.add_mem) (fun c y _ hy ↦ ?_) hx
    have hsmul_img : f '' (S : Set (Fin r → A)) ⊆ (c • ·) ⁻¹' (H : Set _) := by
      rintro _ ⟨u, hu, rfl⟩
      have hcont : Continuous (fun d : completion K A ↦ d • f u) :=
        continuous_smul.comp (.prodMk continuous_id continuous_const)
      have hd : Set.range (toCompletion K A) ⊆
          (fun d : completion K A ↦ d • f u) ⁻¹' (H : Set _) := by
        rintro _ ⟨a, rfl⟩
        have heq : f (a • u) = toCompletion K A a • f u :=
          funext fun i ↦ map_mul (toCompletion K A) a (u i)
        rw [Set.mem_preimage, SetLike.mem_coe, ← heq]
        exact AddSubgroup.le_topologicalClosure H0 ⟨a • u, S.smul_mem a hu, rfl⟩
      exact closure_minimal hd (hH_cl.preimage hcont) (denseRange_toCompletion c)
    exact closure_minimal hsmul_img (hH_cl.preimage (continuous_const_smul c)) (hH_eq ▸ hy)

private theorem closure_image_ker_eq_ker_piBaseChange {r : ℕ} (q : (Fin r → A) →ₗ[A] M)
    (hq : Function.Surjective q) :
    letI := completionAlgebra K A
    closure (algebraMap (Fin r → A) (Fin r → completion K A) ''
        (LinearMap.ker q : Set (Fin r → A))) =
      (LinearMap.ker (piBaseChange (K := K) q) : Set (Fin r → completion K A)) :=
  letI := completionAlgebra K A
  by
    have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
    have := Huber.IsTateRing.of_normedAlgebra K (completion K A)
    have : (uniformity (completion K A)).IsCountablyGenerated :=
      EMetric.instIsCountablyGeneratedUniformity
    have hker_closed :
        IsClosed (LinearMap.ker (piBaseChange (K := K) q) : Set (Fin r → completion K A)) :=
      Huber.isClosed_of_isNoetherian (LinearMap.ker (piBaseChange (K := K) q))
    have hker_eq := ker_piBaseChange_eq_span (K := K) q hq
    refine Set.Subset.antisymm (closure_minimal ?_ hker_closed) ?_
    · rw [hker_eq]
      exact Submodule.subset_span
    · rw [hker_eq]
      exact span_image_le_closure_image (K := K) (LinearMap.ker q)

private theorem isEmbedding_toCompletionTensor_residue [Module.Finite A M] :
    letI := residueNormedCommRing K A
    letI := completionAlgebra K A
    letI : TopologicalSpace M := moduleTopology A M
    letI : TopologicalSpace (completion K A ⊗[A] M) :=
      moduleTopology (completion K A) (completion K A ⊗[A] M)
    Topology.IsEmbedding (toCompletionTensor K A M) :=
  letI := residueNormedCommRing K A
  letI := completionAlgebra K A
  letI : TopologicalSpace M := moduleTopology A M
  letI : TopologicalSpace (completion K A ⊗[A] M) :=
    moduleTopology (completion K A) (completion K A ⊗[A] M)
  by
    have : IsModuleTopology A M := ⟨rfl⟩
    have : IsModuleTopology (completion K A) (completion K A ⊗[A] M) := ⟨rfl⟩
    have : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
    have : IsTopologicalAddGroup (completion K A ⊗[A] M) :=
      IsModuleTopology.isTopologicalAddGroup (completion K A) (completion K A ⊗[A] M)
    obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' A M
    let q' : (Fin r → completion K A) →ₗ[completion K A] completion K A ⊗[A] M :=
      piBaseChange (K := K) q
    have hq' : Function.Surjective q' :=
      (LinearMap.lTensor_surjective (completion K A) hq).comp
        (TensorProduct.piScalarRight A (completion K A) (completion K A) (Fin r)).symm.surjective
    let f := algebraMap (Fin r → A) (Fin r → completion K A)
    have hf_iso : Isometry f := Isometry.postcomp_pi (α := Fin r) (isometry_toCompletion K A)
    have hqf (v : Fin r → A) : q' (f v) = toCompletionTensor K A M (q v) := by
      simp [q', piBaseChange, f, TensorProduct.piScalarRight_symm_algebraMap]
    have hcl := closure_image_ker_eq_ker_piBaseChange (K := K) q hq
    exact ⟨TauCeti.isInducing_of_openQuotient_isometry q
        (IsModuleTopology.isOpenQuotientMap_of_surjective hq) q'
        (IsModuleTopology.isOpenQuotientMap_of_surjective hq')
        f hf_iso (toCompletionTensor K A M) hqf hcl.symm.subset,
      toCompletionTensor_injective (K := K) (A := A)⟩

/-- **Faithfully flat topological embedding for finite modules** (Grosse-Klönne, §1.11). If `A`
carries the topology induced from `toCompletion K A`, then for every finite `A`-module `M`,
`toCompletionTensor K A M : M → completion K A ⊗[A] M` is a topological embedding for the canonical
module topologies. -/
theorem isEmbedding_toCompletionTensor [Module.Finite A M] [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    [TopologicalSpace M] [IsModuleTopology A M] :
    letI := completionAlgebra K A
    letI : TopologicalSpace (completion K A ⊗[A] M) :=
      moduleTopology (completion K A) (completion K A ⊗[A] M)
    Topology.IsEmbedding (toCompletionTensor K A M) :=
  letI := completionAlgebra K A
  letI : TopologicalSpace (completion K A ⊗[A] M) :=
    moduleTopology (completion K A) (completion K A ⊗[A] M)
  by
    have hτM : ‹TopologicalSpace M› = moduleTopology A M := eq_moduleTopology A M
    subst hτM
    have hτA : ‹TopologicalSpace A› =
        (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace :=
      hA.eq_induced.trans (residueNormedCommRing_toTopologicalSpace_eq_induced K A).symm
    subst hτA
    exact isEmbedding_toCompletionTensor_residue (K := K) (A := A) (M := M)

/-- **Finite modules over a dagger algebra are Hausdorff** in their canonical module topology
(Grosse-Klönne, §1.11). -/
theorem t2Space_of_isModuleTopology [Module.Finite A M] [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    [TopologicalSpace M] [IsModuleTopology A M] : T2Space M :=
  letI := completionAlgebra K A
  letI : TopologicalSpace (completion K A ⊗[A] M) :=
    moduleTopology (completion K A) (completion K A ⊗[A] M)
  by
    have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
    have := Huber.IsTateRing.of_normedAlgebra K (completion K A)
    have : T2Space (completion K A ⊗[A] M) :=
      Huber.IsTateRing.t2Space_moduleTopology (A := completion K A) (M := completion K A ⊗[A] M)
    exact (isEmbedding_toCompletionTensor hA).t2Space

/-- **Every submodule with finitely generated quotient over a dagger algebra is closed** in the
canonical module topology (Grosse-Klönne, §1.11). -/
theorem isClosed_submodule_of_isModuleTopology [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    [TopologicalSpace M] [IsModuleTopology A M] (P : Submodule A M) [Module.Finite A (M ⧸ P)] :
    IsClosed (P : Set M) := by
  have : T2Space (M ⧸ P) := t2Space_of_isModuleTopology hA
  have : ContinuousAdd (M ⧸ P) := IsModuleTopology.toContinuousAdd A (M ⧸ P)
  have hP : (P : Set M) = P.mkQ ⁻¹' {0} := by ext x; simp [Submodule.Quotient.mk_eq_zero]
  rw [hP]
  exact isClosed_singleton.preimage (IsModuleTopology.continuous_of_linearMap P.mkQ)

private theorem isEmbedding_baseChange_of_injective [Module.Finite A M] {Q : Type*}
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] (j : Q →ₗ[A] M)
    (hj : Function.Injective j) :
    letI := completionAlgebra K A
    letI : TopologicalSpace (completion K A ⊗[A] Q) :=
      moduleTopology (completion K A) (completion K A ⊗[A] Q)
    letI : TopologicalSpace (completion K A ⊗[A] M) :=
      moduleTopology (completion K A) (completion K A ⊗[A] M)
    Topology.IsEmbedding (j.baseChange (completion K A)) :=
  letI := completionAlgebra K A
  by
    have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
    have := Huber.IsTateRing.of_normedAlgebra K (completion K A)
    -- `synthInstance` cannot synthesize `(uniformity (completion K A)).IsCountablyGenerated`
    -- directly on the Tate quotient `T_n ⧸ I T_n`, so we supply it via `EMetric`.
    have : (uniformity (completion K A)).IsCountablyGenerated :=
      EMetric.instIsCountablyGeneratedUniformity
    have : Module.FaithfullyFlat A (completion K A) :=
      faithfullyFlat_completionAlgebra (K := K) (A := A)
    have hj' : Function.Injective (j.baseChange (completion K A)) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap j hj
    obtain ⟨pQ, _, _, _, hMQ⟩ :=
      exists_complete_norm_of_module_finite (completion K A) (completion K A ⊗[A] Q)
    obtain ⟨pM, _, _, _, hMM⟩ :=
      exists_complete_norm_of_module_finite (completion K A) (completion K A ⊗[A] M)
    let _ := pQ.toNormedAddCommGroup
    let _ := pM.toNormedAddCommGroup
    have hstrict : Topology.IsStrictMap (j.baseChange (completion K A)) :=
      LinearMap.isStrictMap_of_module_finite _
    have hemb : Topology.IsEmbedding (j.baseChange (completion K A)) :=
      Topology.isEmbedding_iff_isStrictMap_injective.mpr ⟨hstrict, hj'⟩
    rwa [hMQ.eq_moduleTopology', hMM.eq_moduleTopology'] at hemb

/-- **Every submodule of a finite module over a dagger algebra carries the `A`-module topology** as
its subspace topology (Grosse-Klönne, §1.11). -/
theorem isModuleTopology_submodule [Module.Finite A M] [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    [TopologicalSpace M] [IsModuleTopology A M] (P : Submodule A M) :
    IsModuleTopology A P :=
  letI := completionAlgebra K A
  by
    have : IsTopologicalRing A := Topology.IsInducing.isTopologicalRing (toCompletion K A) hA
    have : IsNoetherianRing A := IsDaggerAlgebra.isNoetherianRing (K := K) (A := A)
    obtain ⟨s, p, hp⟩ := Module.Finite.exists_fin' A P
    let Q := (Fin s → A) ⧸ LinearMap.ker p
    let eP : Q ≃ₗ[A] P := p.quotKerEquivOfSurjective hp
    let j : Q →ₗ[A] M := P.subtype ∘ₗ eP.toLinearMap
    have hj : Function.Injective j := P.subtype_injective.comp eP.injective
    let _ : TopologicalSpace (completion K A ⊗[A] Q) :=
      moduleTopology (completion K A) (completion K A ⊗[A] Q)
    let _ : TopologicalSpace (completion K A ⊗[A] M) :=
      moduleTopology (completion K A) (completion K A ⊗[A] M)
    have hembQ := isEmbedding_toCompletionTensor (K := K) (A := A) (M := Q) hA
    have hembM := isEmbedding_toCompletionTensor (K := K) (A := A) (M := M) hA
    have hemb_bc := isEmbedding_baseChange_of_injective (K := K) j hj
    have hcomm : (j.baseChange (completion K A) ∘ toCompletionTensor K A Q :
        Q → completion K A ⊗[A] M) = toCompletionTensor K A M ∘ j := by ext x; rfl
    have hemb_j : Topology.IsEmbedding j := hembM.of_comp_iff.mp (hcomm ▸ hemb_bc.comp hembQ)
    have hemb_eP : Topology.IsEmbedding eP := Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hemb_j
    exact IsModuleTopology.iso
      (ContinuousLinearEquiv.ofIsHomeomorph eP
        (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hemb_eP, eP.surjective⟩))

/-- **Every `A`-linear map from a module with the `A`-module topology into a finite module over a
dagger algebra is strict** (Grosse-Klönne, §1.11). -/
theorem isStrictMap_of_linearMap [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    [TopologicalSpace M] [IsModuleTopology A M]
    [TopologicalSpace N] [IsModuleTopology A N] (g : M →ₗ[A] N) :
    Topology.IsStrictMap g :=
  g.isStrictMap_of_isModuleTopology_range (isModuleTopology_submodule hA (LinearMap.range g))

end FiniteModule

/-! ### Edge-case checks -/

section Examples

-- Hausdorffness, closedness of ideals, and strictness of submodule inclusions hold on a nonreduced
-- dagger algebra `A = W_1 ⧸ (X_0 ^ 2)` equipped with its native quotient Gauss-norm topology.
example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    let W := washnitzerAlgebra (Fin 1) K
    let A := W ⧸ Ideal.span ({washnitzerAlgebra.X (Fin 1) K 0 ^ 2} : Set W)
    let J : Ideal A := Ideal.span {Ideal.Quotient.mk _ (washnitzerAlgebra.X (Fin 1) K 0)}
    T2Space A ∧ IsClosed (J : Set A) ∧ Topology.IsStrictMap J.subtype := by
  intro W A J
  have hA : Topology.IsInducing (toCompletion K A) :=
    (isEmbedding_toCompletion_quotient (K := K)
      (Ideal.span ({washnitzerAlgebra.X (Fin 1) K 0 ^ 2} : Set W))).isInducing
  have : IsModuleTopology A J := isModuleTopology_submodule hA J
  exact ⟨t2Space_of_isModuleTopology hA, isClosed_submodule_of_isModuleTopology hA J,
    isStrictMap_of_linearMap hA J.subtype⟩

end Examples

end TauCeti.Dagger
