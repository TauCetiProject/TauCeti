/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Bott.HessianMetric
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Topology.VectorBundle.Attachment
import TauCeti.Geometry.Manifold.Morse.Bott.ThomPair
import TauCeti.Geometry.Manifold.Morse.Deformation.Cohomology
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Topology.Maps.IsEmpty
import TauCeti.Topology.VectorBundle.DiscSphere
import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology

/-!
# Morse–Bott relative homology and cohomology via the Thom pair

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless finite-dimensional manifold, on the level `f = c` with constant Morse index `r`, and
let `g` be a smooth fibre metric on its normal bundle.

We equip the negative normal subbundle `ν⁻` with the continuous Hessian fibre metric `-½ Hessₛ`
(`TauCeti.Geometry.Manifold.Morse.Bott.HessianMetric`). For a Morse–Bott normal form `Θ` and
`ε > 0` with `D_ε ⊆ Θ.source`, rescaling the unit disc bundle `D(ν⁻)` by `√ε` yields
`f (Θ (√ε • v)) = c - ε ‖v‖²` (`IsNondegenerateCriticalSubmanifold.rescale_negativeDiscBundle`),
giving the explicit geometric attaching map `discSpherePairSublevelMap` from `(D(ν⁻), S(ν⁻))` to
`({f ≤ c + ε}, {f ≤ c - ε})`. Disc-bundle attachment
(`TauCeti.exists_isIso_of_homotopyRel_attach_discBundle`) and the deformation retraction
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`) show
that `discSpherePairSublevelMap` induces isomorphisms on both relative singular homology and
relative singular cohomology (`isIso_singularHomologyMap_discSpherePairSublevelMap`,
`isIso_singularCohomologyMap_discSpherePairSublevelMap`), hence identifying `({f ≤ c + ε},
{f ≤ c - ε})` with the Thom pair `(ν⁻, ν⁻₀)`. Regular-collar removal
(`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`,
`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue`) extends both the homology and
cohomology identifications to any compact isolated band `[a, b]` around `c` and to the cobordism
pair `(f⁻¹[a, b], f⁻¹(a))`, yielding vanishing below `r` and the `Subsingleton Kˣ` index-degree
isomorphism `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `discSpherePairSublevelMap` and `discSpherePairSublevelMap_fst_apply`: the attaching map
  `(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` given by `v ↦ Θ (√ε • v)`.
* `isIso_singularHomologyMap_discSpherePairSublevelMap` and
  `isIso_singularCohomologyMap_discSpherePairSublevelMap`: `discSpherePairSublevelMap` induces
  isomorphisms on relative singular homology and cohomology.
* `exists_singularHomology_sublevelPair_iso_thomPair` and
  `exists_singularCohomology_sublevelPair_iso_thomPair`: identification with the relative homology
  and cohomology of the Thom pair `(ν⁻, ν⁻₀)` across `[c - ε, c + ε]`.
* `nonempty_singularHomology_sublevelPair_iso_thomPair`,
  `nonempty_singularHomology_sublevelPair_iso_thomPair_of_preconnectedSpace`, and
  `nonempty_singularHomology_bandPair_iso_thomPair`: identification with `Hₙ(ν⁻, ν⁻₀; R)` on an
  arbitrary compact isolated band `[a, b]`.
* `nonempty_singularCohomology_sublevelPair_iso_thomPair`,
  `nonempty_singularCohomology_sublevelPair_iso_thomPair_of_preconnectedSpace`, and
  `nonempty_singularCohomology_bandPair_iso_thomPair`: the corresponding identifications in
  relative singular cohomology.
* `isZero_singularHomology_sublevelPair_of_lt_index` and
  `isZero_singularCohomology_sublevelPair_of_lt_index`: vanishing below the Morse index.
* `nonempty_singularHomology_sublevelPair_iso_singularHomology_zero`: in the index degree,
  `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)` for a ring with `Subsingleton Kˣ`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and §5.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.1 and 15.4.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Filter Function Limits Module Set Topology
open scoped ContDiff Manifold Bundle

universe u v w w'

namespace TauCeti

namespace SmoothEmbedding

namespace IsNondegenerateCriticalSubmanifold

/-! ### Disc-bundle attachment and Thom-pair comparison in homology and cohomology -/

section HomologyAttachment

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' : Type*} {S : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- The attaching map `(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induced by a Morse–Bott
normal form `Θ`, sending `v` to `Θ (√ε • v)`. -/
def discSpherePairSublevelMap
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (Θ : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {ε : ℝ} (hε : 0 < ε)
    (hDsub : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source) :
    letI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    letI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
        hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.snd‖) ⟶
      sublevelPair f (a := c - ε) (b := c + ε) (by linarith) := by
  letI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  letI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  letI := hV.fiberBundle
  letI := hV.vectorBundle
  letI : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.snd‖
  let scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
    fun v ↦ TotalSpace.mk' P v.proj (Real.sqrt ε • v.snd.val)
  have hres := h.rescale_negativeDiscBundle hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr hε
  have hscale_mem {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      scale v ∈ h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
    rw [← hres.2.2.2, discBundle_def]
    exact mem_image_of_mem scale hv
  have hf_val {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      f (Θ (scale v)) = c - ε * ‖v.snd‖ ^ 2 := by
    rw [hΘf (scale v) (hDsub (hscale_mem hv))]
    linarith [hres.2.2.1 v]
  have hmem₁ (v : gaugeDiscBundle ρ) : Θ (scale v.val) ∈ {y : M | f y ≤ c + ε} := by
    rw [mem_ofPred_eq, hf_val v.property]
    nlinarith [sq_nonneg ‖v.val.snd‖]
  have hmem₂ (v : gaugeSphereBundle ρ) : Θ (scale v.val) ∈ {y : M | f y ≤ c - ε} := by
    rw [mem_ofPred_eq, hf_val (gaugeSphereBundle_subset_gaugeDiscBundle ρ v.property)]
    have hv1 : ‖v.val.snd‖ = 1 := mem_gaugeSphereBundle.1 v.property
    rw [hv1]
    linarith
  exact TopPair.ofHom
    (TopCat.ofHom
      { toFun := fun v ↦ ⟨Θ (scale v.val), hmem₁ v⟩
        continuous_toFun := Continuous.subtype_mk
          (Θ.toOpenPartialHomeomorph.continuousOn.comp_continuous
            (hres.1.comp continuous_subtypeVal) fun v ↦ hDsub (hscale_mem v.property)) hmem₁ })
    (TopCat.ofHom
      { toFun := fun v ↦ ⟨Θ (scale v.val), hmem₂ v⟩
        continuous_toFun := Continuous.subtype_mk
          (Θ.toOpenPartialHomeomorph.continuousOn.comp_continuous
            (hres.1.comp continuous_subtypeVal)
            fun v ↦ hDsub (hscale_mem (gaugeSphereBundle_subset_gaugeDiscBundle ρ v.property)))
          hmem₂ })
    (TopCat.ext fun _ ↦ rfl)

/-- Evaluating `discSpherePairSublevelMap` on a vector `v` of the unit disc bundle gives
`Θ (√ε • v)`. -/
@[simp]
theorem discSpherePairSublevelMap_fst_apply
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (Θ : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {ε : ℝ} (hε : 0 < ε)
    (hDsub : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source)
    (v : haveI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
      haveI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
        (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
      letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
        subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
      letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
      letI : RiemannianBundle ν :=
        ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
          hr).toRiemannianMetric⟩
      letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
      gaugeDiscBundle (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.snd‖)) :
    (TopPair.Hom.fst (h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub) v).val =
      Θ (TotalSpace.mk' P v.val.proj (Real.sqrt ε • v.val.snd.val)) :=
  (rfl)

variable [T2Space M] [CompactSpace S]

/-- Combined homology and cohomology isomorphism for `discSpherePairSublevelMap`, using
`TauCeti.exists_isIso_of_homotopyRel_attach_discBundle`. -/
private theorem isIso_discSpherePairSublevelMap
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (Θ : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {ε : ℝ} (hε : 0 < ε)
    (hDsub : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source)
    (rdef : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      C(↥{y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
        ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))))
    (G : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ((ContinuousMap.inclusion inter_subset_left).comp rdef).HomotopyRel
        (ContinuousMap.id _) {y | (y : M) ∈
          {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε}) :
    (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ),
      IsIso (TopPair.singularHomologyMap
        (h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub) R m)) ∧
    (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
      (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ),
      IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M')
        (h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub) m)) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.snd‖
  let scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
    fun v ↦ TotalSpace.mk' P v.proj (Real.sqrt ε • v.snd.val)
  let attachMap : TotalSpace (Fin r → ℝ) ν → M := fun v ↦ Θ (scale v)
  have hres := h.rescale_negativeDiscBundle hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr hε
  have hscale_mem {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      scale v ∈ h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
    rw [← hres.2.2.2, discBundle_def]
    exact mem_image_of_mem scale hv
  have hf_val {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      f (attachMap v) = c - ε * ‖v.snd‖ ^ 2 := by
    dsimp only [attachMap]
    rw [hΘf (scale v) (hDsub (hscale_mem hv))]
    linarith [hres.2.2.1 v]
  have hρ : IsFiberGauge ρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  have hA : IsClosed {y : M | f y ≤ c - ε} := isClosed_le hfs.continuous continuous_const
  have hgD : attachMap '' gaugeDiscBundle ρ =
      Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
    change (Θ ∘ scale) '' gaugeDiscBundle ρ = _
    rw [image_comp, ← hres.2.2.2, discBundle_def]
  have hDT : Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ {y : M | f y ≤ c + ε} := by
    rw [← hgD]
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_ofPred_eq, hf_val hv]
    nlinarith [sq_nonneg ‖v.snd‖]
  have hg_cont : Continuous ((gaugeDiscBundle ρ).domRestrict attachMap) :=
    Θ.toOpenPartialHomeomorph.continuousOn.comp_continuous (hres.1.comp continuous_subtypeVal)
      fun v ↦ hDsub (hscale_mem v.property)
  have hg_emb : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict attachMap) := by
    have hD_eq : gaugeDiscBundle ρ = {p : TotalSpace (Fin r → ℝ) ν | ‖p.snd‖ ≤ 1} :=
      Set.ext fun _ ↦ mem_gaugeDiscBundle
    have : CompactSpace (gaugeDiscBundle ρ) :=
      isCompact_iff_compactSpace.mp (hD_eq ▸
        TauCeti.isCompact_setOf_norm_le_bundle (F := Fin r → ℝ) (V := ν) (r := fun _ ↦ 1)
          continuous_const)
    refine hg_cont.isClosedEmbedding fun v w hvw ↦ ?_
    exact Subtype.ext
      (hres.2.1 (Θ.injOn (hDsub (hscale_mem v.property)) (hDsub (hscale_mem w.property)) hvw))
  have hgA (v : TotalSpace (Fin r → ℝ) ν) (hv : v ∈ gaugeDiscBundle ρ) :
      attachMap v ∈ {y : M | f y ≤ c - ε} ↔ v ∈ gaugeSphereBundle ρ := by
    rw [mem_ofPred_eq, hf_val hv, mem_gaugeSphereBundle]
    have hv1 : ‖v.snd‖ ≤ 1 := mem_gaugeDiscBundle.1 hv
    have hv0 : 0 ≤ ‖v.snd‖ := norm_nonneg v.snd
    exact ⟨fun hle ↦ by
        dsimp only [ρ]
        have hsq_ge : 1 ≤ ‖v.snd‖ ^ 2 := by nlinarith
        nlinarith,
      fun heq ↦ by dsimp only [ρ] at heq; rw [heq]; linarith⟩
  have hrel : {y : {y | f y ≤ c + ε} | (y : M) ∈
      {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε} =
      {y : {y | f y ≤ c + ε} | (y : M) ∈ {y | f y ≤ c + ε} ∩
        ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)} :=
    Set.ext fun y ↦ ⟨fun hy ↦ ⟨y.property, hy⟩, fun hy ↦ hy.2⟩
  obtain ⟨ψ, hψ, hhom, hcohom⟩ := exists_isIso_of_homotopyRel_attach_discBundle.{u, w, v, _, w'}
    hρ (sublevel_mono f (by linarith)) hA hg_emb hgD hDT hgA rdef (hrel ▸ G)
  have hψ_eq : ψ = h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ Subtype.ext (hψ v))
  rw [← hψ_eq]
  exact ⟨fun R m ↦ hhom R m, fun R k _ _ M' m ↦ hcohom R k M' m⟩

/-- `discSpherePairSublevelMap` induces isomorphisms on relative singular homology. -/
theorem isIso_singularHomologyMap_discSpherePairSublevelMap
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (Θ : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {ε : ℝ} (hε : 0 < ε)
    (hDsub : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source)
    (rdef : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      C(↥{y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
        ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))))
    (G : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ((ContinuousMap.inclusion inter_subset_left).comp rdef).HomotopyRel
        (ContinuousMap.id _) {y | (y : M) ∈
          {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε})
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub) R m) :=
  (h.isIso_discSpherePairSublevelMap.{u, v, w, 0, _, _, _, _} hn hfs hdim g hr Θ hΘf hε hDsub
    rdef G).1 R m

/-- `discSpherePairSublevelMap` induces isomorphisms on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_discSpherePairSublevelMap
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (Θ : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {ε : ℝ} (hε : 0 < ε)
    (hDsub : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source)
    (rdef : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      C(↥{y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
        ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))))
    (G : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ((ContinuousMap.inclusion inter_subset_left).comp rdef).HomotopyRel
        (ContinuousMap.id _) {y | (y : M) ∈
          {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε})
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
    (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M')
      (h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub) m) :=
  (h.isIso_discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε hDsub rdef G).2 R k M' m

variable [SecondCountableTopology M] [J.Boundaryless]

/-- Existence of an isomorphism-inducing map `(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` for
small `ε > 0`, covering both empty and nonempty `S`. -/
private theorem exists_discSpherePairMap_isIso_sublevelPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
        hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∃ ψ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.snd‖) ⟶
          sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1]),
        (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ),
          IsIso (TopPair.singularHomologyMap ψ R m)) ∧
        (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
          (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ),
          IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ψ m)) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
    subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
  let : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  rcases isEmpty_or_nonempty S with hS | hS
  · refine ⟨1, one_pos, fun ε hε hcomp hcrit ↦ ?_⟩
    have hle : c - ε ≤ c + ε := by linarith [hε.1]
    have hreg : ∀ x, c - ε ≤ f x → f x ≤ c + ε → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x h₁ h₂ hx ↦ by
      obtain ⟨s, -⟩ := hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, h₁, h₂⟩
      exact isEmptyElim s
    obtain ⟨rdef, -, ⟨G⟩⟩ := exists_sublevelDeformation hfs hle hcomp hreg
    rw [sublevelInclusion_eq_inclusion] at G
    let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.snd‖
    let g_empty : TotalSpace (Fin r → ℝ) ν → M := fun v ↦ isEmptyElim v.proj
    have : IsEmpty (gaugeDiscBundle ρ) := ⟨fun v ↦ isEmptyElim v.val.proj⟩
    have hρ : IsFiberGauge ρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
    have hA : IsClosed {y : M | f y ≤ c - ε} := isClosed_le hfs.continuous continuous_const
    let r' : C(↥{y : M | f y ≤ c + ε},
        ↥({y : M | f y ≤ c + ε} ∩ ({y : M | f y ≤ c - ε} ∪ ∅))) :=
      (ContinuousMap.inclusion (subset_inter (sublevel_mono f hle) subset_union_left)).comp rdef
    have hincl : (ContinuousMap.inclusion inter_subset_left).comp r' =
        (ContinuousMap.inclusion (sublevel_mono f hle)).comp rdef :=
      ContinuousMap.ext fun _ ↦ rfl
    have hset₂ : {x : {y : M | f y ≤ c + ε} | (x : M) ∈ {y : M | f y ≤ c - ε}} =
        {x : {y : M | f y ≤ c + ε} | (x : M) ∈ {y : M | f y ≤ c - ε} ∪ ∅} := by
      rw [union_empty]
    have hg_emb : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g_empty) :=
      Topology.IsClosedEmbedding.of_isEmpty _
    have hgD : g_empty '' gaugeDiscBundle ρ = ∅ := by
      simp [eq_empty_of_isEmpty (gaugeDiscBundle ρ)]
    obtain ⟨ψ, -, hhom, hcohom⟩ := exists_isIso_of_homotopyRel_attach_discBundle.{u, w, v, _, w'}
      hρ (sublevel_mono f hle) hA hg_emb hgD
      (empty_subset _) (fun v ↦ isEmptyElim v.proj) r' (hincl ▸ hset₂ ▸ G)
    exact ⟨ψ, fun R m ↦ hhom R m, fun R k _ _ M' m ↦ hcohom R k M' m⟩
  · have : Nonempty S := hS
    obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hdef⟩ :=
      h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
    refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
    obtain ⟨hDsub, rdef, -, ⟨G⟩⟩ := hdef ε hε hcomp hcrit
    exact ⟨h.discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf hε.1 hDsub,
      fun R m ↦ h.isIso_singularHomologyMap_discSpherePairSublevelMap hn hfs hdim g hr Θ hΘf
        hε.1 hDsub rdef G R m,
      fun R k _ _ M' m ↦ h.isIso_singularCohomologyMap_discSpherePairSublevelMap hn hfs hdim g hr
        Θ hΘf hε.1 hDsub rdef G R k M' m⟩

/-- **Relative homology across a compact Morse–Bott submanifold equals that of the Thom pair
(small band).** For small `ε > 0` with compact band `f⁻¹[c - ε, c + ε]` whose critical points lie
on `i`, `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R) ≅ Hₙ(ν⁻, ν⁻₀; R)` in every degree, with coefficients in
any abelian category with coproducts. -/
theorem exists_singularHomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ),
        Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1])).singularHomology
            R m ≅
          (thomPair (Fin r → ℝ)
            (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  obtain ⟨ε₀, hε₀, hψ⟩ :=
    h.exists_discSpherePairMap_isIso_sublevelPair.{u, v, w, 0, _, _, _, _} hn hfs hc hdim g hr
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit {A} _ _ _ R m ↦ ?_⟩
  obtain ⟨ψ, hψH, -⟩ := hψ ε hε hcomp hcrit
  have hρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  have := hψH R m
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R m
  exact ⟨(asIso (TopPair.singularHomologyMap ψ R m)).symm ≪≫
    asIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R m)⟩

/-- **Relative cohomology across a compact Morse–Bott submanifold equals that of the Thom pair
(small band).** For small `ε > 0` with compact band `f⁻¹[c - ε, c + ε]` whose critical points lie
on `i`, `Hⁿ({f ≤ c + ε}, {f ≤ c - ε}; R, M') ≅ Hⁿ(ν⁻, ν⁻₀; R, M')` in every degree, with arbitrary
coefficients in any `k`-linear abelian category with coproducts. -/
theorem exists_singularCohomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
        (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ),
        Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1])).singularCohomology
            R k M' m ≅
          (thomPair (Fin r → ℝ)
            (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularCohomology
            R k M' m) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  obtain ⟨ε₀, hε₀, hψ⟩ := h.exists_discSpherePairMap_isIso_sublevelPair hn hfs hc hdim g hr
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit {A} _ _ _ R k _ _ M' m ↦ ?_⟩
  obtain ⟨ψ, -, hψC⟩ := hψ ε hε hcomp hcrit
  have hρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  have := hψC R k M' m
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R k M' m
  exact ⟨asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ψ m) ≪≫
    (asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M')
      (gaugeDiscSpherePairMap hρ) m)).symm⟩

/-! ### Arbitrary compact isolated bands and consequences -/

/-- **Relative homology across a compact Morse–Bott submanifold equals that of the Thom pair.**
Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, on the level `f = c` with constant Morse index `r`, and let `g` be a smooth
fibre metric on its normal bundle. For any compact band `f⁻¹[a, b]` with `a < c < b` whose
critical points all lie on `i`, `Hₙ({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(ν⁻, ν⁻₀; R)` in every degree, with
coefficients in any abelian category with coproducts. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hac : a < c) (hcb : c < b)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R m ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  obtain ⟨ε₀, hε₀, hsmall⟩ :=
    h.exists_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr
  set ε := min (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2))
  have hε_pos : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε_lt : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have haε : a ≤ c - ε := by
    linarith [min_le_right (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2)),
      min_le_left ((c - a) / 2) ((b - c) / 2)]
  have hεb : c + ε ≤ b := by
    linarith [min_le_right (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2)),
      min_le_right ((c - a) / 2) ((b - c) / 2)]
  have hsubIcc : Icc (c - ε) (c + ε) ⊆ Icc a b := Icc_subset_Icc haε hεb
  have hcompε : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) :=
    hcomp.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) (preimage_mono hsubIcc)
  have hcritε : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i :=
    (inter_subset_inter_right _ (preimage_mono hsubIcc)).trans hcrit
  obtain ⟨eThom⟩ := hsmall ε ⟨hε_pos, hε_lt⟩ hcompε hcritε R m
  have hval {s t : ℝ} (hcr : criticalPoints I f ∩ f ⁻¹' Icc s t ⊆ range i) :
      ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c := fun x hx hfx ↦ by
    obtain ⟨p, rfl⟩ := hcr ⟨hx, hfx⟩
    exact hc p
  exact ⟨singularHomologySublevelPairIsoOfCriticalValue hfs hac hcb (by linarith) (by linarith)
    hcomp hcompε (hval hcrit) (hval hcritε) R m ≪≫ eThom⟩

/-- **Relative homology across a connected compact Morse–Bott submanifold.** On a connected
compact Morse–Bott submanifold the Morse index is constant, so the relative homology of any
compact isolated band around its level is that of the Thom pair of its negative normal bundle of
rank `manifoldMorseIndex I f (i s₀)`. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {c a b : ℝ} (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)
    (s₀ : S) (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R m ≅
      (thomPair (Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) :=
  h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g
    (fun s ↦ (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀)
    hac hcb hcomp hcrit R m

/-- **Relative homology of a compact cobordism across a Morse–Bott submanifold.** Under the
hypotheses of `nonempty_singularHomology_sublevelPair_iso_thomPair`, the lower level `a` is
regular, so the band pair `(f⁻¹[a, b], f⁻¹(a))` also has the relative homology of the Thom pair
`(ν⁻, ν⁻₀)`. -/
theorem nonempty_singularHomology_bandPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hac : a < c) (hcb : c < b)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((bandPair f (hac.trans hcb).le).singularHomology R m ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have ha : IsRegularValue I 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hxc, hx⟩ ↦ by
      obtain ⟨s, rfl⟩ := hcrit ⟨hxc, le_of_eq hx.symm, hx.le.trans (hac.trans hcb).le⟩
      exact hac.ne (hx.symm.trans (hc s))
  have := isIso_singularHomologyMap_bandPairInclusion hfs (hac.trans hcb).le hcomp ha R m
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R m
  exact ⟨asIso (TopPair.singularHomologyMap (bandPairInclusion f (hac.trans hcb).le) R m) ≪≫ e⟩

/-- **Relative cohomology across a compact Morse–Bott submanifold equals that of the Thom pair.**
Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, on the level `f = c` with constant Morse index `r`, and let `g` be a smooth
fibre metric on its normal bundle. For any compact band `f⁻¹[a, b]` with `a < c < b` whose
critical points all lie on `i`, `Hⁿ({f ≤ b}, {f ≤ a}; R, M') ≅ Hⁿ(ν⁻, ν⁻₀; R, M')` in every
degree, with arbitrary coefficients in any `k`-linear abelian category with coproducts. -/
theorem nonempty_singularCohomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hac : a < c) (hcb : c < b)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
    (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularCohomology R k M' m ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularCohomology
        R k M' m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  obtain ⟨ε₀, hε₀, hsmall⟩ :=
    h.exists_singularCohomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr
  set ε := min (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2))
  have hε_pos : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε_lt : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have haε : a ≤ c - ε := by
    linarith [min_le_right (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2)),
      min_le_left ((c - a) / 2) ((b - c) / 2)]
  have hεb : c + ε ≤ b := by
    linarith [min_le_right (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2)),
      min_le_right ((c - a) / 2) ((b - c) / 2)]
  have hsubIcc : Icc (c - ε) (c + ε) ⊆ Icc a b := Icc_subset_Icc haε hεb
  have hcompε : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) :=
    hcomp.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) (preimage_mono hsubIcc)
  have hcritε : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i :=
    (inter_subset_inter_right _ (preimage_mono hsubIcc)).trans hcrit
  obtain ⟨eThom⟩ := hsmall ε ⟨hε_pos, hε_lt⟩ hcompε hcritε R k M' m
  have hval {s t : ℝ} (hcr : criticalPoints I f ∩ f ⁻¹' Icc s t ⊆ range i) :
      ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c := fun x hx hfx ↦ by
    obtain ⟨p, rfl⟩ := hcr ⟨hx, hfx⟩
    exact hc p
  exact ⟨singularCohomologySublevelPairIsoOfCriticalValue hfs hac hcb (by linarith) (by linarith)
    hcomp hcompε (hval hcrit) (hval hcritε) R k M' m ≪≫ eThom⟩

/-- **Relative cohomology across a connected compact Morse–Bott submanifold.** On a connected
compact Morse–Bott submanifold the Morse index is constant, so the relative cohomology of any
compact isolated band around its level is that of the Thom pair of its negative normal bundle of
rank `manifoldMorseIndex I f (i s₀)`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_thomPair_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {c a b : ℝ} (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)
    (s₀ : S) (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
    (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularCohomology R k M' m ≅
      (thomPair (Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularCohomology
        R k M' m) :=
  h.nonempty_singularCohomology_sublevelPair_iso_thomPair hn hfs hc hdim g
    (fun s ↦ (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀)
    hac hcb hcomp hcrit R k M' m

/-- **Relative cohomology of a compact cobordism across a Morse–Bott submanifold.** Under the
hypotheses of `nonempty_singularCohomology_sublevelPair_iso_thomPair`, the lower level `a` is
regular, so the band pair `(f⁻¹[a, b], f⁻¹(a))` also has the relative cohomology of the Thom pair
`(ν⁻, ν⁻₀)`. -/
theorem nonempty_singularCohomology_bandPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hac : a < c) (hcb : c < b)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
    (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((bandPair f (hac.trans hcb).le).singularCohomology R k M' m ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularCohomology
        R k M' m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have ha : IsRegularValue I 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hxc, hx⟩ ↦ by
      obtain ⟨s, rfl⟩ := hcrit ⟨hxc, le_of_eq hx.symm, hx.le.trans (hac.trans hcb).le⟩
      exact hac.ne (hx.symm.trans (hc s))
  have := isIso_singularCohomologyMap_bandPairInclusion hfs (hac.trans hcb).le hcomp ha R k M' m
  obtain ⟨e⟩ := h.nonempty_singularCohomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R k M' m
  exact ⟨(asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M')
    (bandPairInclusion f (hac.trans hcb).le) m)).symm ≪≫ e⟩

/-! ### Metric-free consequences: vanishing below the index and index degree -/

/-- Changing the coordinate fibre of a subbundle from `F₁` to `F₂` does not change its Thom
pair: the total space carries the subspace topology from the ambient bundle in both cases. -/
private def subbundleThomPairModelIso (P : Type*) {B : Type w} {F : B → Type w}
    [∀ b, AddCommGroup (F b)] [∀ b, Module ℝ (F b)]
    [TopologicalSpace (TotalSpace P F)] (F₁ F₂ : Type*) (V : ∀ b, Submodule ℝ (F b)) :
    letI := subbundleTopology P (F' := F₁) V
    letI := subbundleTopology P (F' := F₂) V
    thomPair F₁ (fun b ↦ V b) ≅ thomPair F₂ (fun b ↦ V b) :=
  letI := subbundleTopology P (F' := F₁) V
  letI := subbundleTopology P (F' := F₂) V
  thomPairModelIso
    ((isEmbedding_totalSpace_subbundle P F₂ V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle P F₁ V).continuous)
    ((isEmbedding_totalSpace_subbundle P F₁ V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle P F₂ V).continuous)

/-- **Vanishing below the Morse index in homology.** Across a compact Morse–Bott submanifold of
constant index `r`, the relative singular homology `Hₙ({f ≤ b}, {f ≤ a}; R)` vanishes for every
`n < r`, with coefficients in any abelian category with coproducts. -/
theorem isZero_singularHomology_sublevelPair_of_lt_index
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
    {m : ℕ} (hmr : m < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularHomology R m) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
  have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := i.nonempty_contMDiffRiemannianMetric_normalSpace (m' := ⊤) hn (by simp) hdim
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R m
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let hVu := hV.hasLocalSubbundleFrames.comp_equiv Equiv.ulift
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  let := hVu.vectorBundle
  have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
    rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  have hzero : IsZero ((thomPair (ULift.{u} (Fin r) → ℝ) ν).singularHomology R m) :=
    isZero_singularHomology_thomPair_of_compactSpace R (hrank.symm ▸ hmr)
  exact hzero.of_iso (e ≪≫ TopPair.singularHomologyMapIso R
    (subbundleThomPairModelIso P₀ (Fin r → ℝ) (ULift.{u} (Fin r) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)) m)

/-- **Vanishing below the Morse index in cohomology.** Across a compact Morse–Bott submanifold of
constant index `r`, the relative singular cohomology `Hⁿ({f ≤ b}, {f ≤ a}; R, M')` vanishes for
every `n < r` whenever the chain coefficient object `R` is projective. -/
theorem isZero_singularCohomology_sublevelPair_of_lt_index
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) [Projective R]
    (k : Type*) [Ring k] [Linear k A] (M' : A) {m : ℕ} (hmr : m < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularCohomology R k M' m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M' m fun _ hj ↦
    h.isZero_singularHomology_sublevelPair_of_lt_index hfs hc hr hac hcb hcomp hcrit R
      (hj.trans_lt hmr)

/-- **The index-degree relative homology with `Subsingleton Kˣ` coefficients.** Across a compact
Morse–Bott submanifold `i : S → M` of constant index `r`, for any commutative ring `K` whose only
unit is `1` (such as `ZMod 2`), `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)`, without any orientability
assumption on the negative normal bundle. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_zero
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (K : Type u) [CommRing K] [Subsingleton Kˣ] :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) r ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) 0).obj (ModuleCat.of K K)).obj
        (TopCat.of S)) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
  have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := i.nonempty_contMDiffRiemannianMetric_normalSpace (m' := ⊤) hn (by simp) hdim
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit (ModuleCat.of K K) r
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let hVu := hV.hasLocalSubbundleFrames.comp_equiv Equiv.ulift
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  let := hVu.vectorBundle
  have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
    rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let eLift := TopPair.singularHomologyMapIso (ModuleCat.of K K)
    (subbundleThomPairModelIso P₀ (Fin r → ℝ) (ULift.{u} (Fin r) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)) r
  let eThom := eqToIso (congrArg
    ((thomPair (ULift.{u} (Fin r) → ℝ) ν).singularHomology (ModuleCat.of K K)) hrank.symm) ≪≫
    thomPairSingularHomologyFinrankIso K (ULift.{u} (Fin r) → ℝ) ν
  exact ⟨e ≪≫ eLift ≪≫ eThom⟩

end HomologyAttachment

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

end TauCeti
