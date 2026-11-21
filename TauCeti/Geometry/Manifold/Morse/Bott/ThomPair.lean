/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.Subbundle
import TauCeti.Topology.VectorBundle.Riemannian.FiniteDimensional

/-!
# The negative disc bundle and the Thom pair of the negative normal bundle

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold, and let `g`
be a fibre metric on its normal bundle `ν`. The metric selects the negative normal spaces `ν⁻`, on
which the normal Hessian `Hessₛ` is negative definite
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace`). For `ε > 0` the negative
disc bundle `D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`) and its boundary, the negative
sphere bundle `S_ε = {v ∈ D_ε | -½ Hessₛ (v, v) = ε}`, form the negative disc-sphere pair
`(D_ε, S_ε)` (`IsCriticalSubmanifold.negativeDiscSpherePair`). Crossing the level of a compact
Morse–Bott submanifold attaches `D_ε` along `S_ε` to the lower sublevel
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`).

This file identifies the relative homology of such an attachment with that of the Thom pair
`(ν⁻, ν⁻₀)` of `ν⁻`, where `ν⁻₀` is the complement of the zero section. Here `ν⁻` is the vector
bundle of rank `r` whose total space carries the topology of a subspace of the normal bundle
(`TauCeti.subbundleTopology`) and whose local trivializations come from continuous local frames
(`TauCeti.HasLocalSubbundleFrames`). For a Morse–Bott submanifold of constant index `r` and a smooth
fibre metric such frames exist
(`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`).

* The inclusion `(D_ε, S_ε) ⟶ (ν⁻, ν⁻₀)` (`IsCriticalSubmanifold.negativeDiscThomPairMap`)
  induces isomorphisms on relative singular homology and cohomology, with arbitrary coefficients,
  in every degree (`IsCriticalSubmanifold.isIso_singularHomologyMap_negativeDiscThomPairMap` and
  `IsCriticalSubmanifold.isIso_singularCohomologyMap_negativeDiscThomPairMap`).
* If `Z` is obtained from a closed subset `X` by attaching `D_ε` along `S_ε`, then the attaching
  map induces isomorphisms `Hₖ(D_ε, S_ε) ≅ Hₖ(Z, X)` and `Hᵏ(Z, X) ≅ Hᵏ(D_ε, S_ε)`
  (`IsCriticalSubmanifold.isIso_singularHomologyMap_of_attach_negativeDiscBundle` and
  `IsCriticalSubmanifold.isIso_singularCohomologyMap_of_attach_negativeDiscBundle`).

So whenever the region across a level is such an attachment of the negative disc bundle of a
critical submanifold, its relative homology is that of the Thom pair of the negative normal bundle,
which the Thom isomorphism computes from the homology of the submanifold with coefficients twisted
by the orientation local system of `ν⁻`, shifted by the index.

The proof equips `ν⁻` with the inner product `-(2ε)⁻¹ Hessₛ`, which is positive definite and so
defines the topology of the finite-dimensional fibres
(`Bundle.RiemannianMetric.ofFiniteDimensional`). Its unit disc and sphere bundles are `D_ε` and
`S_ε`, read through the inclusion of the total space of `ν⁻` into the normal bundle, and its fibre
norm is continuous because the quadratic form of the normal Hessian is
(`IsCriticalSubmanifold.contMDiff_normalHessian_apply_self`). The comparison of the disc-sphere
pair of a normed vector bundle with its Thom pair
(`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap`, for the fibre gauge
`TauCeti.isFiberGauge_norm`) and the attachment theorem for disc bundles
(`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`) then apply. The norms are
auxiliary: no statement below involves them.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10 (the Thom pair `(E, E₀)` and the Thom isomorphism).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding.IsCriticalSubmanifold

universe u

variable {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} {S : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
  (P : Type*) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn) {ε : ℝ}

/-- The **negative disc-sphere pair** of a critical submanifold, of size `ε`, relative to a fibre
metric `g` on the normal spaces: the negative disc bundle
`D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}` (`IsCriticalSubmanifold.negativeDiscBundle`) relative to its
boundary `{v ∈ D_ε | -½ Hessₛ (v, v) = ε}`, the negative sphere bundle. -/
abbrev negativeDiscSpherePair (ε : ℝ) : TopPair.{u} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace P fun s ↦ i.NormalSpace s hn))
    (inter_subset_left : h.negativeDiscBundle hn P g ε ∩
        {x | -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = ε} ⊆ h.negativeDiscBundle hn P g ε)

variable (r : ℕ)

/-- The inclusion of the negative disc bundle `D_ε` into the total space of the negative normal
bundle `ν⁻`, with the topology of a subspace of the normal bundle. -/
private def negativeDiscBundleInclusion :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    C(h.negativeDiscBundle hn P g ε, TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) :=
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  ⟨fun x ↦ ⟨x.val.proj,
      ⟨x.val.snd, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn x.property⟩⟩,
    (isEmbedding_totalSpace_subbundle P (Fin r → ℝ) (h.negativeNormalSpace hn g)).continuous_iff.2
      continuous_subtypeVal⟩

/-- The inclusion `(D_ε, S_ε) ⟶ (ν⁻, ν⁻₀)` of the negative disc-sphere pair into the Thom pair of
the negative normal bundle `ν⁻`, whose total space carries the topology of a subspace of the normal
bundle (`TauCeti.subbundleTopology`). A vector of `D_ε` is a vector of the negative normal space,
and for `ε > 0` the vectors of `S_ε` are nonzero. -/
def negativeDiscThomPairMap (hε : 0 < ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    h.negativeDiscSpherePair hn P g ε ⟶
      thomPair (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s :=
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let ι := h.negativeDiscBundleInclusion hn P g r (ε := ε)
  TopPair.ofHom (TopCat.ofHom ι)
    (TopCat.ofHom ⟨fun x ↦ ⟨ι (inclusion inter_subset_left x), mem_zeroSectionCompl.2 fun h0 ↦
        hε.ne' <| by
          have h0' : x.val.snd = 0 := congrArg Subtype.val h0
          rw [← x.property.2, h0']
          simp⟩,
      (ι.continuous.comp (continuous_inclusion inter_subset_left)).subtype_mk _⟩)
    (by ext; rfl)

@[simp]
theorem negativeDiscThomPairMap_fst_apply (hε : 0 < ε) (x : h.negativeDiscBundle hn P g ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    TopPair.Hom.fst (h.negativeDiscThomPairMap hn P g r hε) x =
      ⟨x.val.proj, ⟨x.val.snd, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn x.property⟩⟩ :=
  (rfl)

@[simp]
theorem negativeDiscThomPairMap_snd_apply (hε : 0 < ε)
    (x : ↥(h.negativeDiscBundle hn P g ε ∩
      {x | -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = ε})) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    (TopPair.Hom.snd (h.negativeDiscThomPairMap hn P g r hε) x).val =
      ⟨x.val.proj,
        ⟨x.val.snd, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn x.property.1⟩⟩ :=
  (rfl)

section Comparison

variable [FiniteDimensional ℝ E]

/-- The inner product `-(2ε)⁻¹ Hessₛ` on the negative normal spaces, for `ε > 0`. Its unit disc
bundle is the negative disc bundle `D_ε`. -/
private def negativeNormalMetric (hε : 0 < ε) :
    RiemannianMetric fun s ↦ h.negativeNormalSpace hn g s :=
  .ofFiniteDimensional
    (fun s ↦ -(2 * ε)⁻¹ • (h.normalHessian hn s).compl₁₂ (h.negativeNormalSpace hn g s).subtype
      (h.negativeNormalSpace hn g s).subtype)
    (fun s ↦ ⟨fun v w ↦ by simp [(h.isSymm_normalHessian hn s).eq (v : i.NormalSpace s hn) w]⟩)
    (fun s v hv ↦ by
      have hneg := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g v.property
        (by simpa using hv)
      simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
        smul_eq_mul]
      exact mul_pos_of_neg_of_neg (neg_neg_iff_pos.2 (inv_pos.2 (by positivity))) hneg)

/-- The norm on the negative normal spaces given by `negativeNormalMetric`; it induces the
existing topology. -/
private abbrev negativeNormalNorm (hε : 0 < ε) (s : S) :
    NormedAddCommGroup (h.negativeNormalSpace hn g s) :=
  ((h.negativeNormalMetric hn g hε).toCore s).toNormedAddCommGroupOfTopology
    ((h.negativeNormalMetric hn g hε).continuousAt s)
    ((h.negativeNormalMetric hn g hε).isVonNBounded s)

/-- The normed space structure on the negative normal spaces given by `negativeNormalMetric`. -/
private abbrev negativeNormalNormedSpace (hε : 0 < ε) (s : S) :
    letI := h.negativeNormalNorm hn g hε s
    NormedSpace ℝ (h.negativeNormalSpace hn g s) :=
  ((h.negativeNormalMetric hn g hε).toCore s).toNormedSpaceOfTopology
    ((h.negativeNormalMetric hn g hε).continuousAt s)
    ((h.negativeNormalMetric hn g hε).isVonNBounded s)

/-- The square of the norm `negativeNormalNorm` is `-½ Hessₛ (v, v) / ε`. -/
private theorem norm_sq_negativeNormalNorm (hε : 0 < ε) {s : S}
    (v : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    ‖v‖ ^ 2 = -(2⁻¹ * h.normalHessian hn s v v) / ε := by
  let := h.negativeNormalNorm hn g hε s
  -- The norm of `toNormedAddCommGroupOfTopology` is the square root of the inner product.
  have hv : ‖v‖ = √((h.negativeNormalMetric hn g hε).inner s v v) := rfl
  have hpos : 0 ≤ (h.negativeNormalMetric hn g hε).inner s v v := by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · exact ((h.negativeNormalMetric hn g hε).pos s v hv0).le
  rw [hv, Real.sq_sqrt hpos]
  simp only [negativeNormalMetric, RiemannianMetric.ofFiniteDimensional_inner, LinearMap.smul_apply,
    LinearMap.compl₁₂_apply, Submodule.subtype_apply, smul_eq_mul]
  field_simp

private theorem norm_le_one_iff (hε : 0 < ε) {s : S} (v : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    ‖v‖ ≤ 1 ↔ -(2⁻¹ * h.normalHessian hn s v v) ≤ ε := by
  let := h.negativeNormalNorm hn g hε s
  rw [← sq_le_one_iff₀ (norm_nonneg v), h.norm_sq_negativeNormalNorm hn g hε, div_le_one hε]

private theorem norm_eq_one_iff (hε : 0 < ε) {s : S} (v : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    ‖v‖ = 1 ↔ -(2⁻¹ * h.normalHessian hn s v v) = ε := by
  let := h.negativeNormalNorm hn g hε s
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero, h.norm_sq_negativeNormalNorm hn g hε,
    div_eq_one_iff_eq hε.ne']

/-- A vector of the negative normal bundle of norm at most one, for `negativeNormalNorm`, lies in
the negative disc bundle `D_ε`. -/
private theorem mem_negativeDiscBundle_of_norm_le_one (hε : 0 < ε)
    {v : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s}
    (hv : letI := h.negativeNormalNorm hn g hε; ‖v.snd‖ ≤ 1) :
    (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈ h.negativeDiscBundle hn P g ε :=
  (mem_negativeDiscBundle hn).2 ⟨v.snd.property, (h.norm_le_one_iff hn g hε v.snd).1 hv⟩

/-- With the norms `negativeNormalNorm`, the inclusion of the total space of the negative normal
bundle `ν⁻` into the normal bundle carries its unit disc-sphere pair onto the negative disc-sphere
pair `(D_ε, S_ε)`. -/
private def discSpherePairIso (hε : 0 < ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    gaugeDiscSpherePair
        (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖) ≅
      h.negativeDiscSpherePair hn P g ε :=
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  letI := h.negativeNormalNorm hn g hε
  have hι := isEmbedding_totalSpace_subbundle P (Fin r → ℝ) (h.negativeNormalSpace hn g)
  let ι := h.negativeDiscBundleInclusion hn P g r (ε := ε)
  have hD (x : h.negativeDiscBundle hn P g ε) :
      ι x ∈ gaugeDiscBundle
        (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖) :=
    mem_gaugeDiscBundle.2
      ((h.norm_le_one_iff hn g hε _).2 ((mem_negativeDiscBundle hn).1 x.property).2)
  { hom := TopPair.ofHom
      (TopCat.ofHom ⟨fun v ↦ ⟨⟨v.val.proj, v.val.snd⟩,
        h.mem_negativeDiscBundle_of_norm_le_one hn P g r hε (mem_gaugeDiscBundle.1 v.property)⟩,
        (hι.continuous.comp continuous_subtypeVal).subtype_mk _⟩)
      (TopCat.ofHom ⟨fun v ↦ ⟨⟨v.val.proj, v.val.snd⟩,
        h.mem_negativeDiscBundle_of_norm_le_one hn P g r hε
          (mem_gaugeDiscBundle.1 (gaugeSphereBundle_subset_gaugeDiscBundle _ v.property)),
          (h.norm_eq_one_iff hn g hε v.val.snd).1 (mem_gaugeSphereBundle.1 v.property)⟩,
        (hι.continuous.comp continuous_subtypeVal).subtype_mk _⟩)
      (by ext; rfl)
    inv := TopPair.ofHom (TopCat.ofHom ⟨fun x ↦ ⟨ι x, hD x⟩, ι.continuous.subtype_mk _⟩)
      (TopCat.ofHom ⟨fun x ↦ ⟨ι (inclusion inter_subset_left x),
          mem_gaugeSphereBundle.2 ((h.norm_eq_one_iff hn g hε _).2 x.property.2)⟩,
        (ι.continuous.comp (continuous_inclusion inter_subset_left)).subtype_mk _⟩)
      (by ext; rfl)
    hom_inv_id := by ext : 2 <;> rfl
    inv_hom_id := by ext : 2 <;> rfl }

/-- The inclusion of the negative disc-sphere pair into the Thom pair of `ν⁻` is the disc-sphere
pair of the norms `negativeNormalNorm`, read through `discSpherePairIso`. -/
private theorem discSpherePairIso_hom_comp_negativeDiscThomPairMap (hε : 0 < ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    ∀ hρ : IsFiberGauge
        (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖),
      (h.discSpherePairIso hn P g r hε).hom ≫ h.negativeDiscThomPairMap hn P g r hε =
        gaugeDiscSpherePairMap hρ := by
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := h.negativeNormalNorm hn g hε
  intro hρ
  ext x : 2
  · exact Subtype.ext (gaugeDiscSpherePairMap_snd_apply hρ x).symm
  · exact (gaugeDiscSpherePairMap_fst_apply hρ x).symm

/-- The hypotheses of the attachment theorem
`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle` for the disc-sphere pair of the norms
`negativeNormalNorm`, given those of an attachment of the negative disc bundle. -/
private theorem attach_discSpherePairIso_hom_comp (hε : 0 < ε) {Z : Type u} [TopologicalSpace Z]
    {X : Set Z} (φ : h.negativeDiscSpherePair hn P g ε ⟶ TopPair.ofSubset (X := TopCat.of Z) X)
    (hφ : IsClosedEmbedding (TopPair.Hom.fst φ))
    (hφX : ∀ x : h.negativeDiscBundle hn P g ε, TopPair.Hom.fst φ x ∈ X →
      -(2⁻¹ * h.normalHessian hn x.val.proj x.val.snd x.val.snd) = ε)
    (hφcover : X ∪ range (TopPair.Hom.fst φ) = univ) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    IsClosedEmbedding (TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ)) ∧
      (∀ v : gaugeDiscBundle
          (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖),
        TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ) v ∈ X →
          (v : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) ∈
            gaugeSphereBundle
              (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖)) ∧
      X ∪ range (TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ)) = univ := by
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := h.negativeNormalNorm hn g hε
  let e := TopCat.homeoOfIso (TopPair.proj₁.mapIso (h.discSpherePairIso hn P g r hε))
  -- `e` is the first component of `discSpherePairIso` as a homeomorphism: `TopCat.homeoOfIso`,
  -- `Functor.mapIso` and `TopPair.proj₁` keep the underlying function of `TopPair.Hom.fst`, and
  -- the first component of a composite of maps of pairs is the composite of first components.
  have he : ⇑(TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ)) =
      TopPair.Hom.fst φ ∘ e := rfl
  refine ⟨he ▸ hφ.comp e.isClosedEmbedding, fun v hv ↦ ?_, ?_⟩
  · exact mem_gaugeSphereBundle.2 ((h.norm_eq_one_iff hn g hε _).2 (hφX _ hv))
  · exact (congrArg (X ∪ ·) ((congrArg range he).trans (e.surjective.range_comp _))).trans hφcover

/-- The isomorphism `discSpherePairIso` induces isomorphisms on relative singular cohomology, by
functoriality of `TopPair.singularCohomologyFunctor`. -/
private theorem isIso_singularCohomologyMap_discSpherePairIso_hom (hε : 0 < ε) {C : Type*}
    [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (K : Type*) [Ring K] [Linear K C]
    (N : C) (k : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := K) (M := N)
      (h.discSpherePairIso hn P g r hε).hom k) :=
  ((TopPair.singularCohomologyFunctor R K N k).mapIso
    (h.discSpherePairIso hn P g r hε).op).isIso_hom

end Comparison

section Thom

variable {P} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]

/-- The quadratic form of the normal Hessian is continuous on the total space of the normal
bundle. -/
private theorem continuous_normalHessian_apply_self
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') :
    Continuous fun x : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
      h.normalHessian hn x.proj x.snd x.snd := by
  let := i.normalSpaceFiberBundle hn hdim
  -- Adapt the smoothness degrees of `contMDiff_normalHessian_apply_self` to `k = 0`.
  have : IsManifold I (0 + 2) M := by rwa [zero_add]
  have : IsManifold J (0 + 1) S := by rwa [zero_add]
  exact (h.contMDiff_normalHessian_apply_self hn (k := 0)
    (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) (by simpa using h.contMDiffAt)
    hdim).continuous

/-- With the norms `negativeNormalNorm`, the fibre norm is continuous on the total space of the
negative normal bundle. -/
private theorem continuous_norm_negativeNormalNorm
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (hε : 0 < ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    Continuous fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖ := by
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := h.negativeNormalNorm hn g hε
  have hnorm (v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s)) :
      ‖v.snd‖ = √(-(2⁻¹ * h.normalHessian hn v.proj v.snd v.snd) / ε) := by
    rw [← h.norm_sq_negativeNormalNorm hn g hε, Real.sqrt_sq (norm_nonneg _)]
  simp only [hnorm]
  have hι := isEmbedding_totalSpace_subbundle P (Fin r → ℝ) (h.negativeNormalSpace hn g)
  exact ((((h.continuous_normalHessian_apply_self hn hdim).comp hι.continuous).const_mul
    _).neg.div_const _).sqrt

/-- **The negative disc-sphere pair computes the homology of the Thom pair of `ν⁻`.** Let `i` be
a critical submanifold of `f`, let `g` be a fibre metric on its normal bundle, and suppose that the
negative normal spaces have continuous local frames of size `r`, so that they form a vector
bundle `ν⁻` of rank `r`. Then for `ε > 0` the inclusion `(D_ε, S_ε) ⟶ (ν⁻, ν⁻₀)` of the negative
disc-sphere pair into the Thom pair induces isomorphisms `Hₖ(D_ε, S_ε) ≅ Hₖ(ν⁻, ν⁻₀)` on relative
singular homology, with coefficients in any abelian category with coproducts, in every degree. -/
theorem isIso_singularHomologyMap_negativeDiscThomPairMap
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (h.negativeDiscThomPairMap hn P g r hε) R k) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := h.negativeNormalNorm hn g hε
  let := h.negativeNormalNormedSpace hn g hε
  have hρ := isFiberGauge_norm (h.continuous_norm_negativeNormalNorm hn g r hdim hε)
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R k
  rw [← h.discSpherePairIso_hom_comp_negativeDiscThomPairMap hn P g r hε hρ,
    TopPair.singularHomologyMap_comp] at this
  exact IsIso.of_isIso_comp_left
    (TopPair.singularHomologyMap (h.discSpherePairIso hn P g r hε).hom R k) _

/-- **The negative disc-sphere pair computes the cohomology of the Thom pair of `ν⁻`.** Under the
hypotheses of `isIso_singularHomologyMap_negativeDiscThomPairMap`, the inclusion
`(D_ε, S_ε) ⟶ (ν⁻, ν⁻₀)` induces isomorphisms `Hᵏ(ν⁻, ν⁻₀) ≅ Hᵏ(D_ε, S_ε)` on relative singular
cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_negativeDiscThomPairMap
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (K : Type*)
    [Ring K] [Linear K C] (N : C) (k : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := K) (M := N)
      (h.negativeDiscThomPairMap hn P g r hε) k) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := h.negativeNormalNorm hn g hε
  let := h.negativeNormalNormedSpace hn g hε
  have hρ := isFiberGauge_norm (h.continuous_norm_negativeNormalNorm hn g r hdim hε)
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R K N k
  have hiso := h.isIso_singularCohomologyMap_discSpherePairIso_hom hn P g r hε R K N k
  rwa [← h.discSpherePairIso_hom_comp_negativeDiscThomPairMap hn P g r hε hρ,
    TopPair.singularCohomologyMap_comp, isIso_comp_right_iff] at this

/-- **Attaching the negative disc bundle induces isomorphisms on relative homology.** Let `Z` be
obtained from a closed subset `X` by attaching the negative disc bundle `D_ε`, `ε > 0`, along
`S_ε`: a map of pairs `φ : (D_ε, S_ε) ⟶ (Z, X)` which is a closed embedding of `D_ε`, sends a
point of `D_ε` into `X` only if it lies in `S_ε`, and whose image covers `Z` together with `X`.
Then `φ` induces isomorphisms `Hₖ(D_ε, S_ε) ≅ Hₖ(Z, X)` on relative singular homology, with
coefficients in any abelian category with coproducts, in every degree. -/
theorem isIso_singularHomologyMap_of_attach_negativeDiscBundle
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) {Z : Type u} [TopologicalSpace Z] {X : Set Z} (hX : IsClosed X)
    (φ : h.negativeDiscSpherePair hn P g ε ⟶ TopPair.ofSubset (X := TopCat.of Z) X)
    (hφ : IsClosedEmbedding (TopPair.Hom.fst φ))
    (hφX : ∀ x : h.negativeDiscBundle hn P g ε, TopPair.Hom.fst φ x ∈ X →
      -(2⁻¹ * h.normalHessian hn x.val.proj x.val.snd x.val.snd) = ε)
    (hφcover : X ∪ range (TopPair.Hom.fst φ) = univ)
    {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (k : ℕ) :
    IsIso (TopPair.singularHomologyMap φ R k) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := h.negativeNormalNorm hn g hε
  let := h.negativeNormalNormedSpace hn g hε
  obtain ⟨h₁, h₂, h₃⟩ := h.attach_discSpherePairIso_hom_comp hn P g r hε φ hφ hφX hφcover
  have := isIso_singularHomologyMap_of_attach_gaugeDiscBundle
    (isFiberGauge_norm (h.continuous_norm_negativeNormalNorm hn g r hdim hε)) hX R k h₁ h₂ h₃
  rw [TopPair.singularHomologyMap_comp] at this
  exact IsIso.of_isIso_comp_left
    (TopPair.singularHomologyMap (h.discSpherePairIso hn P g r hε).hom R k) _

/-- **Attaching the negative disc bundle induces isomorphisms on relative cohomology.** Under the
hypotheses of `isIso_singularHomologyMap_of_attach_negativeDiscBundle`, the map of pairs
`φ : (D_ε, S_ε) ⟶ (Z, X)` induces isomorphisms `Hᵏ(Z, X) ≅ Hᵏ(D_ε, S_ε)` on relative singular
cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_of_attach_negativeDiscBundle
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) {Z : Type u} [TopologicalSpace Z] {X : Set Z} (hX : IsClosed X)
    (φ : h.negativeDiscSpherePair hn P g ε ⟶ TopPair.ofSubset (X := TopCat.of Z) X)
    (hφ : IsClosedEmbedding (TopPair.Hom.fst φ))
    (hφX : ∀ x : h.negativeDiscBundle hn P g ε, TopPair.Hom.fst φ x ∈ X →
      -(2⁻¹ * h.normalHessian hn x.val.proj x.val.snd x.val.snd) = ε)
    (hφcover : X ∪ range (TopPair.Hom.fst φ) = univ)
    {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (K : Type*) [Ring K]
    [Linear K C] (N : C) (k : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := K) (M := N) φ k) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := h.negativeNormalNorm hn g hε
  let := h.negativeNormalNormedSpace hn g hε
  obtain ⟨h₁, h₂, h₃⟩ := h.attach_discSpherePairIso_hom_comp hn P g r hε φ hφ hφX hφcover
  have := isIso_singularCohomologyMap_of_attach_gaugeDiscBundle
    (isFiberGauge_norm (h.continuous_norm_negativeNormalNorm hn g r hdim hε)) hX R k K N h₁ h₂ h₃
  have hiso := h.isIso_singularCohomologyMap_discSpherePairIso_hom hn P g r hε R K N k
  rwa [TopPair.singularCohomologyMap_comp, isIso_comp_right_iff] at this

end Thom

end TauCeti.SmoothEmbedding.IsCriticalSubmanifold
