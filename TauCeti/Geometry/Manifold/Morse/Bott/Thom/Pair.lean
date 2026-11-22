/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Geometry.Manifold.Morse.Bott.Adjunction
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Homology
public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.Subbundle
public import TauCeti.Topology.Order.Sublevel
import TauCeti.Topology.VectorBundle.Riemannian.FiniteDimensional
import TauCeti.Topology.VectorBundle.Thom.Attachment.Basic

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
* Let `f` be continuous on a Hausdorff manifold, suppose that the negative normal spaces have
  continuous local frames, and let `ε > 0` be such that `D_ε` is compact. If a map `Θ` is
  continuous and injective on `D_ε` and puts `f` there in the Morse–Bott normal form
  `f (Θ v) = c + ½ Hessₛ (v, v)`, then `(D_ε, S_ε)` has the homology of the lower sublevel with
  `Θ(D_ε)` attached, `Hₖ(D_ε, S_ε) ≅ Hₖ({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε})`
  (`IsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_union`).
* If `i` is a nondegenerate critical submanifold of a smooth `f` on the level `f = c`, `a < c < b`,
  the band `f⁻¹[a, b]` is compact and all its critical points lie on `i`, then for all small
  `ε > 0` the relative homology across the level is that of the negative disc-sphere pair,
  `Hₖ({f ≤ b}, {f ≤ a}) ≅ Hₖ(D_ε, S_ε)`, with coefficients in any abelian category with
  coproducts (`nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair`, in the namespace
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
* If `Z` is obtained from `X` by attaching the negative disc bundles `D a ε` of finitely many
  critical submanifolds, with pairwise disjoint images outside `X`, then the attaching maps induce
  isomorphisms `⨁ a, Hₖ(D a ε, S a ε) ≅ Hₖ(Z, X)` and `Hᵏ(Z, X) ≅ ⨁ a, Hᵏ(D a ε, S a ε)`
  (`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_negativeDiscBundles` and
  `TauCeti.isIso_biproductLift_singularCohomologyMap_of_attach_negativeDiscBundles`). This is the
  situation across a critical level carrying several Morse–Bott submanifolds.

So whenever the region across a level is such an attachment of the negative disc bundle of a
critical submanifold, its relative homology is that of the Thom pair of the negative normal bundle,
which the Thom isomorphism computes from the homology of the submanifold with coefficients twisted
by the orientation local system of `ν⁻`, shifted by the index.

For a compact Morse–Bott submanifold the attachment is realized by a Morse–Bott normal form `Θ`.
The function `ρ_ε (v) = √(-½ Hessₛ (v, v) / ε)` on `ν⁻`
(`IsCriticalSubmanifold.negativeNormalGauge`) is a fibre gauge
(`IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge`) whose disc and sphere bundles are carried
onto `D_ε` and `S_ε` by the inclusion of `ν⁻` into `ν`
(`IsCriticalSubmanifold.mem_gaugeDiscBundle_negativeNormalGauge`,
`IsCriticalSubmanifold.mem_gaugeSphereBundle_negativeNormalGauge`). With it, `Θ` restricted to `ν⁻`
induces a map of pairs `(D_{ρ_ε}(ν⁻), S_{ρ_ε}(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` which is an
isomorphism on relative singular homology
(`IsNondegenerateCriticalSubmanifold.exists_isIso_singularHomologyMap_negativeNormalGauge`). Hence
for regular levels `a < c < b` around the critical level `c` with compact band `f⁻¹[a, b]` whose
critical points lie on the submanifold, `Hₙ({f ≤ b}, {f ≤ a}) ≅ Hₙ(ν⁻, ν⁻₀)` for coefficients in
any abelian category with coproducts
(`IsNondegenerateCriticalSubmanifold.nonempty_singularHomology_sublevelPair_iso_thomPair`). For an
isolated nondegenerate critical point of index `r` the Thom pair is `(ℝʳ, ℝʳ ∖ {0})`.

The proof equips `ν⁻` with the inner product `-(2ε)⁻¹ Hessₛ`, which is positive definite and so
defines the topology of the finite-dimensional fibres
(`Bundle.RiemannianMetric.ofFiniteDimensional`). Its unit disc and sphere bundles are `D_ε` and
`S_ε`, read through the inclusion of the total space of `ν⁻` into the normal bundle, and its fibre
norm is continuous because the quadratic form of the normal Hessian is
(`IsCriticalSubmanifold.contMDiff_normalHessian_apply_self`). The comparison of the disc-sphere
pair of a normed vector bundle with its Thom pair
(`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap`, for the fibre gauge
`TauCeti.isFiberGauge_norm`) and the attachment theorem for disc bundles
(`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`) then apply. The metric and its
norm and inner product structures (`IsCriticalSubmanifold.negativeNormalMetric`,
`IsCriticalSubmanifold.negativeNormalNorm`, `IsCriticalSubmanifold.negativeNormalInnerProductSpace`)
are not instances, and no homology statement below involves them. Their inner product is
`-(2ε)⁻¹ Hessₛ` (`IsCriticalSubmanifold.inner_negativeNormalInnerProductSpace`), and they make `D_ε`
and `S_ε` the unit disc and sphere bundles of `ν⁻`
(`IsCriticalSubmanifold.mem_discBundle_iff_mem_negativeDiscBundle` and
`IsCriticalSubmanifold.mem_sphereBundle_iff_mem_negativeSphereBundle`), with continuous fibre
norm (`IsCriticalSubmanifold.continuous_norm_negativeNormalNorm`), so that constructions on the unit
disc bundle of a normed vector bundle, such as its cells over a CW complex, apply to `D_ε`. A set
of vectors of `ν⁻` is homeomorphic to the set of normal vectors it consists of
(`TauCeti.subbundleTotalSpaceHomeomorph`).

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

universe u v w

namespace TauCeti.SmoothEmbedding.IsCriticalSubmanifold

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
bundle is the negative disc bundle `D_ε`
(`IsCriticalSubmanifold.mem_discBundle_iff_mem_negativeDiscBundle`). -/
def negativeNormalMetric (hε : 0 < ε) :
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
existing topology. It is not an instance; install it with `letI`. -/
abbrev negativeNormalNorm (hε : 0 < ε) (s : S) :
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

/-- The inner product space structure on the negative normal spaces given by
`negativeNormalMetric`, whose norm is `negativeNormalNorm`. It is not an instance; install it with
`letI`. -/
abbrev negativeNormalInnerProductSpace (hε : 0 < ε) (s : S) :
    letI := h.negativeNormalNorm hn g hε s
    InnerProductSpace ℝ (h.negativeNormalSpace hn g s) :=
  .ofCoreOfTopology ((h.negativeNormalMetric hn g hε).toCore s)
    ((h.negativeNormalMetric hn g hε).continuousAt s)
    ((h.negativeNormalMetric hn g hε).isVonNBounded s)

/-- The inner product of `negativeNormalInnerProductSpace` is `-(2ε)⁻¹ Hessₛ`. -/
theorem inner_negativeNormalInnerProductSpace (hε : 0 < ε) {s : S}
    (v w : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    letI := h.negativeNormalInnerProductSpace hn g hε s
    inner ℝ v w = -(2 * ε)⁻¹ * h.normalHessian hn s v w := by
  -- The inner product of `InnerProductSpace.ofCoreOfTopology` is that of the metric.
  change (h.negativeNormalMetric hn g hε).inner s v w = _
  simp only [negativeNormalMetric, RiemannianMetric.ofFiniteDimensional_inner, LinearMap.smul_apply,
    LinearMap.compl₁₂_apply, Submodule.subtype_apply, smul_eq_mul]

/-- The square of the norm `negativeNormalNorm` is `-½ Hessₛ (v, v) / ε`. -/
theorem norm_sq_negativeNormalNorm (hε : 0 < ε) {s : S}
    (v : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    ‖v‖ ^ 2 = -(2⁻¹ * h.normalHessian hn s v v) / ε := by
  let := h.negativeNormalNorm hn g hε s
  let := h.negativeNormalInnerProductSpace hn g hε s
  rw [← real_inner_self_eq_norm_sq, h.inner_negativeNormalInnerProductSpace hn g hε]
  ring

/-- For the norm `negativeNormalNorm`, a negative normal vector has norm at most one exactly when
it lies in the negative disc bundle `D_ε`: `-½ Hessₛ (v, v) ≤ ε`. -/
theorem norm_negativeNormalNorm_le_one_iff (hε : 0 < ε) {s : S} (v : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    ‖v‖ ≤ 1 ↔ -(2⁻¹ * h.normalHessian hn s v v) ≤ ε := by
  let := h.negativeNormalNorm hn g hε s
  rw [← sq_le_one_iff₀ (norm_nonneg v), h.norm_sq_negativeNormalNorm hn g hε, div_le_one hε]

/-- For the norm `negativeNormalNorm`, a negative normal vector has norm one exactly when it lies
in the negative sphere bundle `S_ε`: `-½ Hessₛ (v, v) = ε`. -/
theorem norm_negativeNormalNorm_eq_one_iff (hε : 0 < ε) {s : S} (v : h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε s
    ‖v‖ = 1 ↔ -(2⁻¹ * h.normalHessian hn s v v) = ε := by
  let := h.negativeNormalNorm hn g hε s
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero, h.norm_sq_negativeNormalNorm hn g hε,
    div_eq_one_iff_eq hε.ne']

/-- For the norm `negativeNormalNorm`, the unit disc bundle of the negative normal bundle `ν⁻` is
the negative disc bundle `D_ε`, read through the inclusion of `ν⁻` in the normal bundle. -/
theorem mem_discBundle_iff_mem_negativeDiscBundle (hε : 0 < ε)
    (v : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε
    v ∈ discBundle (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↔
      (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈
        h.negativeDiscBundle hn P g ε := by
  let := h.negativeNormalNorm hn g hε
  exact ⟨fun hv ↦ (mem_negativeDiscBundle hn).2
      ⟨v.snd.property,
        (h.norm_negativeNormalNorm_le_one_iff hn g hε v.snd).1 (mem_discBundle.1 hv)⟩,
    fun hv ↦ mem_discBundle.2 <|
      (h.norm_negativeNormalNorm_le_one_iff hn g hε v.snd).2 ((mem_negativeDiscBundle hn).1 hv).2⟩

/-- For the norm `negativeNormalNorm`, the unit sphere bundle of the negative normal bundle `ν⁻` is
the negative sphere bundle `S_ε`, read through the inclusion of `ν⁻` in the normal bundle. -/
theorem mem_sphereBundle_iff_mem_negativeSphereBundle (hε : 0 < ε)
    (v : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) :
    letI := h.negativeNormalNorm hn g hε
    v ∈ sphereBundle (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↔
      (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈
        h.negativeSphereBundle hn P g ε := by
  let := h.negativeNormalNorm hn g hε
  exact ⟨fun hv ↦ (mem_negativeSphereBundle hn).2
      ⟨v.snd.property,
        (h.norm_negativeNormalNorm_eq_one_iff hn g hε v.snd).1 (mem_sphereBundle.1 hv)⟩,
    fun hv ↦ mem_sphereBundle.2 <|
      (h.norm_negativeNormalNorm_eq_one_iff hn g hε v.snd).2 ((mem_negativeSphereBundle hn).1 hv).2⟩

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
  let eD := subbundleTotalSpaceHomeomorph P (h.negativeNormalSpace hn g)
    (gaugeDiscBundle
      fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖)
    (h.negativeDiscBundle hn P g ε)
    (fun v ↦ (mem_gaugeDiscBundle.trans mem_discBundle.symm).trans
      (h.mem_discBundle_iff_mem_negativeDiscBundle hn P g r hε v))
    fun _ hx ↦ mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx
  let eS := subbundleTotalSpaceHomeomorph P (h.negativeNormalSpace hn g)
    (gaugeSphereBundle
      fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖)
    (h.negativeDiscBundle hn P g ε ∩ {x | -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = ε})
    (fun v ↦ ⟨fun hv ↦ ⟨(h.mem_discBundle_iff_mem_negativeDiscBundle hn P g r hε v).1
          (mem_discBundle.2
            (mem_gaugeDiscBundle.1 (gaugeSphereBundle_subset_gaugeDiscBundle _ hv))),
        (h.norm_negativeNormalNorm_eq_one_iff hn g hε v.snd).1 (mem_gaugeSphereBundle.1 hv)⟩,
      fun hv ↦ mem_gaugeSphereBundle.2
        ((h.norm_negativeNormalNorm_eq_one_iff hn g hε v.snd).2 hv.2)⟩)
    fun _ hx ↦ mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx.1
  have hD (v : _) : (eD v : TotalSpace P fun s ↦ i.NormalSpace s hn) = ⟨v.val.proj, v.val.snd⟩ :=
    coe_subbundleTotalSpaceHomeomorph_apply ..
  have hS (v : _) : (eS v : TotalSpace P fun s ↦ i.NormalSpace s hn) = ⟨v.val.proj, v.val.snd⟩ :=
    coe_subbundleTotalSpaceHomeomorph_apply ..
  have hD' (x : _) : (eD.symm x : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) =
      ⟨x.val.proj, ⟨x.val.snd, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn x.property⟩⟩ :=
    coe_subbundleTotalSpaceHomeomorph_symm_apply ..
  have hS' (x : _) : (eS.symm x : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) =
      ⟨x.val.proj,
        ⟨x.val.snd, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn x.property.1⟩⟩ :=
    coe_subbundleTotalSpaceHomeomorph_symm_apply ..
  { hom := TopPair.ofHom (TopCat.ofHom ⟨eD, eD.continuous⟩) (TopCat.ofHom ⟨eS, eS.continuous⟩)
      (by
        ext x
        exact Subtype.ext <| (hS x).trans
          (hD ⟨x.val, gaugeSphereBundle_subset_gaugeDiscBundle _ x.property⟩).symm)
    inv := TopPair.ofHom (TopCat.ofHom ⟨eD.symm, eD.symm.continuous⟩)
      (TopCat.ofHom ⟨eS.symm, eS.symm.continuous⟩) (by
        ext x
        exact Subtype.ext <| (hS' x).trans (hD' ⟨x.val, x.property.1⟩).symm)
    hom_inv_id := by
      ext : 2
      exacts [eS.symm_apply_apply _, eD.symm_apply_apply _]
    inv_hom_id := by
      ext : 2
      exacts [eS.apply_symm_apply _, eD.apply_symm_apply _] }

/-- The first component of `discSpherePairIso` keeps the underlying normal vector. -/
private theorem coe_discSpherePairIso_hom_fst_apply (hε : 0 < ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    ∀ v : gaugeDiscBundle
        (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖),
      (TopPair.Hom.fst (h.discSpherePairIso hn P g r hε).hom v).val = ⟨v.val.proj, v.val.snd⟩ :=
  fun _ ↦ coe_subbundleTotalSpaceHomeomorph_apply ..

/-- The second component of `discSpherePairIso` keeps the underlying normal vector. -/
private theorem coe_discSpherePairIso_hom_snd_apply (hε : 0 < ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    ∀ v : gaugeSphereBundle
        (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖),
      (TopPair.Hom.snd (h.discSpherePairIso hn P g r hε).hom v).val = ⟨v.val.proj, v.val.snd⟩ :=
  fun _ ↦ coe_subbundleTotalSpaceHomeomorph_apply ..

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
  let ι := fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦
    (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn)
  have hι := injective_totalSpace_subbundle P (Fin r → ℝ) (h.negativeNormalSpace hn g)
  -- On both sides, the vector `x` read in the normal bundle.
  ext x : 2
  · exact Subtype.ext (hι ((h.coe_discSpherePairIso_hom_snd_apply hn P g r hε x).trans
      (congrArg ι (gaugeDiscSpherePairMap_snd_apply hρ x)).symm))
  · exact hι ((h.coe_discSpherePairIso_hom_fst_apply hn P g r hε x).trans
      (congrArg ι (gaugeDiscSpherePairMap_fst_apply hρ x)).symm)

/-- The hypotheses of the attachment theorems
`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle` and
`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles` for the disc-sphere
pair of the norms `negativeNormalNorm`, given those of an attachment of the negative disc bundle:
the composite with `discSpherePairIso` is a closed embedding meeting `X` only along the sphere
bundle, with the same range as `φ`. -/
private theorem attach_discSpherePairIso_hom_comp (hε : 0 < ε) {Z : Type u} [TopologicalSpace Z]
    {X : Set Z} (φ : h.negativeDiscSpherePair hn P g ε ⟶ TopPair.ofSubset (X := TopCat.of Z) X)
    (hφ : IsClosedEmbedding (TopPair.Hom.fst φ))
    (hφX : ∀ x : h.negativeDiscBundle hn P g ε, TopPair.Hom.fst φ x ∈ X →
      -(2⁻¹ * h.normalHessian hn x.val.proj x.val.snd x.val.snd) = ε) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := h.negativeNormalNorm hn g hε
    IsClosedEmbedding (TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ)) ∧
      (∀ v : gaugeDiscBundle
          (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖),
        TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ) v ∈ X →
          (v : TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s) ∈
            gaugeSphereBundle
              (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) ↦ ‖v.snd‖)) ∧
      range (TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ)) =
        range (TopPair.Hom.fst φ) := by
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := h.negativeNormalNorm hn g hε
  let e := TopCat.homeoOfIso (TopPair.proj₁.mapIso (h.discSpherePairIso hn P g r hε))
  -- `e` is the first component of `discSpherePairIso` as a homeomorphism: `TopCat.homeoOfIso`,
  -- `Functor.mapIso` and `TopPair.proj₁` keep the underlying function of `TopPair.Hom.fst`, and
  -- the first component of a composite of maps of pairs is the composite of first components.
  have he : ⇑(TopPair.Hom.fst ((h.discSpherePairIso hn P g r hε).hom ≫ φ)) =
      TopPair.Hom.fst φ ∘ e := rfl
  refine ⟨he ▸ hφ.comp e.isClosedEmbedding, fun v hv ↦ ?_,
    (congrArg range he).trans (e.surjective.range_comp _)⟩
  have hv' := hφX (TopPair.Hom.fst (h.discSpherePairIso hn P g r hε).hom v) hv
  rw [h.coe_discSpherePairIso_hom_fst_apply hn P g r hε v] at hv'
  exact mem_gaugeSphereBundle.2 ((h.norm_negativeNormalNorm_eq_one_iff hn g hε _).2 hv')

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
theorem continuous_norm_negativeNormalNorm
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
  obtain ⟨h₁, h₂, h₃⟩ := h.attach_discSpherePairIso_hom_comp hn P g r hε φ hφ hφX
  have := isIso_singularHomologyMap_of_attach_gaugeDiscBundle
    (isFiberGauge_norm (h.continuous_norm_negativeNormalNorm hn g r hdim hε)) hX R k h₁ h₂
    (h₃ ▸ hφcover)
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
  obtain ⟨h₁, h₂, h₃⟩ := h.attach_discSpherePairIso_hom_comp hn P g r hε φ hφ hφX
  have := isIso_singularCohomologyMap_of_attach_gaugeDiscBundle
    (isFiberGauge_norm (h.continuous_norm_negativeNormalNorm hn g r hdim hε)) hX R k K N h₁ h₂
    (h₃ ▸ hφcover)
  have hiso := h.isIso_singularCohomologyMap_discSpherePairIso_hom hn P g r hε R K N k
  rwa [TopPair.singularCohomologyMap_comp, isIso_comp_right_iff] at this

end Thom

end TauCeti.SmoothEmbedding.IsCriticalSubmanifold

open Function

namespace TauCeti

namespace SmoothEmbedding

section Gauge

variable {E S : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0) {P F' : Type*}

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The **gauge of the negative disc bundle** of size `ε` of a critical submanifold, relative to a
fibre metric `g` on its normal spaces: the function `v ↦ √(-½ Hessₛ (v, v) / ε)` on the total space
of the negative normal spaces `ν⁻ s`, where `Hessₛ` is the normal Hessian. For `ε > 0` it is a
fibre gauge (`IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge`) whose disc and sphere
bundles are the negative disc and sphere bundles of size `ε`
(`IsCriticalSubmanifold.mem_gaugeDiscBundle_negativeNormalGauge`). The model fibre `F'` of the
total space plays no role. -/
def negativeNormalGauge (F' : Type*) (ε : ℝ) :
    TotalSpace F' (fun s ↦ h.negativeNormalSpace hn g s) → ℝ :=
  fun v ↦ √(-(2⁻¹ * h.normalHessian hn v.proj v.snd v.snd) / ε)

@[simp]
theorem negativeNormalGauge_apply {ε : ℝ}
    (v : TotalSpace F' fun s ↦ h.negativeNormalSpace hn g s) :
    h.negativeNormalGauge hn g F' ε v = √(-(2⁻¹ * h.normalHessian hn v.proj v.snd v.snd) / ε) :=
  (rfl)

variable {h g}

/-- A vector of the negative normal bundle lies in the disc bundle of the gauge of size `ε > 0`
exactly when, as a normal vector, it lies in the negative disc bundle of size `ε`. -/
theorem mem_gaugeDiscBundle_negativeNormalGauge {ε : ℝ} (hε : 0 < ε)
    {v : TotalSpace F' fun s ↦ h.negativeNormalSpace hn g s} :
    v ∈ gaugeDiscBundle (h.negativeNormalGauge hn g F' ε) ↔
      (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈
        h.negativeDiscBundle hn P g ε := by
  rw [mem_gaugeDiscBundle, negativeNormalGauge_apply, Real.sqrt_le_one, div_le_one hε,
    mem_negativeDiscBundle]
  exact (and_iff_right v.snd.property).symm

/-- A vector of the negative normal bundle lies in the sphere bundle of the gauge of size `ε > 0`
exactly when, as a normal vector, it lies in the negative sphere bundle of size `ε`. -/
theorem mem_gaugeSphereBundle_negativeNormalGauge {ε : ℝ} (hε : 0 < ε)
    {v : TotalSpace F' fun s ↦ h.negativeNormalSpace hn g s} :
    v ∈ gaugeSphereBundle (h.negativeNormalGauge hn g F' ε) ↔
      (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈
        h.negativeSphereBundle hn P g ε := by
  rw [mem_gaugeSphereBundle, negativeNormalGauge_apply, Real.sqrt_eq_one, div_eq_one_iff_eq hε.ne',
    mem_negativeSphereBundle]
  exact (and_iff_right v.snd.property).symm

variable (h g) in
/-- The inclusion of the negative normal bundle into the normal bundle carries the disc bundle of
the gauge of size `ε > 0` onto the negative disc bundle of size `ε`. -/
theorem image_gaugeDiscBundle_negativeNormalGauge {ε : ℝ} (hε : 0 < ε) :
    (fun v : TotalSpace F' (fun s ↦ h.negativeNormalSpace hn g s) ↦
        (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn)) ''
      gaugeDiscBundle (h.negativeNormalGauge hn g F' ε) = h.negativeDiscBundle hn P g ε := by
  ext x
  refine ⟨fun ⟨v, hv, hvx⟩ ↦ hvx ▸ (mem_gaugeDiscBundle_negativeNormalGauge hn hε).1 hv,
    fun hx ↦ ⟨⟨x.proj, ⟨x.snd, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx⟩⟩,
      (mem_gaugeDiscBundle_negativeNormalGauge hn hε).2 hx, rfl⟩⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace ℝ E''] [FiniteDimensional ℝ E''] [IsManifold J 1 S]

variable (h g) in
/-- **The gauge of the negative disc bundle is a fibre gauge.** Let `i` be a critical submanifold
of a function `f` which is `C²` along it, with a fibre metric `g` on its normal bundle, and give the
negative normal spaces the topology of a subspace of the normal bundle. For `ε > 0` the function
`v ↦ √(-½ Hessₛ (v, v) / ε)` is continuous, positively homogeneous on each fibre and positive off
the zero section, since the normal Hessian is negative definite on the negative normal spaces. -/
theorem isFiberGauge_negativeNormalGauge (hk : 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) 2 f (i s))
    (hdim : Module.finrank ℝ E'' = Module.finrank ℝ E - Module.finrank ℝ E') {ε : ℝ}
    (hε : 0 < ε) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := subbundleTopology E'' (F' := F') (h.negativeNormalSpace hn g)
    IsFiberGauge (h.negativeNormalGauge hn g F' ε) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := subbundleTopology E'' (F' := F') (h.negativeNormalSpace hn g)
  have : IsManifold I (0 + 2) M := by simpa using ‹IsManifold I 2 M›
  have : IsManifold J (0 + 1) S := by simpa using ‹IsManifold J 1 S›
  have hH := h.contMDiff_normalHessian_apply_self hn (k := 0) (by simpa using hk)
    (fun s ↦ by simpa using hf s) hdim
  rw [show h.negativeNormalGauge hn g F' ε = _ from funext (negativeNormalGauge_apply hn h g)]
  refine isFiberGauge_sqrt ?_ (fun {t} _ v ↦ ?_) fun {v} hv ↦ ?_
  · -- The quadratic form of the normal Hessian is continuous on the normal bundle, which contains
    -- the negative normal spaces as a subspace.
    exact ((continuous_const.mul (hH.continuous.comp
      (isEmbedding_totalSpace_subbundle E'' F' _).continuous)).neg).div_const ε
  · simp only [TotalSpace.mk', Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · have hneg := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g v.snd.property
      fun h0 ↦ hv (Subtype.ext h0)
    exact div_pos (by linarith) hε

end IsCriticalSubmanifold

end Gauge

section Attachment

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {E' H' P : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}
  {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- **Crossing the level of a compact Morse–Bott submanifold attaches the disc bundle of its
negative normal bundle.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth
function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `S`
compact and nonempty, `f = c` along `i` and Morse index `r` at every point of `i`, and let `g` be a
smooth fibre metric on its normal bundle. Give the total space of the negative normal spaces
relative to `g` the topology of a subspace of the normal bundle; with it they form a vector bundle
`ν⁻` of rank `r` over `S` (`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`).

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on `i`. Then `Θ` induces a map of pairs
`(D_ρ(ν⁻), S_ρ(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` from the disc-sphere pair of the gauge
`ρ = IsCriticalSubmanifold.negativeNormalGauge` of size `ε` on the negative normal bundle `ν⁻`,
which is an isomorphism on relative singular homology, with coefficients in any abelian category
with coproducts, in every degree. -/
theorem exists_isIso_singularHomologyMap_negativeNormalGauge [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [CompactSpace S] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        ∃ ψ : gaugeDiscSpherePair
            (h.negativeNormalGauge hn g.toRiemannianMetric (Fin r → ℝ) ε) ⟶
            sublevelPair f (a := c - ε) (b := c + ε) (by linarith),
          (∀ v : gaugeDiscBundle (h.negativeNormalGauge hn g.toRiemannianMetric (Fin r → ℝ) ε),
            Subtype.val (TopPair.Hom.fst ψ v) = Θ ⟨v.val.proj, v.val.snd⟩) ∧
          ∀ {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ),
            IsIso (TopPair.singularHomologyMap ψ R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  set D := h.negativeDiscBundle hn P g.toRiemannianMetric ε
  obtain ⟨hDΘ, ret, -, ⟨G⟩⟩ := hmain ε ⟨hε, hεε₀⟩ hcompact hcrit
  set ρ := h.negativeNormalGauge hn g.toRiemannianMetric (Fin r → ℝ) ε
  -- The inclusion `ι` of the negative normal bundle into the normal bundle carries `D_ρ` onto `D`.
  set ι := fun v : TotalSpace (Fin r → ℝ)
      (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) ↦
    (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn)
  have hι : IsEmbedding ι := isEmbedding_totalSpace_subbundle P _ _
  have hdisc : ι '' gaugeDiscBundle ρ = D :=
    IsCriticalSubmanifold.image_gaugeDiscBundle_negativeNormalGauge hn _ _ hε
  have hΘD (x) (hx : x ∈ D) : f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd :=
    hΘf x (hDΘ hx)
  -- `Θ ∘ ι` is continuous and injective on the compact set `D_ρ`, so it embeds it as a closed set.
  have : T2Space S := i.isEmbedding.t2Space
  have : CompactSpace (gaugeDiscBundle ρ) := isCompact_iff_compactSpace.1 <|
    hι.isCompact_iff.2 (hdisc ▸ h.isCompact_negativeDiscBundle hn hfs hdim g ε)
  have hmaps : MapsTo ι (gaugeDiscBundle ρ) D := hdisc ▸ mapsTo_image ι _
  have hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict (Θ ∘ ι)) :=
    Continuous.isClosedEmbedding ((Θ.contMDiffOn.continuousOn.mono hDΘ).comp_continuous
      (hι.continuous.comp continuous_subtypeVal) fun v ↦ hmaps v.property)
      fun v w hvw ↦ Subtype.ext (hι.injective
        (Θ.injOn (hDΘ (hmaps v.property)) (hDΘ (hmaps w.property)) hvw))
  refine exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle
    (IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge hn h.toIsCriticalSubmanifold _ (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim hε)
    (sublevel_mono f (by linarith)) (isClosed_le hfs.continuous continuous_const) hg
    (by rw [image_comp, hdisc]) ?_ (fun v hv ↦ ?_) ret G
  · -- On `D` the normal form gives `f ∘ Θ ≤ c`.
    rintro _ ⟨x, hx, rfl⟩
    exact (IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle hΘD hx).trans (by linarith)
  · -- A point of `D_ρ` is carried into `{f ≤ c - ε}` exactly when it lies in `S_ρ`.
    rw [IsCriticalSubmanifold.mem_gaugeSphereBundle_negativeNormalGauge hn hε (P := P)]
    exact (IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le hΘD
      ((IsCriticalSubmanifold.mem_gaugeDiscBundle_negativeNormalGauge hn hε).1 hv)).symm

/-- **The relative homology across the level of a compact Morse–Bott submanifold is that of the
Thom pair of its negative normal bundle.** Let `i : S → M` be a nondegenerate critical submanifold
of a smooth function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless
manifold, with `S` nonempty, `f = c` along `i` and Morse index `r` at every point of `i`, and let
`g` be a smooth fibre metric on its normal bundle. Let `a < c < b` be such that the band
`f⁻¹[a, b]` is compact and all its critical points lie on `i`. Give the total space of the
negative normal spaces relative to `g` the topology of a subspace of the normal bundle; with it
they form a vector bundle `ν⁻` of rank `r` over `S`
(`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`).

Then the relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to the relative homology
`Hₙ(ν⁻, ν⁻₀)` of the Thom pair of `ν⁻`, with `ν⁻₀` the complement of the zero section, for
coefficients in any abelian category with coproducts and in every degree. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
      (thomPair (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
        ).singularHomology R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
    hc hac.le hcb.le hcompact hcrit
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨Θ, -, -, -, ε₀, hε₀, hmain⟩ :=
    h.exists_isIso_singularHomologyMap_negativeNormalGauge hn hfs hc hdim g hr
  -- Choose a width `ε` below `ε₀` with `[c - ε, c + ε] ⊆ [a, b]`.
  set ε := min ε₀ (min (c - a) (b - c)) / 2
  have hm : 0 < min ε₀ (min (c - a) (b - c)) := lt_min hε₀ (lt_min (by linarith) (by linarith))
  have hε : 0 < ε := half_pos hm
  have hεm : ε < min ε₀ (min (c - a) (b - c)) := half_lt_self hm
  -- Every critical point of the band lies on the submanifold, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨s, rfl⟩ := hcrit ⟨hx, hfx⟩
    exact hc s
  obtain ⟨hε', hcompact'⟩ :=
    Icc_subset_and_isCompact_preimage_Icc hfs.continuous hcompact
      (hεm.trans_le (min_le_right _ _)).le
  obtain ⟨φ, -, hφ⟩ := hmain ε hε (hεm.trans_le (min_le_left _ _)) hcompact'
    fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  have hρ := IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge hn h.toIsCriticalSubmanifold
    g.toRiemannianMetric (F' := Fin r → ℝ) (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim hε
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n
  exact ⟨singularHomologySublevelPairIsoSymmetricBand hfs hac hcb hcompact hlev hε
    (hεm.trans_le (min_le_right _ _)).le R n ≪≫ (@asIso _ _ _ _ _ (hφ R n)).symm ≪≫
    asIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n)⟩

end IsNondegenerateCriticalSubmanifold

end Attachment

end SmoothEmbedding

section Family

variable {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I 2 M] {ι : Type*} [Finite ι] {E' H' P : ι → Type*}
  {S : ι → Type u} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  [∀ a, FiniteDimensional ℝ (E' a)] [∀ a, TopologicalSpace (H' a)]
  {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)} [∀ a, TopologicalSpace (S a)]
  [∀ a, ChartedSpace (H' a) (S a)] [∀ a, IsManifold (J a) 1 (S a)]
  [∀ a, NormedAddCommGroup (P a)] [∀ a, NormedSpace ℝ (P a)] [∀ a, FiniteDimensional ℝ (P a)]
  {f : M → ℝ} {n : ℕ∞ω} {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} (hn : n ≠ 0)
  {h : ∀ a, (i a).IsCriticalSubmanifold f}
  {g : ∀ a, RiemannianMetric fun s ↦ (i a).NormalSpace s hn} {ε : ℝ}
  (hdim : ∀ a, Module.finrank ℝ (P a) = Module.finrank ℝ E - Module.finrank ℝ (E' a)) {r : ι → ℕ}
  (hV : ∀ a, letI := (i a).normalSpaceFiberBundle hn (hdim a)
    HasLocalSubbundleFrames (P a) (Fin (r a)) ((h a).negativeNormalSpace hn (g a)))
  (hε : 0 < ε) {Z : Type u} [TopologicalSpace Z] {X : Set Z} (hX : IsClosed X)
  {φ : ∀ a, (h a).negativeDiscSpherePair hn (P a) (g a) ε ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hφ : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (φ a)))
  (hφX : ∀ a (x : (h a).negativeDiscBundle hn (P a) (g a) ε), TopPair.Hom.fst (φ a) x ∈ X →
    -(2⁻¹ * (h a).normalHessian hn x.val.proj x.val.snd x.val.snd) = ε)
  (hdisj : Pairwise fun a b ↦
    Disjoint (range (TopPair.Hom.fst (φ a)) \ X) (range (TopPair.Hom.fst (φ b)) \ X))
  (hφcover : X ∪ ⋃ a, range (TopPair.Hom.fst (φ a)) = univ)

omit [Finite ι] [∀ a, FiniteDimensional ℝ (E' a)] [∀ a, IsManifold (J a) 1 (S a)]
  [∀ a, NormedAddCommGroup (P a)] [∀ a, NormedSpace ℝ (P a)] [∀ a, FiniteDimensional ℝ (P a)] in
include hφ hφX hdisj hφcover in
/-- The hypotheses of the attachment theorems for finite families of gauge disc bundles
(`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles` and
`TauCeti.isIso_biproductLift_singularCohomologyMap_of_attach_gaugeDiscBundles`) for the disc-sphere
pairs of the norms `negativeNormalNorm`, given those of an attachment of the negative disc bundles:
the composites with `discSpherePairIso` are closed embeddings meeting `X` only along the sphere
bundles, with pairwise disjoint images outside `X`, covering `Z` together with `X`. -/
private theorem attach_discSpherePairIso_hom_comp_family :
    letI : ∀ a, TopologicalSpace
        (TotalSpace (Fin (r a) → ℝ) fun s ↦ (h a).negativeNormalSpace hn (g a) s) :=
      fun a ↦ subbundleTopology (P a) ((h a).negativeNormalSpace hn (g a))
    letI := fun a ↦ (h a).negativeNormalNorm hn (g a) hε
    (∀ a, IsClosedEmbedding
        (TopPair.Hom.fst (((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom ≫ φ a))) ∧
      (∀ a (v : gaugeDiscBundle (fun v : TotalSpace (Fin (r a) → ℝ)
          (fun s ↦ (h a).negativeNormalSpace hn (g a) s) ↦ ‖v.snd‖)),
        TopPair.Hom.fst (((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom ≫ φ a) v ∈ X →
          (v : TotalSpace (Fin (r a) → ℝ) fun s ↦ (h a).negativeNormalSpace hn (g a) s) ∈
            gaugeSphereBundle (fun v : TotalSpace (Fin (r a) → ℝ)
              (fun s ↦ (h a).negativeNormalSpace hn (g a) s) ↦ ‖v.snd‖)) ∧
      (Pairwise fun a b ↦ Disjoint
        (range (TopPair.Hom.fst (((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom ≫ φ a)) \ X)
        (range (TopPair.Hom.fst (((h b).discSpherePairIso hn (P b) (g b) (r b) hε).hom ≫ φ b)) \
          X)) ∧
      X ∪ ⋃ a, range
        (TopPair.Hom.fst (((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom ≫ φ a)) = univ := by
  let _ (a : ι) : TopologicalSpace
      (TotalSpace (Fin (r a) → ℝ) fun s ↦ (h a).negativeNormalSpace hn (g a) s) :=
    subbundleTopology (P a) ((h a).negativeNormalSpace hn (g a))
  let _ (a : ι) := (h a).negativeNormalNorm hn (g a) hε
  choose h₁ h₂ h₃ using fun a ↦
    (h a).attach_discSpherePairIso_hom_comp hn (P a) (g a) (r a) hε (φ a) (hφ a) (hφX a)
  exact ⟨h₁, h₂,
    fun a b hab ↦ (congrArg₂ (fun s t ↦ Disjoint (s \ X) (t \ X)) (h₃ a) (h₃ b)).mpr (hdisj hab),
    (congrArg (X ∪ ·) (iUnion_congr h₃)).trans hφcover⟩

include hdim hV hε hX hφ hφX hdisj hφcover in
/-- **Attaching the negative disc bundles of finitely many critical submanifolds induces direct-sum
isomorphisms on relative homology.** Let `i a : S a → M`, for `a` in a finite index type, be
critical submanifolds of `f`, each modelled on its own space, with fibre metrics `g a` on their
normal bundles for which the negative normal spaces form vector bundles `ν⁻ a` of rank `r a`. Let
`Z` be obtained from a closed subset `X` by attaching the negative disc bundles `D a ε`, `ε > 0`,
along their boundaries `S a ε`: maps of pairs `φ a : (D a ε, S a ε) ⟶ (Z, X)` which are closed
embeddings of `D a ε`, send a point of `D a ε` into `X` only if it lies in `S a ε`, have pairwise
disjoint images outside `X`, and cover `Z` together with `X`. Then the maps `φ a` induce an
isomorphism `⨁ a, Hₖ(D a ε, S a ε) ≅ Hₖ(Z, X)` on relative singular homology, with coefficients in
any abelian category with coproducts, in every degree. -/
theorem isIso_biproductDesc_singularHomologyMap_of_attach_negativeDiscBundles
    {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] [HasFiniteBiproducts C] (R : C)
    (k : ℕ) :
    IsIso (biproduct.desc fun a ↦ TopPair.singularHomologyMap (φ a) R k) := by
  let _ (a : ι) : FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
    (i a).normalSpaceFiberBundle hn (hdim a)
  have _ (a : ι) : VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
    (i a).normalSpaceVectorBundle hn (hdim a)
  let _ (a : ι) : TopologicalSpace
      (TotalSpace (Fin (r a) → ℝ) fun s ↦ (h a).negativeNormalSpace hn (g a) s) :=
    subbundleTopology (P a) ((h a).negativeNormalSpace hn (g a))
  let _ (a : ι) := (hV a).fiberBundle
  have _ (a : ι) := (hV a).vectorBundle
  let _ (a : ι) := (h a).negativeNormalNorm hn (g a) hε
  let _ (a : ι) := (h a).negativeNormalNormedSpace hn (g a) hε
  -- Read each attachment through the disc-sphere pair of the norms `negativeNormalNorm`, and apply
  -- the attachment theorem for finite families of gauge disc bundles.
  have hρ (a : ι) := isFiberGauge_norm
    ((h a).continuous_norm_negativeNormalNorm hn (g a) (r a) (hdim a) hε)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := attach_discSpherePairIso_hom_comp_family hn hε hφ hφX hdisj hφcover
  have key := isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles hρ h₁ hX h₂ h₃ h₄
    R k
  have hmap : IsIso (biproduct.map fun a ↦ TopPair.singularHomologyMap
      ((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom R k) :=
    (biproduct.mapIso fun a ↦ TopPair.singularHomologyMapIso R
      ((h a).discSpherePairIso hn (P a) (g a) (r a) hε) k).isIso_hom
  simp only [TopPair.singularHomologyMap_comp, ← biproduct.map_desc] at key
  exact IsIso.of_isIso_comp_left (biproduct.map fun a ↦ TopPair.singularHomologyMap
    ((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom R k) _

include hdim hV hε hX hφ hφX hdisj hφcover in
/-- **Attaching the negative disc bundles of finitely many critical submanifolds induces direct-sum
isomorphisms on relative cohomology.** Under the hypotheses of
`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_negativeDiscBundles`, the maps
`φ a : (D a ε, S a ε) ⟶ (Z, X)` induce an isomorphism `Hᵏ(Z, X) ≅ ⨁ a, Hᵏ(D a ε, S a ε)` on
relative singular cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_biproductLift_singularCohomologyMap_of_attach_negativeDiscBundles
    {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (K : Type*) [Ring K]
    [Linear K C] (N : C) (k : ℕ) :
    IsIso (biproduct.lift fun a ↦
      TopPair.singularCohomologyMap (R := R) (k := K) (M := N) (φ a) k) := by
  let _ (a : ι) : FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
    (i a).normalSpaceFiberBundle hn (hdim a)
  have _ (a : ι) : VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
    (i a).normalSpaceVectorBundle hn (hdim a)
  let _ (a : ι) : TopologicalSpace
      (TotalSpace (Fin (r a) → ℝ) fun s ↦ (h a).negativeNormalSpace hn (g a) s) :=
    subbundleTopology (P a) ((h a).negativeNormalSpace hn (g a))
  let _ (a : ι) := (hV a).fiberBundle
  have _ (a : ι) := (hV a).vectorBundle
  let _ (a : ι) := (h a).negativeNormalNorm hn (g a) hε
  let _ (a : ι) := (h a).negativeNormalNormedSpace hn (g a) hε
  have hρ (a : ι) := isFiberGauge_norm
    ((h a).continuous_norm_negativeNormalNorm hn (g a) (r a) (hdim a) hε)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := attach_discSpherePairIso_hom_comp_family hn hε hφ hφX hdisj hφcover
  have key := isIso_biproductLift_singularCohomologyMap_of_attach_gaugeDiscBundles hρ h₁ hX h₂ h₃ h₄
    R K N k
  have hmap : IsIso (biproduct.map fun a ↦ TopPair.singularCohomologyMap (R := R) (k := K)
      (M := N) ((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom k) :=
    (biproduct.mapIso fun a ↦ @asIso _ _ _ _ _
      ((h a).isIso_singularCohomologyMap_discSpherePairIso_hom hn (P a) (g a) (r a) hε
        R K N k)).isIso_hom
  simp only [TopPair.singularCohomologyMap_comp, ← biproduct.lift_map] at key
  exact IsIso.of_isIso_comp_right _ (biproduct.map fun a ↦ TopPair.singularCohomologyMap
    (R := R) (k := K) (M := N) ((h a).discSpherePairIso hn (P a) (g a) (r a) hε).hom k)

end Family

end TauCeti

namespace TauCeti.SmoothEmbedding

/-! ### The attachment across the level -/

section Attachment

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {E' H' P : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}

namespace IsCriticalSubmanifold

variable [IsManifold I 2 M] [IsManifold J 1 S] {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}
  (hn : n ≠ 0) {h : i.IsCriticalSubmanifold f} (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
  {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M} {c ε : ℝ}

/-- **The negative disc-sphere pair has the homology of its attachment across the level.** Let `i`
be a critical submanifold of a continuous function `f` on a Hausdorff manifold, let `g` be a fibre
metric on its normal bundle, and suppose that the negative normal spaces have continuous local
frames of size `r` and that the negative disc bundle `D_ε`, `ε > 0`, is compact. Let `Θ` be
continuous and injective on `D_ε` and put `f` there in the Morse–Bott normal form
`f (Θ v) = c + ½ Hessₛ (v, v)`. Then `(D_ε, S_ε)` has the relative homology of the lower sublevel
`L = {f ≤ c - ε}` with `Θ(D_ε)` attached: `Hₖ(D_ε, S_ε) ≅ Hₖ(L ∪ Θ(D_ε), L)`, with coefficients in
any abelian category with coproducts, in every degree. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_union (hf : Continuous f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) (hD : IsCompact (h.negativeDiscBundle hn P g ε))
    (hΘc : ContinuousOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘi : InjOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (k : ℕ) :
    Nonempty ((h.negativeDiscSpherePair hn P g ε).singularHomology R k ≅
      (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
        {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g ε)
        ).singularHomology R k) := by
  set D := h.negativeDiscBundle hn P g ε
  set L : Set M := {y | f y ≤ c - ε}
  -- `Θ` restricts to a map of pairs `(D_ε, S_ε) ⟶ (L ∪ Θ(D_ε), L)` attaching `D_ε` along `S_ε`.
  have hχ : MapsTo Θ D (L ∪ Θ '' D) := fun x hx ↦ Or.inr (mem_image_of_mem Θ hx)
  let χ : C(D, (L ∪ Θ '' D : Set M)) := ⟨hχ.restrict, hΘc.mapsToRestrict hχ⟩
  have hS (x : ↥(D ∩ {x | -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = ε})) :
      f (Θ x) ≤ c - ε :=
    (mem_negativeSphereBundle_iff_apply_le hΘ x.property.left).1
      ((mem_negativeSphereBundle hn).2
        ⟨((mem_negativeDiscBundle hn).1 x.property.left).left, x.property.right⟩)
  let φ : h.negativeDiscSpherePair hn P g ε ⟶
      TopPair.ofSubset (X := TopCat.of (L ∪ Θ '' D : Set M)) (Subtype.val ⁻¹' L) :=
    TopPair.ofHom (TopCat.ofHom χ)
      (TopCat.ofHom ⟨fun x ↦ ⟨χ (inclusion inter_subset_left x), hS x⟩,
        ((χ.continuous.comp (continuous_inclusion inter_subset_left)).subtype_mk _)⟩)
      (by ext; rfl)
  have hφ : IsClosedEmbedding χ := by
    have := isCompact_iff_compactSpace.1 hD
    exact χ.continuous.isClosedEmbedding fun x y hxy ↦
      Subtype.ext (hΘi x.property y.property (congrArg Subtype.val hxy))
  have := h.isIso_singularHomologyMap_of_attach_negativeDiscBundle hn g r hdim hV hε
    ((isClosed_le hf continuous_const).preimage continuous_subtypeVal) φ hφ
    (fun x hx ↦ ((mem_negativeSphereBundle hn).1
      ((mem_negativeSphereBundle_iff_apply_le hΘ x.property).2 hx)).right)
    (eq_univ_of_forall fun ⟨y, hy⟩ ↦ by
      rcases hy with hy | ⟨x, hx, rfl⟩
      · exact Or.inl hy
      · exact Or.inr ⟨⟨x, hx⟩, rfl⟩)
    R k
  exact ⟨asIso (TopPair.singularHomologyMap φ R k) ≪≫ TopPair.singularHomologyMapIso R
    (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) (subset_union_left : L ⊆ L ∪ Θ '' D)) k⟩

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [IsManifold I ∞ M] [SecondCountableTopology M] [J.Boundaryless] [IsManifold J ∞ S]
  [Nonempty S] {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The relative homology across a Morse–Bott level is that of the negative disc-sphere pair.**
Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `S` nonempty and `f = c` along
`i`, and let `g` be a smooth fibre metric on its normal bundle. Let `a < c < b` be such that the
band `f⁻¹[a, b]` is compact and all its critical points lie on `i`, and suppose that the negative
normal spaces relative to `g` have continuous local frames of size `r`. Then there is an `ε₀ > 0`
such that for every `0 < ε < ε₀` the relative homology `Hₖ({f ≤ b}, {f ≤ a})` is isomorphic to
the homology `Hₖ(D_ε, S_ε)` of the negative disc-sphere pair, with coefficients in any abelian
category with coproducts, in every degree. -/
theorem nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric)) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
      (R : C) (k : ℕ),
      Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R k ≅
        (h.negativeDiscSpherePair hn P g.toRiemannianMetric ε).singularHomology R k) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : CompactSpace S := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
    (hfs.of_le (by simp)) hc hac.le hcb.le hcompact hcrit
  have : T2Space S := i.isEmbedding.t2Space
  -- Crossing the level attaches `Θ(D_ε)` to `L = {f ≤ c - ε}`, for a normal form `Θ`, and
  -- `(D_ε, S_ε)` has the homology of this attachment.
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hmain⟩ :=
    h.nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle hn hfs hc hac hcb hcompact
      hcrit hdim g
  refine ⟨ε₀, hε₀, fun ε hε C _ _ _ R k ↦ ?_⟩
  obtain ⟨hsrc, hband⟩ := hmain ε hε
  obtain ⟨e₁⟩ := hband R k
  obtain ⟨e₂⟩ :=
    h.toIsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_union hn
      g.toRiemannianMetric hfs.continuous hdim hV hε.1
      (h.isCompact_negativeDiscBundle hn hfs hdim g ε)
      (Θ.contMDiffOn.continuousOn.mono hsrc) (Θ.toPartialEquiv.injOn.mono hsrc)
      (fun x hx ↦ hΘf x (hsrc hx)) R k
  exact ⟨e₁ ≪≫ e₂.symm⟩

end IsNondegenerateCriticalSubmanifold

end Attachment

end TauCeti.SmoothEmbedding
