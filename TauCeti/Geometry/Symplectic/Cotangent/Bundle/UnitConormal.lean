/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Conormal
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ContactType
import Mathlib.Analysis.Normed.Module.Normalize
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The unit conormal bundle is Legendrian

Let `i : Q → M` be a smooth embedding of a boundaryless manifold into a Riemannian manifold
without boundary, of codimension `k`, so that `dim Q + k = dim M`. Its conormal bundle `N*Q`, the
covectors along `i` annihilating the tangent images of `i`, is a vector bundle of rank `k` over `Q`
whose canonical inclusion into `T*M` is a Lagrangian embedding
(`TauCeti.CotangentBundle.isLagrangianEmbedding_conormalInclusion`). Its **unit conormal bundle**
(`TauCeti.CotangentBundle.unitConormal`) is the set of conormal covectors of norm one, the
preimage of the unit cosphere bundle `S*M` under the inclusion of `N*Q`.

The norm of covectors is homogeneous of degree one along the fibres, and the inclusion of `N*Q`
into `T*M` is linear on fibres, so it carries the Euler vector field of `N*Q` to that of `T*M`
(`TauCeti.mfderiv_vectorBundleEulerField_of_linear`). The differential of
the norm therefore sends the Euler field to `1` along the unit conormal bundle, so that it is a
regular level of the norm on `N*Q`. It carries the atlas of regular levels
(`TauCeti.CotangentBundle.unitConormalChartedSpace`), for which it is a smooth manifold of
dimension `dim M - 1` (`TauCeti.CotangentBundle.isManifold_unitConormal`), smoothly embedded in
`N*Q`. Its inclusion `TauCeti.CotangentBundle.unitConormalInclusion` into `S*M` is a smooth
embedding (`TauCeti.CotangentBundle.isSmoothEmbedding_unitConormalInclusion`) with image
`N*Q ∩ S*M` (`TauCeti.CotangentBundle.range_unitConormalInclusion`).

The Liouville form `λ` vanishes on `N*Q`, hence on the unit conormal bundle. So, for an ambient
manifold of positive dimension `n + 1`, the unit conormal bundle is a Legendrian embedding of a
manifold of dimension `n` into the contact manifold `S*M` of dimension `2 n + 1`, for its contact
structure `ker(λ|S*M)` (`TauCeti.CotangentBundle.isLegendrianEmbedding_unitConormalInclusion`).
This is also the kernel of the contact form `α_b = -λ|S*M` of the opposite coorientation, the
boundary form of the primitive `-λ` of `ω = -dλ`.

For a `C¹` closed embedding, the image `N*Q ∩ S*M` of the unit conormal bundle is closed in `S*M`
(`TauCeti.CotangentBundle.isClosed_range_unitConormalInclusion`), since `N*Q` is closed in `T*M`.
Closedness of the submanifold cannot be dropped: in positive codimension every point of the image
of `i` carries a unit conormal covector, and the unit covectors over a compact set form a compact
set, so a closed image of the unit conormal bundle forces a closed image of `i`
(`TauCeti.CotangentBundle.isClosed_range_of_isClosed_range_unitConormalInclusion`). Thus for a
`C¹` embedding of smaller dimension, the unit conormal bundle is closed in `S*M` exactly when the
submanifold is closed in `M` (`TauCeti.CotangentBundle.isClosed_range_unitConormalInclusion_iff`).

The atlas and the manifold structure only use that `i` is smooth with injective differentials;
the embedding into `S*M` uses that `i` is a smooth embedding. The vector bundle structure of `N*Q`
depends on `i`, so it is installed locally by `letI`, as is the atlas of the unit conormal bundle,
in the statements about it.

## Main definitions

* `TauCeti.CotangentBundle.unitConormal`: the unit conormal bundle, a subset of `N*Q`.
* `TauCeti.CotangentBundle.unitConormalInclusion`: its inclusion into `S*M`.
* `TauCeti.CotangentBundle.unitConormalChartedSpace`: its atlas as a regular level of the norm.

## Main results

* `TauCeti.CotangentBundle.isManifold_unitConormal`: the unit conormal bundle is a smooth manifold
  of dimension `dim M - 1`.
* `TauCeti.CotangentBundle.isSmoothEmbedding_unitConormalInclusion`: it is smoothly embedded in
  `S*M`.
* `TauCeti.CotangentBundle.isLegendrianEmbedding_unitConormalInclusion`: it is a Legendrian
  embedding for the contact structure `ker(λ|S*M)`.
* `TauCeti.CotangentBundle.isClosed_range_unitConormalInclusion_iff`: in positive codimension, it
  is closed in `S*M` exactly when the submanifold is closed in `M`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Chapter 1 (spaces of contact elements and their Legendrian submanifolds).
* V. I. Arnold, A. B. Givental, *Symplectic geometry*, in Dynamical Systems IV, Encyclopaedia of
  Mathematical Sciences 4, Springer, 2001, Chapter 4.
-/

public section

noncomputable section

open Bundle Function Manifold Module Set
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ} {i : Q → M}

section Definitions

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (J I k i) in
/-- The **unit conormal bundle** of a map `i : Q → M` into a Riemannian manifold: the conormal
covectors of norm one, as a subset of the total space of the conormal spaces of `i`. It is the
preimage of the unit cosphere bundle `S*M` under the inclusion of the conormal spaces into `T*M`.
-/
def unitConormal : Set (TotalSpace (Fin k → ℝ) fun q ↦ conormalSpace J I i q) :=
  conormalInclusion (Fin k → ℝ) J I i ⁻¹' cosphereBundle I M

@[simp]
theorem mem_unitConormal {z : TotalSpace (Fin k → ℝ) fun q ↦ conormalSpace J I i q} :
    z ∈ unitConormal J I k i ↔ conormalInclusion (Fin k → ℝ) J I i z ∈ cosphereBundle I M :=
  Iff.rfl

variable (J I k i) in
/-- The inclusion of the unit conormal bundle of `i` into the unit cosphere bundle `S*M`: the
restriction of the inclusion of the conormal spaces to the preimage of `S*M`. -/
def unitConormalInclusion : unitConormal J I k i → cosphereBundle I M :=
  (cosphereBundle I M).restrictPreimage (conormalInclusion (Fin k → ℝ) J I i)

@[simp]
theorem coe_unitConormalInclusion (z : unitConormal J I k i) :
    (unitConormalInclusion J I k i z : CotangentBundle I M) =
      conormalInclusion (Fin k → ℝ) J I i z :=
  (rfl)

/-- The image of the unit conormal bundle in `S*M` is the set of unit covectors which are
conormal to `i`, that is, `N*Q ∩ S*M`. -/
@[simp]
theorem range_unitConormalInclusion :
    range (unitConormalInclusion J I k i) =
      {z : cosphereBundle I M | (z : CotangentBundle I M) ∈ conormal J I i} :=
  -- The preimage `Subtype.val ⁻¹' N*Q` is `{z | ↑z ∈ N*Q}` by definition.
  (range_restrictPreimage _ _).trans (by rw [range_conormalInclusion]; rfl)

/-- For an injective map `i`, the inclusion of the unit conormal bundle into `S*M` is injective. -/
theorem unitConormalInclusion_injective (hi : Injective i) :
    Injective (unitConormalInclusion J I k i) :=
  restrictPreimage_injective _ (conormalInclusion_injective (Fin k → ℝ) hi)

end Definitions

section Closed

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **The unit conormal bundle of a closed submanifold is closed.** For a `C¹` closed embedding
`i : Q → M`, the image `N*Q ∩ S*M` of the unit conormal bundle of `i` is closed in `S*M`. -/
theorem isClosed_range_unitConormalInclusion [IsManifold I 1 M] [IsManifold J 1 Q]
    (hi : Topology.IsClosedEmbedding i) (hic : ContMDiff J I 1 i) :
    IsClosed (range (unitConormalInclusion J I k i)) := by
  rw [range_unitConormalInclusion]
  exact (isClosed_conormal hi hic).preimage continuous_subtypeVal

/-- **A closed unit conormal bundle lies over a closed image.** If `Q` has smaller dimension than
`M` and the image `N*Q ∩ S*M` of the unit conormal bundle of `i` is closed in `S*M`, then the image
of `i` is closed in `M`. Indeed, every point of the image of `i` carries a unit conormal covector,
and the unit conormal covectors over a compact subset of `M` form a compact set. -/
theorem isClosed_range_of_isClosed_range_unitConormalInclusion [T2Space M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]
    (hdim : finrank ℝ F < finrank ℝ E) (h : IsClosed (range (unitConormalInclusion J I k i))) :
    IsClosed (range i) := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  rw [range_unitConormalInclusion] at h
  -- The set `{z | ↑z ∈ N*Q}` of `S*M` is the preimage of `N*Q` by definition.
  have hC : IsClosed (cosphereBundle I M ∩ conormal J I i) := by
    have h' : IsClosed ((↑) ⁻¹' conormal J I i : Set (cosphereBundle I M)) := h
    simpa only [Subtype.image_preimage_coe] using h'.trans isClosed_cosphereBundle
  refine isClosed_of_closure_subset fun x hx ↦ ?_
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  -- The unit conormal covectors over `K` form a compact set `A`, whose projection is closed and
  -- contains `range i ∩ K`.
  set A := (cosphereBundle I M ∩
    π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ⁻¹' K) ∩ (cosphereBundle I M ∩
      conormal J I i)
  have hA : IsCompact A := (isCompact_cosphereBundle_inter_preimage_proj (I := I) hK).inter_right hC
  have hsub : range i ∩ K ⊆ π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) '' A := by
    rintro y hy
    obtain ⟨⟨q, rfl⟩, hqK⟩ := mem_inter_iff _ _ _ |>.1 hy
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (conormalSpace_ne_bot (J := J) (I := I) hdim i q)
    have hn : TotalSpace.mk' (E →L[ℝ] ℝ) (i q) (NormedSpace.normalize p) ∈ cosphereBundle I M :=
      mem_cosphereBundle.2 (NormedSpace.norm_normalize (V := TangentSpace I (i q) →L[ℝ] ℝ) hp0)
    have hpn : NormedSpace.normalize p ∈ conormalSpace J I i q := by
      rw [NormedSpace.normalize]
      exact Submodule.smul_mem _ _ hp
    exact mem_image_of_mem _ (mem_inter (mem_inter hn hqK) (mem_inter hn (mk_mem_conormal hpn)))
  have hx' : x ∈ closure (range i ∩ K) :=
    mem_closure_iff_frequently.2 ((mem_closure_iff_frequently.1 hx).and_eventually hxK)
  obtain ⟨z, hz, rfl⟩ :=
    closure_minimal hsub (hA.image (FiberBundle.continuous_proj _ _)).isClosed hx'
  obtain ⟨q, hq, -⟩ := mem_conormal_iff.1 hz.2.2
  exact mem_range.2 ⟨q, hq⟩

/-- **The unit conormal bundle is closed exactly over a closed submanifold.** For a `C¹`
embedding `i : Q → M` into a Riemannian manifold of larger dimension, the image `N*Q ∩ S*M` of the
unit conormal bundle of `i` is closed in `S*M` exactly when the image of `i` is closed in `M`. -/
theorem isClosed_range_unitConormalInclusion_iff [T2Space M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [IsManifold I 1 M] [IsManifold J 1 Q]
    [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] (hi : Topology.IsEmbedding i)
    (hic : ContMDiff J I 1 i) (hdim : finrank ℝ F < finrank ℝ E) :
    IsClosed (range (unitConormalInclusion J I k i)) ↔ IsClosed (range i) :=
  ⟨isClosed_range_of_isClosed_range_unitConormalInclusion hdim,
    fun h ↦ isClosed_range_unitConormalInclusion ⟨hi, h⟩ hic⟩

end Closed

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold J ∞ Q]

section Level

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The norm of conormal covectors is smooth along the unit conormal bundle. -/
theorem contMDiffAt_norm_snd_conormalInclusion (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E)
    {z : TotalSpace (Fin k → ℝ) fun q ↦ conormalSpace J I i q} (hz : z ∈ unitConormal J I k i) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    ContMDiffAt (J.prod 𝓘(ℝ, Fin k → ℝ)) 𝓘(ℝ) ∞
      (fun z ↦ ‖(conormalInclusion (Fin k → ℝ) J I i z).snd‖) z := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  exact (contMDiffAt_norm_snd_of_mem_cosphereBundle _ hz).comp z
    (contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk z)

/-- **The unit conormal bundle is a regular level.** The value `1` is a regular value of the norm
of conormal covectors: its differential sends the Euler vector field of the conormal bundle to the
norm. -/
theorem isRegularValue_norm_snd_conormalInclusion (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    IsRegularValue (J.prod 𝓘(ℝ, Fin k → ℝ)) 𝓘(ℝ)
      (fun z ↦ ‖(conormalInclusion (Fin k → ℝ) J I i z).snd‖) 1 := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
  rw [isRegularValue_iff]
  intro z hz
  rw [isRegularPoint_iff]
  have hz' : z ∈ unitConormal J I k i := mem_unitConormal.2 (mem_cosphereBundle.2 hz)
  have hne := snd_ne_zero_of_mem_cosphereBundle hz'
  have hd : mfderiv (J.prod 𝓘(ℝ, Fin k → ℝ)) 𝓘(ℝ)
      (fun z ↦ ‖(conormalInclusion (Fin k → ℝ) J I i z).snd‖) z (vectorBundleEulerField J z) =
        ‖(conormalInclusion (Fin k → ℝ) J I i z).snd‖ := by
    have hnorm : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ)
        (fun w : CotangentBundle I M ↦ ‖w.snd‖) (conormalInclusion (Fin k → ℝ) J I i z) :=
      (contMDiffAt_norm_snd_of_mem_cosphereBundle _ hz').mdifferentiableAt (by simp)
    have hι : MDifferentiableAt (J.prod 𝓘(ℝ, Fin k → ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (conormalInclusion (Fin k → ℝ) J I i) z :=
      (contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk z).mdifferentiableAt (by simp)
    have h := mfderiv_comp_apply (g := fun w : CotangentBundle I M ↦ ‖w.snd‖) z hnorm hι
      (vectorBundleEulerField J z)
    -- The conormal inclusion is linear on fibres, so it preserves Euler fields.
    rw [mfderiv_vectorBundleEulerField_of_linear (fun q ↦ (conormalSpace J I i q).subtype)
      (conormalInclusion_apply (Fin k → ℝ) J I i) hι,
      mfderiv_norm_snd_vectorBundleEulerField hne] at h
    exact h
  -- The differential is onto `ℝ`, whose tangent spaces are `ℝ` itself.
  intro y
  refine ⟨(NormedSpace.fromTangentSpace (𝕜 := ℝ) ‖(conormalInclusion (Fin k → ℝ) J I i z).snd‖ y /
    ‖(conormalInclusion (Fin k → ℝ) J I i z).snd‖) • vectorBundleEulerField J z, ?_⟩
  rw [map_smul, hd]
  exact div_mul_cancel₀ _ ((norm_ne_zero_iff (a := (conormalInclusion (Fin k → ℝ) J I i z).snd)).2
    hne)

variable [FiniteDimensional ℝ F] [J.Boundaryless]

variable (k) in
/-- The atlas of the unit conormal bundle of a smooth map `i` with injective differentials: the
atlas `TauCeti.regularLevelChartedSpace` of the regular level `‖p‖ = 1` of the norm on the
conormal bundle, modelled on `Fin (dim M - 1) → ℝ`. Install this definition locally with `letI`,
after the conormal bundle structure `TauCeti.CotangentBundle.conormalFiberBundle`. -/
@[instance_reducible]
def unitConormalChartedSpace (hi : ContMDiff J I ∞ i) (hinj : ∀ q, Injective (mfderiv J I i q))
    (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    ChartedSpace (Fin (finrank ℝ E - 1) → ℝ) (unitConormal J I k i) :=
  letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  regularLevelChartedSpace
    (fun z hz ↦ (contMDiffAt_norm_snd_conormalInclusion hi hinj hk hz).of_le ENat.LEInfty.out)
    (isRegularValue_norm_snd_conormalInclusion hi hinj hk)
    (by rw [finrank_self, finrank_conormalBundleModel hk])

/-- **The unit conormal bundle is a smooth manifold**, of dimension `dim M - 1`. -/
theorem isManifold_unitConormal (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    letI := unitConormalChartedSpace k hi hinj hk
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) ∞ (unitConormal J I k i) := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
  exact isManifold_regularLevel ENat.LEInfty.out
    (fun z hz ↦ contMDiffAt_norm_snd_conormalInclusion hi hinj hk hz)
    (isRegularValue_norm_snd_conormalInclusion hi hinj hk)
    (by rw [finrank_self, finrank_conormalBundleModel hk])

/-- **The unit conormal bundle is a smoothly embedded hypersurface** of the conormal bundle. -/
theorem isSmoothEmbedding_coe_unitConormal (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    letI := unitConormalChartedSpace k hi hinj hk
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) (J.prod 𝓘(ℝ, Fin k → ℝ)) ∞
      (Subtype.val :
        unitConormal J I k i → TotalSpace (Fin k → ℝ) fun q ↦ conormalSpace J I i q) := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
  exact isSmoothEmbedding_coe_regularLevel ENat.LEInfty.out
    (fun z hz ↦ contMDiffAt_norm_snd_conormalInclusion hi hinj hk hz)
    (isRegularValue_norm_snd_conormalInclusion hi hinj hk)
    (by rw [finrank_self, finrank_conormalBundleModel hk])

end Level

section Legendrian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]

/-- For a smooth map `i : Q → M` with injective differentials, the inclusion of its unit conormal
bundle into `S*M` is smooth. -/
theorem contMDiff_unitConormalInclusion (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    letI := unitConormalChartedSpace k hi hinj hk
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) ∞ (unitConormalInclusion J I k i) := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := unitConormalChartedSpace k hi hinj hk
  exact isSmoothEmbedding_coe_cosphereBundle.contMDiff_iff_comp.2
    ((contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk).comp
      (isSmoothEmbedding_coe_unitConormal hi hinj hk).contMDiff)

/-- **The unit conormal bundle is smoothly embedded in the unit cosphere bundle.** For a smooth
embedding `i : Q → M`, the inclusion of its unit conormal bundle into `S*M` is a smooth
embedding. -/
theorem isSmoothEmbedding_unitConormalInclusion (hi : IsSmoothEmbedding J I ∞ i)
    (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi.contMDiff (by simp)
      (hi.isImmersion.mfderiv_injective (by simp)) hk
    letI := unitConormalChartedSpace k hi.contMDiff (hi.isImmersion.mfderiv_injective (by simp)) hk
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) ∞ (unitConormalInclusion J I k i) := by
  have hinj := hi.isImmersion.mfderiv_injective (by simp)
  let := conormalFiberBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := unitConormalChartedSpace k hi.contMDiff hinj hk
  have := isManifold_unitConormal hi.contMDiff hinj hk
  have hι := isSmoothEmbedding_conormalInclusion (n := ∞) hi (by simp) hk
  have hv := isSmoothEmbedding_coe_unitConormal hi.contMDiff hinj hk
  have hS := isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)
  have hf := contMDiff_unitConormalInclusion hi.contMDiff hinj hk
  -- Followed by the inclusion of `S*M` into `T*M`, the map is the inclusion of the unit conormal
  -- bundle into the conormal bundle, followed by the inclusion of the conormal bundle into `T*M`.
  have hcomp : (Subtype.val : cosphereBundle I M → CotangentBundle I M) ∘
      unitConormalInclusion J I k i = conormalInclusion (Fin k → ℝ) J I i ∘ Subtype.val :=
    (rfl)
  refine ⟨hf.isImmersion_of_injective_mfderiv (by simp) fun z ↦ ?_,
    Topology.IsEmbedding.of_comp hf.continuous continuous_subtypeVal
      (hcomp ▸ hι.isEmbedding.comp hv.isEmbedding)⟩
  have h : Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (conormalInclusion (Fin k → ℝ) J I i ∘ Subtype.val) z) := by
    rw [mfderiv_comp z ((hι.contMDiff _).mdifferentiableAt (by simp))
      ((hv.contMDiff z).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    exact (hι.isImmersion.mfderiv_injective (by simp) _).comp
      (hv.isImmersion.mfderiv_injective (by simp) z)
  rw [← hcomp, mfderiv_comp z ((hS.contMDiff _).mdifferentiableAt (by simp))
    ((hf z).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

/-- **The unit conormal bundle is Legendrian.** For a smooth embedding `i : Q → M` into a
Riemannian manifold of positive dimension `n + 1`, the inclusion of the unit conormal bundle, a
manifold of dimension `n`, into the unit cosphere bundle is a Legendrian embedding for the contact
structure `ker(λ|S*M)`. This is also the kernel of the contact form `α_b = -λ|S*M`, the
restriction of the primitive `-λ` of `ω = -dλ` (`TauCeti.SmoothForm.kerDistribution_neg`). -/
theorem isLegendrianEmbedding_unitConormalInclusion [Nontrivial E]
    (hi : IsSmoothEmbedding J I ∞ i) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi.contMDiff (by simp)
      (hi.isImmersion.mfderiv_injective (by simp)) hk
    letI := unitConormalChartedSpace k hi.contMDiff (hi.isImmersion.mfderiv_injective (by simp)) hk
    IsLegendrianEmbedding 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ)
      (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
        (liouvilleForm I M)).kerDistribution
      (unitConormalInclusion J I k i) := by
  have hinj := hi.isImmersion.mfderiv_injective (by simp)
  let := conormalFiberBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := unitConormalChartedSpace k hi.contMDiff hinj hk
  have := isManifold_unitConormal hi.contMDiff hinj hk
  have hv := isSmoothEmbedding_coe_unitConormal hi.contMDiff hinj hk
  have hS := isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)
  have hf := contMDiff_unitConormalInclusion hi.contMDiff hinj hk
  -- The kernel of `λ|S*M` is a `C¹` contact structure, which needs a `C²` manifold structure.
  have : IsManifold 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (1 + 1)
      (cosphereBundle I M) := .of_le (n := ∞) (by norm_num)
  refine (isLegendrianEmbedding_iff_of_isSmoothEmbedding
    (isSmoothEmbedding_unitConormalInclusion hi hk)).2
    ⟨isContactForm_mpullback_liouvilleForm_cosphereBundle.isContactDistribution_kerDistribution,
      (isSmoothEmbedding_unitConormalInclusion hi hk).isImmersion, ?_, ?_⟩
  · -- The Liouville form vanishes on conormal covectors.
    rw [SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero _ hf]
    apply Subtype.ext
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
      ← TauCeti.mpullback_comp (hf.mdifferentiable (by simp))
        (hS.contMDiff.mdifferentiable (by simp))]
    exact mpullback_liouvilleForm_eq_zero_of_conormal
      (g := fun z : unitConormal J I k i ↦ z.val.proj)
      (fun z ↦ conormalInclusion_proj (Fin k → ℝ) J I i z.val)
      ((hS.contMDiff.comp hf).mdifferentiable (by simp))
      (((Bundle.contMDiff_proj _).comp hv.contMDiff).mdifferentiable (by simp))
      (fun z ↦ (hi.contMDiff _).mdifferentiableAt (by simp))
      (fun z ↦ conormalInclusion_snd_comp_mfderiv (Fin k → ℝ) J I i z.val)
  · rw [finrank_fin_fun, finrank_fin_fun, finrank_prod, ContinuousLinearMap.dual_finrank_eq]
    have := Module.finrank_pos (R := ℝ) (M := E)
    omega

end Legendrian

end TauCeti.CotangentBundle
