/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The differential image of a smooth embedding as a `C^m` vector subbundle

For a `C^n` map `f : M → N` (`m + 1 ≤ n`) with everywhere injective differential `mfderiv I J f x`,
transporting local frames of `TangentSpace I` along `mfderiv I J f` yields `C^m` local subbundle
frames of `(mfderiv I J f x).toLinearMap.range` inside `f *ᵖ TangentSpace J`
(`ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv`). Over `ℝ` or `ℂ` with
finite-dimensional `E`, this equips `f.pullbackTangentRange` for a `SmoothEmbedding` `f` with its
canonical `C^m` vector subbundle structure (`tangentRangeContMDiffVectorBundle`) and induces a `C^m`
bundle diffeomorphism `f.tangentBundleDiffeomorphTangentRange` from `TangentSpace I` onto
`f.pullbackTangentRange`. We also prove `Manifold.IsImmersion.tangentMap_injective_iff` and
`TauCeti.SmoothEmbedding.ofIsClosedEmbedding`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Proposition 10.34.
-/

public noncomputable section

open Bundle Set Function Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω}

/-- For a `C^n` immersion (`n ≠ 0`), the induced map `tangentMap I J f` on tangent bundles is
injective if and only if the base map `f` is injective. -/
theorem Manifold.IsImmersion.tangentMap_injective_iff {f : M → N}
    (hf : Manifold.IsImmersion I J n f) (hn : n ≠ 0) :
    Injective (tangentMap I J f) ↔ Injective f := by
  refine ⟨fun hinj x₁ x₂ hfx ↦ ?_, fun hinj ⟨x₁, v₁⟩ ⟨x₂, v₂⟩ hp ↦ ?_⟩
  · have h0 : tangentMap I J f ⟨x₁, 0⟩ = tangentMap I J f ⟨x₂, 0⟩ := by
      simp only [tangentMap, map_zero]; congr 1
    exact congrArg TotalSpace.proj (hinj h0)
  · obtain rfl : x₁ = x₂ := hinj (congrArg TotalSpace.proj hp)
    simp only [tangentMap, TotalSpace.mk_inj] at hp ⊢
    exact hf.mfderiv_injective hn x₁ hp

/-- A `C^n` smooth embedding (`n ≠ 0`) has injective `tangentMap`. -/
theorem Manifold.IsSmoothEmbedding.tangentMap_injective {f : M → N}
    (hf : Manifold.IsSmoothEmbedding I J n f) (hn : n ≠ 0) :
    Injective (tangentMap I J f) :=
  (hf.isImmersion.tangentMap_injective_iff hn).2 hf.isEmbedding.injective

/-- A closed topological embedding that is also a `C^n` immersion is a `C^n` smooth embedding. -/
theorem Manifold.IsImmersion.isSmoothEmbedding_of_isClosedEmbedding {f : M → N}
    (hf : Manifold.IsImmersion I J n f) (hcl : IsClosedEmbedding f) :
    Manifold.IsSmoothEmbedding I J n f :=
  ⟨hf, hcl.isEmbedding⟩

namespace TauCeti.SmoothEmbedding

/-- Bundle a `C^n` immersion that is a closed topological embedding as a `SmoothEmbedding`. -/
def ofIsClosedEmbedding (f : M → N) (hf : Manifold.IsImmersion I J n f)
    (hcl : IsClosedEmbedding f) : SmoothEmbedding I J n M N :=
  ofIsSmoothEmbedding f (hf.isSmoothEmbedding_of_isClosedEmbedding hcl)

@[simp]
theorem coe_ofIsClosedEmbedding (f : M → N) (hf : Manifold.IsImmersion I J n f)
    (hcl : IsClosedEmbedding f) : ⇑(ofIsClosedEmbedding f hf hcl) = f := by
  simp [ofIsClosedEmbedding]

@[simp]
theorem ofIsClosedEmbedding_apply (f : M → N) (hf : Manifold.IsImmersion I J n f)
    (hcl : IsClosedEmbedding f) (x : M) : ofIsClosedEmbedding f hf hcl x = f x := by
  simp [ofIsClosedEmbedding]

/-- `ofIsClosedEmbedding` retains its underlying closed-embedding property. -/
theorem isClosedEmbedding_ofIsClosedEmbedding (f : M → N) (hf : Manifold.IsImmersion I J n f)
    (hcl : IsClosedEmbedding f) : IsClosedEmbedding (ofIsClosedEmbedding f hf hcl) := by
  simpa using hcl

/-- A smooth embedding constructed from a closed topological embedding has closed range. -/
theorem isClosed_range_ofIsClosedEmbedding (f : M → N) (hf : Manifold.IsImmersion I J n f)
    (hcl : IsClosedEmbedding f) : IsClosed (range (ofIsClosedEmbedding f hf hcl)) := by
  simpa using hcl.isClosed_range

/-- A bundled `C^n` smooth embedding (`n ≠ 0`) has injective `tangentMap`. -/
theorem tangentMap_injective (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    Injective (tangentMap I J (f : M → N)) :=
  f.isSmoothEmbedding.tangentMap_injective hn

/-- At each point `x : M`, the differential `mfderiv I J f x` of a positive-regularity smooth
embedding restricts to a continuous linear equivalence onto `f.tangentRange x hn`. Neither
finite-dimensionality nor completeness of `𝕜` is required. -/
def tangentSpaceEquivTangentRange (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    TangentSpace I x ≃L[𝕜] f.tangentRange x hn :=
  let heq := LinearEquiv.ofInjective (mfderiv I J (f : M → N) x).toLinearMap
    (f.isImmersion.mfderiv_injective hn x)
  { heq with
    continuous_toFun := (mfderiv I J (f : M → N) x).continuous.subtype_mk _
    continuous_invFun := by
      obtain ⟨L, hL⟩ := isDiffImmersionAt_iff.mp (f.isImmersion.isDiffImmersionAt hn x)
      exact (L.continuous.comp continuous_subtype_val).congr fun ⟨_, u, rfl⟩ ↦
        (hL u).trans (heq.symm_apply_apply u).symm }

@[simp]
theorem coe_tangentSpaceEquivTangentRange_apply (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) (u : TangentSpace I x) :
    (f.tangentSpaceEquivTangentRange x hn u : TangentSpace J (f x)) =
      mfderiv I J (f : M → N) x u := by rfl

@[simp]
theorem tangentSpaceEquivTangentRange_symm_mfderiv (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) (u : TangentSpace I x) :
    (f.tangentSpaceEquivTangentRange x hn).symm
      ⟨mfderiv I J (f : M → N) x u, ⟨u, rfl⟩⟩ = u :=
  (f.tangentSpaceEquivTangentRange x hn).symm_apply_apply u

end TauCeti.SmoothEmbedding

section SubbundleFrames

/-- The image of `mfderiv I J f x` viewed directly as a `𝕜`-submodule of the pullback fibre
`(f *ᵖ (TangentSpace J)) x`. -/
@[expose]
def TauCeti.pullbackMfderivRange (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 V G)
    (f : M → N) (x : M) : Submodule 𝕜 ((f *ᵖ (TangentSpace J)) x) :=
  ((mfderiv I J f x).toLinearMap : TangentSpace I x →ₗ[𝕜] (f *ᵖ (TangentSpace J)) x).range

@[simp]
theorem TauCeti.mem_pullbackMfderivRange_iff (I : ModelWithCorners 𝕜 E H)
    (J : ModelWithCorners 𝕜 V G) (f : M → N) (x : M) (v : (f *ᵖ (TangentSpace J)) x) :
    v ∈ TauCeti.pullbackMfderivRange I J f x ↔ v ∈ (mfderiv I J f x).range := Iff.rfl

variable [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M]

/-- **Local subbundle frames for the image of an injective differential.** If `f : M → N` is `C^n`
with `m + 1 ≤ n` and `mfderiv I J f x` is injective at every `x : M`, then pushing forward local
frames of `TangentSpace I` associated with any basis `b : Module.Basis ι 𝕜 E` gives `C^m` local
subbundle frames of `TauCeti.pullbackMfderivRange I J f` inside `f *ᵖ TangentSpace J`. -/
theorem ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis {ι : Type*}
    (b : Module.Basis ι 𝕜 E) {K : Type*} [FunLike K M N] [ContinuousMapClass K M N] {f : K}
    (hf : ContMDiff I J n f) (hm : m + 1 ≤ n)
    (hinj : ∀ x, Injective (mfderiv I J (f : M → N) x)) :
    TauCeti.HasLocalContMDiffSubbundleFrames I m V ι
      (TauCeti.pullbackMfderivRange I J (f : M → N)) := by
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  have hfm : ContMDiff I J m f := hf.of_le ((le_add_right le_rfl).trans hm)
  have hTf := ContMDiff.contMDiff_tangentMap hf hm
  refine TauCeti.hasLocalContMDiffSubbundleFrames_iff.2 fun x₀ ↦ ?_
  let e := trivializationAt E (TangentSpace I) x₀
  let A (x : M) : TangentSpace I x →ₗ[𝕜] ((f : M → N) *ᵖ (TangentSpace J)) x :=
    (mfderiv I J (f : M → N) x).toLinearMap
  let X (i : ι) (x : M) : ((f : M → N) *ᵖ (TangentSpace J)) x := A x (e.localFrame b i x)
  have hX (i : ι) : ContMDiffOn I (I.prod 𝓘(𝕜, V)) m
      (fun y ↦ TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) y (X i y)) e.baseSet :=
    fun x hx ↦ ((Pullback.contMDiffAt_iff f hfm.contMDiffAt).2 ⟨contMDiffAt_id,
      hTf.contMDiffAt.comp x ((e.contMDiffOn_localFrame_baseSet (I := I) (n := m) b i).contMDiffAt
        (e.open_baseSet.mem_nhds hx))⟩).contMDiffWithinAt
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x₀, X,
    ⟨fun i ↦ (hX i).continuousOn, fun {x} hx ↦ ?_, fun {x} hx ↦
      e.span_range_localFrame_map b (A x) hx⟩, hX⟩
  have hframe : (fun i ↦ e.localFrame b i x) = e.basisAt b hx :=
    funext fun _ ↦ e.localFrame_apply_of_mem_baseSet b hx
  exact (hframe ▸ (e.basisAt b hx).linearIndependent).map' (A x) (LinearMap.ker_eq_bot.2 (hinj x))

/-- Finite-dimensional specialization of
`ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis` using `Module.finBasis 𝕜 E`. -/
theorem ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv [FiniteDimensional 𝕜 E]
    {K : Type*} [FunLike K M N] [ContinuousMapClass K M N] {f : K}
    (hf : ContMDiff I J n f) (hm : m + 1 ≤ n)
    (hinj : ∀ x, Injective (mfderiv I J (f : M → N) x)) :
    TauCeti.HasLocalContMDiffSubbundleFrames I m V (Fin (Module.finrank 𝕜 E))
      (TauCeti.pullbackMfderivRange I J (f : M → N)) :=
  ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis (Module.finBasis 𝕜 E) hf hm hinj

/-- A `C^n` immersion (`n ≠ 0`, `m + 1 ≤ n`) of a finite-dimensional manifold `M` has `C^m` local
subbundle frames for `TauCeti.pullbackMfderivRange I J f` inside `f *ᵖ TangentSpace J`. -/
theorem Manifold.IsImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv
    [FiniteDimensional 𝕜 E] {K : Type*} [FunLike K M N] [ContinuousMapClass K M N] {f : K}
    (hf : Manifold.IsImmersion I J n f) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    TauCeti.HasLocalContMDiffSubbundleFrames I m V (Fin (Module.finrank 𝕜 E))
      (TauCeti.pullbackMfderivRange I J (f : M → N)) :=
  ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv hf.contMDiff hm (hf.mfderiv_injective hn)

namespace TauCeti.SmoothEmbedding

omit [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M] in
/-- `f.tangentRange x hn` viewed directly as a `𝕜`-submodule of the pullback fibre
`((f : M → N) *ᵖ (TangentSpace J)) x`. -/
@[expose]
def pullbackTangentRange (f : SmoothEmbedding I J n M N) (_hn : n ≠ 0) :
    Π x : M, Submodule 𝕜 (((f : M → N) *ᵖ (TangentSpace J)) x) :=
  pullbackMfderivRange I J (f : M → N)

omit [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M] in
@[simp]
theorem mem_pullbackTangentRange_iff (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M)
    (v : ((f : M → N) *ᵖ (TangentSpace J)) x) :
    v ∈ f.pullbackTangentRange hn x ↔ v ∈ f.tangentRange x hn := Iff.rfl

/-- For a `C^n` smooth embedding `f` (`n ≠ 0`, `m + 1 ≤ n`) with finite-dimensional source model
`E`, `f.pullbackTangentRange hn` admits `C^m` local subbundle frames inside
`f *ᵖ TangentSpace J`. -/
theorem hasLocalContMDiffSubbundleFrames_tangentRange [FiniteDimensional 𝕜 E]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    HasLocalContMDiffSubbundleFrames I m V (Fin (Module.finrank 𝕜 E))
      (fun x ↦ f.pullbackTangentRange hn x) :=
  f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv hn hm

section BundleDiffeomorph

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I (m + 1) M] in
/-- The subspace topology on the total space of `f.pullbackTangentRange hn` induced from
`TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))`. Install with `letI`. -/
@[instance_reducible]
def tangentRangeTopology (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    TopologicalSpace
      (TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x)) :=
  subbundleTopology V (F' := Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x)

/-- The fibre-bundle structure on `f.pullbackTangentRange hn` given by its `C^m` local subbundle
frames. Install with `letI`. -/
@[instance_reducible]
def tangentRangeFiberBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    FiberBundle (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x) :=
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).fiberBundle

/-- The `𝕜`-vector bundle structure on `f.pullbackTangentRange hn` as a subbundle of
`f *ᵖ TangentSpace J`. -/
theorem tangentRangeVectorBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    VectorBundle 𝕜 (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x) :=
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).vectorBundle

variable [IsManifold J (m + 1) N]

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]
  [IsManifold I 1 M] [IsManifold I (m + 1) M] in
private theorem pullbackTangentContMDiffVectorBundle (f : SmoothEmbedding I J n M N)
    (hm : m + 1 ≤ n) :
    ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
  letI := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  ContMDiffVectorBundle.pullback V (TangentSpace J) I
    ⟨f, f.contMDiff.of_le ((le_add_right le_rfl).trans hm)⟩

/-- **The differential image `f.pullbackTangentRange hn` is a `C^m` vector subbundle of
`f *ᵖ TangentSpace J`.** -/
theorem tangentRangeContMDiffVectorBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    letI := f.tangentRangeVectorBundle hn hm
    ContMDiffVectorBundle m (Fin (Module.finrank 𝕜 E) → 𝕜)
      (fun x ↦ f.pullbackTangentRange hn x) I :=
  letI := f.pullbackTangentContMDiffVectorBundle hm
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiffVectorBundle (𝕜 := 𝕜)

/-- The canonical inclusion of the subbundle `f.pullbackTangentRange hn` into
`f *ᵖ TangentSpace J` is `C^m` on total spaces. -/
theorem contMDiff_tangentRangeInclusion (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    ContMDiff (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) (I.prod 𝓘(𝕜, V)) m
      (fun v : TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x) ↦
        (⟨v.proj, v.2⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) :=
  letI := f.tangentRangeTopology (E := E) (V := V) hn
  letI := f.tangentRangeFiberBundle hn hm
  letI := f.pullbackTangentContMDiffVectorBundle hm
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiff_totalSpace_inclusion (𝕜 := 𝕜)

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold J 1 N]
  [IsManifold I (m + 1) M] [IsManifold J (m + 1) N] in
/-- `f.tangentSpaceEquivTangentRange x hn` viewed with codomain `f.pullbackTangentRange hn x`. -/
@[expose]
def tangentSpaceEquivPullbackTangentRange (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    TangentSpace I x ≃L[𝕜] f.pullbackTangentRange hn x :=
  letI := IsRCLikeNormedField.rclike 𝕜
  f.tangentSpaceEquivTangentRange x hn

private theorem contMDiff_tangentSpaceEquivTangentRange (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    letI := IsRCLikeNormedField.rclike 𝕜
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' (Fin (Module.finrank 𝕜 E) → 𝕜)
          (E := fun x ↦ f.pullbackTangentRange hn x) q.proj
          (f.tangentSpaceEquivPullbackTangentRange q.proj hn q.2)) := by
  let := IsRCLikeNormedField.rclike 𝕜
  let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm
  let := f.pullbackTangentContMDiffVectorBundle hm
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  intro p
  have hfm := (f.contMDiff.of_le ((le_add_right le_rfl).trans hm)).contMDiffAt (x := p.proj)
  have hw : ContMDiffAt (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, V)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) q.proj
          (mfderiv I J (f : M → N) q.proj q.2)) p :=
    (Pullback.contMDiffAt_iff f hfm).2 ⟨contMDiffAt_proj (TangentSpace I : M → Type _),
      (ContMDiff.contMDiff_tangentMap f.contMDiff hm).contMDiffAt⟩
  exact (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiffAt_totalSpace_mk
    hw fun q ↦ ⟨q.2, rfl⟩

/-- **The tangent bundle of an embedded submanifold is `C^m`-isomorphic to its differential image
subbundle.** Over `ℝ` or `ℂ` (`[IsRCLikeNormedField 𝕜]`), `f.tangentSpaceEquivTangentRange`
induces a `C^m` diffeomorphism of total spaces from `TangentSpace I` onto
`f.pullbackTangentRange hn` equipped with its subbundle structure inside `f *ᵖ TangentSpace J`. -/
def tangentBundleDiffeomorphTangentRange (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    TotalSpace E (TangentSpace I : M → Type _) ≃ₘ^m⟮I.prod 𝓘(𝕜, E),
      I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)⟯
      TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x) :=
  letI := IsRCLikeNormedField.rclike 𝕜
  letI := f.tangentRangeTopology (E := E) (V := V) hn
  letI := f.tangentRangeFiberBundle hn hm
  letI := f.tangentRangeVectorBundle hn hm
  letI := f.tangentRangeContMDiffVectorBundle hn hm
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  bundleDiffeomorph (fun x : M ↦ f.tangentSpaceEquivPullbackTangentRange x hn)
    (f.contMDiff_tangentSpaceEquivTangentRange hn hm)

@[simp]
theorem tangentBundleDiffeomorphTangentRange_apply (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (p : TotalSpace E (TangentSpace I : M → Type _)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    f.tangentBundleDiffeomorphTangentRange hn hm p =
      ⟨p.proj, f.tangentSpaceEquivPullbackTangentRange p.proj hn p.2⟩ := by
  let := IsRCLikeNormedField.rclike 𝕜; let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm; let := f.tangentRangeVectorBundle hn hm
  let := f.tangentRangeContMDiffVectorBundle hn hm
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  rw [tangentBundleDiffeomorphTangentRange.eq_def]; simp

@[simp]
theorem tangentBundleDiffeomorphTangentRange_symm_apply (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (p : TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.pullbackTangentRange hn x)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    (f.tangentBundleDiffeomorphTangentRange (E := E) hn hm).symm p =
      ⟨p.proj, (f.tangentSpaceEquivPullbackTangentRange p.proj hn).symm p.2⟩ := by
  let := IsRCLikeNormedField.rclike 𝕜; let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm; let := f.tangentRangeVectorBundle hn hm
  let := f.tangentRangeContMDiffVectorBundle hn hm
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  rw [tangentBundleDiffeomorphTangentRange.eq_def]; simp

/-- Composing `f.tangentBundleDiffeomorphTangentRange` with subbundle inclusion and
`Bundle.Pullback.lift f` recovers `tangentMap I J f`. -/
@[simp]
theorem lift_inclusion_tangentBundleDiffeomorphTangentRange (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (p : TotalSpace E (TangentSpace I : M → Type _)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    Pullback.lift f ⟨(f.tangentBundleDiffeomorphTangentRange hn hm p).proj,
      ((f.tangentBundleDiffeomorphTangentRange hn hm p).2 :
        ((f : M → N) *ᵖ (TangentSpace J))
          (f.tangentBundleDiffeomorphTangentRange hn hm p).proj)⟩ =
      tangentMap I J (f : M → N) p := by
  let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm
  rw [tangentBundleDiffeomorphTangentRange_apply]; rfl

end BundleDiffeomorph

end TauCeti.SmoothEmbedding

end SubbundleFrames
