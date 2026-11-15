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
finite-dimensional `E`, this equips `x ↦ f.tangentRange x hn` for a `SmoothEmbedding` `f` with its
canonical `C^m` vector subbundle structure (`tangentRangeContMDiffVectorBundle`) inside
`f *ᵖ TangentSpace J` and induces a `C^m` bundle diffeomorphism
`f.tangentBundleDiffeomorphTangentRange` from `TangentSpace I` onto `x ↦ f.tangentRange x hn`.

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

section SubbundleFrames

variable [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I (m + 1) M]

/-- **Local subbundle frames for the image of an injective differential.** If `f : M → N` is `C^n`
with `m + 1 ≤ n` and `mfderiv I J f x` is injective at every `x : M`, then pushing forward local
frames of `TangentSpace I` associated with any basis `b : Module.Basis ι 𝕜 E` gives `C^m` local
subbundle frames of `(mfderiv I J f x).toLinearMap.range` inside `f *ᵖ TangentSpace J`. -/
theorem ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis {ι : Type*}
    (b : Module.Basis ι 𝕜 E) {K : Type*} [FunLike K M N] [ContinuousMapClass K M N] {f : K}
    (hf : ContMDiff I J n f) (hm : m + 1 ≤ n)
    (hinj : ∀ x, Injective (mfderiv I J (f : M → N) x)) :
    TauCeti.HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V ι
      (fun x ↦ (mfderiv I J (f : M → N) x).toLinearMap.range) := by
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
    TauCeti.HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V
      (Fin (Module.finrank 𝕜 E)) (fun x ↦ (mfderiv I J (f : M → N) x).toLinearMap.range) :=
  ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis (Module.finBasis 𝕜 E) hf hm hinj

/-- A `C^n` immersion (`n ≠ 0`, `m + 1 ≤ n`) of a finite-dimensional manifold `M` has `C^m` local
subbundle frames for `(mfderiv I J f x).toLinearMap.range` inside `f *ᵖ TangentSpace J`. -/
theorem Manifold.IsImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv
    [FiniteDimensional 𝕜 E] {K : Type*} [FunLike K M N] [ContinuousMapClass K M N] {f : K}
    (hf : Manifold.IsImmersion I J n f) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    TauCeti.HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V
      (Fin (Module.finrank 𝕜 E)) (fun x ↦ (mfderiv I J (f : M → N) x).toLinearMap.range) :=
  ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv hf.contMDiff hm (hf.mfderiv_injective hn)

namespace TauCeti.SmoothEmbedding

/-- For a `C^n` smooth embedding `f` (`n ≠ 0`, `m + 1 ≤ n`) with finite-dimensional source model
`E`, `x ↦ f.tangentRange x hn` admits `C^m` local subbundle frames inside
`f *ᵖ TangentSpace J`. -/
theorem hasLocalContMDiffSubbundleFrames_tangentRange [FiniteDimensional 𝕜 E]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V
      (Fin (Module.finrank 𝕜 E)) (fun x ↦ f.tangentRange x hn) :=
  f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv hn hm

section BundleDiffeomorph

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I (m + 1) M] in
/-- The subspace topology on the total space of `x ↦ f.tangentRange x hn` induced from
`TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))`. Install with `letI`. -/
@[instance_reducible]
def tangentRangeTopology (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    TopologicalSpace
      (TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn)) :=
  subbundleTopology V (E := (f : M → N) *ᵖ (TangentSpace J))
    (F' := Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn)

/-- The fibre-bundle structure on `x ↦ f.tangentRange x hn` given by its `C^m` local subbundle
frames. Install with `letI`. -/
@[instance_reducible]
def tangentRangeFiberBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    FiberBundle (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn) :=
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).fiberBundle

/-- The `𝕜`-vector bundle structure on `x ↦ f.tangentRange x hn` as a subbundle of
`f *ᵖ TangentSpace J`. -/
theorem tangentRangeVectorBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    VectorBundle 𝕜 (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn) :=
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

/-- **The differential image `x ↦ f.tangentRange x hn` is a `C^m` vector subbundle of
`f *ᵖ TangentSpace J`.** -/
theorem tangentRangeContMDiffVectorBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    letI := f.tangentRangeVectorBundle hn hm
    ContMDiffVectorBundle m (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn) I :=
  letI := f.pullbackTangentContMDiffVectorBundle hm
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiffVectorBundle (𝕜 := 𝕜)

/-- The canonical inclusion of the subbundle `x ↦ f.tangentRange x hn` into
`f *ᵖ TangentSpace J` is `C^m` on total spaces. -/
theorem contMDiff_tangentRangeInclusion (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    ContMDiff (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) (I.prod 𝓘(𝕜, V)) m
      (fun v : TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn) ↦
        (⟨v.proj, v.2.1⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) :=
  letI := f.tangentRangeTopology (E := E) (V := V) hn
  letI := f.tangentRangeFiberBundle hn hm
  letI := f.pullbackTangentContMDiffVectorBundle hm
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiff_totalSpace_inclusion (𝕜 := 𝕜)

private theorem contMDiff_tangentSpaceEquivTangentRange (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' (Fin (Module.finrank 𝕜 E) → 𝕜)
          (E := fun x ↦ f.tangentRange x hn) q.proj
          (f.tangentSpaceEquivTangentRange q.proj hn q.2)) := by
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
  have hmk : ContMDiffAt (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' (Fin (Module.finrank 𝕜 E) → 𝕜)
          (E := fun x ↦ f.tangentRange x hn) q.proj
          ⟨mfderiv I J (f : M → N) q.proj q.2, ⟨q.2, rfl⟩⟩) p :=
    (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiffAt_totalSpace_mk
      hw fun q ↦ ⟨q.2, rfl⟩
  exact hmk.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq <| funext fun q ↦
    congrArg (TotalSpace.mk' _ q.proj) <|
      Subtype.ext (f.coe_tangentSpaceEquivTangentRange_apply q.proj hn q.2))

/-- **The tangent bundle of an embedded submanifold is `C^m`-isomorphic to its differential image
subbundle.** Over `ℝ` or `ℂ` (`[IsRCLikeNormedField 𝕜]`), `f.tangentSpaceEquivTangentRange`
induces a `C^m` diffeomorphism of total spaces from `TangentSpace I` onto
`x ↦ f.tangentRange x hn` equipped with its subbundle structure inside `f *ᵖ TangentSpace J`. -/
def tangentBundleDiffeomorphTangentRange (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    TotalSpace E (TangentSpace I : M → Type _) ≃ₘ^m⟮I.prod 𝓘(𝕜, E),
      I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)⟯
      TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn) :=
  letI := IsRCLikeNormedField.rclike 𝕜
  letI := f.tangentRangeTopology (E := E) (V := V) hn
  letI := f.tangentRangeFiberBundle hn hm
  letI := f.tangentRangeVectorBundle hn hm
  letI := f.tangentRangeContMDiffVectorBundle hn hm
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  bundleDiffeomorph (fun x : M ↦ f.tangentSpaceEquivTangentRange x hn)
    (f.contMDiff_tangentSpaceEquivTangentRange hn hm)

@[simp]
theorem tangentBundleDiffeomorphTangentRange_apply (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (p : TotalSpace E (TangentSpace I : M → Type _)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    f.tangentBundleDiffeomorphTangentRange hn hm p =
      ⟨p.proj, f.tangentSpaceEquivTangentRange p.proj hn p.2⟩ := by
  let := IsRCLikeNormedField.rclike 𝕜; let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm; let := f.tangentRangeVectorBundle hn hm
  let := f.tangentRangeContMDiffVectorBundle hn hm
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  rw [tangentBundleDiffeomorphTangentRange.eq_def]; simp

@[simp]
theorem tangentBundleDiffeomorphTangentRange_symm_apply (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (p : TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.tangentRange x hn)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    (f.tangentBundleDiffeomorphTangentRange (E := E) hn hm).symm p =
      ⟨p.proj, (f.tangentSpaceEquivTangentRange p.proj hn).symm p.2⟩ := by
  let := IsRCLikeNormedField.rclike 𝕜; let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm; let := f.tangentRangeVectorBundle hn hm
  let := f.tangentRangeContMDiffVectorBundle hn hm
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  rw [tangentBundleDiffeomorphTangentRange.eq_def]; simp

/-- Composing `f.tangentBundleDiffeomorphTangentRange` with subbundle inclusion and
`Bundle.Pullback.lift f` recovers `tangentMap I J f`. -/
theorem lift_inclusion_tangentBundleDiffeomorphTangentRange (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (p : TotalSpace E (TangentSpace I : M → Type _)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    letI := f.tangentRangeFiberBundle hn hm
    Pullback.lift f (TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J))
      (f.tangentBundleDiffeomorphTangentRange hn hm p).proj
      (f.tangentBundleDiffeomorphTangentRange hn hm p).2.1) =
      tangentMap I J (f : M → N) p := by
  let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm
  rw [tangentBundleDiffeomorphTangentRange_apply]
  simp [Pullback.lift, tangentMap]

end BundleDiffeomorph

end TauCeti.SmoothEmbedding

end SubbundleFrames
