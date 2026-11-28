/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic

/-!
# Distributions as vector bundles

A distribution `D` on a manifold `M` assigns to every point `x` a subspace `D x` of the tangent
space. Its total space, the pairs `(x, v)` with `v ∈ D x`, carries the topology of a subspace of
the tangent bundle (`TauCeti.instTopologicalSpaceTotalSpaceDistribution`). This file shows that
over `ℝ` or `ℂ` a continuous distribution of rank `k` (a `C^n` distribution of rank `k`, for any
`n`), with this topology, is a topological vector bundle with model fibre `Fin k → 𝕜`: a subbundle
of the tangent bundle. Constructions on real vector bundles, such as the Euler class
`TauCeti.eulerClass`, can then be applied to the tangent field of a foliation.

The local trivializations come from local frames. A `C^n` local frame of `D` is a local frame of
`D`, as a family of subspaces of the tangent bundle, whose members are `C^n` sections
(`TauCeti.IsDistributionFrameOn.isSubbundleFrameOn`). So `D` has `C^n` local frames near every
point (`TauCeti.IsContMDiffDistribution.hasLocalContMDiffSubbundleFrames`), and the general local
frame criterion for subbundles (`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`) applies.
The atlas consists of the trivializations of the `C^n` local frames.

The argument for continuity of the coordinates in a frame, with the derivative of operator
inversion in place of its continuity, shows that the coordinates of a tangent vector field
differentiable at a point are differentiable there
(`TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`).

For a continuous distribution `hD : IsContMDiffDistribution I n k D`, install
`hD.fiberBundle` with `letI`; `hD.vectorBundle` then shows that it is a vector bundle.

On a `C^(n+1)` manifold, the tangent bundle is a `C^n` vector bundle and the `C^n` local frames of
`D` are `C^n` sections of it, so the smooth local frame criterion
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`) applies. Hence a `C^n`
distribution of rank `k` is a `C^n` vector bundle with model fibre `Fin k → 𝕜`
(`hD.contMDiffVectorBundle`), a `C^n` subbundle of the tangent bundle. A local frame of the
distribution, read as sections of this subbundle, is a local frame in Mathlib's `IsLocalFrameOn`
sense.

## Main definitions

* `TauCeti.instTopologicalSpaceTotalSpaceDistribution`: the subspace topology on the total space
  of a distribution.
* `TauCeti.IsContMDiffDistribution.fiberBundle`: a continuous distribution of rank `k` is a fibre
  bundle with fibre `Fin k → 𝕜`.
* `TauCeti.IsContMDiffDistribution.inclusionHom`,
  `TauCeti.IsContMDiffDistribution.toTangentSection`,
  `TauCeti.IsContMDiffDistribution.mkSection`: on a `C^(n+1)` manifold, the `C^n` Hom-bundle
  inclusion `D →L[𝕜] TM`, `C^n`-section inclusion `Γ^n(D) → Γ^n(TM)`, and restriction of `D`-valued
  `C^n` vector fields to `C^n` sections of `D`.

## Main results

* `TauCeti.IsContMDiffDistribution.hasLocalContMDiffSubbundleFrames`: a `C^n` distribution of rank
  `k` has `C^n` local frames of size `k` near every point.
* `TauCeti.IsContMDiffDistribution.mem_trivializationAtlas_fiberBundle_iff`: the trivializations
  of this fibre bundle are those of the `C^n` local frames of `D`.
* `TauCeti.IsContMDiffDistribution.vectorBundle`: a continuous distribution of rank `k` is a
  topological vector bundle.
* `TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`: on a `C^(n+1)` manifold, a `C^n`
  distribution of rank `k` is a `C^n` vector bundle.
* `TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_inclusion`,
  `TauCeti.IsContMDiffDistribution.contMDiffAt_totalSpace_mk`: on a `C^(n+1)` manifold, the
  total-space inclusion of a `C^n` distribution is `C^n` and `C^n` maps into the tangent bundle
  with values in `D` factor as `C^n` maps into `D`.
* `TauCeti.IsContMDiffDistribution.contMDiffAt_pullback_mk`: a section of the pullback of a `C^n`
  distribution along a map is `C^n` where it agrees with a `C^n` section of the pulled-back tangent
  bundle.
* `TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`: a vector field tangent to `D`
  and differentiable at `x` is, near `x`, a combination of a `C¹` local frame with coefficients
  differentiable at `x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (the local frame criterion for smooth subbundles, Lemma 10.32, and its continuous counterpart)
  and Chapter 19 (distributions).
-/

public section

noncomputable section

open Set Filter Function Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} {k : ℕ}

/-- The total space of a distribution `D`, the pairs `(x, v)` with `v ∈ D x`, carries the topology
of a subspace of the tangent bundle (`TauCeti.subbundleTopology`). The model-fibre parameter `F`
of `Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceDistribution {F : Type*}
    (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) :
    TopologicalSpace (TotalSpace F fun x ↦ D x) :=
  subbundleTopology E D

namespace IsDistributionFrameOn

variable {ι : Type*} [Fintype ι] [IsManifold I 2 M] {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  {X : ι → Π x : M, TangentSpace I x} {U : Set M}

/-- **Coefficients in a frame are differentiable.** Let `X` be a `C^n` local frame of `D`, with
`1 ≤ n`, on a neighbourhood of `x`, and let `V` be a vector field, differentiable at `x`, which is
tangent to `D` near `x`. Then near `x` the field `V` is a combination `∑ i, c i • X i` of the
frame whose coefficients `c i` are differentiable at `x`. -/
theorem exists_mdifferentiableAt_coeff [IsRCLikeNormedField 𝕜]
    (hX : IsDistributionFrameOn I n D X U) (hn : 1 ≤ n)
    {x : M} (hU : U ∈ 𝓝 x) {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) :
    ∃ c : ι → M → 𝕜, (∀ i, MDiffAt (c i) x) ∧ ∀ᶠ y in 𝓝 x, V y = ∑ i, c i y • X i y := by
  have : CompleteSpace 𝕜 := by
    let := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  let e := trivializationAt E (TangentSpace I) x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  -- The tangent bundle of a `C²` manifold is a `C¹` vector bundle, in which the frame is `C¹`.
  have : IsManifold I (1 + 1) M := .of_le (n := 2) one_add_one_eq_two.le
  have := TangentBundle.contMDiffVectorBundle (n := 1) (I := I) (M := M)
  -- A `C¹` left inverse of the frame operator recovers the coefficients from `V` read in the
  -- trivialization.
  obtain ⟨L, hL, hLinv⟩ := ContMDiffAt.exists_contMDiffAt_leftInverse
    (IsSubbundleFrameOn.contMDiffAt_trivOperator (n := 1)
      (fun i ↦ ((hX.contMDiffOn i).contMDiffAt hU).of_le hn) hxe)
    (.of_injective_of_finiteDimensional_domain
      (hX.isSubbundleFrameOn.injective_trivOperator (mem_of_mem_nhds hU)))
  let c : M → ι → 𝕜 := fun y ↦ L y (e ⟨y, V y⟩).2
  have hc : MDifferentiableAt I 𝓘(𝕜, ι → 𝕜) c x :=
    (hL.mdifferentiableAt one_ne_zero).clm_apply ((e.mdifferentiableAt_section_iff I V hxe).mp hV)
  refine ⟨fun i y ↦ c y i, fun i ↦ ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i).differentiableAt
      ).comp_mdifferentiableAt hc
  filter_upwards [hVD, hU, e.open_baseSet.mem_nhds hxe, hLinv] with y hyD hyU hye hyL
  obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun 𝕜 |>.mp ((hX.span_eq hyU).symm ▸ hyD)
  have hca : c y = a := by
    simpa [c, ← ha, IsSubbundleFrameOn.trivOperator_apply hye] using hyL a
  simpa [hca] using ha.symm

end IsDistributionFrameOn

namespace IsContMDiffDistribution

variable [IsRCLikeNormedField 𝕜] {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

omit [IsRCLikeNormedField 𝕜] in
/-- A `C^n` distribution of rank `k` has `C^n` local frames of size `k` near every point, as a
family of subspaces of the tangent bundle. -/
theorem hasLocalContMDiffSubbundleFrames (hD : IsContMDiffDistribution I n k D) :
    HasLocalContMDiffSubbundleFrames I n E (Fin k) D :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ by
    obtain ⟨U, hU, hx, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
    exact ⟨U, hU, hx, X, hX.isSubbundleFrameOn, hX.contMDiffOn⟩

/-- A continuous distribution of rank `k` is a fibre bundle with fibre `Fin k → 𝕜`, the topology of
its total space being that of a subspace of the tangent bundle. Its trivializations are those of
the `C^n` local frames of `D` (`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Use this
definition as a local instance, which chooses a local frame at every point. -/
@[instance_reducible]
def fiberBundle (hD : IsContMDiffDistribution I n k D) :
    FiberBundle (Fin k → 𝕜) fun x ↦ D x :=
  hD.hasLocalContMDiffSubbundleFrames.fiberBundle

/-- The trivializations of `hD.fiberBundle` are the trivializations of the `C^n` local frames
of `D`. -/
theorem mem_trivializationAtlas_fiberBundle_iff (hD : IsContMDiffDistribution I n k D)
    (e : Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) fun x ↦ D x)) :
    letI := hD.fiberBundle
    e ∈ trivializationAtlas (Fin k → 𝕜) (fun x ↦ D x) ↔
      ∃ (V : Set M) (hV : IsOpen V) (Y : Fin k → Π y : M, TangentSpace I y)
        (hY : IsDistributionFrameOn I n D Y V), hY.isSubbundleFrameOn.trivialization hV = e :=
  (hD.hasLocalContMDiffSubbundleFrames.mem_trivializationAtlas_fiberBundle_iff e).trans
    ⟨fun ⟨V, hV, Y, hY, hYn, he⟩ ↦ ⟨V, hV, Y, ⟨hYn, hY.linearIndependent, hY.span_eq⟩, he⟩,
      fun ⟨V, hV, Y, hY, he⟩ ↦ ⟨V, hV, Y, hY.isSubbundleFrameOn, hY.contMDiffOn, he⟩⟩

/-- **A continuous distribution of rank `k` is a vector bundle**: with the subspace topology of the
tangent bundle, its local frame trivializations are linear, with continuous coordinate changes. -/
theorem vectorBundle (hD : IsContMDiffDistribution I n k D) :
    letI := hD.fiberBundle
    VectorBundle 𝕜 (Fin k → 𝕜) fun x ↦ D x :=
  hD.hasLocalContMDiffSubbundleFrames.vectorBundle

/-- **A `C^n` distribution of rank `k` is a `C^n` vector bundle.** On a `C^(n+1)` manifold, whose
tangent bundle is a `C^n` vector bundle, the `C^n` local frames of `D` are `C^n` sections of it. So
`D`, with the subspace topology of the tangent bundle and the atlas of `hD.fiberBundle`, is a `C^n`
subbundle of the tangent bundle (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`).
-/
theorem contMDiffVectorBundle [IsManifold I (n + 1) M] (hD : IsContMDiffDistribution I n k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ContMDiffVectorBundle n (Fin k → 𝕜) (fun x ↦ D x) I :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiffVectorBundle

/-- On a `C^(n+1)` manifold, the canonical inclusion `(x, v) ↦ (x, ↑v)` of a `C^n` distribution of
rank `k` into the tangent bundle is `C^n`. -/
theorem contMDiff_totalSpace_inclusion [IsManifold I (n + 1) M]
    (hD : IsContMDiffDistribution I n k D) :
    letI := hD.fiberBundle
    ContMDiff (I.prod 𝓘(𝕜, Fin k → 𝕜)) (I.prod 𝓘(𝕜, E)) n
      (fun v : TotalSpace (Fin k → 𝕜) (fun x ↦ D x) ↦
        (⟨v.proj, v.snd⟩ : TotalSpace E (TangentSpace I))) :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_inclusion

/-- On a `C^(n+1)` manifold, a `C^n` map into the tangent bundle taking values in a `C^n`
distribution `D` of rank `k` is `C^n` as a map into the total space of `D`. -/
theorem contMDiffAt_totalSpace_mk [IsManifold I (n + 1) M] {EM HM N : Type*}
    [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM}
    [TopologicalSpace N] [ChartedSpace HM N] (hD : IsContMDiffDistribution I n k D)
    {b : N → M} {w : ∀ y, TangentSpace I (b y)} {y₀ : N}
    (hw : ContMDiffAt J (I.prod 𝓘(𝕜, E)) n (fun y ↦ (⟨b y, w y⟩ : TotalSpace E (TangentSpace I)))
      y₀) (hmem : ∀ y, w y ∈ D (b y)) :
    letI := hD.fiberBundle
    ContMDiffAt J (I.prod 𝓘(𝕜, Fin k → 𝕜)) n
      (fun y ↦ (⟨b y, ⟨w y, hmem y⟩⟩ : TotalSpace (Fin k → 𝕜) fun x ↦ D x)) y₀ :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiffAt_totalSpace_mk le_rfl hw hmem

/-- On a `C^(n+1)` manifold, a section `w` of the pullback `f^* D` of a `C^n` distribution `D` of
rank `k` along a map `f` that is `C^n` at `y₀` is `C^n` at `y₀` as soon as it agrees near `y₀`
with a section `X` of `f^* TM` that is `C^n` at `y₀`. -/
theorem contMDiffAt_pullback_mk [IsManifold I (n + 1) M] {EN HN N : Type*}
    [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN}
    [TopologicalSpace N] [ChartedSpace HN N] {K : Type*} [FunLike K N M]
    [ContinuousMapClass K N M] (hD : IsContMDiffDistribution I n k D) {f : K} {y₀ : N}
    (hf : ContMDiffAt J I n f y₀) {X : Π y, TangentSpace I (f y)} {w : Π y, D (f y)}
    (hX : ContMDiffAt J (J.prod 𝓘(𝕜, E)) n
      (fun y ↦ TotalSpace.mk' E (E := (f : N → M) *ᵖ (TangentSpace I)) y (X y)) y₀)
    (hwX : ∀ᶠ y in 𝓝 y₀, (w y : TangentSpace I (f y)) = X y) :
    letI := hD.fiberBundle
    ContMDiffAt J (J.prod 𝓘(𝕜, Fin k → 𝕜)) n
      (fun y ↦ TotalSpace.mk' (Fin k → 𝕜) (E := (f : N → M) *ᵖ fun x ↦ D x) y (w y)) y₀ :=
  letI := hD.fiberBundle
  (Bundle.Pullback.contMDiffAt_iff f hf).2 ⟨contMDiffAt_id, hD.contMDiffAt_totalSpace_mk
    (((Bundle.Pullback.contMDiffAt_iff f hf).1 hX).2.congr_of_eventuallyEq
      (hwX.mono fun _ hy ↦ congrArg (TotalSpace.mk _) hy)) fun y ↦ (w y).property⟩

section Sections
variable [IsManifold I (n + 1) M] (hD : IsContMDiffDistribution I n k D)

/-- On a `C^(n+1)` manifold, the fibrewise inclusions `(D x).subtypeL : D x →L[𝕜] TangentSpace I x`
of a `C^n` distribution of rank `k` form a `C^n` section of `D →L[𝕜] TM`. -/
def inclusionHom : letI := hD.fiberBundle; letI := hD.vectorBundle
    Cₛ^n⟮I; (Fin k → 𝕜) →L[𝕜] E, fun x ↦ D x →L[𝕜] TangentSpace I x⟯ :=
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  let := hD.fiberBundle; let := hD.vectorBundle
  ⟨fun x ↦ (D x).subtypeL, (contMDiff_hom_bundle_iff _).2 hD.contMDiff_totalSpace_inclusion⟩

@[simp] theorem inclusionHom_apply (x : M) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; hD.inclusionHom x) = (D x).subtypeL := (rfl)

/-- Inclusion of `C^n` sections of `D` into `C^n` tangent vector fields over `C^n⟮I, M; 𝕜⟯`. -/
def toTangentSection : letI := hD.fiberBundle; letI := hD.vectorBundle
    Cₛ^n⟮I; Fin k → 𝕜, fun x ↦ D x⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      Cₛ^n⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  let := hD.fiberBundle; let := hD.vectorBundle; have h := hD.contMDiff_totalSpace_inclusion
  ContMDiffSection.mapFunctionLinearMap (fun x ↦ (D x).subtype) h

@[simp] theorem toTangentSection_apply : letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ (a : Cₛ^n⟮I; Fin k → 𝕜, fun x ↦ D x⟯) (x : M),
      hD.toTangentSection a x = (a x : TangentSpace I x) :=
  let := hD.fiberBundle; let := hD.vectorBundle
  ContMDiffSection.mapFunctionLinearMap_apply (fun x ↦ (D x).subtype)
    hD.contMDiff_totalSpace_inclusion

theorem toTangentSection_injective : letI := hD.fiberBundle; letI := hD.vectorBundle
    Function.Injective hD.toTangentSection :=
  let := hD.fiberBundle; let := hD.vectorBundle
  ContMDiffSection.mapFunctionLinearMap_injective (fun x ↦ (D x).subtype)
    hD.contMDiff_totalSpace_inclusion fun _ ↦ Subtype.val_injective

/-- A `C^n` tangent vector field taking values in `D` defines a `C^n` section of `D`. -/
def mkSection (X : Cₛ^n⟮I; E, (TangentSpace I : M → Type _)⟯) (hX : ∀ x, X x ∈ D x) :
    letI := hD.fiberBundle; Cₛ^n⟮I; Fin k → 𝕜, fun x ↦ D x⟯ :=
  let := hD.fiberBundle
  ⟨fun x ↦ ⟨X x, hX x⟩, fun _ ↦ hD.contMDiffAt_totalSpace_mk X.contMDiff.contMDiffAt hX⟩

@[simp] theorem coe_mkSection_apply (X : Cₛ^n⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : ∀ x, X x ∈ D x) (x : M) :
    (letI := hD.fiberBundle; (hD.mkSection X hX x : TangentSpace I x)) = X x := (rfl)

@[simp] theorem toTangentSection_mkSection (X : Cₛ^n⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : ∀ x, X x ∈ D x) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; hD.toTangentSection (hD.mkSection X hX)) =
      X := by let := hD.fiberBundle; let := hD.vectorBundle; ext x; simp

@[simp] theorem mkSection_toTangentSection : letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ (a : Cₛ^n⟮I; Fin k → 𝕜, fun x ↦ D x⟯) (h : ∀ x, hD.toTangentSection a x ∈ D x),
      hD.mkSection (hD.toTangentSection a) h = a := by
  let := hD.fiberBundle; let := hD.vectorBundle; intro a h; ext x; simp

end Sections
end IsContMDiffDistribution

namespace IsDistributionFrameOn

variable {ι : Type*} {D : ∀ x : M, Submodule 𝕜 (TangentSpace I x)}
  {X : ι → ∀ x : M, TangentSpace I x} {U : Set M}

/-- The sections of `D` represented by the frame `X` on `U`, with value zero off `U`. -/
noncomputable def bundleFrame (hX : IsDistributionFrameOn I n D X U) (i : ι) (x : M) : D x :=
  open Classical in
  if hx : x ∈ U then hX.isSubbundleFrameOn.basis hx i else 0

/-- The frame as a section of `D` has its original value at every point of its domain. -/
@[simp]
theorem coe_bundleFrame_apply (hX : IsDistributionFrameOn I n D X U)
    (i : ι) {x : M} (hx : x ∈ U) : (hX.bundleFrame i x : TangentSpace I x) = X i x := by
  simp [bundleFrame, hx]

/-- Off its domain the frame as a section of `D` has the junk value zero. -/
@[simp]
theorem bundleFrame_apply_of_notMem (hX : IsDistributionFrameOn I n D X U)
    (i : ι) {x : M} (hx : x ∉ U) : hX.bundleFrame i x = 0 := by
  simp [bundleFrame, hx]

/-- Any `C^n` local frame of a `C^n` distribution gives a `C^n` local frame of its native
vector bundle. The frame may use any index type and its domain need not be open. -/
theorem isLocalFrameOn_bundleFrame [IsRCLikeNormedField 𝕜] [IsManifold I (n + 1) M]
    (hX : IsDistributionFrameOn I n D X U) (hD : IsContMDiffDistribution I n k D) :
    letI := hD.fiberBundle
    IsLocalFrameOn I (Fin k → 𝕜) n hX.bundleFrame U := by
  classical
  let := hD.fiberBundle
  have hvalue {x : M} (hx : x ∈ U) (i : ι) :
      hX.bundleFrame i x = hX.isSubbundleFrameOn.basis hx i := dite_eq_left hx
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_, fun i ↦ ?_⟩
  · simpa only [hvalue hx] using (hX.isSubbundleFrameOn.basis hx).linearIndependent
  · simp only [hvalue hx, (hX.isSubbundleFrameOn.basis hx).span_eq, le_refl]
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have h := (hX.contMDiffOn i).congr (f₁ := T% (fun x ↦ (hX.bundleFrame i x : TangentSpace I x)))
    (fun x hx ↦ by simp only [hX.coe_bundleFrame_apply i hx])
  exact hD.hasLocalContMDiffSubbundleFrames.contMDiffOn_totalSpace_mk le_rfl h
    (fun x ↦ (hX.bundleFrame i x).property)

end IsDistributionFrameOn
end TauCeti
