/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse

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
(`hD.contMDiffVectorBundle`), a `C^n` subbundle of the tangent bundle.

## Main definitions

* `TauCeti.instTopologicalSpaceTotalSpaceDistribution`: the subspace topology on the total space
  of a distribution.
* `TauCeti.IsContMDiffDistribution.fiberBundle`: a continuous distribution of rank `k` is a fibre
  bundle with fibre `Fin k → 𝕜`.

## Main results

* `TauCeti.IsContMDiffDistribution.hasLocalContMDiffSubbundleFrames`: a `C^n` distribution of rank
  `k` has `C^n` local frames of size `k` near every point.
* `TauCeti.IsContMDiffDistribution.mem_trivializationAtlas_fiberBundle_iff`: the trivializations
  of this fibre bundle are those of the `C^n` local frames of `D`.
* `TauCeti.IsContMDiffDistribution.vectorBundle`: a continuous distribution of rank `k` is a
  topological vector bundle.
* `TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`: on a `C^(n+1)` manifold, a `C^n`
  distribution of rank `k` is a `C^n` vector bundle.
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

end IsContMDiffDistribution

end TauCeti
