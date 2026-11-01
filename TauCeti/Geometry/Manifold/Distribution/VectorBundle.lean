/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution

/-!
# Distributions as vector bundles

A distribution `D` on a manifold `M` assigns to every point `x` a subspace `D x` of the tangent
space. Its total space, the pairs `(x, v)` with `v ∈ D x`, carries the topology of a subspace of
the tangent bundle (`TauCeti.instTopologicalSpaceTotalSpaceDistribution`). This file shows that
over `ℝ` or `ℂ` a continuous distribution of rank `k` (a `C^n` distribution of rank `k`, for any
`n`), with this topology, is a topological vector bundle with model fibre `Fin k → 𝕜`: a subbundle
of the tangent bundle. Constructions on real vector bundles, such as the Euler class
`TauCeti.eulerClass`, can then be applied to the tangent field of a foliation.

The local trivializations come from local frames. A `C^n` local frame of `D` is in particular a
continuous local frame of `D` as a family of subspaces of the tangent bundle
(`TauCeti.IsDistributionFrameOn.isSubbundleFrameOn`), so the general local frame criterion for
subbundles of a topological vector bundle (`TauCeti.IsSubbundleFrameOn.trivialization` and
`TauCeti.IsSubbundleFrameOn.continuousOn_coordChangeL`) applies. The atlas consists of the
trivializations of the `C^n` local frames.

The argument for continuity of the coordinates in a frame, with the derivative of operator
inversion in place of its continuity, shows that the coordinates of a tangent vector field
differentiable at a point are differentiable there
(`TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`).

For a continuous distribution `hD : IsContMDiffDistribution I n k D`, install
`hD.fiberBundle` with `letI`; `hD.vectorBundle` then shows that it is a vector bundle.

## Main definitions

* `TauCeti.instTopologicalSpaceTotalSpaceDistribution`: the subspace topology on the total space
  of a distribution.
* `TauCeti.IsContMDiffDistribution.fiberBundle`: a continuous distribution of rank `k` is a fibre
  bundle with fibre `Fin k → 𝕜`.

## Main results

* `TauCeti.IsContMDiffDistribution.mem_trivializationAtlas_fiberBundle_iff`: the trivializations
  of this fibre bundle are those of the `C^n` local frames of `D`.
* `TauCeti.IsContMDiffDistribution.vectorBundle`: a continuous distribution of rank `k` is a
  topological vector bundle.
* `TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`: a vector field tangent to `D`
  and differentiable at `x` is, near `x`, a combination of a `C¹` local frame with coefficients
  differentiable at `x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (the local frame criterion for smooth subbundles, Lemma 10.32, of which this is the continuous
  counterpart) and Chapter 19 (distributions).
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

private theorem mdifferentiableAt_trivOperator (hX : IsDistributionFrameOn I n D X U)
    (hn : 1 ≤ n) {x : M} (hU : U ∈ 𝓝 x) :
    MDiffAt (IsSubbundleFrameOn.trivOperator 𝕜 E X x) x := by
  have hxe := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) x
  have h (i : ι) := ((trivializationAt E (TangentSpace I) x).mdifferentiableAt_section_iff I
    (X i) hxe).mp (((hX.contMDiffOn i).contMDiffAt hU).mdifferentiableAt
      (zero_lt_one.trans_le hn).ne')
  have hsum := MDifferentiableAt.sum (t := Finset.univ) fun i _ ↦
    ((ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) E
      (ContinuousLinearMap.proj i)).differentiableAt).comp_mdifferentiableAt (h i)
  convert hsum using 1
  funext y
  simp [IsSubbundleFrameOn.trivOperator_eq_sum]

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
  -- Compress the frame operator by a left inverse `P` at `x`; the compression is invertible
  -- near `x`, and inverting it recovers the coefficients from `V` read in the trivialization.
  obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional_domain
    (hX.isSubbundleFrameOn.injective_trivOperator (mem_of_mem_nhds hU))
  let Q : M → (ι → 𝕜) →L[𝕜] ι → 𝕜 := fun y ↦ P ∘L IsSubbundleFrameOn.trivOperator 𝕜 E X x y
  have hQ : MDiffAt Q x :=
    mdifferentiableAt_const.clm_comp (mdifferentiableAt_trivOperator hX hn hU)
  have hQx : Q x = ((1 : ((ι → 𝕜) →L[𝕜] ι → 𝕜)ˣ) : (ι → 𝕜) →L[𝕜] ι → 𝕜) :=
    ContinuousLinearMap.ext hP
  let c : M → ι → 𝕜 := fun y ↦ Ring.inverse (Q y) (P (e ⟨y, V y⟩).2)
  have hc : MDifferentiableAt I 𝓘(𝕜, ι → 𝕜) c x :=
    (((differentiableAt_inverse (hQx ▸ isUnit_one)).comp_mdifferentiableAt hQ).clm_apply
      (mdifferentiableAt_const.clm_apply ((e.mdifferentiableAt_section_iff I V hxe).mp hV)))
  refine ⟨fun i y ↦ c y i, fun i ↦ ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i).differentiableAt
      ).comp_mdifferentiableAt hc
  filter_upwards [hVD, hU, e.open_baseSet.mem_nhds hxe,
    hQ.continuousAt.preimage_mem_nhds (hQx ▸ Units.nhds 1)] with y hyD hyU hye hyQ
  obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun 𝕜 |>.mp ((hX.span_eq hyU).symm ▸ hyD)
  have hca : c y = a := by
    have h := congrArg (fun T : (ι → 𝕜) →L[𝕜] ι → 𝕜 ↦ T a) (Ring.inverse_mul_cancel _ hyQ)
    simpa [c, Q, ← ha, IsSubbundleFrameOn.trivOperator_apply hye] using h
  simpa [hca] using ha.symm

end IsDistributionFrameOn

namespace IsContMDiffDistribution

variable [IsRCLikeNormedField 𝕜] {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-- A continuous distribution of rank `k` is a fibre bundle with fibre `Fin k → 𝕜`, the topology of
its total space being that of a subspace of the tangent bundle. Its trivializations are those of
the `C^n` local frames of `D` (`TauCeti.IsSubbundleFrameOn.trivialization`). Use this definition
as a local instance, which chooses a local frame at every point. -/
@[instance_reducible]
def fiberBundle (hD : IsContMDiffDistribution I n k D) :
    FiberBundle (Fin k → 𝕜) fun x ↦ D x :=
  let U := fun x ↦ (isContMDiffDistribution_iff.mp hD x).choose
  have hU := fun x ↦ (isContMDiffDistribution_iff.mp hD x).choose_spec
  let X := fun x ↦ (hU x).2.2.choose
  have hX := fun x ↦ (hU x).2.2.choose_spec
  { totalSpaceMk_isInducing' := isInducing_totalSpaceMk_subbundle E (Fin k → 𝕜) D
    trivializationAtlas' :=
      {e | ∃ (V : Set M) (hV : IsOpen V) (Y : Fin k → Π y : M, TangentSpace I y)
        (hY : IsDistributionFrameOn I n D Y V), hY.isSubbundleFrameOn.trivialization hV = e}
    trivializationAt' := fun x ↦ (hX x).isSubbundleFrameOn.trivialization (hU x).1
    mem_baseSet_trivializationAt' := fun x ↦ by
      rw [IsSubbundleFrameOn.trivialization_baseSet]
      exact (hU x).2.1
    trivialization_mem_atlas' := fun x ↦ ⟨U x, (hU x).1, X x, hX x, rfl⟩ }

/-- The trivializations of `hD.fiberBundle` are the trivializations of the `C^n` local frames
of `D`. -/
theorem mem_trivializationAtlas_fiberBundle_iff (hD : IsContMDiffDistribution I n k D)
    (e : Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) fun x ↦ D x)) :
    letI := hD.fiberBundle
    e ∈ trivializationAtlas (Fin k → 𝕜) (fun x ↦ D x) ↔
      ∃ (V : Set M) (hV : IsOpen V) (Y : Fin k → Π y : M, TangentSpace I y)
        (hY : IsDistributionFrameOn I n D Y V), hY.isSubbundleFrameOn.trivialization hV = e :=
  Iff.rfl

/-- **A continuous distribution of rank `k` is a vector bundle**: with the subspace topology of the
tangent bundle, its local frame trivializations are linear, with continuous coordinate changes. -/
theorem vectorBundle (hD : IsContMDiffDistribution I n k D) :
    letI := hD.fiberBundle
    VectorBundle 𝕜 (Fin k → 𝕜) fun x ↦ D x := by
  let := hD.fiberBundle
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro e he
    obtain ⟨V, hV, Y, hY, rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hD e).mp he.out
    exact hY.isSubbundleFrameOn.isLinear_trivialization hV
  · intro e e' he he'
    obtain ⟨V, hV, Y, hY, rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hD e).mp he.out
    obtain ⟨V', hV', Y', hY', rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hD e').mp he'.out
    simpa only [IsSubbundleFrameOn.trivialization_baseSet] using
      hY.isSubbundleFrameOn.continuousOn_coordChangeL hV hY'.isSubbundleFrameOn hV'

end IsContMDiffDistribution

end TauCeti
