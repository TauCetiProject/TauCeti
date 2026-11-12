/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Analysis.Calculus.ContDiff.LocalInjectivity

/-!
# Local injectivity of maps with injective manifold derivative

A map `f : M → N` between manifolds over `ℝ` or `ℂ` (more generally, over a field `𝕜` with
`IsRCLikeNormedField 𝕜`) that is `C^n`, `n ≠ 0`, at `x`, where the model space of `M` is
finite-dimensional and the manifold derivative `mfderiv I J f x` is injective, is injective on a
neighbourhood of `x` (`ContMDiffAt.exists_mem_nhds_injOn`).

No boundary or smoothness assumption is placed on `M` or `N`: in the extended charts at `x` and
`f x`, the coordinate expression of `f` is `C^n` within the convex range of the model with corners,
and its derivative within that range is `mfderiv I J f x`, so the relative local injectivity
theorem `ContDiffWithinAt.exists_nhdsWithin_injOn` applies. In particular this covers boundary
points, where the inverse function theorem is not available.

In particular a curve which is `C^n`, `n ≠ 0`, at a parameter where its velocity does not vanish
is injective near that parameter (`ContMDiffAt.exists_mem_nhds_injOn_of_curveVelocity_ne_zero`).

Without any smoothness assumption, an injective manifold derivative at `x` still isolates `x` in
its fibre (`TauCeti.eventually_ne_of_mfderiv_injective`): the derivative of the coordinate
expression within the range of the model is injective, hence antilipschitz.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4, where immersions are shown to be locally injective by the rank
  theorem; the argument here avoids the rank theorem so that it also applies at boundary points.
-/

public section

open Function Set Filter
open scoped Manifold Topology

variable {𝕜 E H M E' H' N : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {x : M}

/-- A map between real or complex manifolds, the source modelled on a finite-dimensional space,
that is `C^n`, `n ≠ 0`, at `x` and has injective manifold derivative at `x` is injective on a
neighbourhood of `x`. The manifolds may have boundary or corners. -/
theorem ContMDiffAt.exists_mem_nhds_injOn {n : WithTop ℕ∞} (hf : ContMDiffAt I J n f x)
    (hn : n ≠ 0) (hinj : Injective (mfderiv I J f x)) : ∃ t ∈ 𝓝 x, InjOn f t := by
  let := IsRCLikeNormedField.rclike 𝕜
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  have hx : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  -- The manifold derivative is the derivative of the coordinate expression within `range I`,
  -- up to the identifications of the tangent spaces with the model spaces.
  rw [(hf.mdifferentiableAt hn).mfderiv] at hinj
  obtain ⟨t, ht, hinjt⟩ := (contMDiffAt_iff.1 hf).2.exists_nhdsWithin_injOn hn I.convex_range hx
    (I.uniqueDiffOn _ hx) (by
      simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
        EquivLike.comp_injective, EquivLike.injective_comp, writtenInExtChartAt] using hinj)
  rw [← map_extChartAt_nhds] at ht
  refine ⟨(extChartAt I x).source ∩ extChartAt I x ⁻¹' t,
    inter_mem (extChartAt_source_mem_nhds x) ht, ?_⟩
  rintro a ⟨ha, hat⟩ b ⟨hb, hbt⟩ hab
  refine (extChartAt I x).injOn ha hb (hinjt hat hbt ?_)
  simp only [comp_apply, (extChartAt I x).left_inv ha, (extChartAt I x).left_inv hb, hab]

/-- A curve in a real or complex manifold that is `C^n`, `n ≠ 0`, at `t` and has nonzero velocity
at `t` is injective on a neighbourhood of `t`. The manifold may have boundary or corners. -/
theorem ContMDiffAt.exists_mem_nhds_injOn_of_curveVelocity_ne_zero {n : WithTop ℕ∞} {γ : 𝕜 → N}
    {t : 𝕜} (hγ : ContMDiffAt 𝓘(𝕜, 𝕜) J n γ t) (hn : n ≠ 0)
    (hv : TauCeti.Manifold.curveVelocity J γ t ≠ 0) : ∃ u ∈ 𝓝 t, InjOn γ u := by
  refine hγ.exists_mem_nhds_injOn hn <| (injective_iff_map_eq_zero _).2 fun (c : 𝕜) hc ↦ ?_
  -- On the parameter line the derivative is `c ↦ c • γ' t`: by linearity `c • γ' t` is the
  -- derivative applied to `c • 1`, which is `c * 1` since the tangent space there is `𝕜` itself.
  have hc' : c • TauCeti.Manifold.curveVelocity J γ t = 0 := by
    rw [TauCeti.Manifold.curveVelocity_apply, ← (mfderiv 𝓘(𝕜, 𝕜) J γ t).map_smul c (1 : 𝕜)]
    exact (congrArg (mfderiv 𝓘(𝕜, 𝕜) J γ t) (mul_one c)).trans hc
  exact (smul_eq_zero.1 hc').resolve_right hv

namespace TauCeti

/-- A map between real or complex manifolds, the source modelled on a finite-dimensional space,
with injective manifold derivative at `x` takes values different from `f x` at all points near `x`
other than `x`: the point `x` is isolated in its fibre. Only differentiability at `x` is used,
which follows from the injectivity of the derivative, and the manifolds may have boundary or
corners. -/
theorem eventually_ne_of_mfderiv_injective (hinj : Injective (mfderiv I J f x)) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  let := IsRCLikeNormedField.rclike 𝕜
  -- In the extended charts, `f` has the injective derivative `mfderiv I J f x` within `range I`,
  -- so its coordinate expression avoids its value at `extChartAt I x x` near that point.
  let f' : E →L[𝕜] E' := mfderiv I J f x
  obtain ⟨C, -, hC⟩ := (LinearMap.injective_iff_antilipschitz f'.toLinearMap).1 hinj
  have h := (mdifferentiableAt_of_mfderiv_injective hinj).hasMFDerivAt.2.eventually_ne ⟨C, hC⟩
    (c := writtenInExtChartAt I J x f (extChartAt I x x))
  -- The extended chart at `x` maps the punctured neighbourhoods of `x` into `range I` minus
  -- `extChartAt I x x`, as it is injective on its source.
  have hsrc : ∀ᶠ z in 𝓝[≠] x, z ∈ (extChartAt I x).source :=
    nhdsWithin_le_nhds (extChartAt_source_mem_nhds x)
  have ht : Tendsto (extChartAt I x) (𝓝[≠] x) (𝓝[range I \ {extChartAt I x x}] extChartAt I x x) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuousAt_extChartAt x).tendsto.mono_left nhdsWithin_le_nhds, by
      filter_upwards [self_mem_nhdsWithin, hsrc] with z hzx hzs
      exact ⟨extChartAt_target_subset_range x ((extChartAt I x).map_source hzs),
        fun hz ↦ hzx ((extChartAt I x).injOn hzs (mem_extChartAt_source x) hz)⟩⟩
  filter_upwards [ht.eventually h, hsrc] with z hz hzs hfz
  refine hz ?_
  simp only [writtenInExtChartAt, comp_apply, (extChartAt I x).left_inv hzs,
    (extChartAt I x).left_inv (mem_extChartAt_source x), hfz]

end TauCeti
