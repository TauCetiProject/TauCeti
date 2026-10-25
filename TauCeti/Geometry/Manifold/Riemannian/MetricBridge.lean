/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Coordinate displacement is bounded by Riemannian path length

This file supplies local analytic bridges between the Riemannian distance and coordinate charts.
If the chart derivative is bounded along a `C¹` path, the coordinate displacement of the path is
bounded by that derivative bound times its Riemannian length. Fix a point `x` and `r > 1`. Every
continuous linear map from `T_x M` to a real normed space, read in the extended chart at `x`,
satisfies a Lipschitz bound at the base point `x` for the Riemannian distance: for all `y` in a
neighbourhood of `x` (depending on `r`), its displacement from `x` to `y` is at most `r` times its
norm times the distance from `x` to `y`.

This is the chart-level estimate needed when transferring vector-valued variation estimates to
`Manifold.pathELength` in the Hopf--Rinow lower-semicontinuity argument.  The proof uses the
interval-integral estimate
`enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc` and the chain rule for `mfderivWithin`.

The interval-integral estimate and the local-coordinate differential argument follow the
corresponding constructions in Mathlib's `Geometry/Manifold/Riemannian/Basic.lean`.

## Main results

* `TauCeti.Manifold.enorm_sub_le_mul_pathELength`: a differential bound along a differentiable
  path controls the displacement of a function whose composition with the path is `C¹`.
* `TauCeti.Manifold.enorm_extChartAt_sub_le_mul_pathELength`: the chart-valued specialization.
* `ContinuousLinearMap.enorm_apply_extChartAt_sub_le_mul_pathELength`: the specialization to a
  continuous linear map applied to chart coordinates, with a bound on chart distortion.
* `TauCeti.Manifold.eventually_enorm_apply_extChartAt_sub_le`: the sharp local chart--distance
  estimate for continuous linear maps.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 §2.
-/

public section

open Bundle Filter Manifold MeasureTheory Set
open scoped Bundle ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

section Path

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- A bound on the differential of a vector-valued function applied to the within-derivative of a
differentiable path controls the displacement of the function along that path, provided the
composition is `C¹`. -/
theorem enorm_sub_le_mul_pathELength {f : M → F} {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : MDiff[Icc a b] γ)
    (hf : CMDiff[Icc a b] 1 (f ∘ γ))
    (hfdiff : ∀ t ∈ Icc a b, MDifferentiableAt I 𝓘(ℝ, F) f (γ t))
    {C : ℝ≥0} (hC : ∀ t ∈ Icc a b,
      ‖(mfderiv% f (γ t)) (mfderiv[Icc a b] γ t 1)‖ₑ ≤
        C * ‖mfderiv[Icc a b] γ t 1‖ₑ) :
    ‖f (γ b) - f (γ a)‖ₑ ≤ C * pathELength I γ a b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hbound : ‖(f ∘ γ) b - (f ∘ γ) a‖ₑ ≤ C * pathELength I γ a b := by
    calc
      ‖(f ∘ γ) b - (f ∘ γ) a‖ₑ ≤
          ∫⁻ t in Icc a b, ‖derivWithin (f ∘ γ) (Icc a b) t‖ₑ := by
        apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ hab.le
        rwa [← contMDiffOn_iff_contDiffOn]
      _ ≤ ∫⁻ t in Icc a b, C * ‖mfderiv[Icc a b] γ t 1‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
        have hderiv := (TauCeti.Manifold.hasDerivWithinAt_comp_curve
          (hfdiff t ht)
          (hasMFDerivWithinAt_curveVelocityWithin
            (hγ t ht))).derivWithin
              (uniqueDiffOn_Icc hab t ht)
        rw [hderiv, curveVelocityWithin_apply]
        exact hC t ht
      _ = C * pathELength I γ a b := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]
  simpa using hbound

/-- A chart-valued instance of `enorm_sub_le_mul_pathELength`. -/
theorem enorm_extChartAt_sub_le_mul_pathELength [IsManifold I 1 M] (x : M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : CMDiff[Icc a b] 1 γ)
    (hγsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H x).source)
    {C : ℝ≥0} (hC : ∀ t ∈ Icc a b,
      ‖(mfderiv% (extChartAt I x) (γ t)) (mfderiv[Icc a b] γ t 1)‖ₑ ≤
        C * ‖mfderiv[Icc a b] γ t 1‖ₑ) :
    ‖extChartAt I x (γ b) - extChartAt I x (γ a)‖ₑ ≤ C * pathELength I γ a b := by
  apply enorm_sub_le_mul_pathELength hab (hγ.mdifferentiableOn one_ne_zero)
  · exact contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H x).source)
      hγ (fun t ht ↦ hγsrc t ht)
  · exact fun t ht ↦ mdifferentiableAt_extChartAt (hγsrc t ht)
  · exact hC

/-- Along a `C¹` path which stays where the chart at `x` distorts Riemannian norms by at most
`r`, a continuous linear map `ℓ` from `T_x M` to `F`, read in that chart, changes by at most
`r ‖ℓ‖` times the length of the path. -/
theorem _root_.ContinuousLinearMap.enorm_apply_extChartAt_sub_le_mul_pathELength
    [IsManifold I 1 M] {x : M} {r : ℝ}
    (ℓ : TangentSpace I x →L[ℝ] F) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : CMDiff[Icc a b] 1 γ)
    (hmem : ∀ s ∈ Icc a b, γ s ∈ (chartAt H x).source ∧
      ‖(trivializationAt E (fun x : M ↦ TangentSpace I x) x).symmL ℝ x ∘L
        (trivializationAt E (fun x : M ↦ TangentSpace I x) x).continuousLinearMapAt ℝ (γ s)‖ ≤ r) :
    ‖ℓ (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ ≤
      ENNReal.ofReal r * ‖ℓ‖ₑ * Manifold.pathELength I γ a b := by
  set T := trivializationAt E (fun x : M ↦ TangentSpace I x) x
  -- The same linear map, typed on the model space so that it can be composed with the chart.
  let ℓE : E →L[ℝ] F := ℓ
  let f : M → F := fun z ↦ ℓE (extChartAt I x z)
  have hf : CMDiff[Icc a b] 1 (f ∘ γ) :=
    ℓE.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt.comp (I' := I)
      (t := (chartAt H x).source) hγ fun s hs ↦ (hmem s hs).1)
  have hfdiff : ∀ s ∈ Icc a b, MDifferentiableAt I 𝓘(ℝ, F) f (γ s) := fun s hs ↦
    ℓE.mdifferentiableAt.comp (γ s) (mdifferentiableAt_extChartAt (hmem s hs).1)
  have hC : ∀ s ∈ Icc a b, ‖(mfderiv% f (γ s)) (mfderiv[Icc a b] γ s 1)‖ₑ ≤
      (r.toNNReal * ‖ℓ‖₊ : ℝ≥0) * ‖mfderiv[Icc a b] γ s 1‖ₑ := by
    intro s hs
    set v := mfderiv[Icc a b] γ s 1
    have hcomp : mfderiv% f (γ s) = ℓE ∘L mfderiv% (extChartAt I x) (γ s) := by
      -- Unfold the local wrapper into the composition to which the chain rule applies.
      change mfderiv% (ℓE ∘ extChartAt I x) (γ s) = _
      rw [mfderiv_comp (γ s) ℓE.mdifferentiableAt
        (mdifferentiableAt_extChartAt (hmem s hs).1), ContinuousLinearMap.mfderiv_eq]
      -- `ℓE` is `ℓ` retyped, and the tangent space of `F` is only definitionally `F`.
      rfl
    rw [hcomp]
    calc ‖ℓE (mfderiv% (extChartAt I x) (γ s) v)‖ₑ
        = ‖ℓ ((T.symmL ℝ x ∘L T.continuousLinearMapAt ℝ (γ s)) v)‖ₑ := by
          -- At the base point the inverse trivialization is the identity, and at `γ s` the
          -- trivialization is the derivative of the chart; both identifications, and `ℓE = ℓ`,
          -- hold only up to the definitional equality `TangentSpace I x = E`.
          rw [ContinuousLinearMap.comp_apply,
            TangentBundle.continuousLinearMapAt_trivializationAt (hmem s hs).1,
            TangentBundle.symmL_trivializationAt (mem_chart_source H x),
            mfderivWithin_range_extChartAt_symm]
          rfl
      _ ≤ ‖ℓ‖ₑ * (‖T.symmL ℝ x ∘L T.continuousLinearMapAt ℝ (γ s)‖ₑ * ‖v‖ₑ) :=
          (ℓ.le_opENorm _).trans (by gcongr; exact ContinuousLinearMap.le_opENorm _ _)
      _ ≤ ‖ℓ‖ₑ * (ENNReal.ofReal r * ‖v‖ₑ) := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hmem s hs).2
      _ = (r.toNNReal * ‖ℓ‖₊ : ℝ≥0) * ‖v‖ₑ := by
          rw [ENNReal.coe_mul, mul_comm (r.toNNReal : ℝ≥0∞), mul_assoc]
          rfl
  have key := enorm_sub_le_mul_pathELength hab (hγ.mdifferentiableOn one_ne_zero) hf hfdiff hC
  have hsub : f (γ b) - f (γ a) = ℓ (extChartAt I x (γ b) - extChartAt I x (γ a)) :=
    (map_sub ℓ _ _).symm
  rw [hsub, ENNReal.coe_mul] at key
  exact key

end Path

section LocalComparison

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- **Sharp local Lipschitz bound for the extended chart.** For `r > 1`, near `x` every continuous
linear map `ℓ` from `T_x M` to a real normed space, read in the extended chart at `x`, is
`(r ‖ℓ‖)`-Lipschitz at `x` for the Riemannian distance. -/
theorem eventually_enorm_apply_extChartAt_sub_le [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (x : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, ∀ ℓ : TangentSpace I x →L[ℝ] F,
      ‖ℓ (extChartAt I x y - extChartAt I x x)‖ₑ ≤ ENNReal.ofReal r * ‖ℓ‖ₑ * edist x y := by
  have hu : {y | y ∈ (chartAt H x).source ∧
      ‖(trivializationAt E (fun x : M ↦ TangentSpace I x) x).symmL ℝ x ∘L
        (trivializationAt E (fun x : M ↦ TangentSpace I x) x).continuousLinearMapAt ℝ y‖ < r}
      ∈ 𝓝 x :=
    inter_mem (chart_source_mem_nhds H x)
      (eventually_norm_symmL_trivializationAt_self_comp_lt E (fun x : M ↦ TangentSpace I x) x hr)
  -- Points at Riemannian distance less than `c` from `x` lie in this good neighbourhood.
  obtain ⟨c, hc, hcu⟩ := setOfPred_riemannianEDist_lt_subset_nhds' I hu
  filter_upwards [eventually_riemannianEDist_lt I x hc] with y hy ℓ
  -- A path from `x` to `y` of length less than `δ ≤ c` stays in the good neighbourhood.
  have hδ : ∀ δ, Manifold.riemannianEDist I x y < δ → δ ≤ c →
      ‖ℓ (extChartAt I x y - extChartAt I x x)‖ₑ ≤ ENNReal.ofReal r * ‖ℓ‖ₑ * δ := by
    intro δ hyδ hδc
    obtain ⟨γ, hγ0, hγ1, hγ, hlen, -, -⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hyδ zero_lt_one
    have hmem : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ _ := fun s hs ↦ hcu <|
      calc Manifold.riemannianEDist I x (γ s) ≤ Manifold.pathELength I γ 0 s :=
            Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 rfl hs.1
        _ ≤ Manifold.pathELength I γ 0 1 := Manifold.pathELength_mono le_rfl hs.2
        _ < c := hlen.trans_le hδc
    have key := ℓ.enorm_apply_extChartAt_sub_le_mul_pathELength zero_le_one hγ.contMDiffOn
      (fun s hs ↦ ⟨(hmem s hs).1, (hmem s hs).2.le⟩)
    rw [hγ0, hγ1] at key
    exact key.trans (by gcongr)
  -- Letting `δ` decrease to the distance gives the claim.
  rw [IsRiemannianManifold.out (I := I) x y]
  have : (𝓝[>] (Manifold.riemannianEDist I x y)).NeBot := nhdsGT_neBot_of_exists_gt ⟨c, hy⟩
  have hlim : Tendsto (fun δ ↦ ENNReal.ofReal r * ‖ℓ‖ₑ * δ)
      (𝓝[>] (Manifold.riemannianEDist I x y))
      (𝓝 (ENNReal.ofReal r * ‖ℓ‖ₑ * Manifold.riemannianEDist I x y)) :=
    (ENNReal.Tendsto.const_mul tendsto_id (Or.inr (by finiteness))).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hy] with δ hδmem using hδ δ hδmem.1 hδmem.2.le

end LocalComparison

end Manifold
end TauCeti
