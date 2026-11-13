/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Convexity
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Comparison estimates for Jacobi fields

## An upper curvature bound

Let `J` be a Jacobi field along a geodesic `γ`, and let `ct_κ = s_κ' / s_κ` be the logarithmic
derivative of the model sine `s_κ` of constant curvature `κ`. The Jacobi equation and the
Riccati equation `ct_κ' = -ct_κ² - κ` give, wherever `s_κ(t - a) ≠ 0`,

`(⟨D_t J, J⟩ - ct_κ(t - a) |J|²)' = |D_t J - ct_κ(t - a) J|² + κ |J|² - ⟨R(J, γ')γ', J⟩`.

If `⟨R(J, γ')γ', J⟩ ≤ κ |J|²`, this derivative is nonnegative, so `⟨D_t J, J⟩ - ct_κ(t - a) |J|²`
is nondecreasing. For a unit-speed geodesic and a field normal to it, the hypothesis is the
sectional curvature bound `K(J, γ') ≤ κ`. If moreover `J(a) = 0`, this function tends to zero as
`t` decreases to `a`, which gives

`ct_κ(t - a) |J(t)|² ≤ ⟨D_t J(t), J(t)⟩`

for `t > a` before the first positive zero of `s_κ`. Since `⟨D_t J, J⟩ = |J| |J|'` where `J ≠ 0`,
this bounds the logarithmic derivative of `|J|` from below by that of `s_κ(t - a)`. Covariant
derivatives are taken within the parameter set, so the statements apply to closed intervals.

## Nonpositive curvature

The norm-convexity theorem
`IsJacobiFieldOn.convexOn_norm_of_sectionalCurvature_nonpos` applies to the radial
Jacobi field `J(t) = d(exp_p)_(tv)(tw)`. Convexity and `J(0) = 0`
show that `|J(t)| / t` cannot decrease for positive time. Continuity of `d(exp_p)` at the
origin then gives `norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos`:
`|d(exp_p)_v(w)| ≥ |w|` on the natural exponential domain.

## Main results

* `IsJacobiFieldOn.hasDerivWithinAt_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq`:
  the derivative of `⟨D_t J, J⟩ - ct_κ(t - a) |J|²`.
* `IsJacobiFieldOn.monotoneOn_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq`:
  its monotonicity under an upper curvature bound.
* `IsJacobiFieldOn.curvatureCotangent_mul_norm_sq_le_inner_alongCurveWithin_self`:
  the comparison `ct_κ(b - a) |J(b)|² ≤ ⟨D_t J(b), J(b)⟩` for a Jacobi field vanishing at `a`.
* `norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos`:
  the differential of the exponential map does not decrease norms in nonpositive curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–12 (Jacobi comparison and the Cartan–Hadamard theorem).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold InnerProductSpace Real Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a b t κ : ℝ}

namespace IsJacobiFieldOn

/-- For a Jacobi field `J` along a geodesic `γ`, the function `⟨D_t J, J⟩ - ct_κ(t - a) |J|²`
has derivative `|D_t J - ct_κ(t - a) J|² + κ |J|² - ⟨R(J, γ')γ', J⟩` wherever the model sine
`s_κ(t - a)` is nonzero. Here `ct_κ = s_κ' / s_κ` is the logarithmic derivative of `s_κ`. -/
theorem hasDerivWithinAt_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) (hmodel : curvatureSine κ (t - a) ≠ 0) :
    HasDerivWithinAt
      (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ -
        curvatureCotangent κ (r - a) * ‖V r‖ ^ 2)
      (‖alongCurveWithin (leviCivitaConnection I M) γ V s t -
          curvatureCotangent κ (t - a) • V t‖ ^ 2 + κ * ‖V t‖ ^ 2 -
        ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (V t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t), V t⟫_ℝ) s t := by
  have hd := (h.hasDerivWithinAt_inner_alongCurveWithin_self ht).sub
    (((hasDerivAt_curvatureCotangent hmodel).comp_sub_const t a).hasDerivWithinAt.mul
      (h.hasDerivWithinAt_norm_sq ht))
  convert hd using 1
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Let `J` be a Jacobi field along a geodesic `γ` and let `u` be an interval of parameters on
which the model sine `s_κ(t - a)` does not vanish. If `⟨R(J, γ')γ', J⟩ ≤ κ |J|²` in the interior
of `u`, then `⟨D_t J, J⟩ - ct_κ(t - a) |J|²` is nondecreasing on `u`. -/
theorem monotoneOn_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq
    (h : IsJacobiFieldOn I γ V s) {u : Set ℝ} (hu : IsPreconnected u) (hus : u ⊆ s)
    (hmodel : ∀ t ∈ u, curvatureSine κ (t - a) ≠ 0)
    (hR : ∀ t ∈ interior u, ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (V t)
      (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t), V t⟫_ℝ ≤ κ * ‖V t‖ ^ 2) :
    MonotoneOn (fun t ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, V t⟫_ℝ -
      curvatureCotangent κ (t - a) * ‖V t‖ ^ 2) u := by
  have hd (t : ℝ) (ht : t ∈ u) :=
    (h.hasDerivWithinAt_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq
      (hus ht) (hmodel t ht)).mono hus
  exact monotoneOn_of_hasDerivWithinAt_nonneg (Real.convex_iff_isPreconnected.2 hu)
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).mono interior_subset)
    (fun t ht ↦ sub_nonneg.2 ((hR t ht).trans (le_add_of_nonneg_left (sq_nonneg _))))

/-- At a zero `a` of a Jacobi field `J`, the function `⟨D_t J, J⟩ - ct_κ(t - a) |J|²` tends to
zero as `t` decreases to `a`. -/
private theorem tendsto_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq
    (h : IsJacobiFieldOn I γ V s) (hab : a < b) (hs : Icc a b ⊆ s) (hVa : V a = 0) (κ : ℝ) :
    Tendsto (fun t ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, V t⟫_ℝ -
      curvatureCotangent κ (t - a) * ‖V t‖ ^ 2) (𝓝[>] a) (𝓝 0) := by
  have ha : a ∈ s := hs (left_mem_Icc.2 hab.le)
  have hle : 𝓝[>] a ≤ 𝓝[s \ {a}] a := by
    rw [← nhdsWithin_Ioc_eq_nhdsGT hab]
    exact nhdsWithin_mono a fun t ht ↦ ⟨hs (Ioc_subset_Icc_self ht), ht.1.ne'⟩
  have hpair : Tendsto (fun t ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, V t⟫_ℝ)
      (𝓝[>] a) (𝓝 0) := by
    have hc := (h.hasDerivWithinAt_inner_alongCurveWithin_self ha).continuousWithinAt.tendsto
    rw [hVa, inner_zero_right] at hc
    exact hc.mono_left (hle.trans (nhdsWithin_mono a sdiff_subset))
  have hslope : Tendsto (slope (fun t ↦ ‖V t‖ ^ 2) a) (𝓝[>] a) (𝓝 0) := by
    have hd := h.hasDerivWithinAt_norm_sq ha
    rw [hVa, inner_zero_right, mul_zero] at hd
    exact (hasDerivWithinAt_iff_tendsto_slope.1 hd).mono_left hle
  have hmodel : Tendsto (fun t ↦ (t - a) * curvatureCotangent κ (t - a)) (𝓝[>] a) (𝓝 1) :=
    (tendsto_mul_curvatureCotangent_zero κ).comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_sub_right a).tendsto' a 0 (sub_self a)).mono_left nhdsWithin_le_nhds)
        (eventually_mem_nhdsWithin.mono fun t ht ↦ sub_ne_zero.2 ht.ne')
  have hprod : Tendsto (fun t ↦ curvatureCotangent κ (t - a) * ‖V t‖ ^ 2)
      (𝓝[>] a) (𝓝 (1 * 0)) := by
    refine (hmodel.mul hslope).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have hta : t - a ≠ 0 := sub_ne_zero.2 ht.ne'
    simp only [slope_def_field, hVa, norm_zero]
    field_simp
    ring
  simpa only [mul_zero, sub_zero] using hpair.sub hprod

/-- **Jacobi field comparison under an upper curvature bound**, in logarithmic derivative form.
Let `J` be a Jacobi field along a geodesic `γ` with `J(a) = 0` and `⟨R(J, γ')γ', J⟩ ≤ κ |J|²`
on `(a, b)`, where `b - a < π / √κ` if `κ > 0`. Then `ct_κ(b - a) |J(b)|² ≤ ⟨D_t J(b), J(b)⟩`,
with `ct_κ = s_κ' / s_κ` the logarithmic derivative of the model sine. For a unit-speed geodesic
and a field normal to it, the curvature hypothesis is the sectional curvature bound
`K(J, γ') ≤ κ`. -/
theorem curvatureCotangent_mul_norm_sq_le_inner_alongCurveWithin_self
    (h : IsJacobiFieldOn I γ V s) (hab : a ≤ b) (hs : Icc a b ⊆ s) (hVa : V a = 0)
    (hbound : 0 < κ → b - a < π / √κ)
    (hR : ∀ t ∈ Ioo a b, ⟪(leviCivitaConnection I M).curvatureTensor (γ t) (V t)
      (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t), V t⟫_ℝ ≤ κ * ‖V t‖ ^ 2) :
    curvatureCotangent κ (b - a) * ‖V b‖ ^ 2 ≤
      ⟪alongCurveWithin (leviCivitaConnection I M) γ V s b, V b⟫_ℝ := by
  obtain rfl | hab := hab.eq_or_lt
  · simp [hVa]
  have hmono := h.monotoneOn_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq
    isPreconnected_Ioc (Ioc_subset_Icc_self.trans hs)
    (fun t ht ↦ (curvatureSine_pos (sub_pos.2 ht.1)
      fun hκ ↦ (sub_le_sub_right ht.2 a).trans_lt (hbound hκ)).ne')
    (by rwa [interior_Ioc])
  refine sub_nonneg.1 (le_of_tendsto
    (h.tendsto_inner_alongCurveWithin_self_sub_curvatureCotangent_mul_norm_sq hab hs hVa κ) ?_)
  filter_upwards [Ioc_mem_nhdsGT hab] with t ht
  exact hmono ht (right_mem_Ioc.2 hab) ht.2

end IsJacobiFieldOn

/-- In nonpositive sectional curvature along the radial segment from `0` to `v`, the
exponential differential does not decrease any tangent norm. The segment lies in the natural
exponential domain; completeness, unit speed and orthogonality to the radial vector are not
required. -/
theorem norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos [I.Boundaryless]
    {p : M} {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u z : TangentSpace I (riemannianExp I M p (t • v)),
      LinearIndependent ℝ ![u, z] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (riemannianExp I M p (t • v)) u z ≤ 0)
    (w : TangentSpace I p) :
    ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hJ := (isJacobiFieldOn_mfderiv_riemannianExp p v w).mono
    (uniqueDiffOn_Icc zero_lt_one) hsub
  have hc := hJ.convexOn_norm_of_sectionalCurvature_nonpos isPreconnected_Icc hK
  have hle : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) w‖ ≤
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
    intro t ht
    have h := hc.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    -- The source tangent space is canonically the original vector space. Apply linearity
    -- before rewriting the parameters, since the target fibre norms depend on those parameters.
    have hnorm (r : ℝ) :
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w)‖ =
          |r| * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ := by
      calc
        _ = ‖r • mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ :=
          congrArg norm ((mfderiv 𝓘(ℝ, TangentSpace I p) I
            (riemannianExp I M p) (r • v)).map_smul r w)
        _ = _ := norm_smul r _
    simp_rw [hnorm] at h
    have htcoord : (1 - t) • (0 : ℝ) + t • (1 : ℝ) = t := by simp
    rw [htcoord] at h
    simp only [abs_zero, abs_one, zero_mul, one_mul, smul_eq_mul, abs_of_pos ht.1] at h
    rw [mul_zero, zero_add, one_smul] at h
    exact (mul_le_mul_iff_right₀ ht.1).1 h
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hcont := ((contMDiffOn_riemannianExp p).continuousOn_norm_mfderiv
    (by simp) (isOpen_expDomain p) w).continuousAt
      ((isOpen_expDomain p).mem_nhds (zero_mem_expDomain p))
  have hsmul : Tendsto (fun t : ℝ ↦ t • v) (𝓝[>] 0) (𝓝 0) :=
    ((by fun_prop : Continuous (fun t : ℝ ↦ t • v)).tendsto' 0 0
      (zero_smul ℝ v)).mono_left nhdsWithin_le_nhds
  have hlim := hcont.tendsto.comp hsmul
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds zero_lt_one).filter_mono
      nhdsWithin_le_nhds] with t ht h1
    exact ⟨ht, h1⟩
  have hbound := le_of_tendsto hlim (hevent.mono fun t ht ↦ hle t ht)
  rw [mfderiv_riemannianExp_apply_zero, riemannianExp_zero] at hbound
  exact hbound

end TauCeti.Manifold
