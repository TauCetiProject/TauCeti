/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Topology.Homotopy.AddCircle
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Geometry.Manifold.Flow.Straightening
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Limits of periodic orbits

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold `M`, and let `γᵢ` be
periodic integral curves of `v`, of periods `Tᵢ > 0`, whose initial points `γᵢ 0` converge to `x`
while the periods converge to `T₀`. If `v x ≠ 0` and the trajectory of `x` is defined for all
time, then the limit is again a periodic orbit:

* the limit period is positive, `0 < T₀` (`TauCeti.pos_of_tendsto_period`), because near a point
  where `v` does not vanish the flow cannot return to its starting point in a short time
  (`TauCeti.exists_pos_eventually_flowOf_ne`);
* the trajectory of `x` is `T₀`-periodic (`TauCeti.flowOf_eq_of_tendsto_period`,
  `TauCeti.periodic_flowOf_of_tendsto_period`), by continuity of the flow;
* if the loops `ℝ/Tᵢℤ → M` traced by the `γᵢ` are null-homotopic, so is the loop `ℝ/T₀ℤ → M`
  traced by the trajectory of `x` (`TauCeti.exists_nullhomotopic_of_tendsto_period`).

For the last point, the loops of `x` and of a nearby `y = γᵢ 0` are joined by a cylinder of closed
paths: along a path `p_s` from `x` to `y` in a chart, with periods `T_s` interpolating between `T₀`
and `Tᵢ`, the path `θ ↦ φ^{θ T_s}(w_s(θ))`, where `w_s` runs in the chart from `p_s` to
`φ^{-T_s}(p_s)`, starts and ends at `p_s`. Here `φ` is the flow of `v`.

This is the compactness step of the Hofer–Zehnder–Struwe almost existence theorem: closed
characteristics of bounded period on levels converging to a regular level produce a closed
characteristic on that level, contractible whenever the approximating ones are.

## Main results

* `TauCeti.exists_pos_eventually_flowOf_ne`: periods of points near a nonsingular point are
  bounded below.
* `TauCeti.pos_of_tendsto_period`: the limit of the periods is positive.
* `TauCeti.flowOf_eq_of_tendsto_period`, `TauCeti.periodic_flowOf_of_tendsto_period`: the limit
  point is periodic of the limit period.
* `TauCeti.exists_nullhomotopic_of_tendsto_period`: null-homotopy passes to the limit orbit.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
-/

public section

noncomputable section

open Filter Function Metric Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x} {x : M}

/-- **Short periods are excluded near a nonsingular point.** If a `C¹` vector field does not vanish
at `x`, there is `δ > 0` such that the flow of every point `y` near `x` is defined up to time `δ`
and does not return to `y` at any time in `(0, δ)`. -/
theorem exists_pos_eventually_flowOf_ne [I.Boundaryless] [IsManifold I 2 M]
    (hv : CMDiff 1 (T% v)) (hx : v x ≠ 0) :
    ∃ δ > 0, ∀ᶠ y in 𝓝 x, ∀ t ∈ Ioo 0 δ, (t, y) ∈ flowDomain v ∧ flowOf v t y ≠ y := by
  -- In a straightening chart `e`, the function `g = ℓ ∘ I ∘ e` grows at the constant rate
  -- `‖u‖ ≠ 0` along `v`.
  obtain ⟨e, u, he, hxe, hu, heu⟩ := exists_chart_mfderiv_eq_const (m := 1) (n := 2) le_rfl
    (by norm_num) (hv.contMDiffOn (s := univ)) univ_mem hx
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ u (norm_ne_zero_iff.2 hu)
  have hg {y : M} (hy : y ∈ e.source) : HasMFDerivAt I 𝓘(ℝ) (ℓ ∘ (I ∘ e)) y
      ((ℓ : E →L[ℝ] ℝ).comp (mfderiv I 𝓘(ℝ, E) (I ∘ e) y)) := by
    have hIe : MDifferentiableAt I 𝓘(ℝ, E) (I ∘ e) y :=
      ((I.contMDiff.contMDiffAt).comp y
        ((contMDiffOn_of_mem_maximalAtlas he).contMDiffAt
          (e.open_source.mem_nhds hy))).mdifferentiableAt one_ne_zero
    exact ℓ.hasMFDerivAt.comp y hIe.hasMFDerivAt
  -- The flow keeps the points near `x` in the chart for short times.
  have hU : flowDomain v ∩ (fun p : ℝ × M ↦ flowOf v p.1 p.2) ⁻¹' e.source ∈ 𝓝 ((0 : ℝ), x) :=
    ((contMDiffOn_flowOf le_rfl hv).continuousOn.isOpen_inter_preimage (isOpen_flowDomain hv)
      e.open_source).mem_nhds ⟨mem_flowDomain_zero hv x, by
      rw [mem_preimage, flowOf_zero hv]; exact hxe⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨δ, hδ, mem_of_superset hB fun y hy t ht ↦ ?_⟩
  have hmem {s : ℝ} (hs : s ∈ Icc 0 t) :
      (s, y) ∈ flowDomain v ∧ flowOf v s y ∈ e.source := by
    refine hAB ⟨hδA ?_, hy⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩
  refine ⟨(hmem ⟨ht.1.le, le_rfl⟩).1, fun hty ↦ ?_⟩
  have hderiv {s : ℝ} (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun r ↦ (ℓ ∘ (I ∘ e)) (flowOf v r y)) ‖u‖ s := by
    have h := hasDerivAt_comp_flowOf hv (hmem hs).1 (hg (hmem hs).2).mdifferentiableAt
    rw [mvfderiv_apply_eq_mfderiv_apply, (hg (hmem hs).2).mfderiv] at h
    refine h.congr_deriv ?_
    -- The composite applies `ℓ` to the derivative of the chart; the tangent spaces of `E` are `E`.
    calc _ = ℓ (mfderiv I 𝓘(ℝ, E) (I ∘ e) (flowOf v s y) (v (flowOf v s y))) := rfl
      _ = ‖u‖ := by rw [heu _ (hmem hs).2, hℓ, RCLike.ofReal_real_eq_id, id]
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun r ↦ (ℓ ∘ (I ∘ e)) (flowOf v r y))
    (fun _ ↦ ‖u‖) ht.1 (fun s hs ↦ (hderiv hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ hderiv (Ioo_subset_Icc_self hs))
  rw [hty, flowOf_zero hv, sub_self, zero_div] at hc
  exact norm_ne_zero_iff.2 hu hc

variable {ι : Type*} {l : Filter ι} {γ : ι → ℝ → M} {T : ι → ℝ} {T₀ : ℝ}

/-- **The limit point of periodic orbits is periodic.** If periodic integral curves `γᵢ` of a `C¹`
vector field, of periods `Tᵢ`, have initial points converging to `x` and periods converging to
`T₀`, and the flow of `x` is defined at time `T₀`, then `x` returns to itself at time `T₀`. -/
theorem flowOf_eq_of_tendsto_period [l.NeBot] (hv : CMDiff 1 (T% v))
    (hT₀ : (T₀, x) ∈ flowDomain v) (hγ : ∀ i, IsMIntegralCurve (γ i) v)
    (hper : ∀ i, Periodic (γ i) (T i)) (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x))
    (hT : Tendsto T l (𝓝 T₀)) : flowOf v T₀ x = x := by
  have hc : Tendsto (fun i ↦ flowOf v (T i) (γ i 0)) l (𝓝 (flowOf v T₀ x)) :=
    ((contMDiffOn_flowOf le_rfl hv).continuousOn.continuousAt
      ((isOpen_flowDomain hv).mem_nhds hT₀)).tendsto.comp (hT.prodMk_nhds hx)
  refine tendsto_nhds_unique (hc.congr fun i ↦ ?_) hx
  rw [flowOf_eq_of_isMIntegralCurve hv (hγ i), (hper i).eq]

/-- **The limit orbit of periodic orbits is periodic.** If periodic integral curves `γᵢ` of a `C¹`
vector field, of periods `Tᵢ`, have initial points converging to a point `x` whose trajectory is
defined for all time, and periods converging to `T₀`, then the trajectory of `x` is
`T₀`-periodic. -/
theorem periodic_flowOf_of_tendsto_period [l.NeBot] (hv : CMDiff 1 (T% v))
    (hdom : ∀ t, (t, x) ∈ flowDomain v) (hγ : ∀ i, IsMIntegralCurve (γ i) v)
    (hper : ∀ i, Periodic (γ i) (T i)) (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x))
    (hT : Tendsto T l (𝓝 T₀)) : Periodic (fun t ↦ flowOf v t x) T₀ := fun t ↦ by
  have hxT := flowOf_eq_of_tendsto_period hv (hdom T₀) hγ hper hx hT
  have h := (flowOf_add hv (hdom T₀) (t := t) (by rw [hxT]; exact hdom t)).2
  rw [hxT] at h
  simp only [h, add_comm]

/-- **The limit of the periods of periodic orbits is positive.** If periodic integral curves `γᵢ`
of a `C¹` vector field, of positive periods `Tᵢ`, have initial points converging to a point `x`
where the field does not vanish, then their periods do not converge to `0`. -/
theorem pos_of_tendsto_period [I.Boundaryless] [IsManifold I 2 M] [l.NeBot]
    (hv : CMDiff 1 (T% v)) (hx₀ : v x ≠ 0)
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hper : ∀ i, Periodic (γ i) (T i))
    (hpos : ∀ i, 0 < T i) (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) (hT : Tendsto T l (𝓝 T₀)) :
    0 < T₀ := by
  refine (ge_of_tendsto' hT fun i ↦ (hpos i).le).lt_of_ne' fun h0 ↦ ?_
  subst h0
  obtain ⟨δ, hδ, hev⟩ := exists_pos_eventually_flowOf_ne hv hx₀
  obtain ⟨i, hi, hiδ⟩ := ((hx.eventually hev).and (hT.eventually (gt_mem_nhds hδ))).exists
  refine (hi (T i) ⟨hpos i, hiδ⟩).2 ?_
  rw [flowOf_eq_of_isMIntegralCurve hv (hγ i), (hper i).eq]

/-- Joining the loop of a `T₀`-periodic point `x` to the loops of nearby periodic points by a
cylinder of closed paths. For every `(S, y)` near `(T₀, x)` with `φ^{-S}(y) = y`, there is a
continuous family of closed paths starting with `θ ↦ φ^{θ T₀}(x)` and ending with
`θ ↦ φ^{θ S}(y)`, where `φ` is the flow of `v`. -/
private theorem eventually_exists_cylinder [I.Boundaryless] (hv : CMDiff 1 (T% v)) (hT₀ : 0 < T₀)
    (hdom : ∀ t, (t, x) ∈ flowDomain v) (hxT : flowOf v T₀ x = x) :
    ∀ᶠ p : ℝ × M in 𝓝 (T₀, x), flowOf v (-p.1) p.2 = p.2 → ∃ F : C(unitInterval × unitInterval, M),
      (∀ s, F (s, 0) = F (s, 1)) ∧ (∀ θ : unitInterval, F (0, θ) = flowOf v (θ * T₀) x) ∧
      ∀ θ : unitInterval, F (1, θ) = flowOf v (θ * p.1) p.2 := by
  set Φ : ℝ × M → M := fun p ↦ flowOf v p.1 p.2 with hΦdef
  have hΦ : ContinuousOn Φ (flowDomain v) := (contMDiffOn_flowOf le_rfl hv).continuousOn
  have hD := isOpen_flowDomain hv
  have hxT' : Φ (-T₀, x) = x := by
    simpa only [hΦdef, hxT] using flowOf_neg_flowOf hv (hdom T₀)
  -- The flow is defined on `[-R, R] × V` for a neighbourhood `V` of `x`.
  set R := T₀ + 1
  obtain ⟨U, V, -, hVo, hRu, hxV, hRV⟩ := generalized_tube_lemma (isCompact_Icc (a := -R) (b := R))
    isCompact_singleton hD (by rintro ⟨t, y⟩ ⟨-, rfl⟩; exact hdom t)
  have hdomV {t : ℝ} {y : M} (ht : |t| < R) (hy : y ∈ V) : (t, y) ∈ flowDomain v :=
    hRV ⟨hRu (abs_le.1 ht.le), hy⟩
  set e := extChartAt I x
  -- A ball `ball (e x) r` of the chart mapping into `V`.
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 (inter_mem (extChartAt_target_mem_nhds (I := I) x)
    (extChartAt_preimage_mem_nhds (I := I) (hVo.mem_nhds (hxV rfl))))
  -- Flowing for times near `-T₀` from points of `B` lands in that ball.
  have hS : e.source ∩ e ⁻¹' ball (e x) r ∈ 𝓝 x := inter_mem (extChartAt_source_mem_nhds x)
    ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ hr))
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1
    ((hΦ.continuousAt (hD.mem_nhds (hdom (-T₀)))).preimage_mem_nhds (by rwa [hxT']))
  obtain ⟨ρ, hρ, hρA⟩ := Metric.mem_nhds_iff.1 hA
  -- A smaller ball `ball (e x) r'` of the chart mapping into `B`.
  obtain ⟨r', hr', hr'N⟩ := Metric.mem_nhds_iff.1 (inter_mem (extChartAt_target_mem_nhds (I := I) x)
    (extChartAt_preimage_mem_nhds (I := I) hB))
  set r₀ := min r r'
  have hball : ball (e x) r₀ ∈ 𝓝 (e x) := ball_mem_nhds _ (lt_min hr hr')
  filter_upwards [prod_mem_nhds (ball_mem_nhds T₀ (lt_min hρ one_pos))
    (inter_mem (extChartAt_source_mem_nhds (I := I) x)
      ((continuousAt_extChartAt (I := I) x).preimage_mem_nhds hball))]
    with ⟨S, y⟩ ⟨hS, hysrc, hyball⟩ hyper
  simp only at hyper
  rw [mem_ball, Real.dist_eq, lt_min_iff] at hS
  -- The path of parameters: points `p s = e.symm (a s)` and periods `Ts s`.
  set a : unitInterval → E := fun s ↦ (1 - (s : ℝ)) • e x + (s : ℝ) • e y with ha_def
  set Ts : unitInterval → ℝ := fun s ↦ (1 - (s : ℝ)) * T₀ + s * S with hTs_def
  have ha (s : unitInterval) : a s ∈ ball (e x) r₀ :=
    convex_ball _ _ (mem_ball_self (lt_min hr hr')) hyball (sub_nonneg.2 s.2.2) s.2.1 (by ring)
  have hTs (s : unitInterval) : |Ts s - T₀| < min ρ 1 := by
    have h : Ts s - T₀ = s * (S - T₀) := by rw [hTs_def]; ring
    rw [h, abs_mul, abs_of_nonneg s.2.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) s.2.2) (lt_min_iff.2 hS)
  have hTsR (s : unitInterval) : |Ts s| < R := by
    obtain ⟨-, h1⟩ := lt_min_iff.1 (hTs s)
    rw [abs_lt] at h1 ⊢
    constructor <;> linarith
  have hr₀r : ball (e x) r₀ ⊆ ball (e x) r := ball_subset_ball (min_le_left _ _)
  have hr₀r' : ball (e x) r₀ ⊆ ball (e x) r' := ball_subset_ball (min_le_right _ _)
  set p : unitInterval → M := fun s ↦ e.symm (a s) with hp_def
  have hpV (s : unitInterval) : p s ∈ V := (hrN (hr₀r (ha s))).2
  have hpB (s : unitInterval) : p s ∈ B := (hr'N (hr₀r' (ha s))).2
  have hpdom (s : unitInterval) : (-Ts s, p s) ∈ flowDomain v :=
    hdomV (by rw [abs_neg]; exact hTsR s) (hpV s)
  -- The points `q s = φ^{-Ts s}(p s)`, read in the chart as `b s`.
  set q : unitInterval → M := fun s ↦ Φ (-Ts s, p s) with hq_def
  have hq (s : unitInterval) : q s ∈ e.source ∧ e (q s) ∈ ball (e x) r := by
    refine hAB ⟨hρA ?_, hpB s⟩
    rw [mem_ball, Real.dist_eq, neg_sub_neg, abs_sub_comm]
    exact (hTs s).trans_le (min_le_left _ _)
  set b : unitInterval → E := fun s ↦ e (q s) with hb_def
  -- The closing paths `w s` from `p s` to `q s` in the chart.
  set w : unitInterval × unitInterval → M :=
    fun z ↦ e.symm ((1 - (z.2 : ℝ)) • a z.1 + (z.2 : ℝ) • b z.1) with hw_def
  have hwball (z : unitInterval × unitInterval) :
      (1 - (z.2 : ℝ)) • a z.1 + (z.2 : ℝ) • b z.1 ∈ ball (e x) r :=
    convex_ball _ _ (hr₀r (ha z.1)) (hq z.1).2 (sub_nonneg.2 z.2.2.2) z.2.2.1 (by ring)
  have hwdom (z : unitInterval × unitInterval) : ((z.2 : ℝ) * Ts z.1, w z) ∈ flowDomain v := by
    refine hdomV ?_ (hrN (hwball z)).2
    rw [abs_mul, abs_of_nonneg z.2.2.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) z.2.2.2).trans_lt (hTsR z.1)
  -- Continuity of the pieces.
  have hac : Continuous a := by fun_prop
  have hTsc : Continuous Ts := by fun_prop
  have hpc : Continuous p :=
    (continuousOn_extChartAt_symm x).comp_continuous hac fun s ↦ (hrN (hr₀r (ha s))).1
  have hqc : Continuous q := hΦ.comp_continuous (hTsc.neg.prodMk hpc) hpdom
  have hbc : Continuous b := (continuousOn_extChartAt x).comp_continuous hqc fun s ↦ (hq s).1
  have hwc : Continuous w := (continuousOn_extChartAt_symm x).comp_continuous (by fun_prop)
    fun z ↦ (hrN (hwball z)).1
  let F : C(unitInterval × unitInterval, M) := ⟨fun z ↦ Φ ((z.2 : ℝ) * Ts z.1, w z),
    hΦ.comp_continuous (by fun_prop) hwdom⟩
  have hF (s θ : unitInterval) : F (s, θ) = flowOf v ((θ : ℝ) * Ts s) (w (s, θ)) := rfl
  -- The values at the ends of the paths and of the cylinder.
  have hp0 : p 0 = x := by simp [hp_def, ha_def, e]
  have hp1 : p 1 = y := by simpa [hp_def, ha_def, e] using e.left_inv hysrc
  have hq0 : q 0 = x := by simpa [hq_def, hTs_def, hp0] using hxT'
  have hq1 : q 1 = y := by
    simp only [hq_def, hTs_def, hp1, hΦdef, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    exact hyper
  have hw0 (s : unitInterval) : w (s, 0) = p s := by simp [hw_def, hp_def]
  have hw1 (s : unitInterval) : w (s, 1) = q s := by
    simpa [hw_def, hb_def] using e.left_inv (hq s).1
  have hwx (θ : unitInterval) : w (0, θ) = x := by
    have hb0 : b 0 = e x := by rw [hb_def]; simp only [hq0]
    have ha0 : a 0 = e x := by simp [ha_def]
    simp only [hw_def, ha0, hb0, ← add_smul, sub_add_cancel, one_smul, e, extChartAt_to_inv]
  have hwy (θ : unitInterval) : w (1, θ) = y := by
    have hb1 : b 1 = e y := by rw [hb_def]; simp only [hq1]
    have ha1 : a 1 = e y := by simp [ha_def]
    simp only [hw_def, ha1, hb1, ← add_smul, sub_add_cancel, one_smul]
    exact e.left_inv hysrc
  refine ⟨F, fun s ↦ ?_, fun θ ↦ ?_, fun θ ↦ ?_⟩
  · rw [hF, hF, hw0, hw1, Set.Icc.coe_zero, zero_mul, flowOf_zero hv, Set.Icc.coe_one, one_mul,
      hq_def]
    simpa only [neg_neg] using (flowOf_neg_flowOf hv (hpdom s)).symm
  · rw [hF, hwx]; simp [hTs_def]
  · rw [hF, hwy]; simp [hTs_def]

/-- **Null-homotopy passes to the limit of periodic orbits.** Let `γᵢ` be periodic integral curves
of a `C¹` vector field `v`, of positive periods `Tᵢ`, whose loops `ℝ/Tᵢℤ → M` are eventually
null-homotopic along the filter. If the initial points `γᵢ 0` converge to a point `x`
whose trajectory is defined for all time, and the periods converge to `T₀ > 0`, then the loop
`ℝ/T₀ℤ → M` traced by the trajectory of `x` is null-homotopic. -/
theorem exists_nullhomotopic_of_tendsto_period [I.Boundaryless] [l.NeBot] (hv : CMDiff 1 (T% v))
    (hT₀ : 0 < T₀)
    (hdom : ∀ t, (t, x) ∈ flowDomain v) (hγ : ∀ i, IsMIntegralCurve (γ i) v)
    (hper : ∀ i, Periodic (γ i) (T i)) (hpos : ∀ i, 0 < T i)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) (hT : Tendsto T l (𝓝 T₀))
    (hnull : ∀ᶠ i in l, ∃ g : C(AddCircle (T i), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ i t) :
    ∃ g : C(AddCircle T₀, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = flowOf v t x := by
  have : Fact (0 < T₀) := ⟨hT₀⟩
  have hxT := flowOf_eq_of_tendsto_period hv (hdom T₀) hγ hper hx hT
  -- The loop of `x`, descended from the `T₀`-periodic trajectory.
  have hperx := periodic_flowOf_of_tendsto_period hv hdom hγ hper hx hT
  have hcx : Continuous fun t ↦ flowOf v t x :=
    (contMDiffOn_flowOf le_rfl hv).continuousOn.comp_continuous (by fun_prop) hdom
  let g₀ : C(AddCircle T₀, M) := ⟨hperx.lift,
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (by
      convert hcx using 1; funext t; exact hperx.lift_coe t)⟩
  have hg₀ (t : ℝ) : g₀ t = flowOf v t x := hperx.lift_coe t
  -- A nearby periodic orbit with null-homotopic loop, and the cylinder joining it to `x`.
  obtain ⟨i, hcyl, g, hg, hgγ⟩ := ((((hT.prodMk_nhds hx).eventually
    (eventually_exists_cylinder hv hT₀ hdom hxT))).and hnull).exists
  obtain ⟨F, hF, hF0, hF1⟩ := hcyl (by
    simp only
    rw [flowOf_eq_of_isMIntegralCurve hv (hγ i), (hper i).neg.eq])
  -- Rescale the loop of `γ i` to the period `T₀`.
  have hS : T i / |T i / T₀| = T₀ := by
    rw [abs_of_pos (div_pos (hpos i) hT₀), div_div_cancel₀ (hpos i).ne']
  have h₁ := hg.exists_addCircle_comp_mul (hpos i).ne' (div_pos (hpos i) hT₀).ne'
  rw [hS] at h₁
  obtain ⟨g₁, hg₁, hg₁γ⟩ := h₁
  have hhom : g₀.Homotopic g₁ := ContinuousMap.homotopic_of_forall_apply_zero_eq_apply_one F hF
    (fun θ ↦ by rw [AddCircle.ofUnitInterval_apply, hg₀, hF0])
    (fun θ ↦ by
      rw [AddCircle.ofUnitInterval_apply, hg₁γ, hgγ, hF1, flowOf_eq_of_isMIntegralCurve hv (hγ i)]
      congr 1
      field_simp)
  obtain ⟨c, hc⟩ := hg₁
  exact ⟨g₀, ⟨c, hhom.trans hc⟩, hg₀⟩

end TauCeti
