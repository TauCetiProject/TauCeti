/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.IntervalChart
public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Maps tangent to the suspension vector field of a mapping torus

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold and
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its smooth mapping torus, with suspension flow
`[t, x] ↦ [t + s, x]` and vector field `T = ∂_t`. The line field `ℝ T` is integrable, and its
leaves are the orbits of the suspension flow: in an interval chart `[t, x] ↦ (t, x)`, the field `T`
is the coordinate field `∂_t`, so the curves tangent to it keep their fibre coordinate `x`.

This file proves the global form of that statement. Let `v : C → Y_φ` be a differentiable map from
a preconnected manifold `C`, possibly with boundary or corners, whose differential takes values in
the line `ℝ T` at every point. In an interval chart the fibre coordinate of `v` has zero
differential, so it is locally constant; hence `v` is locally inside one orbit of the suspension
flow. Since these orbits partition `Y_φ` and `C` is preconnected, `v` lies inside a single orbit
(`TauCeti.SmoothMappingTorus.range_subset_orbit_flow_of_mfderiv_mem_span`).

No compactness of `M` or of `C` is needed, and the orbit may be closed or not. Applied to the
mapping torus component of a map into `(ℝ / ℤ) × Y_φ` whose tangent images lie in the horizontal
plane `span(∂_s, T)`, this shows that a connected horizontal curve lies in a single product
`(ℝ / ℤ) × γ` of the circle with one orbit `γ` of the suspension flow.

When `C` is compact and boundaryless, the orbit is closed as soon as the differential of `v`
vanishes nowhere. On an orbit `{[τ, x]}` through a point `x` that is not periodic for `φ`, the
time `τ` is unique, and it depends continuously on the source point, since nearby points of `v`
differ by small flow times. A continuous function on a compact space attains its maximum, where,
read in an interval chart, it has zero differential by Fermat's theorem; there, `v` has zero
differential as well (`TauCeti.SmoothMappingTorus.exists_mfderiv_eq_zero_of_minimalPeriod_eq_zero`).

## Main results

* `TauCeti.SmoothMappingTorus.eventually_exists_abs_lt_flow_eq_of_mfderiv_mem_span`: near each
  point, a map tangent to `T` moves its value at that point by arbitrarily small flow times.
* `TauCeti.SmoothMappingTorus.eventually_mem_orbit_flow_of_mfderiv_mem_span`: near each point,
  a map tangent to `T` stays in the orbit of its value at that point.
* `TauCeti.SmoothMappingTorus.range_subset_orbit_flow_of_mfderiv_mem_span`: a map from a
  preconnected manifold tangent to `T` lies in a single orbit of the suspension flow.
* `TauCeti.SmoothMappingTorus.minimalPeriod_pos_of_mfderiv_ne_zero`: a map from a compact
  connected boundaryless manifold tangent to `T`, with nowhere vanishing differential, lies in a
  closed orbit: the fibre coordinates of its values are periodic points of `φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 19 (integral manifolds of a distribution and the
  leaves of a foliation).
-/

public section

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' 1 C] {v : C → SmoothMappingTorus φ}

/-- **Maps tangent to `T` locally move by small flow times.** Let `v` be a differentiable map into
the mapping torus whose differential takes values in the line spanned by the vector field `T = ∂_t`.
Then for every `ε > 0`, every point `c₀` has a neighbourhood whose points `c` satisfy
`v c = flow s (v c₀)` for some time `s` with `|s| < ε`. -/
theorem eventually_exists_abs_lt_flow_eq_of_mfderiv_mem_span
    (hv : MDifferentiable I' (𝓘(ℝ).prod I) v)
    (hT : ∀ c (w : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod I) v c w ∈ ℝ ∙ timeVectorField φ (v c))
    (c₀ : C) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ c in 𝓝 c₀, ∃ s, |s| < ε ∧ flow φ s (v c₀) = v c := by
  obtain ⟨⟨t₀, x₀⟩, h₀⟩ := uncurry_mk_surjective φ (v c₀)
  have : Nonempty M := ⟨x₀⟩
  -- The half-width `δ` of the interval chart, small enough for the chart and for `ε`.
  set δ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) one_half_pos
  have hδε : 2 * δ ≤ ε := by linarith [min_le_left (ε / 2) (1 / 2)]
  have hab : t₀ + δ ≤ t₀ - δ + 1 := by linarith [min_le_right (ε / 2) (1 / 2)]
  -- The interval chart `[t, x] ↦ (t, x)` over `(t₀ - δ, t₀ + δ)`, around `v c₀`.
  set e := intervalChart φ (t₀ - δ) (t₀ + δ) hab
  have hsrc : v c₀ ∈ e.source := by
    rw [intervalChart_source, ← h₀]
    exact ⟨t₀, ⟨by linarith, by linarith⟩, (proj_mk φ t₀ x₀).symm⟩
  set U := v ⁻¹' e.source
  have hU : IsOpen U := hv.continuous.isOpen_preimage _ e.open_source
  -- The lift `w = e ∘ v` of `v` to `ℝ × M` over `U`.
  set w : C → ℝ × M := fun c ↦ e (v c)
  have hw : ∀ c ∈ U, MDifferentiableAt I' (𝓘(ℝ).prod I) w c := fun c hc ↦
    (e.mdifferentiableAt (by simp) hc).comp c (hv c)
  have hvw : ∀ c ∈ U, uncurry (mk φ) (w c) = v c := fun c hc ↦ mk_intervalChart φ hab hc
  -- The fibre coordinate of `w` has zero differential on `U`.
  have hzero : ∀ c ∈ U, mfderiv I' I (Prod.snd ∘ w) c = 0 := by
    intro c hc
    have hq := (isLocalDiffeomorph_uncurry_mk φ (w c)).isInvertible_mfderiv (by simp)
    have hqd : MDifferentiableAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (w c) :=
      (isLocalDiffeomorph_uncurry_mk φ (w c)).mdifferentiableAt (by simp)
    -- The chain rule for `v = q ∘ w` near `c`, where `q` is the quotient map.
    have hvd : HasMFDerivAt I' (𝓘(ℝ).prod I) v c
        ((mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (w c)).comp
          (mfderiv I' (𝓘(ℝ).prod I) w c)) :=
      (hqd.hasMFDerivAt.comp c (hw c hc).hasMFDerivAt).congr_of_eventuallyEq_abuse
        (Filter.eventually_of_mem (hU.mem_nhds hc) fun c' hc' ↦ (hvw c' hc').symm)
    ext1 ξ
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hT c ξ)
    -- The lift of `v` has differential `a • ∂_t`, because the differential of the quotient map
    -- sends `∂_t` to `T` and is injective.
    have hlift : mfderiv I' (𝓘(ℝ).prod I) w c ξ =
        a • (Manifold.tangentSpaceProdEquiv (w c)).symm ((1 : ℝ), 0) := by
      have hTw : timeVectorField φ (v c) = mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ))
          (w c) ((Manifold.tangentSpaceProdEquiv (w c)).symm ((1 : ℝ), 0)) := by
        rw [← hvw c hc]
        exact timeVectorField_mk φ (w c).1 (w c).2
      refine hq.injective ?_
      rw [map_smul, ← hTw, ← ContinuousLinearMap.comp_apply, ← hvd.mfderiv]
      exact ha.symm
    rw [mfderiv_comp c mdifferentiableAt_snd (hw c hc), ContinuousLinearMap.comp_apply, hlift,
      mfderiv_snd]
    rw [zero_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
    -- The second component of `a • (1, 0)` is `a • 0 = 0`.
    exact smul_zero (A := TangentSpace I (w c).2) a
  have hconst := MDifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero
    (f := Prod.snd ∘ w)
    (fun c hc ↦ (mdifferentiableAt_snd.comp c (hw c hc)).mdifferentiableWithinAt) hU hzero hsrc
  -- Near `c₀`, `v c = [t, x]` for the fibre coordinate `x` of `v c₀`, so the suspension flow
  -- moves `v c₀` to `v c` in the time `t - t₀`, of absolute value less than `2 δ`.
  filter_upwards [hconst, hU.mem_nhds hsrc] with c hc hcU
  rw [Function.comp_apply, Function.comp_apply] at hc
  have hmem : ∀ c' ∈ U, (w c').1 ∈ Ioo (t₀ - δ) (t₀ + δ) := fun c' hc' ↦ by
    have := e.map_source hc'
    rw [intervalChart_target] at this
    exact this.1
  refine ⟨(w c).1 - (w c₀).1, ?_, ?_⟩
  · have h₁ := hmem c hcU
    have h₂ := hmem c₀ hsrc
    rw [abs_lt]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  rw [← hvw c₀ hsrc, ← hvw c hcU, uncurry_apply_pair, uncurry_apply_pair, flow_mk, hc,
    add_sub_cancel]

/-- **Maps tangent to `T` locally stay in one orbit.** Let `v` be a differentiable map into the
mapping torus whose differential takes values in the line spanned by the vector field `T = ∂_t`.
Then every point `c₀` has a neighbourhood that `v` maps into the orbit of `v c₀` under the
suspension flow. -/
theorem eventually_mem_orbit_flow_of_mfderiv_mem_span
    (hv : MDifferentiable I' (𝓘(ℝ).prod I) v)
    (hT : ∀ c (w : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod I) v c w ∈ ℝ ∙ timeVectorField φ (v c))
    (c₀ : C) : ∀ᶠ c in 𝓝 c₀, v c ∈ (flow φ).orbit (v c₀) :=
  (eventually_exists_abs_lt_flow_eq_of_mfderiv_mem_span hv hT c₀ one_pos).mono
    fun _ ⟨s, _, hs⟩ ↦ (flow φ).mem_orbit_iff.2 ⟨s, hs⟩

/-- **Maps tangent to `T` lie in one orbit.** Let `v` be a differentiable map from a preconnected
manifold into the mapping torus whose differential takes values in the line spanned by the vector
field `T = ∂_t`. Then the image of `v` lies in a single orbit of the suspension flow, the orbit
of any of its values. -/
theorem range_subset_orbit_flow_of_mfderiv_mem_span [PreconnectedSpace C]
    (hv : MDifferentiable I' (𝓘(ℝ).prod I) v)
    (hT : ∀ c (w : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod I) v c w ∈ ℝ ∙ timeVectorField φ (v c))
    (c : C) : range v ⊆ (flow φ).orbit (v c) := by
  -- `Flow.orbit` is the orbit of the additive action of the flow, so the orbits of that action
  -- partition the mapping torus.
  let := (flow φ).toAddAction
  -- The orbit of `v c'` is locally constant in `c'`, since the orbits partition `Y_φ`.
  have hloc : IsLocallyConstant fun c' ↦ (flow φ).orbit (v c') := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun c₀ ↦ ?_
    filter_upwards [eventually_mem_orbit_flow_of_mfderiv_mem_span hv hT c₀] with c' hc'
    exact AddAction.orbit_eq_iff.2 hc'
  rintro _ ⟨c', rfl⟩
  rw [hloc.apply_eq_of_preconnectedSpace c c']
  exact (flow φ).mem_orbit_self (v c')

/-- **A compact curve tangent to `T` along an orbit that is not closed has a critical point.** Let
`v` be a differentiable map from a nonempty compact connected boundaryless manifold into the mapping
torus whose differential takes values in the line spanned by `T = ∂_t`, and let `[t, x]` be one of
its values. If `x` is not a periodic point of `φ`, then the differential of `v` vanishes
somewhere. -/
theorem exists_mfderiv_eq_zero_of_minimalPeriod_eq_zero [I'.Boundaryless] [CompactSpace C]
    [PreconnectedSpace C] (hv : MDifferentiable I' (𝓘(ℝ).prod I) v)
    (hT : ∀ c (w : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod I) v c w ∈ ℝ ∙ timeVectorField φ (v c))
    {c : C} {t : ℝ} {x : M} (hc : v c = mk φ t x) (hx : minimalPeriod φ x = 0) :
    ∃ c', mfderiv I' (𝓘(ℝ).prod I) v c' = 0 := by
  have : Nonempty M := ⟨x⟩
  have : Nonempty C := ⟨c⟩
  -- Since `x` is not periodic, the time `τ` with `[τ, x] = v c'` is unique.
  have huniq : ∀ a b : ℝ, mk φ a x = mk φ b x → a = b := fun a b h ↦ by
    rwa [mk_eq_mk_iff_sub_mem_zmultiples, hx, Nat.cast_zero, AddSubgroup.zmultiples_zero_eq_bot,
      AddSubgroup.mem_bot, sub_eq_zero] at h
  have hex : ∀ c', ∃ τ : ℝ, v c' = mk φ τ x := fun c' ↦ by
    obtain ⟨s, hs⟩ := (flow φ).mem_orbit_iff.1
      (range_subset_orbit_flow_of_mfderiv_mem_span hv hT c ⟨c', rfl⟩)
    exact ⟨t + s, by rw [← hs, hc, flow_mk]⟩
  choose τ hτ using hex
  -- The time `τ` is continuous, because nearby points of `v` differ by small flow times.
  have hτc : Continuous τ := by
    refine continuous_iff_continuousAt.2 fun c₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    filter_upwards [eventually_exists_abs_lt_flow_eq_of_mfderiv_mem_span hv hT c₀ hε] with c'
      ⟨s, hs, hflow⟩
    rw [hτ c₀, hτ c', flow_mk] at hflow
    rwa [Real.dist_eq, ← huniq _ _ hflow, add_sub_cancel_left]
  -- The time `τ` attains its maximum at some `c₁`.
  obtain ⟨c₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hτc.continuousOn
  -- Near `c₁`, `τ` is the real coordinate of `v` in an interval chart, so it is differentiable.
  have hab : τ c₁ + 1 / 2 ≤ τ c₁ - 1 / 2 + 1 := by linarith
  set e := intervalChart φ (τ c₁ - 1 / 2) (τ c₁ + 1 / 2) hab
  have hnear : ∀ᶠ c' in 𝓝 c₁, τ c' ∈ Ioo (τ c₁ - 1 / 2) (τ c₁ + 1 / 2) :=
    hτc.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hsrc : v c₁ ∈ e.source := by
    rw [intervalChart_source, hτ c₁]
    exact ⟨τ c₁, ⟨by linarith, by linarith⟩, (proj_mk φ _ x).symm⟩
  have heq : τ =ᶠ[𝓝 c₁] Prod.fst ∘ e ∘ v := by
    filter_upwards [hnear] with c' hc'
    rw [Function.comp_apply, Function.comp_apply, hτ c', intervalChart_mk φ hab hc']
  have hτd : MDifferentiableAt I' 𝓘(ℝ) τ c₁ :=
    (mdifferentiableAt_fst.comp c₁ ((e.mdifferentiableAt (by simp) hsrc).comp c₁
      (hv c₁))).congr_of_eventuallyEq heq
  -- By Fermat's theorem, `τ` has zero differential at its maximum.
  have hτ0 : mfderiv I' 𝓘(ℝ) τ c₁ = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero.1
      ((hmax.isLocalMax univ_mem).mem_criticalPoints (I := I'))
  -- Since `v c' = [τ c', x]`, the chain rule gives `dv = 0` at `c₁`.
  have hpair := (hτ0 ▸ hτd.hasMFDerivAt).prodMk (hasMFDerivAt_const (I := I') (I' := I) x c₁)
  have hq : MDifferentiableAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (τ c₁, x) :=
    (isLocalDiffeomorph_uncurry_mk φ (τ c₁, x)).mdifferentiableAt (by simp)
  have hv' : v = uncurry (mk φ) ∘ fun c' ↦ (τ c', x) := funext hτ
  refine ⟨c₁, ?_⟩
  rw [hv', (hq.hasMFDerivAt.comp c₁ hpair).mfderiv]
  -- The derivative of `(τ, x)` at `c₁` is `(0, 0)`, which the derivative of `q` sends to `0`.
  ext w
  exact map_zero (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (τ c₁, x))

/-- **Compact immersed curves tangent to `T` lie on closed orbits.** Let `v` be a differentiable
map from a nonempty compact connected boundaryless manifold into the mapping torus whose
differential takes values in the line spanned by `T = ∂_t` and vanishes nowhere. Then for every
value `[t, x]` of `v`, the point `x` is periodic for `φ`: its least period is positive. So the
image of `v` lies in a closed orbit of the suspension flow. -/
theorem minimalPeriod_pos_of_mfderiv_ne_zero [I'.Boundaryless] [CompactSpace C]
    [PreconnectedSpace C] (hv : MDifferentiable I' (𝓘(ℝ).prod I) v)
    (hT : ∀ c (w : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod I) v c w ∈ ℝ ∙ timeVectorField φ (v c))
    (hne : ∀ c, mfderiv I' (𝓘(ℝ).prod I) v c ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : v c = mk φ t x) : 0 < minimalPeriod φ x := by
  refine Nat.pos_of_ne_zero fun hx ↦ ?_
  obtain ⟨c', hc'⟩ := exists_mfderiv_eq_zero_of_minimalPeriod_eq_zero hv hT hc hx
  exact hne c' hc'

end SmoothMappingTorus

end TauCeti
