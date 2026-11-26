/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.PseudoGradient
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Dynamics.Flow.Stable
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The flow of a Morse–Bott pseudo-gradient and its local stable sets

Let `X` be a pseudo-gradient field adapted to `f` in the Morse–Bott sense
(`TauCeti.IsBottAdaptedPseudoGradient`) on a compact boundaryless manifold: near each critical
point `x` there is a Morse–Bott chart in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, with weights
`wᵢ ∈ {-1, 0, 1}`. Its flow (`TauCeti.IsBottAdaptedPseudoGradient.flow`) is therefore the linear
flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` for as long as an orbit stays in such a chart. This flow fixes the
coordinates of weight `0`, which run along the critical set, contracts those of weight `1` and
expands those of weight `-1`.

This file describes the local stable sets. Near `x`, the orbit of a point `y` whose coordinates of
negative weight vanish converges to the point `p(y)` of the critical set whose coordinates of
weight `0` are those of `y` and whose other coordinates vanish
(`TauCeti.IsBottAdaptedPseudoGradient.tendsto_flow_of_forall_coord_eq_zero`). If instead some
coordinate of negative weight of `y` is nonzero, the orbit reaches a level below `f x`
(`TauCeti.IsBottAdaptedPseudoGradient.exists_flow_lt_of_coord_ne_zero`). Since
`f` decreases along orbits and takes the value `f x` at every critical point near `x`, such an orbit
cannot converge to any of them. Hence, on a small coordinate cube, `y` lies in the stable set
`W^s(p)` of a critical point `p` exactly when the coordinates of negative weight of `y` vanish and
its coordinates of weight `0` are those of `p`
(`TauCeti.IsBottAdaptedPseudoGradient.exists_forall_mem_stableSet_iff`). So the points of the cube
whose orbits converge to a critical point of the chart form the coordinate slice of dimension
`n - λ` on which the `λ` coordinates of negative weight vanish, and the map sending such a point to
the limit of its orbit is the projection of that slice onto the critical set along the coordinates
of positive weight.

These estimates make every orbit converge, forward and backward in time, to a single critical point
(`TauCeti.IsBottAdaptedPseudoGradient.exists_tendsto_atTop`,
`TauCeti.IsBottAdaptedPseudoGradient.exists_tendsto_atBot`), although the critical points are not
isolated. The ω-limit set of an orbit consists of critical points at one level `c`. Once the orbit
comes close to one of them, it cannot cross the level `c`, so it lies on the stable slice of a
Morse–Bott chart and converges along the linear flow. These limits are the endpoint maps of the
trajectories between critical submanifolds of a Morse–Bott function.

A pseudo-gradient adapted to a Morse function is adapted in the Morse–Bott sense, with no weight
`0`; the corresponding statements for Morse charts, in
`TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic`, are the special case in which the
critical point `p` is the centre of the chart.

## Main declarations

* `TauCeti.IsBottAdaptedPseudoGradient.flow`: the flow of an adapted pseudo-gradient on a compact
  manifold, with `TauCeti.IsBottAdaptedPseudoGradient.neg_flow`: the flow of `-X` is the reversed
  flow.
* `TauCeti.IsBottAdaptedPseudoGradient.flow_toChart_symm_of_forall_mem_uIcc`: in a Morse–Bott
  chart the flow is the linear flow while the linear orbit stays in the chart.
* `TauCeti.IsBottAdaptedPseudoGradient.tendsto_flow_of_forall_coord_eq_zero`: points of the stable
  slice converge to their projection onto the critical set.
* `TauCeti.IsBottAdaptedPseudoGradient.apply_flow_lt_of_le_exp_mul`,
  `TauCeti.IsBottAdaptedPseudoGradient.exists_flow_lt_of_coord_ne_zero`: the energy barrier for the
  other points near the critical set, and
  `TauCeti.IsBottAdaptedPseudoGradient.forall_coord_eq_zero_of_forall_le_apply_flow`: so an orbit
  that never goes below `f x` starts on the stable slice.
* `TauCeti.IsBottAdaptedPseudoGradient.exists_forall_mem_stableSet_iff`: on a small coordinate cube,
  the stable set of a critical point `p` is the slice of the points with vanishing coordinates of
  negative weight and the coordinates of weight `0` of `p`.
* `TauCeti.IsBottAdaptedPseudoGradient.exists_tendsto_atTop`,
  `TauCeti.IsBottAdaptedPseudoGradient.exists_tendsto_atBot`: every orbit converges to a critical
  point forward, and backward, in time.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and their gradient flows).
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5
  (Morse–Bott functions).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 (the Morse case).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The cube of size `r / (4 (n + 1))` lies in the cube of size `r / 2`. -/
private theorem lt_half_of_lt_div {a r : ℝ} (hr : 0 < r) {n : ℕ} (h : a < r / (4 * (n + 1))) :
    a < r / 2 :=
  h.trans_le <| by
    gcongr
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

namespace IsBottAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

omit [FiniteDimensional ℝ E] in
/-- An adapted pseudo-gradient on a compact boundaryless manifold is complete. -/
theorem isCompleteVectorField (hX : IsBottAdaptedPseudoGradient f X) :
    IsCompleteVectorField X :=
  isCompleteVectorField_of_compactSpace (hX.contMDiff.of_le (by simp))

/-- The flow of a pseudo-gradient adapted to `f` in the Morse–Bott sense on a compact boundaryless
manifold. -/
noncomputable def flow (hX : IsBottAdaptedPseudoGradient f X) : Flow ℝ M :=
  globalFlow X (hX.contMDiff.of_le (by simp)) hX.isCompleteVectorField

variable (hX : IsBottAdaptedPseudoGradient f X)

/-- The flow at time `t` is the maximal integral curve of the pseudo-gradient at time `t`. -/
theorem flow_apply (t : ℝ) (y : M) : hX.flow t y = maximalIntegralCurve X y t := by
  rw [flow, globalFlow_apply]

/-- The orbits of the flow are integral curves of the pseudo-gradient. -/
theorem isMIntegralCurve_flow (y : M) : IsMIntegralCurve (fun t ↦ hX.flow t y) X :=
  isMIntegralCurve_globalFlow _ hX.isCompleteVectorField y

/-- `f` is antitone along every orbit of the flow. -/
theorem antitone_flow (y : M) : Antitone fun t ↦ f (hX.flow t y) :=
  hX.antitone_comp (hX.isMIntegralCurve_flow y)

/-- Critical points of `f` are rest points of the flow. -/
theorem flow_apply_of_mfderiv_eq_zero {p : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (t : ℝ) :
    hX.flow t p = p :=
  globalFlow_eq_of_isMIntegralCurve _ hX.isCompleteVectorField
    (isMIntegralCurve_const (hX.eq_zero_of_mfderiv_eq_zero hp)) t

/-- A point along whose orbit `f` is constant is a critical point of `f`. -/
theorem mfderiv_eq_zero_of_forall_eq {z : M}
    (hz : ∀ t, f (hX.flow t z) = f z) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 := by
  by_contra hcrit
  -- `f` is constant along the orbit, so `df(X)` vanishes where the orbit starts.
  have h := (hX.isMIntegralCurve_flow z).isMIntegralCurveAt 0
    |>.mfderiv_apply_eq_zero_of_eventuallyEq_const (hX.mdifferentiable _) (.of_forall hz)
  rw [Flow.map_zero_apply] at h
  exact (hX.mvfderiv_apply_lt_zero z hcrit).ne h

/-- The flow of `-X`, adapted to `-f`, is the flow of `X` run backwards. -/
theorem neg_flow : hX.neg.flow = hX.flow.reverse := by
  ext t y
  have h := globalFlow_eq_of_isMIntegralCurve (hX.neg.contMDiff.of_le (by simp))
    hX.neg.isCompleteVectorField (hX.isMIntegralCurve_flow y).comp_neg t
  simp only [neg_zero, Flow.map_zero_apply] at h
  rw [Flow.reverse_apply, ← h, hX.neg.flow_apply, globalFlow_apply]

/-- **In a Morse–Bott chart, the flow of an adapted pseudo-gradient is linear.** If `X` is the
linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart `φ`, and the linear orbit of `z` stays in the
chart for times in `(a, b)`, then for those times the flow of `X` from the point with coordinates
`z` is the point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem flow_toChart_symm (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : Fin (Module.finrank ℝ E) → ℝ} {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (hz : ∀ t ∈ Ioo a b, φ.coord.symm (φ.linearFlow t z) ∈ φ.toChart.target)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) := by
  have heq := (φ.isMIntegralCurveOn_toChart_symm_linearFlow hφ hz).eqOn_maximalIntegralCurve
    (hX.contMDiff.of_le (by simp)) h0 (by simp :
      φ.toChart.symm (φ.coord.symm (φ.linearFlow 0 z)) = φ.toChart.symm (φ.coord.symm z))
  rw [hX.flow_apply]
  exact heq ht

/-- **In a Morse–Bott chart, the flow of an adapted pseudo-gradient is linear up to time `t`.** If
`X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart `φ`, and the linear orbit of `z`
stays in the chart for all times between `0` and `t`, then at time `t` the flow of `X` from the
point with coordinates `z` is the point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem flow_toChart_symm_of_forall_mem_uIcc (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : Fin (Module.finrank ℝ E) → ℝ} {t : ℝ}
    (hz : ∀ s ∈ uIcc 0 t, φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) := by
  -- The times at which the linear orbit lies in the chart form an open set containing the
  -- endpoints of `[min 0 t, max 0 t]`, so it contains an open interval around each endpoint, and
  -- hence an open interval around the whole closed interval.
  set U := {s : ℝ | φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target}
  have hU : IsOpen U :=
    φ.toChart.open_target.preimage <|
      φ.coord.symm.toLinearMap.continuous_of_finiteDimensional.comp <|
        continuous_iff_continuousAt.2 fun s ↦ (φ.hasDerivAt_linearFlow z s).continuousAt
  have hIcc : Icc (min 0 t) (max 0 t) ⊆ U := fun s hs ↦ hz s (by rwa [← Icc_min_max])
  obtain ⟨a, b₁, ⟨ha, hb₁⟩, hab₁⟩ := mem_nhds_iff_exists_Ioo_subset.1 <|
    hU.mem_nhds (hIcc ⟨le_rfl, min_le_max⟩)
  obtain ⟨a₂, b, ⟨ha₂, hb⟩, hab₂⟩ := mem_nhds_iff_exists_Ioo_subset.1 <|
    hU.mem_nhds (hIcc ⟨min_le_max, le_rfl⟩)
  have hab : Ioo a b ⊆ U := fun s hs ↦ by
    rcases lt_or_ge s (min 0 t) with hsm | hsm
    · exact hab₁ ⟨hs.1, hsm.trans hb₁⟩
    rcases le_or_gt s (max 0 t) with hsM | hsM
    · exact hIcc ⟨hsm, hsM⟩
    · exact hab₂ ⟨ha₂.trans hsM, hs.2⟩
  have hmem {s : ℝ} (hs : s ∈ uIcc 0 t) : s ∈ Ioo a b := by
    rw [← Icc_min_max] at hs
    exact ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  exact hX.flow_toChart_symm φ hφ (hmem left_mem_uIcc) hab (hmem right_mem_uIcc)

/-- **On the stable slice the flow is the linear flow.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart `φ`, and let `z` be small coordinates vanishing in every
direction of negative weight. Then for `t ≥ 0` the flow moves the point with coordinates `z` to the
point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem flow_toChart_symm_of_forall_coord_eq_zero (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ < r / 2) (hu : ∀ i, φ.weight i < 0 → z i = 0) {t : ℝ} (ht : 0 ≤ t) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) := by
  have hr : 0 < r := by linarith [norm_nonneg z]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine hX.flow_toChart_symm φ hφ (a := -Real.log 2) (b := t + 1) ⟨by linarith, by linarith⟩
    (fun s hs ↦ hrT _ (φ.norm_linearFlow_lt hz hs.1 fun i hi ↦ ?_)) ⟨by linarith, by linarith⟩
  rw [hu i hi, abs_zero, mul_zero]
  exact hr

/-- **Points of the stable slice converge to the critical set.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart `φ`, and let the coordinates of `y` be small and vanish in
every direction of negative weight. Then the orbit of `y` converges to the point of the chart whose
coordinates of weight `0` are those of `y` and whose other coordinates vanish, a critical point of
`f` by `TauCeti.MorseBottChart.mfderiv_toChart_symm_coord_symm_eq_zero`. -/
theorem tendsto_flow_of_forall_coord_eq_zero (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source) (hyr : ‖φ.coord (φ.toChart y)‖ < r / 2)
    (hu : ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) :
    Tendsto (fun t ↦ hX.flow t y) atTop (𝓝 (φ.toChart.symm (φ.coord.symm
      fun i ↦ if φ.weight i = 0 then φ.coord (φ.toChart y) i else 0))) := by
  set z := φ.coord (φ.toChart y)
  set w : Fin (Module.finrank ℝ E) → ℝ := fun i ↦ if φ.weight i = 0 then z i else 0
  have hr : 0 < r := by linarith [norm_nonneg z]
  have hw : ‖w‖ < r := (φ.norm_ite_weight_eq_zero_le z).trans_lt (by linarith)
  have hcont : ContinuousAt (fun v ↦ φ.toChart.symm (φ.coord.symm v)) w :=
    (φ.toChart.continuousAt_symm (hrT w hw)).comp
      φ.coord.symm.toLinearMap.continuous_of_finiteDimensional.continuousAt
  refine (hcont.tendsto.comp (φ.tendsto_linearFlow_atTop hu)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [comp_apply, ← hX.flow_toChart_symm_of_forall_coord_eq_zero φ hφ hrT hyr hu ht,
    φ.toChart_symm_coord_symm_coord hy]

/-- **The flow is linear until a coordinate of negative weight grows.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart `φ`, and let the coordinates of `y` have norm less than
`r / 2`. At a time `t ≥ 0` by which no coordinate of negative weight of the linear orbit has grown
to size `r`, the linear orbit has norm less than `r`, and the orbit of `y` is the linear orbit read
on the manifold. -/
theorem norm_linearFlow_lt_and_flow_eq_of_exp_mul_lt (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source) (hyr : ‖φ.coord (φ.toChart y)‖ < r / 2) {t : ℝ}
    (ht : 0 ≤ t) (hsmall : ∀ i, φ.weight i < 0 → Real.exp t * |φ.coord (φ.toChart y) i| < r) :
    ‖φ.linearFlow t (φ.coord (φ.toChart y))‖ < r ∧
      hX.flow t y = φ.toChart.symm (φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart y)))) := by
  set z := φ.coord (φ.toChart y)
  have hnorm : ∀ s ∈ uIcc 0 t, ‖φ.linearFlow s z‖ < r := fun s hs ↦ by
    rw [uIcc_of_le ht] at hs
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    exact φ.norm_linearFlow_lt hyr (by linarith [hs.1]) fun i hi ↦
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hs.2) (abs_nonneg _)).trans_lt (hsmall i hi)
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ fun s hs ↦ hrT _ (hnorm s hs)
  rw [φ.toChart_symm_coord_symm_coord hy] at hflow
  exact ⟨hnorm t right_mem_uIcc, hflow⟩

/-- **The energy barrier, with a time bound.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the
Morse–Bott chart `φ`, and let the coordinates of `y` be small compared with `r`. At every time `t`
by which a coordinate of negative weight of the linear orbit has grown to size `r`, the orbit of `y`
is below the level `f x`. -/
theorem apply_flow_lt_of_le_exp_mul (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source)
    (hyr : ‖φ.coord (φ.toChart y)‖ < r / (4 * (Module.finrank ℝ E + 1)))
    {t : ℝ} {j : Fin (Module.finrank ℝ E)} (hj : φ.weight j < 0)
    (hjr : r ≤ Real.exp t * |φ.coord (φ.toChart y) j|) :
    f (hX.flow t y) < f x := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set z := φ.coord (φ.toChart y)
  have hr : 0 < r :=
    (div_pos_iff_of_pos_right (by positivity)).1 ((norm_nonneg _).trans_lt hyr)
  set ε := r / (4 * (n + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have h1 : ε * (n + 1) = r / 4 := by rw [hεdef]; field_simp
  have hεn : n * ε ^ 2 < (r / 2) ^ 2 := by nlinarith [sq_nonneg ε, mul_pos hε hε]
  have hz2 : ‖z‖ < r / 2 := by nlinarith
  have hzi (i : Fin (Module.finrank ℝ E)) : |z i| < ε := (pi_norm_lt_iff hε).1 hyr i
  -- The largest coordinate of negative weight reaches `r / 2` at a time `T ≤ t`, before which the
  -- orbit is the linear one, and there the quadratic normal form is negative.
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun i ↦ φ.weight i < 0) (fun i ↦ |z i|) ⟨j, by simp [hj]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hmax
  set m := |z j₀|
  have hm0 : 0 < m := (pos_of_mul_pos_right (hr.trans_le hjr) (Real.exp_pos t).le).trans_le
    (hmax j hj)
  have hwj₀ : φ.weight j₀ = -1 := by
    rcases φ.weight_eq_neg_one_or_eq_zero_or_eq_one j₀ with h | h | h
    · exact h
    all_goals rw [h] at hj₀; norm_num at hj₀
  set T := Real.log (r / 2 / m)
  have hT0 : 0 ≤ T := Real.log_nonneg (by rw [le_div_iff₀ hm0]; nlinarith [hzi j₀])
  have hexpT : Real.exp T = r / 2 / m := Real.exp_log (by positivity)
  have hTt : T ≤ t := Real.exp_le_exp.1 <| by
    rw [hexpT, div_le_iff₀ hm0]
    nlinarith [hmax j hj, Real.exp_pos t]
  obtain ⟨hnorm, hflow⟩ := hX.norm_linearFlow_lt_and_flow_eq_of_exp_mul_lt φ hφ hrT hy hz2 hT0
    fun i hi ↦
      calc Real.exp T * |z i| ≤ Real.exp T * m := by gcongr; exact hmax i hi
        _ = r / 2 := by rw [hexpT]; field_simp
        _ < r := half_lt_self hr
  have hT' := hrT _ hnorm
  have hfT : f (hX.flow T y) < f x := by
    rw [hflow, φ.eq_quadratic _ (φ.toChart.map_target hT'), φ.toChart.right_inv hT',
      LinearEquiv.apply_symm_apply]
    have hsum := φ.sum_weight_mul_linearFlow_sq_le (fun i ↦ (hzi i).le) hwj₀ hT0 (c := r / 2)
      (by rw [hexpT]; exact div_mul_cancel₀ _ hm0.ne')
    nlinarith
  exact (hX.antitone_flow y hTt).trans_lt hfT

/-- **The energy barrier.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart
`φ`, and let the coordinates of `y` be small, with some coordinate of negative weight nonzero. Then
the orbit of `y` reaches a level below `f x` at a positive time. -/
theorem exists_flow_lt_of_coord_ne_zero (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source)
    (hyr : ‖φ.coord (φ.toChart y)‖ < r / (4 * (Module.finrank ℝ E + 1)))
    {j : Fin (Module.finrank ℝ E)} (hj : φ.weight j < 0) (hjz : φ.coord (φ.toChart y) j ≠ 0) :
    ∃ T, 0 < T ∧ f (hX.flow T y) < f x := by
  -- The coordinate `j` of the linear orbit has grown to size `r` by the time `r / |z j|`.
  have hzj : 0 < |φ.coord (φ.toChart y) j| := abs_pos.2 hjz
  have hr : 0 < r := (div_pos_iff_of_pos_right (by positivity)).1 ((norm_nonneg _).trans_lt hyr)
  refine ⟨r / |φ.coord (φ.toChart y) j|, by positivity,
    hX.apply_flow_lt_of_le_exp_mul φ hφ hrT hy hyr hj ?_⟩
  calc r = r / |φ.coord (φ.toChart y) j| * |φ.coord (φ.toChart y) j| :=
        (div_mul_cancel₀ _ hzj.ne').symm
    _ ≤ Real.exp (r / |φ.coord (φ.toChart y) j|) * |φ.coord (φ.toChart y) j| := by
        gcongr
        linarith [Real.add_one_le_exp (r / |φ.coord (φ.toChart y) j|)]

/-- **An orbit above the critical level starts on the stable slice.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse–Bott chart `φ`, and let the coordinates of `y` be small. If the orbit
of `y` never goes below the level `f x`, then the coordinates of negative weight of `y` vanish. -/
theorem forall_coord_eq_zero_of_forall_le_apply_flow (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source)
    (hyr : ‖φ.coord (φ.toChart y)‖ < r / (4 * (Module.finrank ℝ E + 1)))
    (hle : ∀ T, f x ≤ f (hX.flow T y)) :
    ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0 := fun _ hi ↦ by_contra fun hz ↦
  let ⟨T, _, hT⟩ := hX.exists_flow_lt_of_coord_ne_zero φ hφ hrT hy hyr hi hz
  hT.not_ge (hle T)

/-- **The local stable sets in a Morse–Bott chart.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ`
in the Morse–Bott chart `φ`. On a small coordinate cube around `x`, a point `y` lies in the stable
set `W^s(p)` of a critical point `p` in the chart exactly when the coordinates of negative weight of
`y` vanish and its coordinates of weight `0` are those of `p`. -/
theorem exists_forall_mem_stableSet_iff (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∃ ε > 0, ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      ∀ p ∈ φ.toChart.source, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 →
        (y ∈ hX.flow.stableSet p ↔ (∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) ∧
          ∀ i, φ.weight i = 0 → φ.coord (φ.toChart y) i = φ.coord (φ.toChart p) i) := by
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  refine ⟨r / (4 * (Module.finrank ℝ E + 1)), by positivity, fun y hy hyε p hp hcrit ↦ ?_⟩
  have hyr : ‖φ.coord (φ.toChart y)‖ < r / 2 := lt_half_of_lt_div hr hyε
  -- The coordinates of nonzero weight of the critical point `p` vanish, so `p` is the projection of
  -- `y` onto the critical set as soon as their coordinates of weight `0` agree.
  have hp0 := (φ.mfderiv_eq_zero_iff hp).1 hcrit
  have hproj (h0 : ∀ i, φ.weight i = 0 → φ.coord (φ.toChart y) i = φ.coord (φ.toChart p) i) :
      (fun i ↦ if φ.weight i = 0 then φ.coord (φ.toChart y) i else 0) =
        φ.coord (φ.toChart p) := by
    funext i
    split_ifs with hi
    · exact h0 i hi
    · exact (hp0 i hi).symm
  constructor
  · intro hs
    -- An orbit converging to `p` never goes below the level `f p = f x`, so it does not cross the
    -- energy barrier: the coordinates of negative weight vanish.
    have hu := hX.forall_coord_eq_zero_of_forall_le_apply_flow φ hφ hrT hy hyε fun T ↦ by
      rw [← φ.apply_eq_of_mfderiv_eq_zero hp hcrit]
      exact Flow.le_of_mem_stableSet_of_antitone (Flow.isInvariant_stableSet _ _ T hs)
        (hX.mdifferentiable p).continuousAt (hX.antitone_flow _)
    -- The orbit then converges to the projection of `y`, which is therefore `p`.
    have hlim := tendsto_nhds_unique (hX.tendsto_flow_of_forall_coord_eq_zero φ hφ hrT hy hyr hu)
      (Flow.mem_stableSet.1 hs)
    have hw := (φ.norm_ite_weight_eq_zero_le _).trans_lt (hyr.trans (half_lt_self hr))
    have hcoord := congrArg (fun q ↦ φ.coord (φ.toChart q)) hlim
    simp only [φ.toChart.right_inv (hrT _ hw), LinearEquiv.apply_symm_apply] at hcoord
    refine ⟨hu, fun i hi ↦ ?_⟩
    simpa [hi] using congrFun hcoord i
  · rintro ⟨hu, h0⟩
    have hlim := hX.tendsto_flow_of_forall_coord_eq_zero φ hφ hrT hy hyr hu
    rw [hproj h0, φ.toChart_symm_coord_symm_coord hp] at hlim
    exact Flow.mem_stableSet.2 hlim

/-- **Every orbit converges forward in time to a critical point.** The critical points of `f` need
not be isolated. The ω-limit set of an orbit consists of critical points at a single level `c`; once
the orbit comes close to one of them, it lies on the stable slice of its Morse–Bott chart, since it
never goes below the level `c`, and it converges along the linear flow. -/
theorem exists_tendsto_atTop (y : M) :
    ∃ p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 ∧ Tendsto (fun t ↦ hX.flow t y) atTop (𝓝 p) := by
  set γ : ℝ → M := fun t ↦ hX.flow t y
  have hfc : Continuous f := hX.mdifferentiable.continuous
  -- A cluster point `p` of the orbit is a critical point, as `f` is constant along its orbit.
  obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (map γ atTop)
  have hp : MapClusterPt p atTop γ := mapClusterPt_def.2 hp
  have hpc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 := hX.mfderiv_eq_zero_of_forall_eq
    (Flow.apply_flow_eq_of_mapClusterPt_of_antitone (hX.antitone_flow y) hfc hp)
  -- The orbit enters a small cube of a Morse–Bott chart at `p` at some time `t₀`.
  obtain ⟨φ, hφ⟩ := hX.exists_morseBottChart p hpc
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  obtain ⟨t₀, ht₀, ht₀r⟩ := (hp.frequently (φ.eventually_mem_source_norm_coord_lt
    (ρ := r / (4 * (Module.finrank ℝ E + 1))) (by positivity))).exists
  -- It never goes below the level `f p`, the infimum of `f` along the orbit, so its coordinates of
  -- negative weight vanish there.
  have hu := hX.forall_coord_eq_zero_of_forall_le_apply_flow φ hφ hrT ht₀ ht₀r fun T ↦ by
    rw [← Flow.map_add]
    exact (Flow.isGLB_of_mapClusterPt_of_antitone (hX.antitone_flow y) hfc.continuousAt hp).1
      ⟨_, rfl⟩
  have hyr : ‖φ.coord (φ.toChart (γ t₀))‖ < r / 2 := lt_half_of_lt_div hr ht₀r
  have hw := (φ.norm_ite_weight_eq_zero_le _).trans_lt (hyr.trans (half_lt_self hr))
  -- From time `t₀` on, the orbit converges along the linear flow to a critical point.
  refine ⟨_, φ.mfderiv_toChart_symm_coord_symm_eq_zero (hrT _ hw) fun i hi ↦ by simp [hi],
    ((hX.tendsto_flow_of_forall_coord_eq_zero φ hφ hrT ht₀ hyr hu).comp
      (tendsto_atTop_add_const_right _ (-t₀) tendsto_id)).congr fun t ↦ ?_⟩
  simp only [comp_apply, id_eq, γ, ← Flow.map_add, neg_add_cancel_right]

/-- **Every orbit converges backward in time to a critical point**: apply
`TauCeti.IsBottAdaptedPseudoGradient.exists_tendsto_atTop` to the reversed pseudo-gradient `-X`,
adapted to `-f`, whose flow is the reversed flow. -/
theorem exists_tendsto_atBot (y : M) :
    ∃ p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 ∧ Tendsto (fun t ↦ hX.flow t y) atBot (𝓝 p) := by
  obtain ⟨p, hp, hlim⟩ := hX.neg.exists_tendsto_atTop y
  refine ⟨p, mfderiv_neg_eq_zero_iff.1 hp, ?_⟩
  rw [hX.neg_flow] at hlim
  simpa only [comp_def, Flow.reverse_apply, neg_neg] using hlim.comp tendsto_neg_atBot_atTop

/-- Every point lies in the stable set of a critical point. -/
theorem exists_mem_stableSet (y : M) :
    ∃ p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 ∧ y ∈ hX.flow.stableSet p :=
  let ⟨p, hp, hlim⟩ := hX.exists_tendsto_atTop y
  ⟨p, hp, Flow.mem_stableSet.2 hlim⟩

/-- Every point lies in the unstable set of a critical point. -/
theorem exists_mem_unstableSet (y : M) :
    ∃ p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 ∧ y ∈ hX.flow.unstableSet p :=
  let ⟨p, hp, hlim⟩ := hX.exists_tendsto_atBot y
  ⟨p, hp, Flow.mem_unstableSet.2 hlim⟩

end IsBottAdaptedPseudoGradient

end TauCeti
