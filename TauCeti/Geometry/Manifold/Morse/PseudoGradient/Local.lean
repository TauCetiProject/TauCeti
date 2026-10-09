/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Dynamics.Flow.Lyapunov

/-!
# Local stable sets of an adapted pseudo-gradient

Near a critical point `x` of `f`, an adapted pseudo-gradient `X` reads in a Morse chart as the
linear field `z ↦ (-wᵢ zᵢ)ᵢ`. Its flow is therefore the linear flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` for as
long as the orbit stays in the chart. On a small coordinate cube around `x`, this identifies the
stable set `W^s(x)` with the coordinate subspace `{zᵢ = 0 whenever wᵢ < 0}`.

One inclusion is read off the linear flow. The other is the energy barrier: an orbit starting in
the cube off the coordinate subspace reaches a level below `f x` before leaving the chart, and `f`
decreases along orbits, so the orbit cannot converge to `x`.

## Main declarations

* `TauCeti.MorseChart.linearFlow`: the linear flow in the coordinates of a Morse chart, with its
  flow law `TauCeti.MorseChart.linearFlow_add`.
* `TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm`: the flow of an adapted pseudo-gradient is
  the linear flow while the linear orbit stays in the chart.
* `TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm_of_forall_coord_eq_zero`: on the coordinate
  subspace of the positive weights, the flow is the contraction `z ↦ e^{-t} z`.
* `TauCeti.IsAdaptedPseudoGradient.mem_stableSet_of_forall_coord_eq_zero`: near `x`, the points
  of the coordinate subspace of the positive weights lie in `W^s(x)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_flow_lt_of_coord_ne_zero`: the energy barrier for the
  other points near `x`.
* `TauCeti.IsAdaptedPseudoGradient.exists_forall_mem_stableSet_iff`: on a small coordinate cube,
  `W^s(x)` is the coordinate subspace of the positive weights.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The linear flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` of the negative gradient of the quadratic normal form, in
the coordinates of a Morse chart. -/
noncomputable def linearFlow (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Fin (Module.finrank ℝ E) → ℝ :=
  fun i ↦ Real.exp (-(φ.weight i * t)) * z i

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The coordinates of the linear flow. -/
theorem linearFlow_apply (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) (i : Fin (Module.finrank ℝ E)) :
    φ.linearFlow t z i = Real.exp (-(φ.weight i * t)) * z i := by
  rw [linearFlow]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- At time zero the linear flow is the identity. -/
@[simp]
theorem linearFlow_zero (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow 0 z = z := by
  ext i
  simp [linearFlow_apply]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The flow law of the linear flow. -/
theorem linearFlow_add (s t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.linearFlow (s + t) z = φ.linearFlow s (φ.linearFlow t z) := by
  ext i
  simp only [linearFlow_apply, ← mul_assoc, ← Real.exp_add]
  ring_nf

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The linear flow solves the ODE `z' = (-wᵢ zᵢ)ᵢ`. -/
theorem hasDerivAt_linearFlow (z : Fin (Module.finrank ℝ E) → ℝ) (t : ℝ) :
    HasDerivAt (fun t ↦ φ.linearFlow t z) (fun i ↦ -(φ.weight i * φ.linearFlow t z i)) t := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  simp only [linearFlow_apply]
  convert ((((hasDerivAt_id' t).const_mul (φ.weight i)).neg.exp).mul_const (z i)) using 1
  simp only [Pi.neg_apply]
  ring

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A coordinate of positive weight decays like `e^{-t}`. -/
theorem linearFlow_of_weight_eq_one {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = 1) (t : ℝ)
    (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow t z i = Real.exp (-t) * z i := by
  rw [linearFlow_apply, hi, one_mul]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A coordinate of negative weight grows like `e^{t}`. -/
theorem linearFlow_of_weight_eq_neg_one {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = -1)
    (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) : φ.linearFlow t z i = Real.exp t * z i := by
  rw [linearFlow_apply, hi, neg_one_mul, neg_neg]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Coordinates of small sup norm are coordinates of points of the chart. -/
theorem exists_pos_forall_norm_lt_mem_target :
    ∃ r > 0, ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target := by
  have h0 : (0 : Fin (Module.finrank ℝ E) → ℝ) ∈ φ.coordL.symm ⁻¹' φ.toChart.target := by
    rw [mem_preimage, map_zero, ← φ.apply_self]
    exact φ.toChart.map_source φ.mem_source
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
    (φ.toChart.open_target.preimage φ.coordL.symm.continuous) 0 h0
  exact ⟨r, hr, fun z hz ↦ by simpa using hball (mem_ball_zero_iff.2 hz)⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- For times `t > -log 2`, a coordinate of positive weight grows at most by a factor `2`. -/
theorem norm_linearFlow_lt_of_weight_eq_one {r : ℝ} {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ < r / 2) {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i = 1) {t : ℝ}
    (ht : -Real.log 2 < t) : ‖φ.linearFlow t z i‖ < r := by
  have hexp : Real.exp (-t) < 2 := by
    rw [← Real.exp_log two_pos]
    exact Real.exp_lt_exp.2 (by linarith)
  rw [φ.linearFlow_of_weight_eq_one hi, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-t) * ‖z i‖ ≤ 2 * ‖z‖ := by
        gcongr
        · exact norm_le_pi_norm z i
    _ < r := by linarith

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A point of the chart is the point with its own coordinates. -/
theorem toChart_symm_coord_symm_coord {y : M} (hy : y ∈ φ.toChart.source) :
    φ.toChart.symm (φ.coord.symm (φ.coord (φ.toChart y))) = y := by
  rw [LinearEquiv.symm_apply_apply, φ.toChart.left_inv hy]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The critical point is the point with coordinates `0`. -/
theorem toChart_symm_coord_symm_zero : φ.toChart.symm (φ.coord.symm 0) = x := by
  rw [map_zero, ← φ.apply_self, φ.toChart.left_inv φ.mem_source]

end MorseChart

namespace IsAdaptedPseudoGradient

variable [CompactSpace M] [T2Space M]

/-- **In a Morse chart, the flow of an adapted pseudo-gradient is linear.** If `X` is the linear
field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and the linear orbit of `z` stays in the chart for
times in `(a, b)`, then for those times the flow of `X` from the point with coordinates `z` is the
point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem flow_toChart_symm (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : Fin (Module.finrank ℝ E) → ℝ} {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (hz : ∀ t ∈ Ioo a b, φ.coord.symm (φ.linearFlow t z) ∈ φ.toChart.target)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) := by
  set ℓ : ℝ → E := fun t ↦ φ.coord.symm (φ.linearFlow t z) with hℓ
  have hℓd (s : ℝ) :
      HasDerivAt ℓ (φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow s z i)) s := by
    simpa [ℓ, Function.comp_def] using
      φ.coordL.symm.hasFDerivAt.comp_hasDerivAt s (φ.hasDerivAt_linearFlow z s)
  have hψ1 : φ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas
  have hmd : φ.toChart.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨fun y hy ↦ (mdifferentiableAt_of_mem_maximalAtlas hψ1 hy).mdifferentiableWithinAt,
      fun w hw ↦ (mdifferentiableAt_symm_of_mem_maximalAtlas hψ1 hw).mdifferentiableWithinAt⟩
  have hcurve : IsMIntegralCurveOn (φ.toChart.symm ∘ ℓ) X (Ioo a b) := by
    intro s hs
    have hsT : ℓ s ∈ φ.toChart.target := hz s hs
    have hy : φ.toChart.symm (ℓ s) ∈ φ.toChart.source := φ.toChart.map_target hsT
    have hψy : φ.toChart (φ.toChart.symm (ℓ s)) = ℓ s := φ.toChart.right_inv hsT
    have h1 : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) ℓ s ((1 : ℝ →L[ℝ] ℝ).smulRight
        (φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow s z i))) :=
      hasMFDerivAt_iff_hasFDerivAt.2 (hℓd s).hasFDerivAt
    have h2 := (hmd.mdifferentiableAt_symm hsT).hasMFDerivAt
    refine ((h2.comp s h1).hasMFDerivWithinAt).congr_mfderiv ?_
    refine ContinuousLinearMap.ext_ring ?_
    have hXy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart (φ.toChart.symm (ℓ s))
        (X (φ.toChart.symm (ℓ s))) = φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow s z i) := by
      apply φ.coord.injective
      rw [hφ _ hy, hψy, LinearEquiv.apply_symm_apply]
      simp
    have hinv := congr($(hmd.symm_comp_deriv hy) (X (φ.toChart.symm (ℓ s))))
    rw [ContinuousLinearMap.comp_apply, hXy, hψy, ContinuousLinearMap.id_apply] at hinv
    -- Both sides are `smulRight 1` applied to `1`.
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (ℓ s)
        ((1 : ℝ) • φ.coord.symm fun i ↦ -(φ.weight i * φ.linearFlow s z i)) =
      (1 : ℝ) • X (φ.toChart.symm (ℓ s))
    rw [one_smul, one_smul]
    exact hinv
  have heq := hcurve.eqOn_maximalIntegralCurve (hX.contMDiff.of_le (by simp)) h0
    (by simp [ℓ] : (φ.toChart.symm ∘ ℓ) 0 = φ.toChart.symm (φ.coord.symm z))
  rw [hX.flow_apply]
  exact heq ht

variable (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
  {y : M} (hy : y ∈ φ.toChart.source)
include hX hφ hrT hy

omit hy in
/-- **On the stable subspace the flow contracts.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in
the Morse chart `φ`, and let `z` be small coordinates vanishing in every direction of negative
weight. Then for `t ≥ 0` the flow moves the point with coordinates `z` to the point with
coordinates `e^{-t} z`. -/
theorem flow_toChart_symm_of_forall_coord_eq_zero {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ < r / 2) (hu : ∀ i, φ.weight i < 0 → z i = 0) {t : ℝ} (ht : 0 ≤ t) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (Real.exp (-t) • z)) := by
  have hr : 0 < r := by linarith [norm_nonneg z]
  have hstay : ∀ s ∈ Ioo (-Real.log 2) (t + 1),
      φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target := fun s hs ↦
    hrT _ ((pi_norm_lt_iff hr).2 fun i ↦ by
      rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
      · rw [φ.linearFlow_of_weight_eq_neg_one hi, hu i (by rw [hi]; norm_num), mul_zero,
          norm_zero]
        exact hr
      · exact φ.norm_linearFlow_lt_of_weight_eq_one hz hi hs.1)
  have hlin : φ.linearFlow t z = Real.exp (-t) • z := by
    ext i
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · rw [φ.linearFlow_of_weight_eq_neg_one hi, Pi.smul_apply, hu i (by rw [hi]; norm_num),
        mul_zero, smul_zero]
    · rw [φ.linearFlow_of_weight_eq_one hi, Pi.smul_apply, smul_eq_mul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← hlin]
  exact hX.flow_toChart_symm φ hφ ⟨by linarith, by linarith⟩ hstay ⟨by linarith, by linarith⟩

/-- **Points of the stable subspace converge to the critical point.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and let the coordinates of `y` be small and vanish in every
direction of negative weight. Then the orbit of `y` converges to `x`. -/
theorem mem_stableSet_of_forall_coord_eq_zero (hyr : ‖φ.coord (φ.toChart y)‖ < r / 2)
    (hu : ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) : y ∈ hX.flow.stableSet x := by
  have hr : 0 < r := by linarith [norm_nonneg (φ.coord (φ.toChart y))]
  set z := φ.coord (φ.toChart y)
  have hcont : Tendsto (fun w ↦ φ.toChart.symm (φ.coord.symm w)) (𝓝 0)
      (𝓝 (φ.toChart.symm (φ.coord.symm 0))) := by
    refine (φ.toChart.continuousAt_symm (hrT 0 (by simpa using hr))).comp ?_
    exact φ.coordL.symm.continuous.continuousAt.congr (.of_forall φ.coordL_symm_apply)
  have hlin : Tendsto (fun t ↦ Real.exp (-t) • z) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.smul_const z
  have h := (hcont.comp hlin).congr' (f₂ := fun t ↦ hX.flow t y) <| by
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [comp_apply, ← hX.flow_toChart_symm_of_forall_coord_eq_zero φ hφ hrT hyr hu ht,
      φ.toChart_symm_coord_symm_coord hy]
  rw [φ.toChart_symm_coord_symm_zero] at h
  exact Flow.mem_stableSet.2 h

/-- **The energy barrier.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`,
and let the coordinates of `y` be small, with some coordinate of negative weight nonzero. Then the
orbit of `y` reaches a level below `f x`. -/
theorem exists_flow_lt_of_coord_ne_zero
    (hyr : ‖φ.coord (φ.toChart y)‖ < r / (4 * (Module.finrank ℝ E + 1)))
    {j : Fin (Module.finrank ℝ E)} (hj : φ.weight j < 0) (hjz : φ.coord (φ.toChart y) j ≠ 0) :
    ∃ T, f (hX.flow T y) < f x := by
  -- The coordinates of negative weight grow until the largest one has size `r / 2`, while the
  -- others stay small, so the quadratic normal form becomes negative.
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hr : 0 < r := by
    have h := (norm_nonneg _).trans_lt hyr
    rwa [div_pos_iff_of_pos_right (by positivity)] at h
  set ε := r / (4 * (n + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεr : 2 * ε ≤ r := by
    rw [hεdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hεn : n * ε ^ 2 < (r / 2) ^ 2 := by
    have h1 : ε * (n + 1) = r / 4 := by
      rw [hεdef]; field_simp
    nlinarith [sq_nonneg ε, mul_pos hε hε]
  set z := φ.coord (φ.toChart y)
  have hz2 : ‖z‖ < r / 2 := by linarith
  have hzi (i : Fin (Module.finrank ℝ E)) : |z i| < ε := by
    rw [← Real.norm_eq_abs]
    exact (pi_norm_lt_iff hε).1 hyr i
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun i ↦ φ.weight i < 0) (fun i ↦ |z i|) ⟨j, by simp [hj]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hmax
  set m := |z j₀|
  have hm0 : 0 < m := (abs_pos.2 hjz).trans_le (hmax j hj)
  have hwj₀ : φ.weight j₀ = -1 := (φ.weight_eq_neg_one_or_eq_one j₀).resolve_right
    (by intro h; rw [h] at hj₀; norm_num at hj₀)
  -- The time at which the largest coordinate of negative weight reaches `r / 2`.
  set T := Real.log (r / 2 / m)
  have hrm : 1 ≤ r / 2 / m := by rw [le_div_iff₀ hm0]; linarith [hzi j₀]
  have hT0 : 0 ≤ T := Real.log_nonneg hrm
  have hexpT : Real.exp T = r / 2 / m := Real.exp_log (by positivity)
  have hTb : T < Real.log (r / m) := Real.log_lt_log (by positivity) (by gcongr; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hstay : ∀ t ∈ Ioo (-Real.log 2) (Real.log (r / m)),
      φ.coord.symm (φ.linearFlow t z) ∈ φ.toChart.target := by
    intro t ht
    refine hrT _ ((pi_norm_lt_iff hr).2 fun i ↦ ?_)
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · rw [φ.linearFlow_of_weight_eq_neg_one hi, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hzm : |z i| ≤ m := hmax i (by rw [hi]; norm_num)
      calc Real.exp t * |z i| ≤ Real.exp t * m := by gcongr
        _ < Real.exp (Real.log (r / m)) * m := by gcongr; exact ht.2
        _ = r := by rw [Real.exp_log (by positivity)]; field_simp
    · exact φ.norm_linearFlow_lt_of_weight_eq_one hz2 hi ht.1
  have hTmem : T ∈ Ioo (-Real.log 2) (Real.log (r / m)) := ⟨by linarith, hTb⟩
  have hflow := hX.flow_toChart_symm φ hφ ⟨by linarith, by linarith⟩ hstay hTmem
  rw [φ.toChart_symm_coord_symm_coord hy] at hflow
  refine ⟨T, ?_⟩
  have hT' := hstay T hTmem
  rw [hflow, φ.eq_quadratic _ (φ.toChart.map_target hT'), φ.toChart.right_inv hT',
    LinearEquiv.apply_symm_apply]
  have hsum : ∑ i, φ.weight i * φ.linearFlow T z i ^ 2 ≤
      ∑ i, (ε ^ 2 + if i = j₀ then -(r / 2) ^ 2 - ε ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    split_ifs with hij
    · subst hij
      have hzm : z i ^ 2 = m ^ 2 := (sq_abs _).symm
      rw [hwj₀, φ.linearFlow_of_weight_eq_neg_one hwj₀, mul_pow, hexpT, hzm]
      field_simp
      ring_nf
      rfl
    · rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
      · rw [hi]; nlinarith [sq_nonneg (φ.linearFlow T z i)]
      · rw [hi, one_mul, φ.linearFlow_of_weight_eq_one hi, mul_pow, add_zero]
        have hexp1 : Real.exp (-T) ^ 2 ≤ 1 := by
          rw [← Real.exp_nat_mul, Real.exp_le_one_iff]; push_cast; linarith
        have hzi2 : z i ^ 2 ≤ ε ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hzi i).le 2
        nlinarith [sq_nonneg (z i), sq_nonneg (Real.exp (-T))]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, nsmul_eq_mul] at hsum
  nlinarith

omit hrT hy

/-- **The local stable set in a Morse chart.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in
the Morse chart `φ`. On a small coordinate cube around `x`, a point lies in the stable set
`W^s(x)` exactly when its coordinates of negative weight vanish. -/
theorem exists_forall_mem_stableSet_iff (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) :
    ∃ ε > 0, ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      (y ∈ hX.flow.stableSet x ↔ ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) := by
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  refine ⟨r / (4 * (Module.finrank ℝ E + 1)), by positivity, fun y hy hyε ↦ ⟨fun hs ↦ ?_, fun hu ↦
    hX.mem_stableSet_of_forall_coord_eq_zero φ hφ hrT hy (hyε.trans_le ?_) hu⟩⟩
  · by_contra hne
    push Not at hne
    obtain ⟨j, hj, hjz⟩ := hne
    obtain ⟨T, hT⟩ := hX.exists_flow_lt_of_coord_ne_zero φ hφ hrT hy hyε hj hjz
    exact hT.not_ge (Flow.le_of_mem_stableSet_of_antitone (Flow.isInvariant_stableSet _ _ T hs)
      hf.continuous.continuousAt (hX.antitone_flow hf _))
  · gcongr
    linarith

end IsAdaptedPseudoGradient

end TauCeti
