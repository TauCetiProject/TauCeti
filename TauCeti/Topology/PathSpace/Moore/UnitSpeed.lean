/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop
import TauCeti.Analysis.Calculus.MetricVariation
import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Unit-speed Moore loops do not form a closed subspace

The duration of a Moore loop is continuous on the free Moore loop space `𝓛X`, but the loops
parametrized at unit speed, the ones whose variation on every parameter subinterval `[x, y]` of
`[0, duration]` is `y - x` (so that, in particular, their duration is their geometric length), do
not form a closed subspace of `𝓛X`, even in the flat torus. This file proves this with the loops

`γₙ(t) = i (1 - e^{2π i n t}) / (2π n) = (sin 2πnt, 1 - cos 2πnt) / (2πn)`

of duration `1` (`TauCeti.unitSpeedCircle`): each runs `n` times, at unit speed, around a circle
of radius `1 / (2πn)` through the origin. As `n → ∞` they converge uniformly to the constant loop
at the origin of duration `1`, which is not parametrized at unit speed: its unit-speed
representative is the constant loop of duration `0`. So a limit in `𝓛X` of unit-speed loops need
not be parametrized at unit speed, and constructions that require the subspace of unit-speed loops
to be closed in `𝓛X` are unavailable.

The flat torus is modelled as a quotient `ℂ ⧸ S`, with the quotient metric, by an additive
subgroup `S` whose nonzero elements all have norm at least some `δ > 0`; this covers the square
torus `ℂ ⧸ ℤ[i] = ℝ² ⧸ ℤ²`, with `δ = 1`, and the plane itself, with `S = ⊥`. Once its diameter
`1 / (πn)` is at most `δ / 2`, the projection `ℂ → ℂ ⧸ S` preserves the distances between the
points of `γₙ` (`QuotientAddGroup.dist_mk_eq_dist`), hence its variation
(`eVariationOn.comp_eq_of_edist_eq`). So the projected loops `TauCeti.unitSpeedCircleLoop S n`
still have unit speed on `[0, 1]`.

## Main definitions

* `TauCeti.unitSpeedCircle n`: the curve `t ↦ i (1 - e^{2π i n t}) / (2π n)` in `ℂ`.
* `TauCeti.unitSpeedCircleLoop S n`: its restriction to `[0, 1]`, as a free Moore loop of
  duration `1` in `ℂ ⧸ S`.

## Main results

* `TauCeti.hasUnitSpeedOn_unitSpeedCircle`: for `n ≠ 0`, `γₙ` has unit speed.
* `TauCeti.hasUnitSpeedOn_unitSpeedCircleLoop`: the loop `γₙ` in `ℂ ⧸ S` has unit speed on its
  parameter interval `[0, 1]` once its diameter is at most `δ / 2`.
* `TauCeti.tendsto_unitSpeedCircleLoop`: the loops `γₙ` converge in `𝓛(ℂ ⧸ S)` to the constant
  loop of duration `1`.
* `TauCeti.not_isClosed_setOf_hasUnitSpeedOn`: the free Moore loops in `ℂ ⧸ S` parametrized at
  unit speed do not form a closed subset of `𝓛(ℂ ⧸ S)`, and
  `TauCeti.not_isClosed_setOf_hasUnitSpeedOn_gaussianInt` is the case of the square flat torus
  `ℂ ⧸ ℤ[i]`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 4.5: its retraction of the Moore
  loops of bounded duration onto the unit-speed ones is not available on the Moore carrier, whose
  unit-speed loops are not closed.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti

/-! ### The curves -/

/-- The curve `γₙ(t) = i (1 - e^{2π i n t}) / (2π n)` in `ℂ`, that is
`(sin 2πnt, 1 - cos 2πnt) / (2πn)`: the circle of radius `r = 1 / (2πn)` centred at `r i`, at the
angle `2πnt - π / 2`. For `n ≠ 0` it runs around this circle at unit speed, starting at the origin
and returning to it at every integer time. -/
def unitSpeedCircle (n : ℕ) (t : ℝ) : ℂ :=
  circleMap (↑(2 * Real.pi * n)⁻¹ * I) (2 * Real.pi * n)⁻¹ (2 * Real.pi * n * t - Real.pi / 2)

theorem unitSpeedCircle_def (n : ℕ) (t : ℝ) :
    unitSpeedCircle n t = circleMap (↑(2 * Real.pi * n)⁻¹ * I) (2 * Real.pi * n)⁻¹
      (2 * Real.pi * n * t - Real.pi / 2) :=
  (rfl)

@[simp]
theorem unitSpeedCircle_zero (n : ℕ) : unitSpeedCircle n 0 = 0 := by
  rw [unitSpeedCircle, mul_zero, zero_sub, ← neg_div, circleMap_neg_pi_div_two, sub_self]

@[simp]
theorem unitSpeedCircle_one (n : ℕ) : unitSpeedCircle n 1 = 0 := by
  rw [← unitSpeedCircle_zero n, unitSpeedCircle, unitSpeedCircle,
    ← (periodic_circleMap _ _).nat_mul n (2 * Real.pi * n * 0 - Real.pi / 2)]
  congr 1
  ring

private theorem hasDerivAt_unitSpeedCircle (n : ℕ) (t : ℝ) :
    HasDerivAt (unitSpeedCircle n)
      ((2 * Real.pi * n) • (circleMap 0 (2 * Real.pi * n)⁻¹ (2 * Real.pi * n * t - Real.pi / 2) *
        I)) t := by
  have h := ((hasDerivAt_id t).const_mul (2 * Real.pi * n)).sub_const (Real.pi / 2)
  rw [mul_one] at h
  exact (hasDerivAt_circleMap _ _ _).scomp t h

/-- The curve `γₙ` is smooth. -/
theorem contDiff_unitSpeedCircle (n : ℕ) {k : WithTop ℕ∞} : ContDiff ℝ k (unitSpeedCircle n) :=
  (contDiff_circleMap _ _).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

@[fun_prop]
theorem continuous_unitSpeedCircle (n : ℕ) : Continuous (unitSpeedCircle n) :=
  (contDiff_unitSpeedCircle n (k := 0)).continuous

/-- For `n ≠ 0`, the velocity of `γₙ` has norm `1`. -/
theorem norm_deriv_unitSpeedCircle {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ‖deriv (unitSpeedCircle n) t‖ = 1 := by
  have hpos : 0 < 2 * Real.pi * n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  rw [(hasDerivAt_unitSpeedCircle n t).deriv, norm_smul, norm_mul (circleMap _ _ _),
    norm_circleMap_zero, norm_I, mul_one, Real.norm_of_nonneg hpos.le, abs_inv, abs_of_pos hpos,
    mul_inv_cancel₀ hpos.ne']

/-- Any two points of `γₙ` are at distance at most `1 / (π n)`, the diameter of its circle. -/
theorem dist_unitSpeedCircle_le (n : ℕ) (s t : ℝ) :
    dist (unitSpeedCircle n s) (unitSpeedCircle n t) ≤ 1 / (Real.pi * n) := by
  have hR : (0 : ℝ) ≤ (2 * Real.pi * n)⁻¹ := by positivity
  have hs := circleMap_mem_sphere (↑(2 * Real.pi * n)⁻¹ * I) hR (2 * Real.pi * n * s - Real.pi / 2)
  have ht := circleMap_mem_sphere (↑(2 * Real.pi * n)⁻¹ * I) hR (2 * Real.pi * n * t - Real.pi / 2)
  rw [Metric.mem_sphere] at hs ht
  calc dist (unitSpeedCircle n s) (unitSpeedCircle n t)
      ≤ dist (unitSpeedCircle n s) (↑(2 * Real.pi * n)⁻¹ * I) +
        dist (unitSpeedCircle n t) (↑(2 * Real.pi * n)⁻¹ * I) := dist_triangle_right _ _ _
    _ = 1 / (Real.pi * n) := by
        rw [unitSpeedCircle, unitSpeedCircle, hs, ht]
        ring

/-- `γₙ` stays within distance `1 / (π n)` of the origin. -/
theorem norm_unitSpeedCircle_le (n : ℕ) (t : ℝ) : ‖unitSpeedCircle n t‖ ≤ 1 / (Real.pi * n) := by
  simpa using dist_unitSpeedCircle_le n t 0

/-- The variation of `γₙ` on `[x, y]` is `y - x`. -/
theorem eVariationOn_unitSpeedCircle {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (hxy : x ≤ y) :
    eVariationOn (unitSpeedCircle n) (Icc x y) = ENNReal.ofReal (y - x) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have h1 : ∀ t ∈ Icc x y, ‖derivWithin (unitSpeedCircle n) (Icc x y) t‖ₑ = 1 := fun t ht ↦ by
    have hd := ((contDiff_unitSpeedCircle n (k := 1)).differentiable one_ne_zero t).hasDerivAt
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hxy t ht), ← ofReal_norm,
      norm_deriv_unitSpeedCircle hn, ENNReal.ofReal_one]
  rw [eVariationOn_eq_lintegral_enorm_derivWithin (contDiff_unitSpeedCircle n).contDiffOn,
    setLIntegral_congr_fun measurableSet_Icc h1, setLIntegral_one, Real.volume_Icc]

/-- For `n ≠ 0`, `γₙ` has unit speed. -/
theorem hasUnitSpeedOn_unitSpeedCircle {n : ℕ} (hn : n ≠ 0) :
    HasUnitSpeedOn (unitSpeedCircle n) univ := by
  refine hasConstantSpeedOnWith_iff_ordered.2 fun x _ y _ hxy ↦ ?_
  rw [univ_inter, eVariationOn_unitSpeedCircle hn hxy, NNReal.coe_one, one_mul]

/-! ### The loops in a flat torus -/

variable {S : AddSubgroup ℂ}

/-- The projection `ℂ → ℂ ⧸ S` preserves the distances between the points of `γₙ` when the nonzero
elements of `S` have norm at least `δ` and the diameter `1 / (π n)` of `γₙ` is at most `δ / 2`. -/
theorem dist_mk_unitSpeedCircle {δ : ℝ} (hS : ∀ s ∈ S, s ≠ 0 → δ ≤ ‖s‖) {n : ℕ}
    (hn : 2 ≤ Real.pi * n * δ) (s t : ℝ) :
    dist (unitSpeedCircle n s : ℂ ⧸ S) (unitSpeedCircle n t) =
      dist (unitSpeedCircle n s) (unitSpeedCircle n t) := by
  refine QuotientAddGroup.dist_mk_eq_dist fun z hz hz0 ↦ le_trans ?_ (hS z hz hz0)
  have hpos : 0 < Real.pi * n := by
    rcases eq_or_ne n 0 with rfl | hn0
    · norm_num at hn
    · have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      positivity
  calc 2 * dist (unitSpeedCircle n s) (unitSpeedCircle n t) ≤ 2 * (1 / (Real.pi * n)) := by
        gcongr
        exact dist_unitSpeedCircle_le n s t
    _ ≤ δ := by
        rw [mul_one_div, div_le_iff₀ hpos]
        linarith

/-- For every `δ > 0`, eventually `2 ≤ π n δ`: the loops `γₙ` eventually have diameter at most
`δ / 2`. -/
private theorem eventually_two_le_pi_mul_mul {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ Real.pi * n * δ := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (mul_pos Real.pi_pos hδ)
  filter_upwards [h.eventually_ge_atTop 2] with n hn
  linarith

variable (S) in
/-- The loop `γₙ(t) = i (1 - e^{2π i n t}) / (2π n)`, `t ∈ [0, 1]`, as a free Moore loop of
duration `1` in `ℂ ⧸ S`. -/
def unitSpeedCircleLoop (n : ℕ) : MooreFreeLoopSpace (ℂ ⧸ S) :=
  MooreFreeLoopSpace.ofClosedUnitPath
    ⟨⟨fun t : unitInterval ↦ (unitSpeedCircle n t : ℂ ⧸ S), by fun_prop⟩, by simp⟩

@[simp]
theorem unitSpeedCircleLoop_apply (n : ℕ) (t : ℝ≥0) :
    (unitSpeedCircleLoop S n).toMoorePath t = (unitSpeedCircle n (min (t : ℝ) 1) : ℂ ⧸ S) := by
  rw [unitSpeedCircleLoop, MooreFreeLoopSpace.toMoorePath_ofClosedUnitPath,
    MoorePath.ofUnitPath_apply, ContinuousMap.coe_mk, coe_projIcc, max_eq_right (by positivity),
    min_comm]

@[simp]
theorem length_unitSpeedCircleLoop (n : ℕ) : (unitSpeedCircleLoop S n).length = 1 := by
  rw [← MooreFreeLoopSpace.length_toMoorePath, unitSpeedCircleLoop,
    MooreFreeLoopSpace.toMoorePath_ofClosedUnitPath, MoorePath.length_ofUnitPath]

@[simp]
theorem basepoint_unitSpeedCircleLoop (n : ℕ) : (unitSpeedCircleLoop S n).basepoint = 0 := by
  rw [← MooreFreeLoopSpace.source_toMoorePath, MoorePath.source_def, unitSpeedCircleLoop_apply]
  simp

/-- The loop `γₙ` in `ℂ ⧸ S` has unit speed on its parameter interval `[0, 1]` when the nonzero
elements of `S` have norm at least `δ` and the diameter `1 / (π n)` of `γₙ` is at most `δ / 2`. -/
theorem hasUnitSpeedOn_unitSpeedCircleLoop {δ : ℝ} (hS : ∀ s ∈ S, s ≠ 0 → δ ≤ ‖s‖) {n : ℕ}
    (hn : 2 ≤ Real.pi * n * δ) :
    HasUnitSpeedOn (fun t : ℝ ↦ (unitSpeedCircleLoop S n).toMoorePath t.toNNReal) (Icc 0 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at hn
  refine hasConstantSpeedOnWith_iff_ordered.2 fun x hx y hy hxy ↦ ?_
  have hI : Icc (0 : ℝ) 1 ∩ Icc x y = Icc x y := inter_eq_right.2 (Icc_subset_Icc hx.1 hy.2)
  have heq : EqOn (fun t : ℝ ↦ (unitSpeedCircleLoop S n).toMoorePath t.toNNReal)
      ((↑) ∘ unitSpeedCircle n : ℝ → ℂ ⧸ S) (Icc x y) := fun t ht ↦ by
    have ht0 : 0 ≤ t := hx.1.trans ht.1
    simp [Real.coe_toNNReal t ht0, min_eq_left (ht.2.trans hy.2)]
  rw [hI, eVariationOn.eq_of_eqOn heq, eVariationOn.comp_eq_of_edist_eq fun s _ t _ ↦ by
      rw [edist_dist, edist_dist, dist_mk_unitSpeedCircle hS hn],
    eVariationOn_unitSpeedCircle hn0 hxy, NNReal.coe_one, one_mul]

variable (S) in
/-- The loops `γₙ` converge in `𝓛(ℂ ⧸ S)` to the constant loop at the origin of duration `1`. -/
theorem tendsto_unitSpeedCircleLoop :
    Tendsto (unitSpeedCircleLoop S) atTop
      (𝓝 ⟨MoorePath.constOfLength (0 : ℂ ⧸ S) 1, by simp⟩) := by
  rw [MooreFreeLoopSpace.isEmbedding_toMoorePath.tendsto_nhds_iff,
    MoorePath.isEmbedding_length_toContinuousMap.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ (ContinuousMap.tendsto_of_tendstoLocallyUniformly
    (TendstoUniformly.tendstoLocallyUniformly ?_))
  · simp only [Function.comp_apply, MoorePath.length_constOfLength,
      MooreFreeLoopSpace.length_toMoorePath, length_unitSpeedCircleLoop]
    exact tendsto_const_nhds
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn t
  have hn' : (N + 1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Function.comp_apply, MoorePath.constOfLength_apply, unitSpeedCircleLoop_apply]
  calc dist (0 : ℂ ⧸ S) (unitSpeedCircle n (min (t : ℝ) 1))
      ≤ ‖unitSpeedCircle n (min (t : ℝ) 1)‖ := by
        rw [dist_comm, dist_zero_right]
        exact QuotientAddGroup.norm_mk_le_norm
    _ ≤ 1 / (Real.pi * n) := norm_unitSpeedCircle_le n _
    _ ≤ 1 / (1 * (N + 1)) := by
        gcongr
        exact Real.one_le_pi_div_two.trans (by linarith [Real.pi_pos])
    _ < ε := by rwa [one_mul]

/-- Let `S` be a subgroup of `ℂ` whose nonzero elements have norm at least `δ > 0`. The free Moore
loops in the flat torus `ℂ ⧸ S` that are parametrized at unit speed do not form a closed subset of
`𝓛(ℂ ⧸ S)`: the unit-speed loops `γₙ` converge to the constant loop of duration `1`, which is not
parametrized at unit speed. -/
theorem not_isClosed_setOf_hasUnitSpeedOn {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ s ∈ S, s ≠ 0 → δ ≤ ‖s‖) :
    ¬ IsClosed {γ : MooreFreeLoopSpace (ℂ ⧸ S) |
      HasUnitSpeedOn (fun t : ℝ ↦ γ.toMoorePath t.toNNReal) (Icc 0 γ.length)} := by
  intro h
  have hmem := h.mem_of_tendsto (tendsto_unitSpeedCircleLoop S)
    ((eventually_two_le_pi_mul_mul hδ).mono fun n hn ↦ by
      rw [mem_ofPred_eq, length_unitSpeedCircleLoop, NNReal.coe_one]
      exact hasUnitSpeedOn_unitSpeedCircleLoop hS hn)
  simp only [mem_ofPred_eq, ← MooreFreeLoopSpace.length_toMoorePath,
    MoorePath.length_constOfLength, NNReal.coe_one] at hmem
  have h01 := hmem (x := 0) (by simp) (y := 1) (by simp)
  rw [eVariationOn.constant_on (by simp [MoorePath.constOfLength_apply])] at h01
  simp at h01

/-- The free Moore loops in the square flat torus `ℂ ⧸ ℤ[i] = ℝ² ⧸ ℤ²` that are parametrized at unit
speed do not form a closed subset of its free Moore loop space. -/
theorem not_isClosed_setOf_hasUnitSpeedOn_gaussianInt :
    ¬ IsClosed {γ : MooreFreeLoopSpace
        (ℂ ⧸ (GaussianInt.toComplex : GaussianInt →+* ℂ).range.toAddSubgroup) |
      HasUnitSpeedOn (fun t : ℝ ↦ γ.toMoorePath t.toNNReal) (Icc 0 γ.length)} := by
  refine not_isClosed_setOf_hasUnitSpeedOn one_pos ?_
  rintro _ ⟨x, rfl⟩ hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h1 : (1 : ℝ) ≤ normSq (x : ℂ) := by
    rw [← GaussianInt.intCast_real_norm]
    exact_mod_cast GaussianInt.norm_pos.2 hx0
  rw [← Real.sqrt_one, Complex.norm_def]
  exact Real.sqrt_le_sqrt h1

end TauCeti
