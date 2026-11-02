/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.MeasureTheory.OptimalTransport.Cost.NoCrossing
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# The continuity equation along the displacement interpolation of a plan

Let `π` be a finite measure on `E × E`, where `E` is a finite-dimensional real normed space, for
instance a coupling of two laws `μ` and `ν`. Moving the mass of each pair `(x, y)` at constant
speed along the segment from `x` to `y` gives the curve of laws

`μₜ = (Fₜ)₊ π`, where `Fₜ (x, y) = (1 - t) • x + t • y`,

from `μ₀ = π.fst` to `μ₁ = π.snd`. When `1 ≤ p`, both marginals are probability measures with
finite `p`-th moment, and `π` is an optimal coupling for `W_p`, this is the displacement
interpolation of `μ` and `ν`, a geodesic segment of `P_p (E)`
(`TauCeti.WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul`). This file describes the
curve in Eulerian terms. Unlike the linear interpolation of a map
(`TauCeti.exists_isContinuityEquation_map_smul_add_smul`), no transport map is needed: the mass at
a point may split, so the statements cover every source law, atoms included.

If the displacement `y - x` has finite first moment under `π`, then `μₜ` solves the continuity
equation on `(0, 1)` with the *barycentric velocity* `vₜ w = E_π [Y - X | Fₜ (X, Y) = w]`, the
average displacement of the pairs whose interpolating point at time `t` is `w`. Its `p`-action is
at most the `p`-th moment of the displacement,
`∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt ≤ ∫ ‖y - x‖ ^ p dπ` for every `p ≥ 1`.

If moreover no two pairs meet at the same time and place once a `dt ⊗ π`-null set of times and
pairs is discarded (for instance if almost every `Fₜ` with `0 < t < 1` is injective on a measurable
set carrying `π`), then no averaging takes place: `vₜ ((1 - t) • x + t • y) = y - x` for almost
every `t ∈ (0, 1)` and `π`-almost every `(x, y)`, and the `p`-action of `v` equals the `p`-th
moment of the displacement.

For an optimal coupling of `μ` and `ν` at finite Wasserstein distance `W_p (μ, ν)`, with
`1 ≤ p < ∞`, the `p`-th moment of the displacement is `W_p (μ, ν) ^ p`, so the displacement
interpolation solves the continuity equation with action at most `W_p (μ, ν) ^ p`: this is the
upper bound in the Benamou–Brenier formula `W_p (μ, ν) ^ p = inf ∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt`, over
the solutions of the continuity equation joining `μ` to `ν`. If `E` is strictly convex and
`1 < p`, an optimal coupling is concentrated on its support, which is cyclically monotone, and
the segments joining the pairs of a cyclically monotone set do not cross
(`TauCeti.IsCyclicallyMonotone.injOn_smul_add_smul`). The velocity is then the displacement
itself and the action is exactly `W_p (μ, ν) ^ p`. Combined with the lower bound
`W_p (μ, ν) ^ p ≤ ∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt` for every solution joining `μ` to `ν`
(`TauCeti.IsContinuityEquation.wassersteinEDist_rpow_le`), this makes the displacement
interpolation a minimiser in the Benamou–Brenier formula
(`TauCeti.isLeast_lintegral_isContinuityEquation`).

## Main results

* `TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd`: the displacement interpolation
  of a plan whose displacement has finite first moment solves the continuity equation with its
  barycentric velocity, whose `p`-action is at most the `p`-th moment of the displacement.
* `TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_injOn`: when for every `t`
  the interpolating map `Fₜ` is injective on the fibre at `t` of a measurable set of full
  `dt ⊗ π` measure, the velocity field is the displacement read along the interpolation, and its
  `p`-action equals the `p`-th moment of the displacement.
* `TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_ae_injOn`: the special case in
  which almost every interpolating map is injective on one measurable set carrying the plan.
* `TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling_le`: for
  `1 ≤ p < ∞`, the displacement interpolation of an optimal coupling at finite Wasserstein
  distance solves the continuity equation with `p`-action at most `W_p (μ, ν) ^ p`.
* `TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling`: on a
  strictly convex space and for `1 < p < ∞`, the velocity of the displacement interpolation of an
  optimal coupling is the displacement, and its `p`-action is `W_p (μ, ν) ^ p`.

## References

* J.-D. Benamou and Y. Brenier, *A computational fluid mechanics solution to the
  Monge–Kantorovich mass transfer problem*, Numer. Math. 84 (2000), 375--393.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1 and §8.3.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.4.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- **The continuity equation along the displacement interpolation of a plan.** Let `π` be a finite
measure on `E × E` whose displacement `y - x` has finite first moment. Then the laws `μₜ` of
`(1 - t) • x + t • y` under `π` solve the continuity equation on `(0, 1)` with the barycentric
velocity `v`: its value at `(t, (1 - t) • x + t • y)` is the conditional expectation of the
displacement `y - x` given the time `t` and the position `(1 - t) • x + t • y`, for the measure
`dt ⊗ π` on `(0, 1) × (E × E)`. For every `p ≥ 1` its `p`-action is at most the `p`-th moment of
the displacement: `∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt ≤ ∫ ‖y - x‖ ^ p dπ`. -/
theorem exists_isContinuityEquation_map_smul_fst_add_smul_snd (π : Measure (E × E))
    [IsFiniteMeasure π] (hint : ∫⁻ z, ‖z.2 - z.1‖ₑ ∂π < ∞) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ π.map fun z ↦ (1 - t) • z.1 + t • z.2) v 0 1 ∧
      (fun q : ℝ × (E × E) ↦ v q.1 ((1 - q.1) • q.2.1 + q.1 • q.2.2)) =
        ((volume.restrict (Ioo 0 1)).prod π)[fun q ↦ q.2.2 - q.2.1 |
          MeasurableSpace.comap (fun q : ℝ × (E × E) ↦ (q.1, (1 - q.1) • q.2.1 + q.1 • q.2.2))
            inferInstance] ∧
      ∀ p : ℝ, 1 ≤ p →
        ∫⁻ t in Ioo 0 1, ∫⁻ w, ‖v t w‖ₑ ^ p ∂π.map (fun z ↦ (1 - t) • z.1 + t • z.2) ≤
          ∫⁻ z, ‖z.2 - z.1‖ₑ ^ p ∂π := by
  obtain ⟨v, hce, hv, hact⟩ := exists_isContinuityEquation_map π
    (γ := fun z t ↦ (1 - t) • z.1 + t • z.2) (V := fun z _ ↦ z.2 - z.1) (a := 0) (b := 1)
    (by fun_prop) (by fun_prop)
    (.of_forall fun z ↦ (by fun_prop : ContDiff ℝ 1 fun t : ℝ ↦ (1 - t) • z.1 + t • z.2).contDiffOn
      |>.absolutelyContinuousOnInterval)
    (.of_forall fun z ↦ .of_forall fun t _ ↦
      ((((hasDerivAt_id' t).const_sub 1).smul_const z.1).add
        ((hasDerivAt_id' t).smul_const z.2)).congr_deriv (by simp [neg_add_eq_sub]))
    (by simpa using hint)
  exact ⟨v, hce, hv, fun p hp ↦ (hact p hp).trans_eq (by simp)⟩

/-- **The velocity along a non-crossing displacement interpolation.** Let `π` be a finite measure
on `E × E` whose displacement `y - x` has finite first moment, and let `A` be a measurable set of
times and pairs carrying `dt ⊗ π` on `(0, 1) × (E × E)` such that for every `t` the interpolating
map `(x, y) ↦ (1 - t) • x + t • y` is injective on the pairs `(x, y)` with `(t, (x, y)) ∈ A`. Then
the laws `μₜ` of `(1 - t) • x + t • y` under `π` solve the continuity equation on `(0, 1)` with a
velocity field `v` equal to the displacement along the interpolation:
`vₜ ((1 - t) • x + t • y) = y - x` for almost every `t ∈ (0, 1)` and `π`-almost every `(x, y)`.
Consequently, for every exponent `p` the `p`-action of `v` is the `p`-th moment of the
displacement: `∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt = ∫ ‖y - x‖ ^ p dπ`. -/
theorem exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_injOn (π : Measure (E × E))
    [IsFiniteMeasure π] (hint : ∫⁻ z, ‖z.2 - z.1‖ₑ ∂π < ∞) {A : Set (ℝ × (E × E))}
    (hA : MeasurableSet A) (hAπ : ∀ᵐ q ∂(volume.restrict (Ioo 0 1)).prod π, q ∈ A)
    (hinj : ∀ t, InjOn (fun z : E × E ↦ (1 - t) • z.1 + t • z.2) {z | (t, z) ∈ A}) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ π.map fun z ↦ (1 - t) • z.1 + t • z.2) v 0 1 ∧
      (∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ z ∂π, v t ((1 - t) • z.1 + t • z.2) = z.2 - z.1) ∧
      ∀ p : ℝ, ∫⁻ t in Ioo 0 1, ∫⁻ w, ‖v t w‖ₑ ^ p ∂π.map (fun z ↦ (1 - t) • z.1 + t • z.2) =
        ∫⁻ z, ‖z.2 - z.1‖ₑ ^ p ∂π := by
  obtain ⟨v, hce, hv, -⟩ := exists_isContinuityEquation_map_smul_fst_add_smul_snd π hint
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  -- the time and position map `G` is injective on `A`, so conditioning on it is trivial
  set G : ℝ × (E × E) → ℝ × E := fun q ↦ (q.1, (1 - q.1) • q.2.1 + q.1 • q.2.2)
  have hG : Measurable G := by fun_prop
  have hGinj : InjOn G A := by
    rintro ⟨t, z⟩ hz ⟨t', z'⟩ hz' he
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    exact Prod.ext rfl (hinj t hz hz' he)
  have hW : Integrable (fun z : E × E ↦ z.2 - z.1) π :=
    ⟨by fun_prop, hasFiniteIntegral_iff_enorm.2 hint⟩
  have hae : ∀ᵐ q ∂(volume.restrict (Ioo 0 1)).prod π,
      v q.1 ((1 - q.1) • q.2.1 + q.1 • q.2.2) = q.2.2 - q.2.1 := by
    filter_upwards [MeasureTheory.condExp_comap_ae_eq_of_injOn hG hA hAπ hGinj
      (hW.comp_snd (volume.restrict (Ioo 0 1)))] with q hq
    rw [← hq]
    exact congrFun hv q
  have hae' : ∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ z ∂π, v t ((1 - t) • z.1 + t • z.2) = z.2 - z.1 := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact Measure.ae_ae_of_ae_prod hae
  refine ⟨v, hce, hae', fun p ↦ ?_⟩
  have hvm (t : ℝ) : Measurable (v t) := hce.measurable_velocity.comp measurable_prodMk_left
  calc ∫⁻ t in Ioo 0 1, ∫⁻ w, ‖v t w‖ₑ ^ p ∂π.map (fun z ↦ (1 - t) • z.1 + t • z.2)
      = ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ z, ‖z.2 - z.1‖ₑ ^ p ∂π := by
        refine setLIntegral_congr_fun_ae measurableSet_Ioo ?_
        filter_upwards [hae'] with t ht hmem
        rw [lintegral_map ((hvm t).enorm.pow_const p) (by fun_prop)]
        exact lintegral_congr_ae ((ht hmem).mono fun z hz ↦ by simp [hz])
    _ = ∫⁻ z, ‖z.2 - z.1‖ₑ ^ p ∂π := by simp

/-- **The velocity along a displacement interpolation injective on a fixed set.** The special case
of `exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_injOn` in which, for almost every
`t ∈ (0, 1)`, the map `(x, y) ↦ (1 - t) • x + t • y` is injective on one measurable set `S`
carrying `π`: then `vₜ ((1 - t) • x + t • y) = y - x` for almost every `t ∈ (0, 1)` and `π`-almost
every `(x, y)`, and for every exponent `p` the `p`-action of `v` is the `p`-th moment of the
displacement. -/
theorem exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_ae_injOn (π : Measure (E × E))
    [IsFiniteMeasure π] (hint : ∫⁻ z, ‖z.2 - z.1‖ₑ ∂π < ∞) {S : Set (E × E)}
    (hS : MeasurableSet S) (hSπ : ∀ᵐ z ∂π, z ∈ S)
    (hinj : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → InjOn (fun z : E × E ↦ (1 - t) • z.1 + t • z.2) S) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ π.map fun z ↦ (1 - t) • z.1 + t • z.2) v 0 1 ∧
      (∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ z ∂π, v t ((1 - t) • z.1 + t • z.2) = z.2 - z.1) ∧
      ∀ p : ℝ, ∫⁻ t in Ioo 0 1, ∫⁻ w, ‖v t w‖ₑ ^ p ∂π.map (fun z ↦ (1 - t) • z.1 + t • z.2) =
        ∫⁻ z, ‖z.2 - z.1‖ₑ ^ p ∂π := by
  -- `U` is a measurable set of full measure in `(0, 1)` of times at which the interpolation is
  -- injective on `S`
  set N := toMeasurable volume
    {t | ¬(t ∈ Ioo (0 : ℝ) 1 → InjOn (fun z : E × E ↦ (1 - t) • z.1 + t • z.2) S)}
  set U := Ioo (0 : ℝ) 1 \ N
  have hU : MeasurableSet U := measurableSet_Ioo.diff (measurableSet_toMeasurable _ _)
  have hUπ : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), t ∈ U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1
        ((measure_toMeasurable _).trans (ae_iff.1 hinj)))] with t ht htN using ⟨ht, htN⟩
  have hUinj (t : ℝ) (ht : t ∈ U) : InjOn (fun z : E × E ↦ (1 - t) • z.1 + t • z.2) S := by
    by_contra h
    exact ht.2 (subset_toMeasurable _ _ fun h' ↦ h (h' ht.1))
  exact exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_injOn π hint (hU.prod hS)
    ((Measure.ae_prod_mem_iff_ae_ae_mem (hU.prod hS)).2
      (hUπ.mono fun _ ht ↦ hSπ.mono fun _ hz ↦ ⟨ht, hz⟩))
    fun t _ hz _ hz' ↦ hUinj t hz.1 hz.2 hz'.2

/-- **The Benamou–Brenier upper bound.** Let `1 ≤ p < ∞`, and let `π` be an optimal coupling of a
finite measure `μ` and a measure `ν` on `E` for the cost `d(x, y) ^ p`, at finite Wasserstein
distance `W_p (μ, ν)`. Then the displacement interpolation, the laws `μₜ` of
`(1 - t) • x + t • y` under `π`, solves the continuity equation on `(0, 1)` with a velocity field
of `p`-action at most `W_p (μ, ν) ^ p`: `∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt ≤ W_p (μ, ν) ^ p`. -/
theorem exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling_le
    {μ ν : Measure E} [IsFiniteMeasure μ] {π : Measure (E × E)} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ∞) (hopt : IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ p.toReal) π μ ν)
    (hfin : wassersteinEDist p μ ν ≠ ∞) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ π.map fun z ↦ (1 - t) • z.1 + t • z.2) v 0 1 ∧
      ∫⁻ t in Ioo 0 1, ∫⁻ w, ‖v t w‖ₑ ^ p.toReal ∂π.map (fun z ↦ (1 - t) • z.1 + t • z.2) ≤
        wassersteinEDist p μ ν ^ p.toReal := by
  have : IsFiniteMeasure π := hopt.toIsCoupling.isFiniteMeasure
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hint : ∫⁻ z, ‖z.2 - z.1‖ₑ ∂π < ∞ := hasFiniteIntegral_iff_enorm.1
    (memLp_one_iff_integrable.1 ((hopt.memLp_sub hp0 hp_top hfin).mono_exponent hp)).2
  obtain ⟨v, hce, -, hact⟩ := exists_isContinuityEquation_map_smul_fst_add_smul_snd π hint
  have hp₁ : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  exact ⟨v, hce, (hact p.toReal hp₁).trans_eq (hopt.lintegral_enorm_sub_rpow_eq hp0 hp_top)⟩

/-- **The velocity along an optimal displacement interpolation.** Let `E` be strictly convex, let
`1 < p < ∞`, and let `π` be an optimal coupling of a finite measure `μ` and a measure `ν` on `E`
for the cost `d(x, y) ^ p`, at finite Wasserstein distance `W_p (μ, ν)`. Then the displacement
interpolation, the laws `μₜ` of `(1 - t) • x + t • y` under `π`, solves the continuity equation on
`(0, 1)` with a velocity field `v` equal to the displacement along the interpolation,
`vₜ ((1 - t) • x + t • y) = y - x` for almost every `t ∈ (0, 1)` and `π`-almost every `(x, y)`,
and the `p`-action of `v` is the `p`-th power of the Wasserstein distance:
`∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt = W_p (μ, ν) ^ p`.

The optimal coupling is concentrated on its support, which is cyclically monotone, and transport
segments between pairs of a cyclically monotone set do not cross
(`TauCeti.IsCyclicallyMonotone.injOn_smul_add_smul`), so no averaging takes place. -/
theorem exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling
    [StrictConvexSpace ℝ E] {μ ν : Measure E} [IsFiniteMeasure μ] {π : Measure (E × E)}
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞)
    (hopt : IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ p.toReal) π μ ν)
    (hfin : wassersteinEDist p μ ν ≠ ∞) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ π.map fun z ↦ (1 - t) • z.1 + t • z.2) v 0 1 ∧
      (∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ z ∂π, v t ((1 - t) • z.1 + t • z.2) = z.2 - z.1) ∧
      ∫⁻ t in Ioo 0 1, ∫⁻ w, ‖v t w‖ₑ ^ p.toReal ∂π.map (fun z ↦ (1 - t) • z.1 + t • z.2) =
        wassersteinEDist p μ ν ^ p.toReal := by
  have : IsFiniteMeasure π := hopt.toIsCoupling.isFiniteMeasure
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hp₁ : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  have hint : ∫⁻ z, ‖z.2 - z.1‖ₑ ∂π < ∞ := hasFiniteIntegral_iff_enorm.1
    (memLp_one_iff_integrable.1 ((hopt.memLp_sub hp0 hp_top hfin).mono_exponent hp.le)).2
  -- the optimal plan is concentrated on its support, which is cyclically monotone
  have hc : Continuous fun z : E × E ↦ edist z.1 z.2 ^ p.toReal :=
    ENNReal.continuous_rpow_const.comp continuous_edist
  have hcost : transportCost (fun z : E × E ↦ edist z.1 z.2 ^ p.toReal) μ ν ≠ ∞ := by
    rw [← wassersteinEDist_rpow_eq_transportCost measurable_edist hp0 hp_top]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hfin
  obtain ⟨v, hce, hv, hact⟩ := exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_ae_injOn π
    hint Measure.isClosed_support.measurableSet π.support_mem_ae
    (.of_forall fun _ ht ↦ (hopt.isCyclicallyMonotone_support hc hcost).injOn_smul_add_smul hp₁ ht)
  exact ⟨v, hce, hv, (hact p.toReal).trans (hopt.lintegral_enorm_sub_rpow_eq hp0 hp_top)⟩

end TauCeti
