/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Section

/-!
# The engulfing property of sections of Monge–Ampère solutions

Let `E` be a real inner product space of finite dimension `n ≥ 1` with an additive Haar measure
`μ`, and let `u` be convex on an open set `Ω` with `λ μ ≤ MA_u ≤ Λ μ` on `Ω`, where `MA_u` is the
Aleksandrov Monge–Ampère measure of `u` and `0 < λ`. Write
`S(x, h) = {y ∈ Ω | u y < u x + ℓ (y - x) + h}` for the section of `u` at `x` with a supporting
slope `ℓ` and height `h`. This file proves Caffarelli's **engulfing property**: there is a
constant `C`, depending only on `E` and `μ`, such that whenever `S(x, 2h)` is bounded with closure
inside `Ω`, every `y ∈ S(x, h)` and every supporting slope `m` of `u` at `y` satisfy

  `S(x, h) ⊆ S(y, θ h)` with `θ = 1 + C Λ / λ`,

where `S(y, θ h)` is taken with the slope `m`. So every section centred at a point of `S(x, h)`,
of height `θ h`, swallows `S(x, h)`. Together with the volume estimates for
sections (`TauCeti.exists_mul_measure_convexSection_sq_le_mul_ofReal_pow`), this is the property
that lets sections play the role of balls in Caffarelli's interior regularity theory.

The engulfing property rests on an affine invariant interior estimate
(`TauCeti.exists_add_smul_sub_mem_of_mongeAmpereMeasure_le`). Let `v` be convex on a bounded open
set `G`, continuous on its closure, vanishing on its frontier and bounded below by `-k`, with
`λ μ ≤ MA_v` on `G` and `MA_v(G) ≤ Λ μ(G)`. If `v y ≤ -h` and `z ∈ G`, then `G` contains the
points `y + t (y - z)` for every `t ≥ 0` with `C Λ kⁿ t < λ hⁿ`: a point where `v` is deep is
uniformly far from the boundary of `G`, measured along chords. In a position normalized by an
affine equivalence (`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`), the point
`y` is within `2 t` of the boundary if `y + t (y - z)` leaves `G`
(`TauCeti.infDist_image_compl_le_of_add_smul_sub_notMem`). The depth bound
(`TauCeti.exists_ofReal_neg_pow_le_mul_ofReal_mul_measure_mul_mongeAmpereMeasure`) then bounds
`hⁿ` by `t` times the volume and the Monge–Ampère mass, and the volume estimate bounds their
product in terms of `kⁿ`.

For the engulfing property apply this to `v = u - u x - ℓ (· - x) - 2h` on `G = S(x, 2h)`, with
`k = 2h`, at `y ∈ S(x, h)`, where `v y < -h`. For `z ∈ S(x, h)` the point
`w = y + t (y - z)` lies in `G` for a fixed `t` comparable to `λ / Λ`, and the supporting plane at
`y` with slope `m` lies below `u w < u x + ℓ (w - x) + 2h`. Along the line through `z`, `y` and
`w` this bounds `m (y - z)` from above, which is the inequality `u z < u y + m (z - y) + θ h`.

## Main statements

* `TauCeti.infDist_image_compl_le_of_add_smul_sub_notMem` — distance to the boundary along a
  chord, in normalized position;
* `TauCeti.exists_add_smul_sub_mem_of_mongeAmpereMeasure_le` — the interior estimate along chords;
* `TauCeti.exists_convexSection_subset_convexSection` — **the engulfing property** of sections.

## References

* L. A. Caffarelli, *Some regularity properties of solutions of Monge Ampère equation*, Comm.
  Pure Appl. Math. 44 (1991), 965–969.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §3.3 (the engulfing property).
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Metric Module
open scoped ENNReal NNReal

section Chord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Distance to the boundary along a chord, in normalized position.** Let `T` be an affine
equivalence mapping `G` into the unit ball. If `y, z ∈ G` and the point `y + t (y - z)`, with
`t ≥ 0`, lies outside `G`, then `T y` is within `2 t` of the complement of `T '' G`. -/
theorem infDist_image_compl_le_of_add_smul_sub_notMem {G : Set E} (T : E ≃ᵃ[ℝ] E)
    (hT : T '' G ⊆ ball 0 1) {y z : E} (hy : y ∈ G) (hz : z ∈ G) {t : ℝ} (ht : 0 ≤ t)
    (hw : y + t • (y - z) ∉ G) : infDist (T y) (T '' G)ᶜ ≤ 2 * t := by
  -- `T` maps `y + t (y - z)` to `T y + t (T y - T z)`, and `‖T y - T z‖ < 2`.
  have hline (a b : E) : a + t • (a - b) = AffineMap.lineMap a b (-t) := by
    rw [AffineMap.lineMap_apply_module']
    module
  have hTw : T (y + t • (y - z)) = T y + t • (T y - T z) := by
    rw [hline, hline, T.apply_lineMap]
  refine (infDist_le_dist_of_mem (show T (y + t • (y - z)) ∈ (T '' G)ᶜ from
    fun h' => hw (T.injective.mem_set_image.1 h'))).trans ?_
  have hy' : ‖T y‖ < 1 := by simpa using hT (mem_image_of_mem T hy)
  have hz' : ‖T z‖ < 1 := by simpa using hT (mem_image_of_mem T hz)
  rw [hTw, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht]
  nlinarith [norm_sub_le (T y) (T z)]

end Chord

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Deep points are far from the boundary along chords.** There is a constant `C`, depending
only on `E` and `μ`, with the following property. Let `G` be a bounded open set and `v` convex on
`G`, continuous on its closure, vanishing on its frontier and bounded below by `-k` on `G`, such
that the Monge–Ampère measure of `v` (extended by `⊤` off `G`) is at least `λ μ` on `G` and has
mass `MA_v(G) ≤ Λ μ(G)`. If `y, z ∈ G` and `v y ≤ -h` with `0 ≤ h`, then `y + t (y - z) ∈ G` for
every `t ≥ 0` with `C Λ kⁿ t < λ hⁿ`, where `n = finrank ℝ E`. -/
theorem exists_add_smul_sub_mem_of_mongeAmpereMeasure_le :
    ∃ C : ℝ≥0, ∀ (G : Set E) [DecidablePred (· ∈ G)] (v : E → ℝ) (lam Lam : ℝ≥0) (h k : ℝ),
      IsOpen G → Bornology.IsBounded G → ConvexOn ℝ G v → ContinuousOn v (closure G) →
      (∀ x ∈ frontier G, v x = 0) → (∀ x ∈ G, -k ≤ v x) →
      (lam : ℝ≥0∞) • μ.restrict G ≤
        mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) →
      mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) G ≤ Lam * μ G →
      ∀ y ∈ G, 0 ≤ h → v y ≤ -h → ∀ z ∈ G, ∀ t : ℝ, 0 ≤ t →
        C * Lam * k ^ finrank ℝ E * t < lam * h ^ finrank ℝ E → y + t • (y - z) ∈ G := by
  classical
  obtain ⟨C₁, hC₁⟩ := exists_ofReal_neg_pow_le_mul_ofReal_mul_measure_mul_mongeAmpereMeasure μ
    (E := E)
  obtain ⟨C₂, hC₂⟩ := exists_mul_measure_sq_le_mul_ofReal_pow μ (E := E)
  set n := finrank ℝ E
  refine ⟨2 * C₁ * C₂, fun G _ v lam Lam h k hGo hGb hv hvc hfr hlow hMA hMAG y hy hh hvy z hz t
    ht hlt => ?_⟩
  by_contra hw
  have hk : 0 ≤ k := by linarith [hlow y hy]
  -- If `y + t (y - z)` leaves `G`, then `y` is within `2 t` of the boundary in every normalized
  -- position, so the depth bound applies with `d = 2 t`; the volume estimate bounds `λ μ(G)²`.
  have hdepth := hC₁ G v (2 * t) hGo hGb hv hvc (fun p hp => (hfr p hp).ge) y hy
    fun T hT => infDist_image_compl_le_of_add_smul_sub_notMem T hT hy hz ht hw
  have hvol := hC₂ G v lam k hGo hGb hv hvc (fun p hp => (hfr p hp).le) hlow hMA
  set M := mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) G
  set X := ENNReal.ofReal h ^ n
  have hX : X ≤ ENNReal.ofReal (-v y) ^ n :=
    pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (by linarith)) n
  -- Combine: `λ hⁿ ≤ 2 C₁ C₂ Λ kⁿ t`.
  have hle : lam * X ≤ (2 * C₁ * C₂ : ℝ≥0) * Lam * ENNReal.ofReal k ^ n * ENNReal.ofReal t :=
    calc lam * X ≤ lam * (C₁ * ENNReal.ofReal (2 * t) * μ G * (Lam * μ G)) := by
          gcongr
          exact hX.trans (hdepth.trans (by gcongr))
      _ = 2 * C₁ * Lam * ENNReal.ofReal t * (lam * μ G ^ 2) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
          ring
      _ ≤ 2 * C₁ * Lam * ENNReal.ofReal t * (C₂ * ENNReal.ofReal k ^ n) := by gcongr
      _ = (2 * C₁ * C₂ : ℝ≥0) * Lam * ENNReal.ofReal k ^ n * ENNReal.ofReal t := by
          push_cast
          ring
  -- This contradicts the hypothesis `C Λ kⁿ t < λ hⁿ`.
  have hpos : 0 < (lam : ℝ) * h ^ n := (by positivity : (0 : ℝ) ≤ _).trans_lt hlt
  have hlt' := (ENNReal.ofReal_lt_ofReal_iff hpos).2 hlt
  have hl : ENNReal.ofReal (lam * h ^ n) = lam * X := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow hh]
  have hr : ENNReal.ofReal ((2 * C₁ * C₂ : ℝ≥0) * Lam * k ^ n * t) =
      (2 * C₁ * C₂ : ℝ≥0) * Lam * ENNReal.ofReal k ^ n * ENNReal.ofReal t := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_pow hk]
  rw [hl, hr] at hlt'
  exact (not_le.2 hlt') hle

/-- **The engulfing property of sections.** There is a constant `C`, depending only on `E` and
`μ`, with the following property. Let `u` be convex on an open set `Ω`, with
`λ μ ≤ MA_u ≤ Λ μ` on `Ω` for the Monge–Ampère measure of `u` extended by `⊤` off `Ω` and
`0 < λ`, let `ℓ` be a supporting slope of `u` at `x`, and let the section `S(x, 2h)` be bounded
with closure inside `Ω`. Then for every `y ∈ S(x, h)` and every supporting slope `m` of `u` at `y`,
the section `S(x, h)` is contained in the section of `u` at `y` with slope `m` and height
`(1 + C Λ / λ) h`. -/
theorem exists_convexSection_subset_convexSection :
    ∃ C : ℝ≥0, ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (x : E) (ℓ : E →ₗ[ℝ] ℝ)
      (h : ℝ) (lam Lam : ℝ≥0), IsOpen Ω → ConvexOn ℝ Ω u → (∀ y ∈ Ω, u x + (ℓ y - ℓ x) ≤ u y) →
      Bornology.IsBounded (convexSection Ω u x ℓ (2 * h)) →
      closure (convexSection Ω u x ℓ (2 * h)) ⊆ Ω → 0 < lam →
      (lam : ℝ≥0∞) • μ.restrict Ω ≤
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) →
      mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) ≤
        (Lam : ℝ≥0∞) • μ.restrict Ω →
      ∀ y ∈ convexSection Ω u x ℓ h, ∀ m : E →ₗ[ℝ] ℝ, (∀ z ∈ Ω, u y + (m z - m y) ≤ u z) →
        convexSection Ω u x ℓ h ⊆ convexSection Ω u y m ((1 + C * Lam / lam) * h) := by
  classical
  obtain ⟨C₁, hC₁⟩ := exists_add_smul_sub_mem_of_mongeAmpereMeasure_le μ (E := E)
  set n := finrank ℝ E
  refine ⟨2 ^ (n + 2) * C₁ + 1, fun Ω _ u x ℓ h lam Lam hΩ hu hℓx hSb hSΩ hlam hMA hMA' y hy m
    hm z hz => ?_⟩
  have hh : 0 < h := by
    have h₁ := hℓx y (convexSection_subset hy)
    have h₂ := (mem_convexSection_iff.1 hy).2
    simp only [map_sub] at h₂
    linarith
  set G := convexSection Ω u x ℓ (2 * h)
  have hℓ : Continuous ℓ := ℓ.continuous_of_finiteDimensional
  have huc : ContinuousOn u Ω := hu.continuousOn hΩ
  have hGo : IsOpen G := isOpen_convexSection hΩ huc hℓ
  have hGΩ : G ⊆ Ω := convexSection_subset
  have hyG : y ∈ G := convexSection_mono_height (by linarith) hy
  have hzG : z ∈ G := convexSection_mono_height (by linarith) hz
  -- The upper bound `Λ` is positive, since `G` is a nonempty open set.
  have hLam : 0 < Lam := by
    refine pos_of_ne_zero fun h0 => ?_
    have hle := Measure.le_iff'.1 (hMA.trans hMA') G
    simp only [h0, ENNReal.coe_zero, zero_smul, Measure.coe_zero, Pi.zero_apply,
      Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hGo.measurableSet,
      inter_eq_left.2 hGΩ, nonpos_iff_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hle
    exact hle.elim hlam.ne' (hGo.measure_pos μ ⟨y, hyG⟩).ne'
  -- Subtract the plane: `v p = u p - u x - ℓ (p - x) - 2h` vanishes on the frontier of `G`.
  set c := ℓ x - u x - 2 * h
  have hfr : ∀ p ∈ frontier G, u p + (-ℓ) p + c = 0 := fun p hp => by
    have := eq_of_mem_frontier_convexSection hΩ huc hℓ hSΩ hp
    simp only [LinearMap.neg_apply, map_sub, c] at this ⊢
    linarith
  have hlow : ∀ p ∈ G, -(2 * h) ≤ u p + (-ℓ) p + c := fun p hp => by
    have := hℓx p (hGΩ hp)
    simp only [LinearMap.neg_apply, c]
    linarith
  have hMAup : mongeAmpereMeasure μ
      (fun p => if p ∈ G then ((u p + (-ℓ) p + c : ℝ) : EReal) else ⊤) G ≤ Lam * μ G := by
    rw [mongeAmpereMeasure_ite_convexSection_add_linearMap μ hΩ hu, Measure.restrict_apply_self]
    simpa [Measure.restrict_apply hGo.measurableSet, inter_eq_left.2 hGΩ] using
      Measure.le_iff'.1 hMA' G
  have hvy : u y + (-ℓ) y + c ≤ -h := by
    have := (mem_convexSection_iff.1 hy).2
    simp only [LinearMap.neg_apply, map_sub, c] at this ⊢
    linarith
  -- The step `t = 2 λ / (C Λ)` along the chord from `z` through `y` stays in `G`.
  set Cr : ℝ := 2 ^ (n + 2) * C₁ + 1
  have hCr : 0 < Cr := by positivity
  set t : ℝ := 2 * lam / (Cr * Lam)
  have ht : 0 < t := by positivity
  have hstep : (C₁ : ℝ) * Lam * (2 * h) ^ n * t < lam * h ^ n := by
    have heq : (C₁ : ℝ) * Lam * (2 * h) ^ n * t = 2 ^ (n + 1) * C₁ / Cr * (lam * h ^ n) := by
      simp only [t, mul_pow, pow_succ]
      field_simp
    have hlt1 : 2 ^ (n + 1) * (C₁ : ℝ) / Cr < 1 := by
      rw [div_lt_one hCr]
      have : (0 : ℝ) ≤ 2 ^ (n + 1) * C₁ := by positivity
      simp only [Cr, pow_succ] at this ⊢
      linarith
    rw [heq]
    exact mul_lt_of_lt_one_left (by positivity) hlt1
  have hw := hC₁ G (fun p => u p + (-ℓ) p + c) lam Lam h (2 * h) hGo hSb
    (convexOn_convexSection_add_linearMap hu (-ℓ) c)
    (continuousOn_closure_convexSection_add_linearMap huc hℓ.neg hSΩ c) hfr hlow
    (smul_restrict_le_mongeAmpereMeasure_ite_convexSection_add_linearMap μ hΩ hu (-ℓ) c hMA)
    hMAup y hyG hh.le hvy z hzG t ht.le hstep
  -- The supporting plane at `y` with slope `m` lies below `u` at `w = y + t (y - z)`.
  have hθ : (1 + ((2 ^ (n + 2) * C₁ + 1 : ℝ≥0) : ℝ) * Lam / lam) * h = h + 2 * h / t := by
    simp only [t, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_one, Cr]
    field_simp
  rw [hθ]
  exact mem_convexSection_of_add_smul_sub_mem (hℓx y (convexSection_subset hy)) hm hz ht hw

end TauCeti
