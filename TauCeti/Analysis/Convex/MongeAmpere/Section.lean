/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Affine
public import TauCeti.Analysis.Convex.MongeAmpere.Comparison
public import TauCeti.Analysis.Convex.Section.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Convex.AffineNormalization
import TauCeti.Analysis.Convex.StrictConvexSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Volume of sections of solutions of the Monge–Ampère equation

Let `E` be a real inner product space of finite dimension `n ≥ 1` with an additive Haar measure
`μ`, and let `v` be convex on a bounded open set `G`, continuous on its closure. The Monge–Ampère
mass of `v` on `G`, the volume of `G` and the depth of `v` below its boundary values control
each other, with constants depending only on `E` and `μ`:

* if `v ≥ 0` on the frontier of `G`, then `(max 0 (-v x₀)) ^ n ≤ C μ(G) MA_v(G)` for every
  `x₀ ∈ G`;
* if `v ≤ 0` on the frontier of `G`, `v ≥ -h` on `G` and `MA_v ≥ λ μ` on `G`, then
  `λ μ(G)² ≤ C hⁿ`.

So a convex function with `λ ≤ MA_v ≤ Λ` vanishing on the boundary of `G` has depth comparable
to `μ(G) ^ (2 / n)`. Both bounds are affine invariant. They are proved for a domain normalized by
an affine equivalence `T` between the balls of radii `r` and `1` about `0`
(`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`), and transferred back by the change
of variables `MA_{v ∘ T⁻¹}(s) = |det L| MA_v(T⁻¹ '' s)`, where `L` is the linear part of `T⁻¹`
(`TauCeti.mongeAmpereMeasure_comp_affineEquiv_apply`), together with
`μ(T⁻¹ '' s) = |det L| μ(s)`. In the normalized position the first bound is the Aleksandrov
maximum principle (`TauCeti.ofReal_neg_pow_mul_addHaar_ball_le_mul_mongeAmpereMeasure`), and the
second is the comparison principle (`TauCeti.le_of_mongeAmpereMeasure_le_of_le_frontier`) against
the quadratic `y ↦ (a / 2) (‖y‖² - r²)` whose Monge–Ampère measure is `aⁿ μ`
(`TauCeti.mongeAmpereMeasure_ite_mul_norm_sq_add`).

Applied to `v = u - u x - ℓ (· - x) - h` on a section `S = {y ∈ Ω | u y < u x + ℓ (y - x) + h}`
whose closure lies in the domain `Ω` of `u`, these give the volume estimates for sections: if
`λ ≤ MA_u ≤ Λ` on `Ω` and `ℓ` is a supporting slope at `x`, then `λ μ(S)² ≤ C hⁿ` and
`hⁿ ≤ C Λ μ(S)²`, i.e. `μ(S)` is comparable to `h ^ (n / 2)`. These estimates are the starting
point for the geometry of sections used in the regularity theory of the Monge–Ampère equation.

## Main statements

* `TauCeti.mongeAmpereMeasure_ite_mul_norm_sq_add` — the Monge–Ampère measure of
  `y ↦ (a / 2) ‖y‖² + c` on an open convex set is `aⁿ μ`;
* `TauCeti.mongeAmpereMeasure_ite_convexSection_add_linearMap` — subtracting a plane from `u`
  on a section `S` restricts the Monge–Ampère measure of `u` to `S`;
* `TauCeti.exists_ofReal_neg_pow_le_mul_ofReal_mul_measure_mul_mongeAmpereMeasure` — the depth
  bound `(max 0 (-v x₀)) ^ n ≤ C d μ(G) MA_v(G)` when `d` bounds the distance to the boundary in
  every normalized position;
* `TauCeti.exists_ofReal_neg_pow_le_mul_measure_mul_mongeAmpereMeasure` — the depth bound
  `(max 0 (-v x₀)) ^ n ≤ C μ(G) MA_v(G)`;
* `TauCeti.exists_mul_measure_sq_le_mul_ofReal_pow` — the volume bound `λ μ(G)² ≤ C hⁿ`;
* `TauCeti.exists_ofReal_pow_le_mul_measure_convexSection_mul_mongeAmpereMeasure` and
  `TauCeti.exists_mul_measure_convexSection_sq_le_mul_ofReal_pow` — the corresponding lower and
  upper volume estimates `hⁿ ≤ C μ(S) MA_u(S)` and `λ μ(S)² ≤ C hⁿ` for sections.

## References

* L. A. Caffarelli, *A localization property of viscosity solutions to the Monge–Ampère equation
  and their strict convexity*, Ann. of Math. 131 (1990), 129–134.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §3.2.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Metric Module
open scoped ENNReal NNReal Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The Monge–Ampère measure of a quadratic.** For `a ≥ 0`, the function
`y ↦ (a / 2) ‖y‖² + c` on an open convex set `U`, extended by `⊤` off `U`, has Monge–Ampère
measure `aⁿ μ` on `U` with respect to an additive Haar measure `μ`, where `n = finrank ℝ E`: its
gradient is `y ↦ a • y`. -/
theorem mongeAmpereMeasure_ite_mul_norm_sq_add {U : Set E} [DecidablePred (· ∈ U)]
    (hU : IsOpen U) (hUc : Convex ℝ U) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    mongeAmpereMeasure μ (fun y => if y ∈ U then ((a / 2 * ‖y‖ ^ 2 + c : ℝ) : EReal) else ⊤) =
      ENNReal.ofReal (a ^ finrank ℝ E) • μ.restrict U := by
  -- The gradient is `y ↦ a • y`, hence the Hessian is `a • id`.
  have hH (y : E) :
      HasFDerivAt (∇ fun y : E => a / 2 * ‖y‖ ^ 2 + c) (a • ContinuousLinearMap.id ℝ E) y := by
    rw [show (∇ fun y : E => a / 2 * ‖y‖ ^ 2 + c) = fun y => a • y from
      funext (gradient_mul_norm_sq_add a c)]
    exact (hasFDerivAt_id y).const_smul a
  rw [mongeAmpereMeasure_ite_eq_withDensity_det μ hU (convexOn_mul_norm_sq_add hUc ha c)
    (fun y _ => (hasGradientAt_mul_norm_sq_add a c y).differentiableAt.differentiableWithinAt)
    (fun y _ => (hH y).differentiableAt.differentiableWithinAt)]
  simp only [(hH _).fderiv, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact withDensity_const _

/-- **Subtracting a plane on a section.** Let `u` be convex on an open set `Ω`, and let
`S = {y ∈ Ω | u y < u x + ℓ (y - x) + h}`. The Monge–Ampère measure of `u + L + c`, extended by
`⊤` off `S`, is the restriction to `S` of the Monge–Ampère measure of `u` extended by `⊤` off
`Ω`. With `L = -ℓ` and `c = ℓ x - u x - h` this is the potential `u - u x - ℓ (· - x) - h`, which
vanishes on the frontier of `S`. -/
theorem mongeAmpereMeasure_ite_convexSection_add_linearMap {Ω : Set E} [DecidablePred (· ∈ Ω)]
    {u : E → ℝ} {x : E} {ℓ : E →ₗ[ℝ] ℝ} {h : ℝ} [DecidablePred (· ∈ convexSection Ω u x ℓ h)]
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (L : E →ₗ[ℝ] ℝ) (c : ℝ) :
    mongeAmpereMeasure μ
        (fun y => if y ∈ convexSection Ω u x ℓ h then ((u y + L y + c : ℝ) : EReal) else ⊤) =
      (mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤)).restrict
        (convexSection Ω u x ℓ h) := by
  rw [mongeAmpereMeasure_ite_add_linearMap μ u L c,
    mongeAmpereMeasure_ite_eq_restrict μ hΩ
      (isOpen_convexSection hΩ (hu.continuousOn hΩ) ℓ.continuous_of_finiteDimensional)
      (convex_convexSection hu) convexSection_subset hu AbsolutelyContinuous.rfl]

/-- A lower bound `a μ ≤ MA_u` on `Ω` gives the lower bound `a μ ≤ MA_{u + L + c}` on a section
`S` of `u`, for the Monge–Ampère measures of `u` extended by `⊤` off `Ω` and of `u + L + c`
extended by `⊤` off `S`. -/
theorem smul_restrict_le_mongeAmpereMeasure_ite_convexSection_add_linearMap {Ω : Set E}
    [DecidablePred (· ∈ Ω)] {u : E → ℝ} {x : E} {ℓ : E →ₗ[ℝ] ℝ} {h : ℝ}
    [DecidablePred (· ∈ convexSection Ω u x ℓ h)] (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u)
    (L : E →ₗ[ℝ] ℝ) (c : ℝ) {a : ℝ≥0∞}
    (hMA : a • μ.restrict Ω ≤ mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤)) :
    a • μ.restrict (convexSection Ω u x ℓ h) ≤ mongeAmpereMeasure μ
      (fun y => if y ∈ convexSection Ω u x ℓ h then ((u y + L y + c : ℝ) : EReal) else ⊤) := by
  rw [mongeAmpereMeasure_ite_convexSection_add_linearMap μ hΩ hu L c,
    ← Measure.restrict_restrict_of_subset convexSection_subset, ← Measure.restrict_smul]
  exact Measure.restrict_mono_measure hMA _

variable [Nontrivial E]

/-- **The depth of a convex function is controlled by its distance to the boundary, volume and
Monge–Ampère mass.** There is a constant `C`, depending only on `E` and `μ`, with the following
property. Let `G` be a bounded open set, `v` convex on `G`, continuous on its closure and
nonnegative on its frontier, and `x₀ ∈ G`. If `d` bounds the distance from `T x₀` to the
complement of `T '' G` for every affine equivalence `T` mapping `G` into the unit ball, then
`(max 0 (-v x₀)) ^ n ≤ C d μ(G) MA_v(G)` for the Monge–Ampère measure of `v` extended by `⊤` off
`G`, where `n = finrank ℝ E`. Both the hypothesis and the conclusion are invariant under affine
changes of coordinates. -/
theorem exists_ofReal_neg_pow_le_mul_ofReal_mul_measure_mul_mongeAmpereMeasure :
    ∃ C : ℝ≥0, ∀ (G : Set E) [DecidablePred (· ∈ G)] (v : E → ℝ) (d : ℝ), IsOpen G →
      Bornology.IsBounded G → ConvexOn ℝ G v → ContinuousOn v (closure G) →
      (∀ x ∈ frontier G, 0 ≤ v x) → ∀ x₀ ∈ G,
      (∀ T : E ≃ᵃ[ℝ] E, T '' G ⊆ ball 0 1 → infDist (T x₀) (T '' G)ᶜ ≤ d) →
      ENNReal.ofReal (-v x₀) ^ finrank ℝ E ≤ C * ENNReal.ofReal d * μ G *
        mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) G := by
  classical
  obtain ⟨r, hr, hnorm⟩ := exists_affineEquiv_ball_subset_image_subset_ball E
  set n := finrank ℝ E
  set B := μ (ball (0 : E) 1)
  have hB0 : B ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hBtop : B ≠ ∞ := measure_ball_lt_top.ne
  -- In normalized position the diameter is at most `2`.
  set c₁ : ℝ≥0∞ := 2 ^ (n + 1) * ENNReal.ofReal (2 ^ (n - 1))
  set R : ℝ≥0∞ := ENNReal.ofReal (r ^ n) * B
  have hR0 : R ≠ 0 := mul_ne_zero (by simp [hr, n]) hB0
  have hRtop : R ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop
  have hRB0 : R * B ≠ 0 := mul_ne_zero hR0 hB0
  have hRBtop : R * B ≠ ∞ := ENNReal.mul_ne_top hRtop hBtop
  have hK : c₁ * (R * B)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.2 hRB0)
  refine ⟨(c₁ * (R * B)⁻¹).toNNReal, fun G _ v d hGo hGb hv hvc hfr x₀ hx₀ hd => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  -- Normalize `G` by an affine equivalence `T`, so that `ball 0 r ⊆ G' ⊆ ball 0 1`.
  obtain ⟨T, hTr, hT1⟩ := hnorm G hv.1 hGb ⟨x₀, hGo.interior_eq.symm ▸ hx₀⟩
  have hdist := hd T hT1
  rw [show T '' G = T.symm ⁻¹' G from T.toEquiv.image_eq_preimage_symm G] at hTr hT1 hdist
  set G' := T.symm ⁻¹' G
  set H := (AffineEquiv.toContinuousAffineEquiv T.symm).toHomeomorph
  set D := ENNReal.ofReal |LinearMap.det (T.symm.linear : E →ₗ[ℝ] E)|
  have hμG : μ G = D * μ G' := by
    rw [← addHaar_image_affineEquiv μ T.symm, image_preimage_eq _ T.symm.surjective]
  have hG'o : IsOpen G' := hGo.preimage H.continuous
  have hG'b : Bornology.IsBounded G' := isBounded_ball.subset hT1
  have hcl : closure G' = T.symm ⁻¹' closure G := (H.preimage_closure G).symm
  have hfr' : frontier G' = T.symm ⁻¹' frontier G := (H.preimage_frontier G).symm
  -- The Aleksandrov maximum principle for `v ∘ T⁻¹` on `G'`, at `T x₀`.
  have hconv' : ConvexOn ℝ G' fun y => v (T.symm y) := hv.comp_affineMap (T.symm : E →ᵃ[ℝ] E)
  have hcont' : ContinuousOn (fun y => v (T.symm y)) (closure G') := by
    rw [hcl]
    exact hvc.comp H.continuous.continuousOn fun y hy => hy
  have hmax := ofReal_neg_pow_mul_addHaar_ball_le_mul_mongeAmpereMeasure μ hG'o hG'b hconv'
    hcont' (fun y hy => hfr _ (by rw [hfr'] at hy; exact hy)) (x₀ := T x₀)
    (by simpa [G'] using hx₀)
  rw [mongeAmpereMeasure_ite_comp_symm_apply μ T G v hG'o.measurableSet,
    image_preimage_eq _ T.symm.surjective, AffineEquiv.symm_apply_apply] at hmax
  -- Bound the diameter and the distance to the complement in normalized position.
  have hdiam : diam G' ≤ 2 :=
    (diam_mono hT1 isBounded_ball).trans ((diam_ball zero_le_one).trans_eq (mul_one 2))
  have hgeom : ENNReal.ofReal (diam G' ^ (n - 1) * infDist (T x₀) G'ᶜ) ≤
      ENNReal.ofReal (2 ^ (n - 1)) * ENNReal.ofReal d := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul (pow_le_pow_left₀ diam_nonneg hdiam _) hdist
      infDist_nonneg (by positivity))
  -- The volume of `G'` is at least that of `ball 0 r`.
  have hRG' : R ≤ μ G' := (addHaar_ball μ 0 hr.le).symm.trans_le (measure_mono hTr)
  set M := mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) G
  set X := ENNReal.ofReal (-v x₀) ^ n
  have hmain : X * (R * B) ≤ c₁ * ENNReal.ofReal d * μ G * M :=
    calc X * (R * B) = X * B * R := by ring
      _ ≤ 2 ^ (n + 1) * ENNReal.ofReal (diam G' ^ (n - 1) * infDist (T x₀) G'ᶜ) * (D * M) * R :=
        mul_le_mul_left hmax R
      _ ≤ 2 ^ (n + 1) * (ENNReal.ofReal (2 ^ (n - 1)) * ENNReal.ofReal d) * (D * M) * μ G' :=
        mul_le_mul' (mul_le_mul_left (mul_le_mul_right hgeom _) _) hRG'
      _ = c₁ * ENNReal.ofReal d * μ G * M := by rw [hμG]; ring
  calc X = X * (R * B) * (R * B)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hRB0 hRBtop, mul_one]
    _ ≤ c₁ * ENNReal.ofReal d * μ G * M * (R * B)⁻¹ := mul_le_mul_left hmain _
    _ = c₁ * (R * B)⁻¹ * ENNReal.ofReal d * μ G * M := by ring

/-- **The depth of a convex function is controlled by its volume and Monge–Ampère mass.** There
is a constant `C`, depending only on `E` and `μ`, such that for every bounded open set `G`, every
`v` convex on `G`, continuous on its closure and nonnegative on its frontier, and every `x₀ ∈ G`,
`(max 0 (-v x₀)) ^ n ≤ C μ(G) MA_v(G)` for the Monge–Ampère measure of `v` extended by `⊤` off
`G`, where `n = finrank ℝ E`. Unlike the Aleksandrov maximum principle it involves no diameter
or distance, so it is invariant under affine changes of coordinates. -/
theorem exists_ofReal_neg_pow_le_mul_measure_mul_mongeAmpereMeasure :
    ∃ C : ℝ≥0, ∀ (G : Set E) [DecidablePred (· ∈ G)] (v : E → ℝ), IsOpen G →
      Bornology.IsBounded G → ConvexOn ℝ G v → ContinuousOn v (closure G) →
      (∀ x ∈ frontier G, 0 ≤ v x) → ∀ x₀ ∈ G,
      ENNReal.ofReal (-v x₀) ^ finrank ℝ E ≤
        C * μ G * mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) G := by
  obtain ⟨C, hC⟩ := exists_ofReal_neg_pow_le_mul_ofReal_mul_measure_mul_mongeAmpereMeasure μ
    (E := E)
  refine ⟨C * 2, fun G _ v hGo hGb hv hvc hfr x₀ hx₀ => ?_⟩
  -- In normalized position the distance to the boundary is at most `2`.
  have hd (T : E ≃ᵃ[ℝ] E) (hT : T '' G ⊆ ball 0 1) : infDist (T x₀) (T '' G)ᶜ ≤ 2 := by
    obtain ⟨z, hz⟩ := exists_norm_eq E zero_le_one
    have hzG : z ∈ (T '' G)ᶜ := fun hz' => by simpa [hz] using hT hz'
    have hx₀' : ‖T x₀‖ < 1 := by simpa using hT (mem_image_of_mem T hx₀)
    refine (infDist_le_dist_of_mem hzG).trans ?_
    rw [dist_eq_norm]
    linarith [norm_sub_le (T x₀) z]
  simpa using hC G v 2 hGo hGb hv hvc hfr x₀ hx₀ hd

/-- **The volume of a domain is controlled by the depth of a convex function on it.** There is a
constant `C`, depending only on `E` and `μ`, with the following property. Let `G` be a bounded
open set and `v` convex on `G`, continuous on its closure, with `v ≤ 0` on the frontier of `G` and
`v ≥ -h` on `G`. If the Monge–Ampère measure of `v` (extended by `⊤` off `G`) is at least `λ μ`
on `G`, then `λ μ(G)² ≤ C hⁿ`, where `n = finrank ℝ E`. -/
theorem exists_mul_measure_sq_le_mul_ofReal_pow :
    ∃ C : ℝ≥0, ∀ (G : Set E) [DecidablePred (· ∈ G)] (v : E → ℝ) (lam : ℝ≥0) (h : ℝ),
      IsOpen G → Bornology.IsBounded G → ConvexOn ℝ G v → ContinuousOn v (closure G) →
      (∀ x ∈ frontier G, v x ≤ 0) → (∀ x ∈ G, -h ≤ v x) →
      (lam : ℝ≥0∞) • μ.restrict G ≤
        mongeAmpereMeasure μ (fun x => if x ∈ G then (v x : EReal) else ⊤) →
      lam * μ G ^ 2 ≤ C * ENNReal.ofReal h ^ finrank ℝ E := by
  classical
  obtain ⟨r, hr, hnorm⟩ := exists_affineEquiv_ball_subset_image_subset_ball E
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  set B := μ (ball (0 : E) 1)
  have hBtop : B ≠ ∞ := measure_ball_lt_top.ne
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 / r ^ 2) ^ n) * B ^ 2
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hBtop)
  refine ⟨K.toNNReal, fun G _ v lam h hGo hGb hv hvc hfr hlow hMA => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  rcases G.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  -- Normalize `G` by an affine equivalence `T`, so that `ball 0 r ⊆ G' ⊆ ball 0 1`.
  obtain ⟨T, hTr, hT1⟩ := hnorm G hv.1 hGb ⟨x₀, hGo.interior_eq.symm ▸ hx₀⟩
  rw [show T '' G = T.symm ⁻¹' G from T.toEquiv.image_eq_preimage_symm G] at hTr hT1
  set G' := T.symm ⁻¹' G
  set H := (AffineEquiv.toContinuousAffineEquiv T.symm).toHomeomorph
  set d := |LinearMap.det (T.symm.linear : E →ₗ[ℝ] E)|
  have hμG : μ G = ENNReal.ofReal d * μ G' := by
    rw [← addHaar_image_affineEquiv μ T.symm, image_preimage_eq _ T.symm.surjective]
  have hG'o : IsOpen G' := hGo.preimage H.continuous
  have hG'b : Bornology.IsBounded G' := isBounded_ball.subset hT1
  have hcl : closure G' = T.symm ⁻¹' closure G := (H.preimage_closure G).symm
  have hfr' : frontier G' = T.symm ⁻¹' frontier G := (H.preimage_frontier G).symm
  have h0 : (0 : E) ∈ G' := hTr (mem_ball_self hr)
  have hconv' : ConvexOn ℝ G' fun y => v (T.symm y) := hv.comp_affineMap (T.symm : E →ᵃ[ℝ] E)
  have hcont' : ContinuousOn (fun y => v (T.symm y)) (closure G') := by
    rw [hcl]
    exact hvc.comp H.continuous.continuousOn fun y hy => hy
  -- The comparison function `w y = (a / 2) (‖y‖² - r²)` with `aⁿ = λ d²`.
  set a := ((lam : ℝ) * d ^ 2) ^ (n⁻¹ : ℝ)
  have ha : 0 ≤ a := by positivity
  have han : a ^ n = lam * d ^ 2 := Real.rpow_inv_natCast_pow (by positivity) hn
  -- The Monge–Ampère measure of `v ∘ T⁻¹` dominates `aⁿ μ = λ d² μ` on `G'`, which is that of `w`.
  have hle : mongeAmpereMeasure μ (fun y => if y ∈ G' then
        ((a / 2 * ‖y‖ ^ 2 + -(a / 2 * r ^ 2) : ℝ) : EReal) else ⊤) ≤
      mongeAmpereMeasure μ (fun y => if y ∈ G' then (v (T.symm y) : EReal) else ⊤) := by
    rw [mongeAmpereMeasure_ite_mul_norm_sq_add μ hG'o hconv'.1 ha, han, Measure.le_iff]
    intro s hs
    rw [mongeAmpereMeasure_ite_comp_symm_apply μ T G v hs]
    refine le_trans ?_ (mul_le_mul' le_rfl (Measure.le_iff'.1 hMA (T.symm '' s)))
    rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul, Measure.smul_apply,
      smul_eq_mul, Measure.restrict_apply' hGo.measurableSet, ← image_inter_preimage,
      addHaar_image_affineEquiv μ T.symm, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (abs_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact le_of_eq (by ring)
  -- The comparison principle on `G'`: `v ∘ T⁻¹ ≤ w`, since `w ≥ 0 ≥ v ∘ T⁻¹` on the frontier.
  have hcomp := le_of_mongeAmpereMeasure_le_of_le_frontier μ hG'o hG'b
    (convexOn_mul_norm_sq_add hconv'.1 ha _) hconv' (by fun_prop) hcont' hle
    (fun y hy => ?_) h0
  rotate_left
  · -- On the frontier of `G'`, `‖y‖ ≥ r` and `v (T⁻¹ y) ≤ 0`.
    have hyG' : y ∉ G' := by rw [hG'o.frontier_eq] at hy; exact hy.2
    have hry : r ≤ ‖y‖ := by
      by_contra! hlt
      exact hyG' (hTr (mem_ball_zero_iff.2 hlt))
    have hvy : v (T.symm y) ≤ 0 := hfr _ (by rw [hfr'] at hy; exact hy)
    nlinarith [mul_le_mul hry hry hr.le (norm_nonneg y)]
  simp only [norm_zero] at hcomp
  -- Hence `a r² / 2 ≤ h`, so `λ d² ≤ (2 h / r²)ⁿ`.
  have hvh := hlow _ h0
  have har : a ≤ 2 * h / r ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hh : 0 ≤ h := by nlinarith [mul_nonneg ha (sq_nonneg r)]
  have hpow : (lam : ℝ) * d ^ 2 ≤ (2 / r ^ 2) ^ n * h ^ n := by
    rw [← han, ← mul_pow]
    exact pow_le_pow_left₀ ha (by rw [div_mul_eq_mul_div]; exact har) n
  -- Finally `μ(G) = d μ(G') ≤ d μ(ball 0 1)`.
  have hμG' : μ G ≤ ENNReal.ofReal d * B := by
    rw [hμG]
    exact mul_le_mul' le_rfl (measure_mono hT1)
  calc (lam : ℝ≥0∞) * μ G ^ 2 ≤ lam * (ENNReal.ofReal d * B) ^ 2 := by gcongr
    _ = ENNReal.ofReal (lam * d ^ 2) * B ^ 2 := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (abs_nonneg _),
        ENNReal.ofReal_coe_nnreal]
      ring
    _ ≤ ENNReal.ofReal ((2 / r ^ 2) ^ n * h ^ n) * B ^ 2 := by gcongr
    _ = K * ENNReal.ofReal h ^ n := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hh]
      ring
/-! ### Sections -/

/-- **Lower volume estimate for sections.** There is a constant `C`, depending only on `E` and
`μ`, with the following property. Let `u` be convex on an open set `Ω`, let `x ∈ Ω`, and let
`S = {y ∈ Ω | u y < u x + ℓ (y - x) + h}` be a bounded section whose closure lies in `Ω`. Then
`hⁿ ≤ C μ(S) MA_u(S)` for the Monge–Ampère measure of `u` extended by `⊤` off `Ω`, where
`n = finrank ℝ E`. In particular, if `MA_u ≤ Λ μ` on `Ω`, then `hⁿ ≤ C Λ μ(S)²`. -/
theorem exists_ofReal_pow_le_mul_measure_convexSection_mul_mongeAmpereMeasure :
    ∃ C : ℝ≥0, ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (x : E) (ℓ : E →ₗ[ℝ] ℝ)
      (h : ℝ), IsOpen Ω → ConvexOn ℝ Ω u → x ∈ Ω →
      Bornology.IsBounded (convexSection Ω u x ℓ h) → closure (convexSection Ω u x ℓ h) ⊆ Ω →
      ENNReal.ofReal h ^ finrank ℝ E ≤ C * μ (convexSection Ω u x ℓ h) *
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤)
          (convexSection Ω u x ℓ h) := by
  classical
  obtain ⟨C, hC⟩ := exists_ofReal_neg_pow_le_mul_measure_mul_mongeAmpereMeasure μ (E := E)
  refine ⟨C, fun Ω _ u x ℓ h hΩ hu hx hSb hSΩ => ?_⟩
  set S := convexSection Ω u x ℓ h
  rcases le_or_gt h 0 with hh | hh
  · rw [ENNReal.ofReal_of_nonpos hh, zero_pow finrank_pos.ne']
    exact bot_le
  have hℓ : Continuous ℓ := ℓ.continuous_of_finiteDimensional
  have huc : ContinuousOn u Ω := hu.continuousOn hΩ
  have hSo : IsOpen S := isOpen_convexSection hΩ huc hℓ
  -- Subtract the plane: `v y = u y - u x - ℓ (y - x) - h` vanishes on the boundary of `S`.
  set c := ℓ x - u x - h
  have hfr : ∀ y ∈ frontier S, 0 ≤ u y + (-ℓ) y + c := fun y hy => by
    have := eq_of_mem_frontier_convexSection hΩ huc hℓ hSΩ hy
    simp only [LinearMap.neg_apply, map_sub, c] at this ⊢
    linarith
  have key := hC S (fun y => u y + (-ℓ) y + c) hSo hSb
    (convexOn_convexSection_add_linearMap hu (-ℓ) c)
    (continuousOn_closure_convexSection_add_linearMap huc hℓ.neg hSΩ c) hfr x
    (mem_convexSection_iff.2 ⟨hx, by simpa using hh⟩)
  beta_reduce at key
  rw [mongeAmpereMeasure_ite_convexSection_add_linearMap μ hΩ hu, Measure.restrict_apply_self,
    show -(u x + (-ℓ) x + c) = h by simp only [LinearMap.neg_apply, c]; ring] at key
  exact key

/-- **Upper volume estimate for sections.** There is a constant `C`, depending only on `E` and
`μ`, with the following property. Let `u` be convex on an open set `Ω`, let `ℓ` be a supporting
slope of `u` at `x`, and let `S = {y ∈ Ω | u y < u x + ℓ (y - x) + h}` be a bounded section whose
closure lies in `Ω`. If the Monge–Ampère measure of `u` (extended by `⊤` off `Ω`) is at least
`λ μ` on `Ω`, then `λ μ(S)² ≤ C hⁿ`, where `n = finrank ℝ E`. -/
theorem exists_mul_measure_convexSection_sq_le_mul_ofReal_pow :
    ∃ C : ℝ≥0, ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (x : E) (ℓ : E →ₗ[ℝ] ℝ)
      (h : ℝ) (lam : ℝ≥0), IsOpen Ω → ConvexOn ℝ Ω u → (∀ y ∈ Ω, u x + (ℓ y - ℓ x) ≤ u y) →
      Bornology.IsBounded (convexSection Ω u x ℓ h) → closure (convexSection Ω u x ℓ h) ⊆ Ω →
      (lam : ℝ≥0∞) • μ.restrict Ω ≤
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) →
      lam * μ (convexSection Ω u x ℓ h) ^ 2 ≤ C * ENNReal.ofReal h ^ finrank ℝ E := by
  classical
  obtain ⟨C, hC⟩ := exists_mul_measure_sq_le_mul_ofReal_pow μ (E := E)
  refine ⟨C, fun Ω _ u x ℓ h lam hΩ hu hℓx hSb hSΩ hMA => ?_⟩
  set S := convexSection Ω u x ℓ h
  have hℓ : Continuous ℓ := ℓ.continuous_of_finiteDimensional
  have huc : ContinuousOn u Ω := hu.continuousOn hΩ
  have hSo : IsOpen S := isOpen_convexSection hΩ huc hℓ
  -- Subtract the plane: `v y = u y - u x - ℓ (y - x) - h` lies between `-h` and `0` on `S`.
  set c := ℓ x - u x - h
  have hfr : ∀ y ∈ frontier S, u y + (-ℓ) y + c ≤ 0 := fun y hy => by
    have := eq_of_mem_frontier_convexSection hΩ huc hℓ hSΩ hy
    simp only [LinearMap.neg_apply, map_sub, c] at this ⊢
    linarith
  have hlow : ∀ y ∈ S, -h ≤ u y + (-ℓ) y + c := fun y hy => by
    have := hℓx y (mem_convexSection_iff.1 hy).1
    simp only [LinearMap.neg_apply, c]
    linarith
  exact hC S (fun y => u y + (-ℓ) y + c) lam h hSo hSb
    (convexOn_convexSection_add_linearMap hu (-ℓ) c)
    (continuousOn_closure_convexSection_add_linearMap huc hℓ.neg hSΩ c) hfr hlow
    (smul_restrict_le_mongeAmpereMeasure_ite_convexSection_add_linearMap μ hΩ hu (-ℓ) c hMA)

end TauCeti
