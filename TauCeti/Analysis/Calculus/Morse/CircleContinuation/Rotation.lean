/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Basin
public import TauCeti.Geometry.Manifold.Morse.Circle
import TauCeti.Algebra.AddCircle
import TauCeti.Topology.Circle.AddCircle

/-!
# The circle continuation counterexamples

On the circle `ℝ ⧸ 2πℤ`, the functions `f_r(θ) = δ cos (2 (θ - r))`, `δ > 0`, have the maxima
`p_j(r) = r + j π` (`TauCeti.circleCosTwoMax r j`) and the minima `q_j(r) = r + π / 2 + j π`
(`TauCeti.circleCosTwoMin r j`), `j ∈ {0, 1}`. A path `t ↦ r t` gives the continuation family
`f_{r(t)}`, whose parameter field `TauCeti.circleContinuationField` has the trajectories in
`0 < t < 1` given by the solutions of `Θ' = circleContinuationSlope δ r t (Θ t)`, `Θ` being a lift
of the angle. This file counts these trajectories on the circle, and computes the continuation of
three explicit paths, which shows how continuation maps differ from the tracking of critical
points.

**Counts on the circle.** Let the path be constant, `r₀` on `(0, a]` and `r₁` on `[b, 1)`, with
`0 < a ≤ b < 1`, let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bound the drift of the angle across the
window `[a, b]`, and let `n` be an integer with `|r₁ - r₀ - n π| + D < π / 2`. Write
`c = r₁ - r₀ - n π` for the residual rotation.

* Every trajectory leaving a source minimum `q_j(r₀)` ends at the target minimum `q_j(r₀) + c`
  (`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`),
  and every trajectory arriving at a target maximum `p_k(r₁)` starts at the source maximum
  `p_k(r₁) - c`
  (`TauCeti.tendsto_coe_circleCosTwoMax_sub_of_hasDerivAt_circleContinuationSlope`).
* Such trajectories exist when the path is continuous on the window
  (`TauCeti.exists_hasDerivAt_circleContinuationSlope_tendsto_coe_circleCosTwoMin`,
  `TauCeti.exists_hasDerivAt_circleContinuationSlope_tendsto_coe_circleCosTwoMax`), and they are
  unique: two trajectories leaving the same source minimum, or arriving at the same target maximum,
  have the same image in the circle
  (`TauCeti.eqOn_coe_of_tendsto_coe_circleCosTwoMin_of_hasDerivAt_circleContinuationSlope`,
  `TauCeti.eqOn_coe_of_tendsto_coe_circleCosTwoMax_of_hasDerivAt_circleContinuationSlope`).
* No trajectory joins a source minimum to a target maximum
  (`TauCeti.not_tendsto_coe_circleCosTwoMax_of_hasDerivAt_circleContinuationSlope`).
  Both are zeros of the parameter field with a one-dimensional unstable manifold, so this is the
  admissibility of the path: for a large amplitude such a connection exists
  (`TauCeti.exists_circleContinuationField_connection`).

So the trajectories that preserve the Morse index of the end functions give the continuation map
`q_j(r₀) ↦ q_j(r₀) + c` on the minima, and `p_k(r₁) - c ↦ p_k(r₁)` on the maxima, each with a single
trajectory. The trajectories are counted on the circle: the hypotheses only ask the image of `Θ` in
the circle to tend to the critical points, and a lift of the angle is recovered from it
(`AddCircle.exists_tendsto_add_int_mul_of_tendsto_coe`).

**The examples.** Let `ρ` be `0` for `t ≤ 1/3` and `1` for `t ≥ 2/3`, and let `δ > 0` satisfy
`2 δ T < π / 12` on the window `[1/6, 5/6]`, where `T = ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt`. The
theorems below say where the trajectories go; when `ρ` is continuous, so are the paths, and the
trajectories exist by the existence theorems above.

* For the half-turn `r = r₀ + π ρ`, from `f_{r₀}` to the same function `f_{r₀ + π}`, the
  continuation sends each critical point to itself: in fixed spatial bases it is the identity in
  both degrees. Tracking the critical points along the path, however, `q_j(r₀)` becomes
  `q_j(r₀ + π)`, which is the other minimum `q_{j + 1}(r₀)` (`TauCeti.circleCosTwoMin_add_pi`). In
  the tracked labels the continuation is the exchange `S` of the two generators, in both degrees
  (`TauCeti.tendsto_coe_circleCosTwoMin_add_pi_iff`,
  `TauCeti.tendsto_coe_circleCosTwoMax_iff_of_add_pi`).
* For a third of a turn, `r = r₀ + (π / 3) ρ`, the continuation agrees with the tracked labels:
  it is the identity `I` in both degrees
  (`TauCeti.tendsto_coe_circleCosTwoMin_add_pi_div_three_iff`,
  `TauCeti.tendsto_coe_circleCosTwoMax_iff_of_add_pi_div_three`). This holds for the
  paths `Γ₁` from `0` to `π / 3` and `Γ₂` from `π / 3` to `2 π / 3`.
* For their concatenation, `Γ₁` run on `[0, 1/2]` at double speed followed by `Γ₂` on `[1/2, 1]`,
  the continuation is again `S` in the tracked labels
  (`TauCeti.tendsto_coe_circleCosTwoMin_add_two_mul_pi_div_three_iff`,
  `TauCeti.tendsto_coe_circleCosTwoMax_iff_of_add_two_mul_pi_div_three`). So
  `Φ_{Γ₁} = Φ_{Γ₂} = I` but `Φ_{Γ₂ * Γ₁} = S`: continuation maps do not compose strictly.

The counts here are unsigned; the signs, the identification with the continuation map
`TauCeti.morseContinuationMap` of the cylinder `S¹ × ℝ`, and the chain homotopy between `I` and
`S` are not treated.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open AddCircle Filter Real Set Topology

namespace TauCeti

variable {δ a b r₀ r₁ : ℝ} {r Θ Θ₁ Θ₂ : ℝ → ℝ}

/-! ### Lifting trajectories from the circle -/

/-- Translating a solution by a multiple of `2π` gives a solution. -/
private theorem hasDerivAt_add_int_mul_two_pi
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (m : ℤ) :
    ∀ t ∈ Ioo 0 1, HasDerivAt (fun t ↦ Θ t + m * (2 * π))
      (circleContinuationSlope δ r t (Θ t + m * (2 * π))) t := fun t ht ↦ by
  rw [show Θ t + m * (2 * π) = Θ t + ((2 * m : ℤ) : ℝ) * π by push_cast; ring,
    circleContinuationSlope_add_int_mul_pi]
  exact (hΘ t ht).add_const _

/-- The image in the circle of a limit of a lift. -/
private theorem tendsto_coe {l : Filter ℝ} {y : ℝ} (h : Tendsto Θ l (𝓝 y)) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) l (𝓝 (y : AddCircle (2 * π))) :=
  ((AddCircle.continuous_mk' (2 * π)).tendsto y).comp h

/-- A solution whose image in the circle tends to the class of `y` at `0` tends to a lift of it. -/
private theorem exists_tendsto_nhdsGT_zero_of_tendsto_coe
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {y : ℝ}
    (h : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (y : AddCircle (2 * π)))) :
    ∃ m : ℤ, Tendsto Θ (𝓝[>] 0) (𝓝 (y + m * (2 * π))) :=
  exists_tendsto_add_int_mul_of_tendsto_coe (X := ℝ) two_pi_pos
    (fun _ hu ↦ let ⟨c, hc, hcu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hu
      ⟨Ioo 0 c, Ioo_mem_nhdsGT hc, hcu, isPreconnected_Ioo⟩)
    (Ioo_mem_nhdsGT one_pos) (fun t ht ↦ (hΘ t ht).continuousAt.continuousWithinAt) h

/-- A solution whose image in the circle tends to the class of `y` at `1` tends to a lift of it. -/
private theorem exists_tendsto_nhdsLT_one_of_tendsto_coe
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {y : ℝ}
    (h : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (y : AddCircle (2 * π)))) :
    ∃ m : ℤ, Tendsto Θ (𝓝[<] 1) (𝓝 (y + m * (2 * π))) :=
  exists_tendsto_add_int_mul_of_tendsto_coe (X := ℝ) two_pi_pos
    (fun _ hu ↦ let ⟨c, hc, hcu⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hu
      ⟨Ioo c 1, Ioo_mem_nhdsLT hc, hcu, isPreconnected_Ioo⟩)
    (Ioo_mem_nhdsLT one_pos) (fun t ht ↦ (hΘ t ht).continuousAt.continuousWithinAt) h

/-- The hypothesis of `Basin.lean` on the labels for a source minimum `i` and the target minimum
`i - n`. -/
private theorem abs_add_mul_pi_sub_add_sub_mul_pi_add_lt {D : ℝ} {n : ℤ}
    (hn : |r₁ - r₀ - n * π| + D < π / 2) (i : ℤ) :
    |r₀ + i * π - (r₁ + ((i - n : ℤ) : ℝ) * π)| + D < π / 2 := by
  rwa [show r₀ + i * π - (r₁ + ((i - n : ℤ) : ℝ) * π) = -(r₁ - r₀ - n * π) by push_cast; ring,
    abs_neg]

/-- The hypothesis of `Basin.lean` on the labels for a source maximum `i + n` and the target
maximum `i`. -/
private theorem abs_add_mul_pi_sub_add_add_mul_pi_add_lt {D : ℝ} {n : ℤ}
    (hn : |r₁ - r₀ - n * π| + D < π / 2) (i : ℤ) :
    |r₁ + i * π - (r₀ + ((i + n : ℤ) : ℝ) * π)| + D < π / 2 := by
  rwa [show r₁ + i * π - (r₀ + ((i + n : ℤ) : ℝ) * π) = r₁ - r₀ - n * π by push_cast; ring]

/-! ### Counting the index-preserving trajectories on the circle -/

section Counts

variable (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
  (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
  (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) {n : ℤ}
  (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
include hδ ha hab hb hr₀ hr₁ hΘ hn

/-- **The trajectory leaving a source minimum.** Let the path `r` be constant, `r₀` on `(0, a]` and
`r₁` on `[b, 1)`, let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bound the drift of the angle across the
window `[a, b]`, and let `n` be an integer with `|r₁ - r₀ - n π| + D < π / 2`. A trajectory leaving
the source minimum `q_j(r₀)` ends at the minimum `q_j(r₀) + (r₁ - r₀ - n π)` of the target
function. -/
theorem tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope
    {j : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j))) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1)
      (𝓝 (circleCosTwoMin r₀ j + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)))) := by
  rw [circleCosTwoMin_def] at hlim ⊢
  obtain ⟨m, hm⟩ := exists_tendsto_nhdsGT_zero_of_tendsto_coe hΘ hlim
  have h := tendsto_nhdsLT_one_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ ha
    hab hb hr₀ hr₁ hΘ (j := (j : ℕ) + 2 * m) (k := (j : ℕ) + 2 * m - n)
    (abs_add_mul_pi_sub_add_sub_mul_pi_add_lt hn _)
    (by convert hm using 2; push_cast; ring)
  rw [← coe_add]
  convert tendsto_coe h using 2
  exact coe_eq_coe_iff_exists_zsmul.2 ⟨-m, by rw [zsmul_eq_mul]; push_cast; ring⟩

/-- **The trajectory arriving at a target maximum.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`,
a trajectory arriving at the target maximum `p_k(r₁)` starts at the maximum
`p_k(r₁) - (r₁ - r₀ - n π)` of the source function. -/
theorem tendsto_coe_circleCosTwoMax_sub_of_hasDerivAt_circleContinuationSlope
    {k : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMax r₁ k))) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0)
      (𝓝 (circleCosTwoMax r₁ k - ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)))) := by
  rw [circleCosTwoMax_def] at hlim ⊢
  obtain ⟨m, hm⟩ := exists_tendsto_nhdsLT_one_of_tendsto_coe hΘ hlim
  have h := tendsto_nhdsGT_zero_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ ha
    hab hb hr₀ hr₁ hΘ (j := (k : ℕ) + 2 * m + n) (k := (k : ℕ) + 2 * m)
    (abs_add_mul_pi_sub_add_add_mul_pi_add_lt hn _)
    (by convert hm using 2; push_cast; ring)
  rw [← coe_sub]
  convert tendsto_coe h using 2
  exact coe_eq_coe_iff_exists_zsmul.2 ⟨-m, by rw [zsmul_eq_mul]; push_cast; ring⟩

/-- **The continuation coefficients of the minima.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`,
a trajectory leaving the source minimum `q_j(r₀)` ends at the target minimum `q_k(r₁)` exactly when
`q_k(r₁) = q_j(r₀) + (r₁ - r₀ - n π)`. -/
theorem tendsto_coe_circleCosTwoMin_iff_of_hasDerivAt_circleContinuationSlope
    {j : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)))
    (k : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMin r₁ k)) ↔
      circleCosTwoMin r₁ k =
        circleCosTwoMin r₀ j + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) := by
  have h := tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope
    hδ ha hab hb hr₀ hr₁ hΘ hn hlim
  exact ⟨fun h' ↦ tendsto_nhds_unique h' h, fun e ↦ by rwa [e]⟩

/-- **The continuation coefficients of the maxima.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`,
a trajectory arriving at the target maximum `p_k(r₁)` starts at the source maximum `p_j(r₀)` exactly
when `p_j(r₀) = p_k(r₁) - (r₁ - r₀ - n π)`. -/
theorem tendsto_coe_circleCosTwoMax_iff_of_hasDerivAt_circleContinuationSlope
    {k : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMax r₁ k)))
    (j : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMax r₀ j)) ↔
      circleCosTwoMax r₀ j =
        circleCosTwoMax r₁ k - ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) := by
  have h := tendsto_coe_circleCosTwoMax_sub_of_hasDerivAt_circleContinuationSlope
    hδ ha hab hb hr₀ hr₁ hΘ hn hlim
  exact ⟨fun h' ↦ tendsto_nhds_unique h' h, fun e ↦ by rwa [e]⟩

/-- **Admissibility: no trajectory from a source minimum to a target maximum.** Under the
hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`,
a trajectory leaving a source minimum ends at a target minimum, hence at no target maximum. Both are
zeros of index `1` of the parameter field, and for a large amplitude `δ` such a connection exists
(`TauCeti.exists_circleContinuationField_connection`). -/
theorem not_tendsto_coe_circleCosTwoMax_of_hasDerivAt_circleContinuationSlope
    {j : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)))
    (k : Fin 2) :
    ¬Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMax r₁ k)) := by
  intro h
  obtain ⟨i, hi⟩ := exists_circleCosTwoMin_eq r₁ ((j : ℕ) - n)
  refine circleCosTwoMin_ne_circleCosTwoMax r₁ i k ?_
  rw [← tendsto_nhds_unique
    (tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope hδ ha
      hab hb hr₀ hr₁ hΘ hn hlim) h, hi, circleCosTwoMin_def, ← coe_add]
  congr 1
  push_cast
  ring

end Counts

/-- **Existence of the trajectory leaving a source minimum.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`,
if moreover the path `r` is continuous on the window `[a, b]`, a trajectory leaves every source
minimum. -/
theorem exists_hasDerivAt_circleContinuationSlope_tendsto_coe_circleCosTwoMin (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr : ContinuousOn r (Icc a b))
    (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) {n : ℤ}
    (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) (j : Fin 2) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)) := by
  obtain ⟨Θ, hΘ, h₀, -⟩ := exists_hasDerivAt_circleContinuationSlope_tendsto_add_pi_div_two hδ ha
    hab hb hr hr₀ hr₁ (j := (j : ℕ)) (k := (j : ℕ) - n)
    (abs_add_mul_pi_sub_add_sub_mul_pi_add_lt hn _)
  refine ⟨Θ, hΘ, ?_⟩
  rw [circleCosTwoMin_def]
  exact_mod_cast tendsto_coe h₀

/-- **Existence of the trajectory arriving at a target maximum.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope`,
if moreover the path `r` is continuous on the window `[a, b]`, a trajectory arrives at every target
maximum. -/
theorem exists_hasDerivAt_circleContinuationSlope_tendsto_coe_circleCosTwoMax (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hr : ContinuousOn r (Icc a b))
    (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁) {n : ℤ}
    (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2) (k : Fin 2) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMax r₁ k)) := by
  obtain ⟨Θ, hΘ, -, h₁⟩ := exists_hasDerivAt_circleContinuationSlope_tendsto_add_int_mul_pi hδ ha
    hab hb hr hr₀ hr₁ (j := (k : ℕ) + n) (k := (k : ℕ))
    (abs_add_mul_pi_sub_add_add_mul_pi_add_lt hn _)
  refine ⟨Θ, hΘ, ?_⟩
  rw [circleCosTwoMax_def]
  exact_mod_cast tendsto_coe h₁

/-- **Uniqueness of the trajectory leaving a source minimum.** If the path `r` is constant, `r₀`
on `(0, a]`, two trajectories leaving the same source minimum `q_j(r₀)` have the same image in the
circle. -/
theorem eqOn_coe_of_tendsto_coe_circleCosTwoMin_of_hasDerivAt_circleContinuationSlope (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a < 1) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) {j : Fin 2}
    (h₁ : Tendsto (fun t ↦ (Θ₁ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)))
    (h₂ : Tendsto (fun t ↦ (Θ₂ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j))) :
    EqOn (fun t ↦ (Θ₁ t : AddCircle (2 * π))) (fun t ↦ (Θ₂ t : AddCircle (2 * π))) (Ioo 0 1) := by
  rw [circleCosTwoMin_def] at h₁ h₂
  obtain ⟨m₁, hm₁⟩ := exists_tendsto_nhdsGT_zero_of_tendsto_coe hΘ₁ h₁
  obtain ⟨m₂, hm₂⟩ := exists_tendsto_nhdsGT_zero_of_tendsto_coe hΘ₂ h₂
  -- Translate the second lift onto the first one, and apply uniqueness on the universal cover.
  have heq := eqOn_of_tendsto_nhdsGT_zero_of_hasDerivAt_circleContinuationSlope hδ ha ha1 hr₀ hΘ₁
    (hasDerivAt_add_int_mul_two_pi hΘ₂ (m₁ - m₂)) (j := (j : ℕ) + 2 * m₁)
    (by convert hm₁ using 2; push_cast; ring)
    (by convert hm₂.add_const (((m₁ - m₂ : ℤ) : ℝ) * (2 * π)) using 2; push_cast; ring)
  intro t ht
  simp only [heq ht, coe_add_int_mul_period]

/-- **Uniqueness of the trajectory arriving at a target maximum.** If the path `r` is constant,
`r₁` on `[b, 1)`, two trajectories arriving at the same target maximum `p_k(r₁)` have the same image
in the circle. -/
theorem eqOn_coe_of_tendsto_coe_circleCosTwoMax_of_hasDerivAt_circleContinuationSlope (hδ : 0 ≤ δ)
    (hb : 0 < b) (hb1 : b < 1) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
    (hΘ₁ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₁ (circleContinuationSlope δ r t (Θ₁ t)) t)
    (hΘ₂ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ₂ (circleContinuationSlope δ r t (Θ₂ t)) t) {k : Fin 2}
    (h₁ : Tendsto (fun t ↦ (Θ₁ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMax r₁ k)))
    (h₂ : Tendsto (fun t ↦ (Θ₂ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMax r₁ k))) :
    EqOn (fun t ↦ (Θ₁ t : AddCircle (2 * π))) (fun t ↦ (Θ₂ t : AddCircle (2 * π))) (Ioo 0 1) := by
  rw [circleCosTwoMax_def] at h₁ h₂
  obtain ⟨m₁, hm₁⟩ := exists_tendsto_nhdsLT_one_of_tendsto_coe hΘ₁ h₁
  obtain ⟨m₂, hm₂⟩ := exists_tendsto_nhdsLT_one_of_tendsto_coe hΘ₂ h₂
  -- Translate the second lift onto the first one, and apply uniqueness on the universal cover.
  have heq := eqOn_of_tendsto_nhdsLT_one_of_hasDerivAt_circleContinuationSlope hδ hb hb1 hr₁ hΘ₁
    (hasDerivAt_add_int_mul_two_pi hΘ₂ (m₁ - m₂)) (k := (k : ℕ) + 2 * m₁)
    (by convert hm₁ using 2; push_cast; ring)
    (by convert hm₂.add_const (((m₁ - m₂ : ℤ) : ℝ) * (2 * π)) using 2; push_cast; ring)
  intro t ht
  simp only [heq ht, coe_add_int_mul_period]

/-! ### The half-turn, the third-turns and their concatenation -/

section Examples

variable {ρ : ℝ → ℝ}

/-- A rotation `r₀ + c ρ` with `ρ = 0` for `t ≤ 1/3` is `r₀` on `(0, 1/6]`. -/
private theorem rotation_eq_left (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (c : ℝ) :
    ∀ t ∈ Ioc (0 : ℝ) (1 / 6), r₀ + c * ρ t = r₀ := fun t ht ↦ by
  rw [h0 t (by linarith [ht.2]), mul_zero, add_zero]

/-- A rotation `r₀ + c ρ` with `ρ = 1` for `t ≥ 2/3` is `r₀ + c` on `[5/6, 1)`. -/
private theorem rotation_eq_right (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (c : ℝ) :
    ∀ t ∈ Ico (5 / 6 : ℝ) 1, r₀ + c * ρ t = r₀ + c := fun t ht ↦ by
  rw [h1 t (by linarith [ht.1]), mul_one]

/-- **The half-turn: the identity in fixed bases, the exchange in tracked labels, on minima.** Let
`ρ` be `0` for `t ≤ 1/3` and `1` for `t ≥ 2/3`, and let `δ > 0` with
`2 δ ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt < π / 12`. For the path `r = r₀ + π ρ`, a trajectory leaving
the source minimum `q_j(r₀)` ends at the target minimum `q_k(r₀ + π)` exactly when `k = j + 1`. As
points of the circle `q_{j + 1}(r₀ + π) = q_j(r₀)` (`TauCeti.circleCosTwoMin_add_pi`), so in fixed
spatial bases the continuation is the identity; in the labels tracked along the path it is the
exchange of the two minima. -/
theorem tendsto_coe_circleCosTwoMin_add_pi_iff (h0 : ∀ t ≤ 1 / 3, ρ t = 0)
    (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hΘ : ∀ t ∈ Ioo 0 1,
      HasDerivAt Θ (circleContinuationSlope δ (fun t ↦ r₀ + π * ρ t) t (Θ t)) t) {j : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)))
    (k : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 (circleCosTwoMin (r₀ + π) k)) ↔
      k = j + 1 := by
  have hc : r₀ + π - r₀ - ((1 : ℤ) : ℝ) * π = 0 := by push_cast; ring
  rw [tendsto_coe_circleCosTwoMin_iff_of_hasDerivAt_circleContinuationSlope hδ
    (by norm_num) (by norm_num) (by norm_num) (rotation_eq_left h0 π) (rotation_eq_right h1 π) hΘ
    (by rw [hc, abs_zero]; linarith [pi_pos]) hlim, hc, coe_zero, add_zero,
    circleCosTwoMin_add_pi, circleCosTwoMin_inj]
  fin_cases j <;> fin_cases k <;> decide

/-- **The half-turn: the identity in fixed bases, the exchange in tracked labels, on maxima.**
Under the hypotheses of `TauCeti.tendsto_coe_circleCosTwoMin_add_pi_iff`, a trajectory
arriving at the target maximum `p_k(r₀ + π)` starts at the source maximum `p_j(r₀)` exactly when
`j = k + 1`, that is, at the same point of the circle
(`TauCeti.circleCosTwoMax_add_pi`). -/
theorem tendsto_coe_circleCosTwoMax_iff_of_add_pi (h0 : ∀ t ≤ 1 / 3, ρ t = 0)
    (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hΘ : ∀ t ∈ Ioo 0 1,
      HasDerivAt Θ (circleContinuationSlope δ (fun t ↦ r₀ + π * ρ t) t (Θ t)) t) {k : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1)
      (𝓝 (circleCosTwoMax (r₀ + π) k)))
    (j : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMax r₀ j)) ↔
      j = k + 1 := by
  have hc : r₀ + π - r₀ - ((1 : ℤ) : ℝ) * π = 0 := by push_cast; ring
  rw [tendsto_coe_circleCosTwoMax_iff_of_hasDerivAt_circleContinuationSlope hδ
    (by norm_num) (by norm_num) (by norm_num) (rotation_eq_left h0 π) (rotation_eq_right h1 π) hΘ
    (by rw [hc, abs_zero]; linarith [pi_pos]) hlim, hc, coe_zero, sub_zero,
    circleCosTwoMax_add_pi, circleCosTwoMax_inj]

/-- **A third of a turn agrees with the tracked labels, on minima.** Under the hypotheses on `ρ`
and `δ` of `TauCeti.tendsto_coe_circleCosTwoMin_add_pi_iff`, for the path
`r = r₀ + (π / 3) ρ`, a trajectory leaving the source minimum `q_j(r₀)` ends at the target minimum
`q_k(r₀ + π / 3)` exactly when `k = j`. -/
theorem tendsto_coe_circleCosTwoMin_add_pi_div_three_iff (h0 : ∀ t ≤ 1 / 3, ρ t = 0)
    (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hΘ : ∀ t ∈ Ioo 0 1,
      HasDerivAt Θ (circleContinuationSlope δ (fun t ↦ r₀ + π / 3 * ρ t) t (Θ t)) t) {j : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)))
    (k : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1)
        (𝓝 (circleCosTwoMin (r₀ + π / 3) k)) ↔ k = j := by
  have hc : r₀ + π / 3 - r₀ - ((0 : ℤ) : ℝ) * π = π / 3 := by push_cast; ring
  rw [tendsto_coe_circleCosTwoMin_iff_of_hasDerivAt_circleContinuationSlope hδ
    (by norm_num) (by norm_num) (by norm_num) (rotation_eq_left h0 _) (rotation_eq_right h1 _) hΘ
    (by rw [hc, abs_of_pos (by positivity)]; linarith [pi_pos]) hlim, hc,
    circleCosTwoMin_add_coe, circleCosTwoMin_inj]

/-- **A third of a turn agrees with the tracked labels, on maxima.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_pi_div_three_iff`, a trajectory arriving at the
target maximum `p_k(r₀ + π / 3)` starts at the source maximum `p_j(r₀)` exactly when `j = k`. -/
theorem tendsto_coe_circleCosTwoMax_iff_of_add_pi_div_three
    (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hΘ : ∀ t ∈ Ioo 0 1,
      HasDerivAt Θ (circleContinuationSlope δ (fun t ↦ r₀ + π / 3 * ρ t) t (Θ t)) t) {k : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1)
      (𝓝 (circleCosTwoMax (r₀ + π / 3) k)))
    (j : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMax r₀ j)) ↔
      j = k := by
  have hc : r₀ + π / 3 - r₀ - ((0 : ℤ) : ℝ) * π = π / 3 := by push_cast; ring
  rw [tendsto_coe_circleCosTwoMax_iff_of_hasDerivAt_circleContinuationSlope hδ
    (by norm_num) (by norm_num) (by norm_num) (rotation_eq_left h0 _) (rotation_eq_right h1 _) hΘ
    (by rw [hc, abs_of_pos (by positivity)]; linarith [pi_pos]) hlim, hc]
  simp [circleCosTwoMax_sub_coe]

/-- The concatenation of the third-turns `r₀ + (π / 3) ρ` and `r₀ + π / 3 + (π / 3) ρ`, run at
double speed on `[0, 1/2]` and `[1/2, 1]`, is `r₀` on `(0, 1/6]` and `r₀ + 2 π / 3` on
`[5/6, 1)`. -/
private theorem concat_rotation (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) :
    (∀ t ∈ Ioc (0 : ℝ) (1 / 6),
      (if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1)) = r₀) ∧
    ∀ t ∈ Ico (5 / 6 : ℝ) 1,
      (if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1)) =
        r₀ + 2 * π / 3 := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · simp only [show t ≤ 1 / 2 by linarith [ht.2], ↓reduceIte,
      h0 _ (by linarith [ht.2] : 2 * t ≤ 1 / 3), mul_zero, add_zero]
  · simp only [show ¬t ≤ 1 / 2 by linarith [ht.1], ↓reduceIte,
      h1 _ (by linarith [ht.1] : 2 / 3 ≤ 2 * t - 1)]
    ring

/-- **The concatenation of two third-turns is the exchange, on minima.** Under the hypotheses on `ρ`
and `δ` of `TauCeti.tendsto_coe_circleCosTwoMin_add_pi_iff`, for the concatenation of
the third-turns `Γ₁ = r₀ + (π / 3) ρ` and `Γ₂ = r₀ + π / 3 + (π / 3) ρ`, run at double speed on
`[0, 1/2]` and `[1/2, 1]`, a trajectory leaving the source minimum `q_j(r₀)` ends at the target
minimum `q_k(r₀ + 2 π / 3)` exactly when `k = j + 1`. Each third-turn agrees with the tracked labels
(`TauCeti.tendsto_coe_circleCosTwoMin_add_pi_div_three_iff`), but their concatenation
exchanges them. -/
theorem tendsto_coe_circleCosTwoMin_add_two_mul_pi_div_three_iff
    (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ (fun t ↦
      if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1)) t
        (Θ t)) t) {j : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMin r₀ j)))
    (k : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1)
        (𝓝 (circleCosTwoMin (r₀ + 2 * π / 3) k)) ↔ k = j + 1 := by
  obtain ⟨hr₀, hr₁⟩ := concat_rotation (r₀ := r₀) h0 h1
  have hc : r₀ + 2 * π / 3 - r₀ - ((1 : ℤ) : ℝ) * π = -(π / 3) := by push_cast; ring
  rw [tendsto_coe_circleCosTwoMin_iff_of_hasDerivAt_circleContinuationSlope hδ
    (by norm_num) (by norm_num) (by norm_num) hr₀ hr₁ hΘ
    (by rw [hc, abs_neg, abs_of_pos (by positivity)]; linarith [pi_pos]) hlim, hc,
    circleCosTwoMin_add_coe, show r₀ + 2 * π / 3 = r₀ + -(π / 3) + π by ring]
  simp only [circleCosTwoMin_add_pi, circleCosTwoMin_inj]
  fin_cases j <;> fin_cases k <;> decide

/-- **The concatenation of two third-turns is the exchange, on maxima.** Under the hypotheses of
`TauCeti.tendsto_coe_circleCosTwoMin_add_two_mul_pi_div_three_iff`, a trajectory arriving
at the target maximum `p_k(r₀ + 2 π / 3)` starts at the source maximum `p_j(r₀)` exactly when
`j = k + 1`. -/
theorem tendsto_coe_circleCosTwoMax_iff_of_add_two_mul_pi_div_three
    (h0 : ∀ t ≤ 1 / 3, ρ t = 0) (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
    (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ (fun t ↦
      if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1)) t
        (Θ t)) t) {k : Fin 2}
    (hlim : Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1)
      (𝓝 (circleCosTwoMax (r₀ + 2 * π / 3) k)))
    (j : Fin 2) :
    Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 (circleCosTwoMax r₀ j)) ↔
      j = k + 1 := by
  obtain ⟨hr₀, hr₁⟩ := concat_rotation (r₀ := r₀) h0 h1
  have hc : r₀ + 2 * π / 3 - r₀ - ((1 : ℤ) : ℝ) * π = -(π / 3) := by push_cast; ring
  rw [tendsto_coe_circleCosTwoMax_iff_of_hasDerivAt_circleContinuationSlope hδ
    (by norm_num) (by norm_num) (by norm_num) hr₀ hr₁ hΘ
    (by rw [hc, abs_neg, abs_of_pos (by positivity)]; linarith [pi_pos]) hlim, hc,
    circleCosTwoMax_sub_coe, show r₀ + 2 * π / 3 - -(π / 3) = r₀ + π by ring]
  simp

end Examples

end TauCeti
