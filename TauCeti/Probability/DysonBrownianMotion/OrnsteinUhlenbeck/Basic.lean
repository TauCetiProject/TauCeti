/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Probability.DysonBrownianMotion.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.HalfLinePrimitive
import TauCeti.Analysis.SpecialFunctions.Exp.Half
import TauCeti.Analysis.SpecialFunctions.Log.Basic

/-!
# The Ornstein–Uhlenbeck Dyson system and its exponential time change

The Ornstein–Uhlenbeck Dyson system adds the confining drift `-λᵢ / 2` to the Dyson system,
`dλᵢ = √(2 / (β n)) dBᵢ + (n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹ - λᵢ / 2) dt`. As for the Dyson system, the
noise is additive, so a solution driven by a forcing path `w` is the pathwise integral identity
`Y t i = x i + w t i + ∫ s in (0 : ℝ)..t, (dysonDrift n (Y s.toNNReal) i - Y s.toNNReal i / 2)`,
recorded by `IsDysonOUPath`.

Because `dysonDrift n` is homogeneous of degree `-1`, the deterministic time change
`Y t = e^{-t/2} X (e^t - 1)` (`ouTimeChange`) carries Dyson trajectories to Ornstein–Uhlenbeck
Dyson trajectories, and `X s = √(1 + s) Y (log (1 + s))` (`ouTimeChangeInv`) carries them back.
The forcing paths transform by `ouTimeChangeForcing` and `ouTimeChangeInvForcing`, the pathwise
integration-by-parts forms of `w 0 + ∫ e^{-u/2} dw(e^u - 1)` and
`w 0 + ∫ (1 + r)^{1/2} dw(log (1 + r))`; for continuous paths each undoes the other. So the
Ornstein–Uhlenbeck system is solved pathwise exactly by time-changed Dyson trajectories
(`isDysonOUPath_iff_isDysonPath_ouTimeChangeInv`, `isDysonPath_iff_isDysonOUPath_ouTimeChange`).
Existence and noncollision for the system driven by `w` therefore reduce pathwise to those of the
Dyson system driven by `ouTimeChangeInvForcing w`; each coordinate of that transformed forcing
of a Brownian motion is again a Brownian motion
(`TauCeti.Probability.isBrownianReal_ouTimeChangeInvForcing`, in
`TauCeti.Probability.DysonBrownianMotion.OrnsteinUhlenbeck.Forcing`). Uniqueness follows
outright.

Pathwise `ℓ²` contraction of the Dyson system becomes exponential contraction at rate `e^{-(t - s)}`
(`IsDysonOUPath.sum_sub_sq_le_of_le`), which gives pathwise and almost-sure uniqueness.

## Main declarations

* `TauCeti.Probability.IsDysonOUPath` and `TauCeti.Probability.IsDysonOUSolution`: pathwise and
  almost-sure solutions of the Ornstein–Uhlenbeck Dyson system.
* `TauCeti.Probability.ouTimeChange`, `TauCeti.Probability.ouTimeChangeInv`: the exponential time
  change and its inverse.
* `TauCeti.Probability.ouTimeChangeForcing`, `TauCeti.Probability.ouTimeChangeInvForcing`: the
  transformed forcing paths, with `ouTimeChangeForcing_ouTimeChangeInvForcing` and
  `ouTimeChangeInvForcing_ouTimeChangeForcing`.
* `TauCeti.Probability.IsDysonPath.isDysonOUPath_ouTimeChange` and
  `TauCeti.Probability.IsDysonOUPath.isDysonPath_ouTimeChangeInv`: the two time changes.
* `TauCeti.Probability.isDysonOUPath_iff_isDysonPath_ouTimeChangeInv` and
  `TauCeti.Probability.isDysonPath_iff_isDysonOUPath_ouTimeChange`: the characterizations.
* `TauCeti.Probability.IsDysonOUPath.sum_sub_sq_le_of_le`,
  `TauCeti.Probability.IsDysonOUPath.sum_sub_sq_le` and `TauCeti.Probability.IsDysonOUPath.eq`:
  exponential `ℓ²` contraction and pathwise uniqueness.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1 and the proof of Lemma 4.3.17.
* M. Potters, J.-P. Bouchaud, *A First Course in Random Matrix Theory*, Cambridge University
  Press, 2020, ch. 9.
-/

public section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-! ### Scalar time-change computations -/

/-- The Dyson drift along a continuous trajectory that is strictly decreasing at positive times is
continuous at every positive time. -/
private theorem continuousAt_dysonDrift_comp {n : ℕ} {Z : ℝ≥0 → Fin n → ℝ} (hZ : Continuous Z)
    (hsa : ∀ t : ℝ≥0, 0 < t → StrictAnti (Z t)) {r : ℝ} (hr : 0 < r) (i : Fin n) :
    ContinuousAt (fun s : ℝ ↦ dysonDrift n (Z s.toNNReal) i) r :=
  (continuous_apply i).continuousAt.comp <| ContinuousAt.comp
    (continuousAt_dysonDrift (hsa _ (Real.toNNReal_pos.2 hr)).injective)
    (hZ.comp continuous_real_toNNReal).continuousAt

/-- A coordinate of a continuous path, read along `Real.toNNReal`, is continuous. -/
private theorem continuous_apply_toNNReal {n : ℕ} {Z : ℝ≥0 → Fin n → ℝ} (hZ : Continuous Z)
    (i : Fin n) : Continuous fun s : ℝ ↦ Z s.toNNReal i :=
  ((continuous_apply i).comp hZ).comp continuous_real_toNNReal

/-- A coordinate of a continuous path, read at time `e^u - 1` and weighted by `e^{-u/2}`, is
continuous in `u`. -/
private theorem continuous_exp_neg_half_mul_comp {n : ℕ} {Z : ℝ≥0 → Fin n → ℝ}
    (hZ : Continuous Z) (i : Fin n) :
    Continuous fun u : ℝ ↦ Real.exp (-(u / 2)) * Z (Real.exp u - 1).toNNReal i :=
  (Real.continuous_exp.comp (continuous_id.div_const 2).neg).mul
    ((continuous_apply_toNNReal hZ i).comp (Real.continuous_exp.sub continuous_const))

/-- For `0 ≤ s`, the interval `[0, s]` lies in `[0, ∞)`. -/
private theorem uIcc_zero_subset_Ici {s : ℝ} (hs : 0 ≤ s) : uIcc 0 s ⊆ Ici (0 : ℝ) := by
  rw [uIcc_of_le hs]
  exact Icc_subset_Ici_self

/-- `u ↦ log (1 + u)` is continuous on `[0, ∞)`. -/
private theorem continuousOn_log_one_add : ContinuousOn (fun u : ℝ ↦ Real.log (1 + u)) (Ici 0) :=
  (continuousOn_const.add continuousOn_id).log fun u hu ↦
    (by linarith [mem_Ici.1 hu] : (0 : ℝ) < 1 + u).ne'

/-- `s ↦ log (1 + s)` is continuous on `ℝ≥0`. -/
private theorem continuous_log_one_add_coe : Continuous fun s : ℝ≥0 ↦ Real.log (1 + s) :=
  continuousOn_log_one_add.comp_continuous NNReal.continuous_coe fun s ↦ s.coe_nonneg

/-- The weight `g (log (1 + r)) / (2 √(1 + r))` of the inverse forcing is continuous on
`[0, ∞)`. -/
private theorem continuousOn_comp_log_one_add_div {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun r : ℝ ↦ g (Real.log (1 + r)) / (2 * √(1 + r))) (Ici 0) :=
  (hg.comp_continuousOn continuousOn_log_one_add).div
    (continuousOn_const.mul
      (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousOn)
    fun r hr ↦ (mul_pos two_pos (Real.sqrt_pos.2 (by linarith [mem_Ici.1 hr]))).ne'

/-- **Scalar core of the time changes.** Let `ξ r = x + ω r + ∫₀ʳ (D + b ξ)` on `[0, ∞)`, and let
`c`, `τ` be time-change data with `τ 0 = 0`. If the drift transforms by
`c (D ∘ τ + b ξ ∘ τ) τ' = E + (a c - c') ξ ∘ τ`, then `c ξ(τ ·)` satisfies the integral equation
with forcing `c ω(τ ·) - ∫ c' ω(τ ·)`, drift `E` and linear coefficient `a`. -/
private theorem mul_comp_eq_integral {c c' τ τ' D E ξ ω : ℝ → ℝ} {a b x t : ℝ} (ht : 0 ≤ t)
    (hc : ∀ u, 0 < u → HasDerivAt c (c' u) u) (hcc : ContinuousOn c (Ici 0))
    (hc'c : ContinuousOn c' (Ici 0))
    (hτ : ∀ u, 0 < u → HasDerivAt τ (τ' u) u) (hτc : ContinuousOn τ (Ici 0)) (hτ0 : τ 0 = 0)
    (hτpos : ∀ u, 0 < u → 0 < τ u) (hτmono : MonotoneOn τ (Ici 0))
    (hξc : ContinuousOn ξ (Ici 0)) (hωc : ContinuousOn ω (Ici 0))
    (hD : ∀ r, 0 < r → ContinuousAt D r) (hDint : ∀ r, 0 ≤ r → IntervalIntegrable D volume 0 r)
    (hξ : ∀ r, 0 ≤ r → ξ r = x + ω r + ∫ u in (0 : ℝ)..r, (D u + b * ξ u))
    (hE : ∀ u, 0 < u → ContinuousAt E u) (hEint : IntervalIntegrable E volume 0 t)
    (hrel : ∀ u, 0 < u →
      c u * (D (τ u) + b * ξ (τ u)) * τ' u = E u + (a * c u - c' u) * ξ (τ u)) :
    c t * ξ (τ t) = c 0 * x + (c t * ω (τ t) - ∫ u in (0 : ℝ)..t, c' u * ω (τ u)) +
      ∫ u in (0 : ℝ)..t, (E u + a * (c u * ξ (τ u))) := by
  -- Proof: with `P r = ∫₀ʳ (D + b ξ)`, the function
  -- `φ u = c u (x + P (τ u)) + ∫₀ᵘ c' ω(τ ·) - ∫₀ᵘ (E + a c ξ(τ ·))` is continuous on `[0, t]`,
  -- has derivative `0` on `(0, t)` by `hrel` and `hξ`, hence `φ t = φ 0 = c 0 x` by the mean
  -- value theorem. Integrability and continuity facts used in both steps come first.
  have hτmaps : MapsTo τ (Ici 0) (Ici 0) := fun u hu ↦ by
    have := hτmono (le_refl (0 : ℝ)) hu hu
    rwa [hτ0] at this
  have hGint (r : ℝ) (hr : 0 ≤ r) : IntervalIntegrable (fun u ↦ D u + b * ξ u) volume 0 r :=
    (hDint r hr).add
      (((hξc.mono (uIcc_zero_subset_Ici hr)).intervalIntegrable (μ := volume)).const_mul b)
  have hGat (r : ℝ) (hr : 0 < r) : ContinuousAt (fun u ↦ D u + b * ξ u) r :=
    (hD r hr).add (continuousAt_const.mul (hξc.continuousAt (Ici_mem_nhds hr)))
  have hPderiv (r : ℝ) (hr : 0 < r) :
      HasDerivAt (fun s ↦ ∫ u in (0 : ℝ)..s, (D u + b * ξ u)) (D r + b * ξ r) r :=
    intervalIntegral.integral_hasDerivAt_right (hGint r hr.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        (fun s hs ↦ (hGat s hs).continuousWithinAt) r hr) (hGat r hr)
  have hHc : ContinuousOn (fun u ↦ c' u * ω (τ u)) (Ici 0) := hc'c.mul (hωc.comp hτc hτmaps)
  have hLc : ContinuousOn (fun u ↦ a * (c u * ξ (τ u))) (Ici 0) :=
    continuousOn_const.mul (hcc.mul (hξc.comp hτc hτmaps))
  have hKat (u : ℝ) (hu : 0 < u) : ContinuousAt (fun v ↦ E v + a * (c v * ξ (τ v))) u :=
    (hE u hu).add (hLc.continuousAt (Ici_mem_nhds hu))
  have hKint (s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      IntervalIntegrable (fun v ↦ E v + a * (c v * ξ (τ v))) volume 0 s :=
    (hEint.mono_set (by rw [uIcc_of_le hs, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hst)).add
      (hLc.mono (uIcc_zero_subset_Ici hs)).intervalIntegrable
  have hξτ (u : ℝ) (hu : 0 ≤ u) :
      ξ (τ u) = x + ω (τ u) + ∫ v in (0 : ℝ)..τ u, (D v + b * ξ v) :=
    hξ (τ u) (hτmaps hu)
  -- The case `t = 0` is the initial condition `ξ 0 = x + ω 0`.
  rcases ht.eq_or_lt with rfl | htpos
  · rw [hτ0, hξ 0 le_rfl]
    simp
    ring
  -- Continuity of `φ` on `[0, t]`.
  have hφc : ContinuousOn (fun u ↦ c u * (x + ∫ v in (0 : ℝ)..τ u, (D v + b * ξ v)) +
      (∫ v in (0 : ℝ)..u, c' v * ω (τ v)) - ∫ v in (0 : ℝ)..u, (E v + a * (c v * ξ (τ v))))
      (Icc 0 t) := by
    have hτt : 0 ≤ τ t := (hτpos t htpos).le
    have hP := intervalIntegral.continuousOn_primitive_interval' (hGint (τ t) hτt) left_mem_uIcc
    have hPτ : ContinuousOn (fun u ↦ ∫ v in (0 : ℝ)..τ u, (D v + b * ξ v)) (Icc 0 t) :=
      hP.comp (hτc.mono Icc_subset_Ici_self) fun u hu ↦ by
        rw [uIcc_of_le hτt]
        exact ⟨hτmaps hu.1, hτmono hu.1 ht hu.2⟩
    have hH := intervalIntegral.continuousOn_primitive_interval'
      ((hHc.mono (uIcc_zero_subset_Ici ht)).intervalIntegrable (μ := volume)) left_mem_uIcc
    have hK := intervalIntegral.continuousOn_primitive_interval' (hKint t ht le_rfl) left_mem_uIcc
    rw [uIcc_of_le ht] at hH hK
    exact (((hcc.mono Icc_subset_Ici_self).mul (continuousOn_const.add hPτ)).add hH).sub hK
  -- `φ` has derivative `0` on `(0, t)`.
  have hφd (u : ℝ) (hu : u ∈ Ioo 0 t) : HasDerivAt (fun u ↦ c u * (x +
      ∫ v in (0 : ℝ)..τ u, (D v + b * ξ v)) + (∫ v in (0 : ℝ)..u, c' v * ω (τ v)) -
      ∫ v in (0 : ℝ)..u, (E v + a * (c v * ξ (τ v)))) 0 u := by
    have hu0 : 0 < u := hu.1
    have h1 : HasDerivAt (fun v ↦ c v * (x + ∫ w in (0 : ℝ)..τ v, (D w + b * ξ w)))
        (c' u * (x + ∫ w in (0 : ℝ)..τ u, (D w + b * ξ w)) +
          c u * ((D (τ u) + b * ξ (τ u)) * τ' u)) u :=
      (hc u hu0).mul (((hPderiv (τ u) (hτpos u hu0)).comp u (hτ u hu0)).const_add x)
    have h2 : HasDerivAt (fun v ↦ ∫ w in (0 : ℝ)..v, c' w * ω (τ w)) (c' u * ω (τ u)) u :=
      intervalIntegral.integral_hasDerivAt_right
        (hHc.mono (uIcc_zero_subset_Ici hu0.le)).intervalIntegrable
        ((hHc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi u hu0)
        (hHc.continuousAt (Ici_mem_nhds hu0))
    have h3 : HasDerivAt (fun v ↦ ∫ w in (0 : ℝ)..v, (E w + a * (c w * ξ (τ w))))
        (E u + a * (c u * ξ (τ u))) u :=
      intervalIntegral.integral_hasDerivAt_right (hKint u hu0.le hu.2.le)
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
          (fun v hv ↦ (hKat v hv).continuousWithinAt) u hu0) (hKat u hu0)
    convert (h1.add h2).sub h3 using 1
    linear_combination (-1 : ℝ) * hrel u hu0 + c' u * hξτ u hu0.le
  -- Mean value theorem.
  obtain ⟨u, -, hslope⟩ := exists_hasDerivAt_eq_slope _ (fun _ ↦ (0 : ℝ)) htpos hφc hφd
  have hφt := (div_eq_zero_iff.1 hslope.symm).resolve_right (sub_ne_zero.2 htpos.ne')
  simp only [hτ0, intervalIntegral.integral_same, add_zero, sub_zero] at hφt
  linear_combination c t * hξτ t ht + hφt

/-- `mul_comp_eq_integral` for the exponential time change `c u = e^{-u/2}`, `τ u = e^u - 1`,
which adds the linear drift `-ξ / 2`. -/
private theorem exp_comp_eq_integral {D E ξ ω : ℝ → ℝ} {x t : ℝ} (ht : 0 ≤ t)
    (hξc : ContinuousOn ξ (Ici 0)) (hωc : ContinuousOn ω (Ici 0))
    (hD : ∀ r, 0 < r → ContinuousAt D r) (hDint : ∀ r, 0 ≤ r → IntervalIntegrable D volume 0 r)
    (hξ : ∀ r, 0 ≤ r → ξ r = x + ω r + ∫ u in (0 : ℝ)..r, D u)
    (hE : ∀ u, 0 < u → ContinuousAt E u) (hEint : IntervalIntegrable E volume 0 t)
    (hrel : ∀ u, 0 < u → Real.exp (-(u / 2)) * D (Real.exp u - 1) * Real.exp u = E u) :
    Real.exp (-(t / 2)) * ξ (Real.exp t - 1) = x + (Real.exp (-(t / 2)) * ω (Real.exp t - 1) +
      ∫ u in (0 : ℝ)..t, Real.exp (-(u / 2)) * ω (Real.exp u - 1) / 2) +
      ∫ u in (0 : ℝ)..t, (E u - Real.exp (-(u / 2)) * ξ (Real.exp u - 1) / 2) := by
  have key := mul_comp_eq_integral (c := fun u ↦ Real.exp (-(u / 2)))
    (c' := fun u ↦ -(Real.exp (-(u / 2)) / 2)) (τ := fun u ↦ Real.exp u - 1) (τ' := Real.exp)
    (a := -(1 / 2)) (b := 0) ht
    (fun u _ ↦ by
      convert ((hasDerivAt_id' u).div_const 2).neg.exp using 1
      simp only [Pi.neg_apply]
      ring)
    (by fun_prop) (by fun_prop) (fun u _ ↦ (Real.hasDerivAt_exp u).sub_const 1) (by fun_prop)
    (by simp) (fun u hu ↦ by linarith [Real.add_one_lt_exp hu.ne'])
    (fun u _ v _ huv ↦ by dsimp only; gcongr) hξc hωc hD hDint
    (fun r hr ↦ by simpa using hξ r hr) hE hEint
    (fun u hu ↦ by linear_combination hrel u hu)
  have h1 : ∫ u in (0 : ℝ)..t, -(Real.exp (-(u / 2)) / 2) * ω (Real.exp u - 1) =
      -∫ u in (0 : ℝ)..t, Real.exp (-(u / 2)) * ω (Real.exp u - 1) / 2 := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun u _ ↦ by ring
  have h2 : ∫ u in (0 : ℝ)..t, (E u + -(1 / 2) * (Real.exp (-(u / 2)) * ξ (Real.exp u - 1))) =
      ∫ u in (0 : ℝ)..t, (E u - Real.exp (-(u / 2)) * ξ (Real.exp u - 1) / 2) :=
    intervalIntegral.integral_congr fun u _ ↦ by ring
  beta_reduce at key
  rw [key, h1, h2]
  simp

/-- `mul_comp_eq_integral` for the logarithmic time change `c u = √(1 + u)`, `τ u = log (1 + u)`,
which removes the linear drift `-ξ / 2`. -/
private theorem log_comp_eq_integral {D E ξ ω : ℝ → ℝ} {x t : ℝ} (ht : 0 ≤ t)
    (hξc : ContinuousOn ξ (Ici 0)) (hωc : ContinuousOn ω (Ici 0))
    (hD : ∀ r, 0 < r → ContinuousAt D r) (hDint : ∀ r, 0 ≤ r → IntervalIntegrable D volume 0 r)
    (hξ : ∀ r, 0 ≤ r → ξ r = x + ω r + ∫ u in (0 : ℝ)..r, (D u - ξ u / 2))
    (hE : ∀ u, 0 < u → ContinuousAt E u) (hEint : IntervalIntegrable E volume 0 t)
    (hrel : ∀ u, 0 < u → D (Real.log (1 + u)) = √(1 + u) * E u) :
    √(1 + t) * ξ (Real.log (1 + t)) = x + (√(1 + t) * ω (Real.log (1 + t)) -
      ∫ u in (0 : ℝ)..t, ω (Real.log (1 + u)) / (2 * √(1 + u))) + ∫ u in (0 : ℝ)..t, E u := by
  have key := mul_comp_eq_integral (c := fun u ↦ √(1 + u)) (c' := fun u ↦ 1 / (2 * √(1 + u)))
    (τ := fun u ↦ Real.log (1 + u)) (τ' := fun u ↦ 1 / (1 + u)) (a := 0) (b := -(1 / 2)) ht
    (fun u hu ↦ ((hasDerivAt_id' u).const_add 1).sqrt (by positivity)) (by fun_prop)
    (continuousOn_const.div (by fun_prop) fun u hu ↦
      (mul_pos two_pos (Real.sqrt_pos.2 (by linarith [mem_Ici.1 hu]))).ne')
    (fun u hu ↦ ((hasDerivAt_id' u).const_add 1).log (by positivity)) continuousOn_log_one_add
    (by simp) (fun u hu ↦ Real.log_pos (by linarith))
    (fun u hu v _ huv ↦ Real.log_le_log (by linarith [mem_Ici.1 hu]) (by linarith))
    hξc hωc hD hDint
    (fun r hr ↦ by
      rw [hξ r hr]
      congr 1
      exact intervalIntegral.integral_congr fun u _ ↦ by ring)
    hE hEint (fun u hu ↦ ?_)
  · have h1 : ∫ u in (0 : ℝ)..t, 1 / (2 * √(1 + u)) * ω (Real.log (1 + u)) =
        ∫ u in (0 : ℝ)..t, ω (Real.log (1 + u)) / (2 * √(1 + u)) :=
      intervalIntegral.integral_congr fun u _ ↦ by ring
    beta_reduce at key
    simp only [zero_mul, add_zero, Real.sqrt_one, one_mul, h1] at key
    exact key
  · rw [hrel u hu]
    have hs : 0 < √(1 + u) := Real.sqrt_pos.2 (by linarith)
    have hsq : 1 + u = √(1 + u) ^ 2 := (Real.sq_sqrt (by linarith)).symm
    generalize √(1 + u) = s at hs hsq ⊢
    rw [hsq]
    field_simp
    ring

/-- Integrability transfer along a monotone `C¹` time change `τ`, weighted by a continuous `c`. -/
private theorem intervalIntegrable_mul_deriv_mul_comp {c τ τ' S : ℝ → ℝ} {t R : ℝ} (ht : 0 ≤ t)
    (hτ : ∀ u ∈ Icc 0 t, HasDerivAt τ (τ' u) u) (hτ' : ∀ u ∈ Icc 0 t, 0 ≤ τ' u)
    (hinj : InjOn τ (Icc 0 t)) (hmaps : MapsTo τ (Icc 0 t) (uIcc 0 R))
    (hS : IntervalIntegrable S volume 0 R) (hc : ContinuousOn c (Icc 0 t)) :
    IntervalIntegrable (fun u ↦ c u * (τ' u * S (τ u))) volume 0 t := by
  have hSon : IntegrableOn S (τ '' Icc 0 t) :=
    ((intervalIntegrable_iff' (f := S) (μ := volume) (a := 0) (b := R)).1 hS).mono_set
      hmaps.image_subset
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (fun u hu ↦ (hτ u hu).hasDerivWithinAt) hinj S).1 hSon
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  refine (h.continuousOn_mul hc isCompact_Icc).congr_fun (fun u hu ↦ ?_) measurableSet_Icc
  simp [abs_of_nonneg (hτ' u hu)]

/-! ### The Ornstein–Uhlenbeck Dyson system -/

/-- **A deterministic Ornstein–Uhlenbeck Dyson trajectory** of `n` particles started at `x` and
driven by an additive forcing path `w`: `Y` is continuous, lies in the open decreasing Weyl chamber
at every strictly positive time, has locally integrable repulsion sums, and satisfies the Dyson
integral equation with the added confining drift `-Y / 2` coordinatewise. -/
structure IsDysonOUPath (n : ℕ) (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ)
    (Y : ℝ≥0 → Fin n → ℝ) : Prop where
  /-- The trajectory `Y` is continuous on `[0, ∞)`. -/
  continuous : Continuous Y
  /-- At every strictly positive time, the coordinates are strictly decreasing. -/
  strictAnti : ∀ t : ℝ≥0, 0 < t → StrictAnti (Y t)
  /-- Each coordinate's singular repulsion sum is interval-integrable on `[0, t]`. -/
  intervalIntegrable : ∀ (t : ℝ≥0) (i : Fin n),
    IntervalIntegrable
      (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i, (Y s.toNNReal i - Y s.toNNReal j)⁻¹) volume 0 t
  /-- Each coordinate satisfies the Ornstein–Uhlenbeck Dyson integral equation driven by `w`. -/
  eq_integral : ∀ (t : ℝ≥0) (i : Fin n),
    Y t i = x i + w t i + ∫ s in (0 : ℝ)..t, (dysonDrift n (Y s.toNNReal) i - Y s.toNNReal i / 2)

namespace IsDysonOUPath

variable {n : ℕ} {x y : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} {X Y : ℝ≥0 → Fin n → ℝ}

/-- **Absorbing the confining drift into the forcing.** An Ornstein–Uhlenbeck Dyson trajectory
driven by `w` is a Dyson trajectory driven by `w t - ∫₀ᵗ Y / 2`, so every `IsDysonPath` lemma
applies to it. -/
theorem isDysonPath (hY : IsDysonOUPath n x w Y) :
    IsDysonPath n x (fun t i ↦ w t i - ∫ s in (0 : ℝ)..t, Y s.toNNReal i / 2) Y where
  continuous := hY.continuous
  strictAnti := hY.strictAnti
  intervalIntegrable := hY.intervalIntegrable
  eq_integral t i := by
    rw [hY.eq_integral t i, intervalIntegral.integral_sub
      (by simpa only [dysonDrift_apply] using (hY.intervalIntegrable t i).const_mul (n : ℝ)⁻¹)
      (((continuous_apply_toNNReal hY.continuous i).div_const 2).intervalIntegrable 0 t)]
    ring

/-- Coordinatewise interval integrability of `dysonDrift` along an Ornstein–Uhlenbeck Dyson
trajectory. -/
theorem intervalIntegrable_dysonDrift (hY : IsDysonOUPath n x w Y) (t : ℝ≥0) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift n (Y s.toNNReal) i) volume 0 t :=
  hY.isDysonPath.intervalIntegrable_dysonDrift t i

/-- Value of an Ornstein–Uhlenbeck Dyson trajectory at time `0`. -/
theorem eval_zero (hY : IsDysonOUPath n x w Y) : Y 0 = x + w 0 :=
  funext fun i ↦ by simpa using hY.isDysonPath.eval_zero_apply i

/-- Every Ornstein–Uhlenbeck Dyson trajectory forces its driving path `w` to be continuous. -/
theorem continuous_driving (hY : IsDysonOUPath n x w Y) : Continuous w := by
  have hI : Continuous fun (t : ℝ≥0) (i : Fin n) ↦ ∫ s in (0 : ℝ)..t, Y s.toNNReal i / 2 :=
    continuous_pi fun i ↦ (intervalIntegral.continuous_primitive (fun a b ↦
      ((continuous_apply_toNNReal hY.continuous i).div_const 2).intervalIntegrable a b) 0).comp
        NNReal.continuous_coe
  convert hY.isDysonPath.continuous_driving.add hI using 1
  ext t i
  simp

end IsDysonOUPath

/-! ### The exponential time change -/

section TimeChange

variable {n : ℕ}

/-- **The exponential time change** `Y t = e^{-t/2} X (e^t - 1)`, which carries Dyson trajectories
to Ornstein–Uhlenbeck Dyson trajectories. -/
noncomputable def ouTimeChange (X : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) : Fin n → ℝ :=
  Real.exp (-((t : ℝ) / 2)) • X (Real.exp t - 1).toNNReal

/-- **The inverse exponential time change** `X s = √(1 + s) Y (log (1 + s))`, which carries
Ornstein–Uhlenbeck Dyson trajectories to Dyson trajectories. -/
noncomputable def ouTimeChangeInv (Y : ℝ≥0 → Fin n → ℝ) (s : ℝ≥0) : Fin n → ℝ :=
  √(1 + s) • Y (Real.log (1 + s)).toNNReal

/-- **Forcing of the exponential time change.** For a Dyson forcing path `w`, this is
`e^{-t/2} w (e^t - 1) + ∫₀ᵗ e^{-u/2} w (e^u - 1) / 2 du`, the pathwise integration-by-parts form
of `w 0 + ∫₀ᵗ e^{-u/2} d(w (e^u - 1)) = w 0 + ∫₀^{e^t - 1} (1 + r)^{-1/2} dw(r)`. -/
noncomputable def ouTimeChangeForcing (w : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) (i : Fin n) : ℝ :=
  Real.exp (-((t : ℝ) / 2)) * w (Real.exp t - 1).toNNReal i +
    ∫ u in (0 : ℝ)..t, Real.exp (-(u / 2)) * w (Real.exp u - 1).toNNReal i / 2

/-- **Forcing of the inverse exponential time change.** For an Ornstein–Uhlenbeck forcing path `w`,
this is `√(1 + s) w (log (1 + s)) - ∫₀ˢ w (log (1 + r)) / (2 √(1 + r)) dr`, the pathwise
integration-by-parts form of `w 0 + ∫₀ˢ √(1 + r) d(w (log (1 + r)))`. -/
noncomputable def ouTimeChangeInvForcing (w : ℝ≥0 → Fin n → ℝ) (s : ℝ≥0) (i : Fin n) : ℝ :=
  √(1 + s) * w (Real.log (1 + s)).toNNReal i -
    ∫ r in (0 : ℝ)..s, w (Real.log (1 + r)).toNNReal i / (2 * √(1 + r))

/-- Coordinate evaluation of `ouTimeChange`. -/
theorem ouTimeChange_apply (X : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) (i : Fin n) :
    ouTimeChange X t i = Real.exp (-((t : ℝ) / 2)) * X (Real.exp t - 1).toNNReal i :=
  (rfl)

/-- Coordinate evaluation of `ouTimeChangeInv`. -/
theorem ouTimeChangeInv_apply (Y : ℝ≥0 → Fin n → ℝ) (s : ℝ≥0) (i : Fin n) :
    ouTimeChangeInv Y s i = √(1 + s) * Y (Real.log (1 + s)).toNNReal i :=
  (rfl)

/-- Coordinate evaluation of `ouTimeChangeForcing`. -/
theorem ouTimeChangeForcing_apply (w : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) (i : Fin n) :
    ouTimeChangeForcing w t i = Real.exp (-((t : ℝ) / 2)) * w (Real.exp t - 1).toNNReal i +
      ∫ u in (0 : ℝ)..t, Real.exp (-(u / 2)) * w (Real.exp u - 1).toNNReal i / 2 :=
  (rfl)

/-- Coordinate evaluation of `ouTimeChangeInvForcing`. -/
theorem ouTimeChangeInvForcing_apply (w : ℝ≥0 → Fin n → ℝ) (s : ℝ≥0) (i : Fin n) :
    ouTimeChangeInvForcing w s i = √(1 + s) * w (Real.log (1 + s)).toNNReal i -
      ∫ r in (0 : ℝ)..s, w (Real.log (1 + r)).toNNReal i / (2 * √(1 + r)) :=
  (rfl)

/-- The inverse time change evaluated at `e^t - 1` is `e^{t/2}` times the original path at `t`. -/
theorem ouTimeChangeInv_exp_sub_one (Y : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) :
    ouTimeChangeInv Y (Real.exp t - 1).toNNReal = Real.exp ((t : ℝ) / 2) • Y t := by
  rw [ouTimeChangeInv, Real.coe_toNNReal_exp_sub_one t.coe_nonneg, add_sub_cancel, Real.log_exp,
    Real.toNNReal_coe, ← Real.exp_half]

/-- `ouTimeChange` is a left inverse of `ouTimeChangeInv`. -/
@[simp]
theorem ouTimeChange_ouTimeChangeInv (Y : ℝ≥0 → Fin n → ℝ) :
    ouTimeChange (ouTimeChangeInv Y) = Y := by
  ext t i
  rw [ouTimeChange_apply, ouTimeChangeInv_exp_sub_one, Pi.smul_apply, smul_eq_mul]
  linear_combination Y t i * Real.exp_half_mul_exp_neg_half t

/-- `ouTimeChangeInv` is a left inverse of `ouTimeChange`. -/
@[simp]
theorem ouTimeChangeInv_ouTimeChange (X : ℝ≥0 → Fin n → ℝ) :
    ouTimeChangeInv (ouTimeChange X) = X := by
  ext s i
  rw [ouTimeChangeInv_apply, ouTimeChange_apply, Real.coe_toNNReal_log_one_add s.coe_nonneg,
    Real.exp_log (by positivity), add_sub_cancel_left, Real.toNNReal_coe, ← mul_assoc,
    Real.sqrt_mul_exp_neg_half_log (by positivity), one_mul]

/-- The exponential time change of a continuous path is continuous. -/
theorem continuous_ouTimeChange {X : ℝ≥0 → Fin n → ℝ} (hX : Continuous X) :
    Continuous (ouTimeChange X) :=
  (Real.continuous_exp.comp (NNReal.continuous_coe.div_const 2).neg).smul
    (hX.comp (continuous_real_toNNReal.comp
      ((Real.continuous_exp.comp NNReal.continuous_coe).sub continuous_const)))

/-- The inverse exponential time change of a continuous path is continuous. -/
theorem continuous_ouTimeChangeInv {Y : ℝ≥0 → Fin n → ℝ} (hY : Continuous Y) :
    Continuous (ouTimeChangeInv Y) :=
  (Real.continuous_sqrt.comp (continuous_const.add NNReal.continuous_coe)).smul
    (hY.comp (continuous_real_toNNReal.comp continuous_log_one_add_coe))

/-- The forcing of a continuous path is continuous. -/
theorem continuous_ouTimeChangeForcing {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    Continuous (ouTimeChangeForcing w) := by
  refine continuous_pi fun i ↦ ?_
  have hg := continuous_exp_neg_half_mul_comp hw i
  exact (hg.comp NNReal.continuous_coe).add ((intervalIntegral.continuous_primitive
    (fun a b ↦ (hg.div_const 2).intervalIntegrable a b) 0).comp NNReal.continuous_coe)

/-- The inverse forcing of a continuous path is continuous. -/
theorem continuous_ouTimeChangeInvForcing {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    Continuous (ouTimeChangeInvForcing w) := by
  refine continuous_pi fun i ↦ ?_
  have hint : Continuous fun s : ℝ≥0 ↦
      ∫ r in (0 : ℝ)..s, w (Real.log (1 + r)).toNNReal i / (2 * √(1 + r)) :=
    ((continuous_halfLinePrimitive ((continuousOn_comp_log_one_add_div
      (continuous_apply_toNNReal hw i)).locallyIntegrableOn measurableSet_Ici)).comp
        NNReal.continuous_coe).congr fun s ↦
          halfLinePrimitive_eq_integral_of_nonneg s.coe_nonneg
  exact ((Real.continuous_sqrt.comp (continuous_const.add NNReal.continuous_coe)).mul
    ((continuous_apply_toNNReal hw i).comp continuous_log_one_add_coe)).sub hint

/-- The forcing transform commutes with scalar multiplication of `w`. -/
theorem ouTimeChangeForcing_const_mul (a : ℝ) (w : ℝ≥0 → Fin n → ℝ) :
    ouTimeChangeForcing (fun t i ↦ a * w t i) = fun t i ↦ a * ouTimeChangeForcing w t i := by
  ext t i
  simp only [ouTimeChangeForcing, mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · congr 1; ext u; ring

/-- The inverse forcing transform commutes with scalar multiplication of `w`. -/
theorem ouTimeChangeInvForcing_const_mul (a : ℝ) (w : ℝ≥0 → Fin n → ℝ) :
    ouTimeChangeInvForcing (fun t i ↦ a * w t i) = fun t i ↦ a * ouTimeChangeInvForcing w t i := by
  ext t i
  simp only [ouTimeChangeInvForcing, mul_sub, ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · congr 1; ext u; ring

/-- **The forward forcing transform undoes the inverse one.** For a continuous Ornstein–Uhlenbeck
forcing path `w`, transforming its inverse forcing forward recovers `w`. -/
theorem ouTimeChangeForcing_ouTimeChangeInvForcing {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    ouTimeChangeForcing (ouTimeChangeInvForcing w) = w := by
  ext t i
  have hf := continuous_apply_toNNReal (continuous_ouTimeChangeInvForcing hw) i
  have hwi := continuous_apply_toNNReal hw i
  have hg := continuousOn_comp_log_one_add_div hwi
  -- `ouTimeChangeInvForcing w` solves the drift-free equation with forcing
  -- `√(1 + r) w (log (1 + r))` and drift `-w (log (1 + r)) / (2 √(1 + r))`.
  have key := exp_comp_eq_integral (x := 0) (ξ := fun r ↦ ouTimeChangeInvForcing w r.toNNReal i)
    (ω := fun r ↦ √(1 + r) * w (Real.log (1 + r)).toNNReal i)
    (D := fun r ↦ -(w (Real.log (1 + r)).toNNReal i / (2 * √(1 + r))))
    (E := fun u ↦ -(w u.toNNReal i / 2)) t.coe_nonneg
    hf.continuousOn
    ((by fun_prop : Continuous fun r : ℝ ↦ √(1 + r)).continuousOn.mul
      (hwi.comp_continuousOn continuousOn_log_one_add))
    (fun r hr ↦ (hg.continuousAt (Ici_mem_nhds hr)).neg)
    (fun r hr ↦ ((hg.mono (uIcc_zero_subset_Ici hr)).intervalIntegrable (μ := volume)).neg)
    (fun r hr ↦ by
      simp only [ouTimeChangeInvForcing, Real.coe_toNNReal r hr, zero_add,
        intervalIntegral.integral_neg, sub_eq_add_neg])
    (fun u _ ↦ (hwi.div_const 2).neg.continuousAt)
    ((hwi.div_const 2).neg.intervalIntegrable (μ := volume) _ _) (fun u _ ↦ ?_)
  · beta_reduce at key
    simp only [add_sub_cancel, Real.log_exp, ← Real.exp_half, Real.toNNReal_coe, zero_add] at key
    have hA : Continuous fun u : ℝ ↦ -(w u.toNNReal i / 2) - Real.exp (-(u / 2)) *
        ouTimeChangeInvForcing w (Real.exp u - 1).toNNReal i / 2 :=
      (hwi.div_const 2).neg.sub
        ((continuous_exp_neg_half_mul_comp (continuous_ouTimeChangeInvForcing hw) i).div_const 2)
    have hB : Continuous fun u : ℝ ↦
        Real.exp (-(u / 2)) * (Real.exp (u / 2) * w u.toNNReal i) / 2 := by fun_prop
    have hsum : (∫ u in (0 : ℝ)..t,
        Real.exp (-(u / 2)) * (Real.exp (u / 2) * w u.toNNReal i) / 2) + (∫ u in (0 : ℝ)..t,
          (-(w u.toNNReal i / 2) - Real.exp (-(u / 2)) *
            ouTimeChangeInvForcing w (Real.exp u - 1).toNNReal i / 2)) =
        -∫ u in (0 : ℝ)..t,
          Real.exp (-(u / 2)) * ouTimeChangeInvForcing w (Real.exp u - 1).toNNReal i / 2 := by
      rw [← intervalIntegral.integral_add (hB.intervalIntegrable 0 t)
        (hA.intervalIntegrable 0 t), ← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun u _ ↦ by
        linear_combination w u.toNNReal i / 2 * Real.exp_half_mul_exp_neg_half u
    rw [ouTimeChangeForcing]
    linear_combination key + hsum + w t i * Real.exp_half_mul_exp_neg_half t
  · simp only [add_sub_cancel, Real.log_exp, ← Real.exp_half]
    rw [show ∀ A : ℝ, Real.exp (-(u / 2)) * A * Real.exp u = A * (Real.exp (-(u / 2)) *
      Real.exp u) from fun A ↦ by ring, Real.exp_neg_half_mul_exp]
    field_simp

/-- **The inverse forcing transform undoes the forward one.** For a continuous Dyson forcing path
`w`, transforming its forward forcing back recovers `w`. -/
theorem ouTimeChangeInvForcing_ouTimeChangeForcing {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    ouTimeChangeInvForcing (ouTimeChangeForcing w) = w := by
  ext t i
  have hf := continuous_apply_toNNReal (continuous_ouTimeChangeForcing hw) i
  have hω := continuous_exp_neg_half_mul_comp hw i
  have hωL := continuousOn_comp_log_one_add_div hω
  have hfL := continuousOn_comp_log_one_add_div hf
  have hIcc := uIcc_zero_subset_Ici t.coe_nonneg
  -- `ouTimeChangeForcing w` solves the equation with forcing `e^{-r/2} w (e^r - 1)`, linear drift
  -- `-ξ / 2` and drift `D r = e^{-r/2} w (e^r - 1) / 2 + ξ r / 2`.
  have key := log_comp_eq_integral (x := 0) (ξ := fun r ↦ ouTimeChangeForcing w r.toNNReal i)
    (ω := fun r ↦ Real.exp (-(r / 2)) * w (Real.exp r - 1).toNNReal i)
    (D := fun r ↦ Real.exp (-(r / 2)) * w (Real.exp r - 1).toNNReal i / 2 +
      ouTimeChangeForcing w r.toNNReal i / 2)
    (E := fun u ↦ (Real.exp (-(Real.log (1 + u) / 2)) *
      w (Real.exp (Real.log (1 + u)) - 1).toNNReal i +
        ouTimeChangeForcing w (Real.log (1 + u)).toNNReal i) / (2 * √(1 + u)))
    t.coe_nonneg hf.continuousOn hω.continuousOn
    (fun r _ ↦ ((hω.div_const 2).add (hf.div_const 2)).continuousAt)
    (fun r _ ↦ ((hω.div_const 2).add (hf.div_const 2)).intervalIntegrable _ _)
    (fun r hr ↦ by
      rw [ouTimeChangeForcing, Real.coe_toNNReal r hr, zero_add]
      congr 1
      exact intervalIntegral.integral_congr fun u _ ↦ by ring)
    (fun u hu ↦ (continuousOn_comp_log_one_add_div (hω.add hf)).continuousAt (Ici_mem_nhds hu))
    (((continuousOn_comp_log_one_add_div (hω.add hf)).mono hIcc).intervalIntegrable)
    (fun u hu ↦ by
      have := Real.sqrt_pos.2 (by linarith : (0 : ℝ) < 1 + u)
      field_simp)
  beta_reduce at key
  have hsplit := intervalIntegral.integral_add ((hωL.mono hIcc).intervalIntegrable (μ := volume))
    ((hfL.mono hIcc).intervalIntegrable (μ := volume))
  simp only [← add_div] at hsplit
  have hwt : (Real.exp (Real.log (1 + t)) - 1).toNNReal = t := by
    simp [Real.exp_log (by positivity : (0 : ℝ) < 1 + t)]
  rw [hwt] at key
  rw [ouTimeChangeInvForcing]
  linear_combination key + hsplit +
    w t i * Real.sqrt_mul_exp_neg_half_log (by positivity : (0 : ℝ) < 1 + t)

end TimeChange

/-! ### Time changes between Dyson and Ornstein–Uhlenbeck Dyson trajectories -/

section Paths

variable {n : ℕ} {x : Fin n → ℝ}

/-- Integrability of the repulsion sums is preserved by the exponential time change. -/
private theorem intervalIntegrable_sum_inv_ouTimeChange {X : ℝ≥0 → Fin n → ℝ}
    (hX : ∀ (t : ℝ≥0) (i : Fin n), IntervalIntegrable
      (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i, (X s.toNNReal i - X s.toNNReal j)⁻¹) volume 0 t)
    (t : ℝ≥0) (i : Fin n) : IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
      (ouTimeChange X s.toNNReal i - ouTimeChange X s.toNNReal j)⁻¹) volume 0 t := by
  have hS := hX (Real.exp t - 1).toNNReal i
  rw [Real.coe_toNNReal_exp_sub_one t.coe_nonneg] at hS
  refine (intervalIntegrable_mul_deriv_mul_comp (c := fun u ↦ Real.exp (-(u / 2)))
    (τ := fun u ↦ Real.exp u - 1) t.coe_nonneg (fun u _ ↦ (Real.hasDerivAt_exp u).sub_const 1)
    (fun u _ ↦ (Real.exp_pos u).le)
    (fun u _ v _ huv ↦ Real.exp_injective (sub_left_injective huv))
    (fun u hu ↦ by
      rw [uIcc_of_le (sub_nonneg.2 (Real.one_le_exp t.coe_nonneg))]
      exact ⟨sub_nonneg.2 (Real.one_le_exp hu.1), by dsimp only; gcongr; exact hu.2⟩)
    hS (by fun_prop)).congr_uIoo fun u hu ↦ ?_
  rw [uIoo_of_le t.coe_nonneg] at hu
  simp only [ouTimeChange_apply, Real.coe_toNNReal u hu.1.le, ← mul_sub, mul_inv,
    ← Finset.mul_sum]
  rw [← mul_assoc, Real.exp_neg_half_mul_exp, Real.exp_neg, inv_inv]

/-- Integrability of the repulsion sums is preserved by the inverse exponential time change. -/
private theorem intervalIntegrable_sum_inv_ouTimeChangeInv {Y : ℝ≥0 → Fin n → ℝ}
    (hY : ∀ (t : ℝ≥0) (i : Fin n), IntervalIntegrable
      (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i, (Y s.toNNReal i - Y s.toNNReal j)⁻¹) volume 0 t)
    (t : ℝ≥0) (i : Fin n) : IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
      (ouTimeChangeInv Y s.toNNReal i - ouTimeChangeInv Y s.toNNReal j)⁻¹) volume 0 t := by
  have hS := hY (Real.log (1 + t)).toNNReal i
  rw [Real.coe_toNNReal_log_one_add t.coe_nonneg] at hS
  refine (intervalIntegrable_mul_deriv_mul_comp (c := fun u ↦ √(1 + u))
    (τ := fun u ↦ Real.log (1 + u)) (τ' := fun u ↦ 1 / (1 + u)) t.coe_nonneg
    (fun u hu ↦ ((hasDerivAt_id' u).const_add 1).log (by linarith [hu.1]))
    (fun u hu ↦ by have := hu.1; positivity)
    (fun u hu v hv huv ↦ by
      have := Real.log_injOn_pos (mem_Ioi.2 (by linarith [hu.1] : (0 : ℝ) < 1 + u))
        (mem_Ioi.2 (by linarith [hv.1] : (0 : ℝ) < 1 + v)) huv
      linarith)
    (fun u hu ↦ by
      rw [uIcc_of_le (Real.log_nonneg (by linarith [t.coe_nonneg]))]
      exact ⟨Real.log_nonneg (by linarith [hu.1]),
        Real.log_le_log (by linarith [hu.1]) (by linarith [hu.2])⟩)
    hS (by fun_prop)).congr_uIoo fun u hu ↦ ?_
  rw [uIoo_of_le t.coe_nonneg] at hu
  simp only [ouTimeChangeInv_apply, Real.coe_toNNReal u hu.1.le, ← mul_sub, mul_inv,
    ← Finset.mul_sum]
  rw [← mul_assoc, mul_one_div, Real.sqrt_div_self]

/-- **Dyson trajectories time-change to Ornstein–Uhlenbeck Dyson trajectories.** If `X` is a Dyson
trajectory driven by `w`, then `e^{-t/2} X (e^t - 1)` is an Ornstein–Uhlenbeck Dyson trajectory
from the same start, driven by `ouTimeChangeForcing w`. -/
theorem IsDysonPath.isDysonOUPath_ouTimeChange {w X : ℝ≥0 → Fin n → ℝ}
    (hX : IsDysonPath n x w X) : IsDysonOUPath n x (ouTimeChangeForcing w) (ouTimeChange X) := by
  have hY (u : ℝ) (hu : 0 ≤ u) :
      ouTimeChange X u.toNNReal = Real.exp (-(u / 2)) • X (Real.exp u - 1).toNNReal := by
    rw [ouTimeChange, Real.coe_toNNReal u hu]
  have hcont : Continuous (ouTimeChange X) := continuous_ouTimeChange hX.continuous
  have hsa (t : ℝ≥0) (ht : 0 < t) : StrictAnti (ouTimeChange X t) := fun i j hij ↦ by
    simp only [ouTimeChange_apply]
    refine mul_lt_mul_of_pos_left (hX.strictAnti _ (Real.toNNReal_pos.2 ?_) hij) (Real.exp_pos _)
    linarith [Real.add_one_lt_exp (NNReal.coe_pos.2 ht).ne', NNReal.coe_pos.2 ht]
  have hint := intervalIntegrable_sum_inv_ouTimeChange hX.intervalIntegrable
  refine ⟨hcont, hsa, hint, fun t i ↦ ?_⟩
  have key := exp_comp_eq_integral (x := x i) (D := fun r ↦ dysonDrift n (X r.toNNReal) i)
    (E := fun u ↦ dysonDrift n (ouTimeChange X u.toNNReal) i) (ξ := fun r ↦ X r.toNNReal i)
    (ω := fun r ↦ w r.toNNReal i) t.coe_nonneg
    (continuous_apply_toNNReal hX.continuous i).continuousOn
    (continuous_apply_toNNReal hX.continuous_driving i).continuousOn
    (fun r hr ↦ continuousAt_dysonDrift_comp hX.continuous hX.strictAnti hr i)
    (fun r hr ↦ by
      simpa [Real.coe_toNNReal r hr] using hX.intervalIntegrable_dysonDrift r.toNNReal i)
    (fun r hr ↦ by simpa [Real.coe_toNNReal r hr] using hX.eq_integral r.toNNReal i)
    (fun u hu ↦ continuousAt_dysonDrift_comp hcont hsa hu i)
    (by simpa only [dysonDrift_apply] using (hint t i).const_mul (n : ℝ)⁻¹) (fun u hu ↦ ?_)
  · beta_reduce at key
    rw [ouTimeChange_apply, ouTimeChangeForcing, key]
    congr 1
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    simp only [hY s hs.1, Pi.smul_apply, smul_eq_mul]
  · simp only [hY u hu.le, dysonDrift_smul, Pi.smul_apply, smul_eq_mul, ← Real.exp_neg, neg_neg]
    linear_combination dysonDrift n (X (Real.exp u - 1).toNNReal) i * Real.exp_neg_half_mul_exp u

/-- **Ornstein–Uhlenbeck Dyson trajectories time-change to Dyson trajectories.** If `Y` is an
Ornstein–Uhlenbeck Dyson trajectory driven by `w`, then `√(1 + s) Y (log (1 + s))` is a Dyson
trajectory from the same start, driven by `ouTimeChangeInvForcing w`. -/
theorem IsDysonOUPath.isDysonPath_ouTimeChangeInv {w Y : ℝ≥0 → Fin n → ℝ}
    (hY : IsDysonOUPath n x w Y) :
    IsDysonPath n x (ouTimeChangeInvForcing w) (ouTimeChangeInv Y) := by
  have hX (s : ℝ) (hs : 0 ≤ s) :
      ouTimeChangeInv Y s.toNNReal = √(1 + s) • Y (Real.log (1 + s)).toNNReal := by
    rw [ouTimeChangeInv, Real.coe_toNNReal s hs]
  have hcont : Continuous (ouTimeChangeInv Y) := continuous_ouTimeChangeInv hY.continuous
  have hsa (t : ℝ≥0) (ht : 0 < t) : StrictAnti (ouTimeChangeInv Y t) := fun i j hij ↦ by
    simp only [ouTimeChangeInv_apply]
    refine mul_lt_mul_of_pos_left
      (hY.strictAnti _ (Real.toNNReal_pos.2 (Real.log_pos ?_)) hij) (Real.sqrt_pos.2 ?_)
    · linarith [NNReal.coe_pos.2 ht]
    · positivity
  have hint := intervalIntegrable_sum_inv_ouTimeChangeInv hY.intervalIntegrable
  refine ⟨hcont, hsa, hint, fun t i ↦ ?_⟩
  have key := log_comp_eq_integral (x := x i) (D := fun r ↦ dysonDrift n (Y r.toNNReal) i)
    (E := fun u ↦ dysonDrift n (ouTimeChangeInv Y u.toNNReal) i) (ξ := fun r ↦ Y r.toNNReal i)
    (ω := fun r ↦ w r.toNNReal i) t.coe_nonneg
    (continuous_apply_toNNReal hY.continuous i).continuousOn
    (continuous_apply_toNNReal hY.continuous_driving i).continuousOn
    (fun r hr ↦ continuousAt_dysonDrift_comp hY.continuous hY.strictAnti hr i)
    (fun r hr ↦ by
      simpa [Real.coe_toNNReal r hr] using hY.intervalIntegrable_dysonDrift r.toNNReal i)
    (fun r hr ↦ by
      have := hY.eq_integral r.toNNReal i
      rwa [Real.coe_toNNReal r hr] at this)
    (fun u hu ↦ continuousAt_dysonDrift_comp hcont hsa hu i)
    (by simpa only [dysonDrift_apply] using (hint t i).const_mul (n : ℝ)⁻¹) (fun u hu ↦ ?_)
  · exact key
  · have hs : 0 < √(1 + u) := Real.sqrt_pos.2 (by linarith)
    simp only [hX u hu.le, dysonDrift_smul, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- **Ornstein–Uhlenbeck Dyson trajectories are exactly time-changed Dyson trajectories.** For a
continuous forcing path `w`, `Y` solves the Ornstein–Uhlenbeck Dyson system driven by `w` if and
only if its inverse time change solves the Dyson system driven by `ouTimeChangeInvForcing w`. -/
theorem isDysonOUPath_iff_isDysonPath_ouTimeChangeInv {w Y : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    IsDysonOUPath n x w Y ↔ IsDysonPath n x (ouTimeChangeInvForcing w) (ouTimeChangeInv Y) := by
  refine ⟨IsDysonOUPath.isDysonPath_ouTimeChangeInv, fun h ↦ ?_⟩
  simpa [ouTimeChangeForcing_ouTimeChangeInvForcing hw] using h.isDysonOUPath_ouTimeChange

/-- **Dyson trajectories are exactly time-changed Ornstein–Uhlenbeck Dyson trajectories.** For a
continuous forcing path `w`, `X` solves the Dyson system driven by `w` if and only if its
exponential time change solves the Ornstein–Uhlenbeck Dyson system driven by
`ouTimeChangeForcing w`. -/
theorem isDysonPath_iff_isDysonOUPath_ouTimeChange {w X : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    IsDysonPath n x w X ↔ IsDysonOUPath n x (ouTimeChangeForcing w) (ouTimeChange X) := by
  refine ⟨IsDysonPath.isDysonOUPath_ouTimeChange, fun h ↦ ?_⟩
  simpa [ouTimeChangeInvForcing_ouTimeChangeForcing hw] using h.isDysonPath_ouTimeChangeInv

namespace IsDysonOUPath

variable {y : Fin n → ℝ} {w X Y : ℝ≥0 → Fin n → ℝ}

/-- **Exponential pathwise `ℓ²` contraction.** Two Ornstein–Uhlenbeck Dyson trajectories driven by
the same path `w` approach each other at rate `e^{-(t - s)}` in squared Euclidean distance between
times `s ≤ t`. -/
theorem sum_sub_sq_le_of_le (hX : IsDysonOUPath n x w X) (hY : IsDysonOUPath n y w Y)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ i : Fin n, (X t i - Y t i) ^ 2 ≤
      Real.exp (-((t : ℝ) - s)) * ∑ i : Fin n, (X s i - Y s i) ^ 2 := by
  have h := hX.isDysonPath_ouTimeChangeInv.sum_sub_sq_le_of_le hY.isDysonPath_ouTimeChangeInv
    (Real.toNNReal_le_toNNReal (by gcongr) :
      (Real.exp s - 1).toNNReal ≤ (Real.exp t - 1).toNNReal)
  have he (u : ℝ) : Real.exp (u / 2) ^ 2 = Real.exp u := by rw [sq, Real.exp_half_mul_exp_half]
  simp only [ouTimeChangeInv_exp_sub_one, Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_pow,
    ← Finset.mul_sum, he] at h
  have hts : Real.exp t * Real.exp (-((t : ℝ) - s)) = Real.exp s := by
    rw [← Real.exp_add]
    ring_nf
  refine le_of_mul_le_mul_left ?_ (Real.exp_pos t)
  rw [← mul_assoc, hts]
  linarith

/-- **Exponential pathwise `ℓ²` contraction from the start.** Two Ornstein–Uhlenbeck Dyson
trajectories driven by the same path `w` approach each other at rate `e^{-t}` in squared Euclidean
distance. -/
theorem sum_sub_sq_le (hX : IsDysonOUPath n x w X) (hY : IsDysonOUPath n y w Y) (t : ℝ≥0) :
    ∑ i : Fin n, (X t i - Y t i) ^ 2 ≤ Real.exp (-(t : ℝ)) * ∑ i : Fin n, (x i - y i) ^ 2 := by
  simpa [hX.eval_zero, hY.eval_zero] using hX.sum_sub_sq_le_of_le hY _root_.zero_le

/-- **Pathwise uniqueness.** Two Ornstein–Uhlenbeck Dyson trajectories started at the same
configuration and driven by the same forcing path are identical. -/
theorem eq (hX : IsDysonOUPath n x w X) (hY : IsDysonOUPath n x w Y) : X = Y := by
  have h := congrArg ouTimeChange (hX.isDysonPath_ouTimeChangeInv.eq hY.isDysonPath_ouTimeChangeInv)
  simpa using h

end IsDysonOUPath

end Paths

/-! ### Measure-level Ornstein–Uhlenbeck Dyson solutions -/

section MeasureLevel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A pathwise solution of the `n`-particle Ornstein–Uhlenbeck Dyson system** with parameter `β`
started at `x` and driven by `B` under `P`: almost every sample path is an `IsDysonOUPath` driven
by `√(2 / (β n)) B`. Adaptedness to a filtration is not part of this predicate. -/
def IsDysonOUSolution (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsDysonOUPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ Y t ω)

variable {β : ℝ} {n : ℕ} {x y : Fin n → ℝ} {P : Measure Ω} {B : Fin n → ℝ≥0 → Ω → ℝ}
  {X Y : ℝ≥0 → Ω → Fin n → ℝ}

/-- Definitional unfolding of `IsDysonOUSolution` in terms of `IsDysonOUPath`. -/
theorem isDysonOUSolution_def :
    IsDysonOUSolution β n x P B Y ↔
      ∀ᵐ ω ∂P, IsDysonOUPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ Y t ω) :=
  Iff.rfl

/-- Explicit expanded form of `IsDysonOUSolution` in terms of sample-path continuity, strictly
decreasing coordinates (`StrictAnti`) at positive times, drift integrability, and the coordinatewise
integral equation with the confining drift. -/
theorem isDysonOUSolution_iff :
    IsDysonOUSolution β n x P B Y ↔
      ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) ∧ (∀ t, 0 < t → StrictAnti (Y t ω)) ∧
        ∀ (t : ℝ≥0) (i : Fin n),
          IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ Finset.univ.erase i,
            (Y s.toNNReal ω i - Y s.toNNReal ω j)⁻¹) volume 0 t ∧
          Y t ω i = x i + Real.sqrt (2 / (β * n)) * B i t ω +
            ∫ s in (0 : ℝ)..t, ((n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
              (Y s.toNNReal ω i - Y s.toNNReal ω j)⁻¹ - Y s.toNNReal ω i / 2) := by
  refine eventually_congr (.of_forall fun _ ↦ ⟨fun h ↦ ⟨h.continuous, h.strictAnti, fun t i ↦
    ⟨h.intervalIntegrable t i, ?_⟩⟩, fun ⟨hc, hsa, hi⟩ ↦ ⟨hc, hsa, fun t i ↦ (hi t i).1,
      fun t i ↦ ?_⟩⟩)
  · simpa [dysonDrift_apply] using h.eq_integral t i
  · simpa [dysonDrift_apply] using (hi t i).2

/-- Almost every sample path of an `IsDysonOUSolution` is a deterministic `IsDysonOUPath`. -/
theorem IsDysonOUSolution.ae_isDysonOUPath (hY : IsDysonOUSolution β n x P B Y) :
    ∀ᵐ ω ∂P, IsDysonOUPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ Y t ω) :=
  hY

/-- Congruence of `IsDysonOUSolution` under indistinguishable modifications of the driving process
`B` and the solution process `X`. -/
theorem IsDysonOUSolution.congr {B' : Fin n → ℝ≥0 → Ω → ℝ} (hX : IsDysonOUSolution β n x P B X)
    (hB : ∀ i, ∀ᵐ ω ∂P, ∀ t, B i t ω = B' i t ω) (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    IsDysonOUSolution β n x P B' Y := by
  filter_upwards [hX, ae_all_iff.2 hB, hXY] with ω hω hωB hωX
  have hB_eq : (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) =
      fun t i ↦ Real.sqrt (2 / (β * n)) * B' i t ω := by
    ext t i; rw [hωB i t]
  rwa [← hB_eq, ← funext hωX]

/-- **Almost-sure pathwise uniqueness for `IsDysonOUSolution`.** -/
theorem IsDysonOUSolution.ae_eq (hX : IsDysonOUSolution β n x P B X)
    (hY : IsDysonOUSolution β n x P B Y) : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [hX, hY] with _ hωX hωY
  exact congrFun (hωX.eq hωY)

/-- Almost-sure exponential `ℓ²` contraction for solutions driven by the same process `B`. -/
theorem IsDysonOUSolution.ae_sum_sub_sq_le (hX : IsDysonOUSolution β n x P B X)
    (hY : IsDysonOUSolution β n y P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∑ i : Fin n, (X t ω i - Y t ω i) ^ 2 ≤
      Real.exp (-(t : ℝ)) * ∑ i : Fin n, (x i - y i) ^ 2 := by
  filter_upwards [hX, hY] with _ hωX hωY t
  exact hωX.sum_sub_sq_le hωY t

/-- **Dyson solutions time-change to Ornstein–Uhlenbeck Dyson solutions**, driven by the
transformed process `ouTimeChangeForcing B`. -/
theorem IsDysonSolution.isDysonOUSolution_ouTimeChange (hX : IsDysonSolution β n x P B X) :
    IsDysonOUSolution β n x P (fun i t ω ↦ ouTimeChangeForcing (fun s j ↦ B j s ω) t i)
      (fun t ω ↦ ouTimeChange (fun s ↦ X s ω) t) := by
  filter_upwards [isDysonSolution_def.1 hX] with ω hω
  simpa [ouTimeChangeForcing_const_mul] using hω.isDysonOUPath_ouTimeChange

/-- **Ornstein–Uhlenbeck Dyson solutions time-change to Dyson solutions**, driven by the
transformed process `ouTimeChangeInvForcing B`. -/
theorem IsDysonOUSolution.isDysonSolution_ouTimeChangeInv (hY : IsDysonOUSolution β n x P B Y) :
    IsDysonSolution β n x P (fun i t ω ↦ ouTimeChangeInvForcing (fun s j ↦ B j s ω) t i)
      (fun t ω ↦ ouTimeChangeInv (fun s ↦ Y s ω) t) := by
  rw [isDysonSolution_def]
  filter_upwards [hY] with ω hω
  simpa [ouTimeChangeInvForcing_const_mul] using hω.isDysonPath_ouTimeChangeInv

end MeasureLevel

end TauCeti.Probability
