/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Probability.Dyson.Drift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.Deriv.PositivePart
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pathwise Dyson trajectories, `IsDysonSolution`, comparison, and uniqueness

Because the Brownian forcing in Dyson Brownian motion is additive, the stochastic differential
equation
`dXᵢ(t) = √(2 / (β n)) dBᵢ(t) + n⁻¹ ∑_{j ≠ i} (Xᵢ(t) - Xⱼ(t))⁻¹ dt`
admits a pathwise integral formulation requiring no stochastic integral (AGZ §4.3.1): almost every
sample path `t ↦ X t ω` is continuous on `ℝ≥0`, lies in the open decreasing chamber `{x₁ > ⋯ > xₙ}`
at all positive times, has locally integrable pairwise inverse gaps, and satisfies the integral
identity on `[0, t]`.

When two Dyson trajectories `γ₁` and `γ₂` are driven by the same additive forcing path `w` (with no
regularity assumption on `w`), their difference `γ₁ - γ₂` cancels `w` identically and is
differentiable on `(0, ∞)` with derivative `dysonDrift n (γ₁ u) - dysonDrift n (γ₂ u)`. Combining
the positive-part chain rule `HasDerivAt.max_zero_pow` with the open-chamber dissipativity
inequality `sum_sub_dysonDrift_mul_max_sub_nonpos` shows that `t ↦ ∑ᵢ max (γ₁ t i - γ₂ t i) 0 ^ 2`
is antitone on `ℝ≥0`. This yields in turn:

* coordinatewise order comparison `x ≤ y → γ₁ t ≤ γ₂ t` (AGZ Lemma 4.3.6);
* `ℓ²`-contraction `∑ᵢ (γ₁ t i - γ₂ t i)² ≤ ∑ᵢ (xᵢ - yᵢ)²` and continuous dependence on the initial
  configuration (AGZ Proposition 4.3.5);
* unconditional pathwise uniqueness `IsDysonPath.eq` and `IsDysonSolution.ae_eq` for all `β`, `n`,
  `x`, `P`, and `B`, including coincident initial coordinates.

We also construct explicit solutions for `n ≤ 1` (pure additive forcing) and for the deterministic
two-particle system from any `Antitone` initial configuration `x : Fin 2 → ℝ`, including the
coincident boundary `x 0 = x 1` where the drift has an integrable `t⁻¹/²` singularity at `t = 0`.

## Main declarations

* `TauCeti.Probability.IsDysonPath`: deterministic pathwise Dyson integral equation.
* `TauCeti.Probability.IsDysonPath.le_of_le`: coordinatewise comparison principle (AGZ Lemma 4.3.6).
* `TauCeti.Probability.IsDysonPath.sum_sq_sub_le` and `TauCeti.Probability.IsDysonPath.eq`:
  `ℓ²`-contraction and pathwise uniqueness (AGZ Proposition 4.3.5).
* `TauCeti.Probability.IsDysonSolution`: almost-sure Dyson particle system driven by `B`.
* `TauCeti.Probability.IsDysonSolution.ae_eq`: almost-sure pathwise uniqueness of `IsDysonSolution`.
* `TauCeti.Probability.isDysonSolution_of_subsingleton` and
  `TauCeti.Probability.isDysonPath_dysonZeroNoiseTwo`: existence witnesses for `n ≤ 1` and for
  `n = 2` at zero noise from arbitrary `Antitone` starts.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1, Proposition 4.3.5 and Lemma 4.3.6.
-/

public section

open Finset Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-! ### Deterministic pathwise Dyson trajectories -/

/-- **Pathwise Dyson trajectory.** A curve `γ : ℝ≥0 → Fin n → ℝ` solves the `n`-particle Dyson
integral equation from initial configuration `x` driven by `w : ℝ≥0 → Fin n → ℝ` if `γ` is
continuous, lies in the open decreasing chamber at every positive time, has interval-integrable
off-diagonal inverse gaps on `[0, t]`, and satisfies
`γ t i = x i + w t i + ∫ s in 0..t, dysonDrift n (γ s.toNNReal) i`. -/
def IsDysonPath (n : ℕ) (x : Fin n → ℝ) (w γ : ℝ≥0 → Fin n → ℝ) : Prop :=
  Continuous γ ∧ (∀ t : ℝ≥0, 0 < t → StrictAnti (γ t)) ∧
    ∀ (t : ℝ≥0) (i : Fin n),
      IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
        (γ s.toNNReal i - γ s.toNNReal j)⁻¹) volume 0 t ∧
      γ t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift n (γ s.toNNReal) i

/-- Defining equivalence for `IsDysonPath`. -/
theorem isDysonPath_iff {n : ℕ} {x : Fin n → ℝ} {w γ : ℝ≥0 → Fin n → ℝ} :
    IsDysonPath n x w γ ↔
      Continuous γ ∧ (∀ t : ℝ≥0, 0 < t → StrictAnti (γ t)) ∧
        ∀ (t : ℝ≥0) (i : Fin n),
          IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
            (γ s.toNNReal i - γ s.toNNReal j)⁻¹) volume 0 t ∧
          γ t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift n (γ s.toNNReal) i :=
  Iff.rfl

namespace IsDysonPath

section Basic

variable {n : ℕ} {x : Fin n → ℝ} {w γ : ℝ≥0 → Fin n → ℝ}

/-- Continuity of a pathwise Dyson trajectory. -/
protected theorem continuous (h : IsDysonPath n x w γ) : Continuous γ :=
  h.1

/-- Strict decreasing order of coordinates at every positive time. -/
protected theorem strictAnti (h : IsDysonPath n x w γ) {t : ℝ≥0} (ht : 0 < t) :
    StrictAnti (γ t) :=
  h.2.1 t ht

/-- Interval integrability of the unnormalized pairwise inverse-gap sum on `[0, t]`. -/
theorem intervalIntegrable_sum_inv (h : IsDysonPath n x w γ) (t : ℝ≥0) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
      (γ s.toNNReal i - γ s.toNNReal j)⁻¹) volume 0 t :=
  (h.2.2 t i).1

/-- Interval integrability of `s ↦ dysonDrift n (γ s.toNNReal) i` on `[0, t]`. -/
theorem intervalIntegrable_dysonDrift (h : IsDysonPath n x w γ) (t : ℝ≥0) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift n (γ s.toNNReal) i) volume 0 t := by
  simpa only [dysonDrift_apply] using (h.intervalIntegrable_sum_inv t i).const_mul (n : ℝ)⁻¹

/-- Coordinatewise integral equation for a pathwise Dyson trajectory. -/
theorem apply_eq (h : IsDysonPath n x w γ) (t : ℝ≥0) (i : Fin n) :
    γ t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDrift n (γ s.toNNReal) i :=
  (h.2.2 t i).2

/-- At time `0`, a pathwise Dyson trajectory equals `x + w 0`. -/
theorem eval_zero (h : IsDysonPath n x w γ) : γ 0 = x + w 0 := by
  ext i
  simpa using h.apply_eq 0 i

/-- If the driving path vanishes at `0`, the trajectory starts at `x`. -/
theorem eval_zero_of_eq_zero (h : IsDysonPath n x w γ) (hw : w 0 = 0) : γ 0 = x := by
  rw [h.eval_zero, hw, add_zero]

/-- Coordinates of a pathwise Dyson trajectory lie in the closed chamber `{z₁ ≥ ⋯ ≥ zₙ}` at all
times `t ≥ 0` (by continuity as `t → 0⁺` when `t = 0`). -/
protected theorem antitone (h : IsDysonPath n x w γ) (t : ℝ≥0) : Antitone (γ t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · intro i j hij
    have hseq : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0) + 1)⁻¹) atTop (𝓝 (0 : ℝ≥0)) := by
      rw [← NNReal.tendsto_coe]
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hpos : ∀ k : ℕ, (0 : ℝ≥0) < ((k : ℝ≥0) + 1)⁻¹ := fun k ↦ inv_pos.2 (by positivity)
    exact le_of_tendsto_of_tendsto
      (((continuous_apply j).comp h.continuous).tendsto 0 |>.comp hseq)
      (((continuous_apply i).comp h.continuous).tendsto 0 |>.comp hseq)
      (Eventually.of_forall fun k ↦ (h.strictAnti (hpos k)).antitone hij)
  · exact (h.strictAnti (pos_iff_ne_zero.2 ht)).antitone

/-- If `w 0 = 0` and a pathwise Dyson trajectory exists from `x`, then `x` must lie in the closed
decreasing chamber `Antitone x`. -/
theorem antitone_init (h : IsDysonPath n x w γ) (hw : w 0 = 0) : Antitone x := by
  simpa only [h.eval_zero_of_eq_zero hw] using h.antitone 0

/-- **Center-of-mass identity.** Because `∑ᵢ dysonDrift n z i = 0` identically, the coordinate sum
of a Dyson trajectory equals `∑ᵢ xᵢ + ∑ᵢ w t i` at every time `t`. -/
theorem sum_apply (h : IsDysonPath n x w γ) (t : ℝ≥0) :
    ∑ i, γ t i = (∑ i, x i) + ∑ i, w t i := by
  have hsum : ∑ i, γ t i = (∑ i, x i) + (∑ i, w t i) +
      ∑ i, ∫ s in (0 : ℝ)..t, dysonDrift n (γ s.toNNReal) i := by
    simp_rw [h.apply_eq t]
    simp [sum_add_distrib, add_assoc]
  rw [hsum, ← _root_.intervalIntegral.integral_finsetSum
    fun i _ ↦ h.intervalIntegrable_dysonDrift t i]
  simp [sum_dysonDrift]

/-- Subtracting the driving path `w` leaves a function differentiable at every positive real time
`u > 0`, with derivative `dysonDrift n (γ u.toNNReal) i`. -/
theorem hasDerivAt_sub_drive (h : IsDysonPath n x w γ) (i : Fin n) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ ↦ γ s.toNNReal i - w s.toNNReal i)
      (dysonDrift n (γ u.toNNReal) i) u := by
  set f : ℝ → ℝ := fun s ↦ dysonDrift n (γ s.toNNReal) i
  have hcont : ∀ v ∈ Ioi (0 : ℝ), ContinuousAt f v := fun v hv ↦ by
    have hγv : ContinuousAt (fun s : ℝ ↦ γ s.toNNReal) v :=
      (h.continuous.comp continuous_real_toNNReal).continuousAt
    have hdr : ContinuousAt (fun s : ℝ ↦ dysonDrift n (γ s.toNNReal)) v :=
      ContinuousAt.comp (continuousAt_dysonDrift (h.strictAnti (Real.toNNReal_pos.2 hv)).injective)
        hγv
    exact ContinuousAt.comp (continuous_apply i).continuousAt hdr
  have hint : IntervalIntegrable f volume 0 u := by
    simpa [f, Real.coe_toNNReal u hu.le] using h.intervalIntegrable_dysonDrift u.toNNReal i
  have hd : HasDerivAt (fun s : ℝ ↦ x i + ∫ r in (0 : ℝ)..s, f r) (f u) u :=
    (_root_.intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hcont u hu) (hcont u hu)).const_add (x i)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hu] with s (hs : 0 < s)
  have heq := h.apply_eq s.toNNReal i
  rw [Real.coe_toNNReal s hs.le] at heq
  linarith

end Basic

/-! ### Pathwise comparison, `ℓ²`-contraction, and uniqueness -/

section Comparison

variable {n : ℕ} {x y : Fin n → ℝ} {w γ₁ γ₂ : ℝ≥0 → Fin n → ℝ}

/-- For two Dyson trajectories driven by the same path `w`, the difference `γ₁ - γ₂` cancels `w`
and has derivative `dysonDrift n (γ₁ u.toNNReal) i - dysonDrift n (γ₂ u.toNNReal) i` at every
`u > 0`. -/
theorem hasDerivAt_sub (h₁ : IsDysonPath n x w γ₁) (h₂ : IsDysonPath n y w γ₂) (i : Fin n)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ ↦ γ₁ s.toNNReal i - γ₂ s.toNNReal i)
      (dysonDrift n (γ₁ u.toNNReal) i - dysonDrift n (γ₂ u.toNNReal) i) u :=
  ((h₁.hasDerivAt_sub_drive i hu).sub (h₂.hasDerivAt_sub_drive i hu)).congr_of_eventuallyEq
    (Eventually.of_forall fun _ ↦ by simp)

/-- **One-sided `ℓ²`-dissipativity along trajectories.** For any two Dyson trajectories driven by
the same path `w`, `t ↦ ∑ᵢ max (γ₁ t i - γ₂ t i) 0 ^ 2` is antitone on `ℝ≥0`. -/
theorem antitone_sum_max_sub_zero_sq (h₁ : IsDysonPath n x w γ₁) (h₂ : IsDysonPath n y w γ₂) :
    Antitone (fun t : ℝ≥0 ↦ ∑ i, max (γ₁ t i - γ₂ t i) 0 ^ 2) := by
  set φ : ℝ → ℝ := fun u ↦ ∑ i, max (γ₁ u.toNNReal i - γ₂ u.toNNReal i) 0 ^ 2
  have hφ_cont : Continuous φ :=
    continuous_finsetSum _ fun i _ ↦
      ((((continuous_apply i).comp h₁.continuous).sub
        ((continuous_apply i).comp h₂.continuous)).comp continuous_real_toNNReal).max
          continuous_const |>.pow 2
  have hφ_deriv : ∀ u : ℝ, 0 < u → HasDerivAt φ
      (2 * ∑ i, (dysonDrift n (γ₁ u.toNNReal) i - dysonDrift n (γ₂ u.toNNReal) i) *
        max (γ₁ u.toNNReal i - γ₂ u.toNNReal i) 0) u := by
    intro u hu
    have hsum := HasDerivAt.sum fun i (_ : i ∈ (univ : Finset (Fin n))) ↦
      (h₁.hasDerivAt_sub h₂ i hu).max_zero_pow (by decide : 2 ≠ 1)
    convert hsum using 1
    · ext y
      simp [φ]
    · rw [mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
  have hanti : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hφ_cont.continuousOn ?_ ?_
    · rw [interior_Ici]
      exact fun u hu ↦ (hφ_deriv u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro u (hu : 0 < u)
      rw [(hφ_deriv u hu).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos zero_le_two
        (sum_sub_dysonDrift_mul_max_sub_nonpos (h₁.strictAnti (Real.toNNReal_pos.2 hu))
          (h₂.strictAnti (Real.toNNReal_pos.2 hu)))
  intro s t hst
  simpa [φ] using hanti (NNReal.coe_nonneg s) (NNReal.coe_nonneg t) (NNReal.coe_le_coe.2 hst)

/-- One-sided `ℓ²` bound in terms of the initial configurations `x` and `y`. -/
theorem sum_max_sub_zero_sq_le (h₁ : IsDysonPath n x w γ₁) (h₂ : IsDysonPath n y w γ₂)
    (t : ℝ≥0) :
    ∑ i, max (γ₁ t i - γ₂ t i) 0 ^ 2 ≤ ∑ i, max (x i - y i) 0 ^ 2 := by
  have hle := h₁.antitone_sum_max_sub_zero_sq h₂ (zero_le : 0 ≤ t)
  simpa only [h₁.eval_zero, h₂.eval_zero, Pi.add_apply, add_sub_add_right_eq_sub] using hle

/-- **Coordinatewise comparison principle** (AGZ Lemma 4.3.6). If `x ≤ y`, any two Dyson
trajectories from `x` and `y` driven by the same path `w` satisfy `γ₁ t ≤ γ₂ t` for all `t`. -/
theorem le_of_le (h₁ : IsDysonPath n x w γ₁) (h₂ : IsDysonPath n y w γ₂) (hxy : x ≤ y)
    (t : ℝ≥0) : γ₁ t ≤ γ₂ t := by
  intro i
  have h0 : ∑ k, max (x k - y k) 0 ^ 2 = 0 :=
    sum_eq_zero fun k _ ↦ by simp [max_eq_right (sub_nonpos.2 (hxy k))]
  have hle : max (γ₁ t i - γ₂ t i) 0 ^ 2 ≤ 0 := by
    calc max (γ₁ t i - γ₂ t i) 0 ^ 2
        ≤ ∑ k, max (γ₁ t k - γ₂ t k) 0 ^ 2 :=
          single_le_sum (f := fun k ↦ max (γ₁ t k - γ₂ t k) 0 ^ 2)
            (fun k _ ↦ sq_nonneg _) (mem_univ i)
      _ ≤ ∑ k, max (x k - y k) 0 ^ 2 := h₁.sum_max_sub_zero_sq_le h₂ t
      _ = 0 := h0
  have hmax : max (γ₁ t i - γ₂ t i) 0 = 0 :=
    sq_eq_zero_iff.1 ((sq_nonneg _).antisymm' hle)
  exact sub_nonpos.1 ((le_max_left _ 0).trans_eq hmax)

/-- **Two-sided `ℓ²`-contraction.** For any two Dyson trajectories driven by the same path `w`,
`t ↦ ∑ᵢ (γ₁ t i - γ₂ t i)²` is antitone on `ℝ≥0`. -/
theorem antitone_sum_sq_sub (h₁ : IsDysonPath n x w γ₁) (h₂ : IsDysonPath n y w γ₂) :
    Antitone (fun t : ℝ≥0 ↦ ∑ i, (γ₁ t i - γ₂ t i) ^ 2) := by
  have hsplit : (fun t : ℝ≥0 ↦ ∑ i, (γ₁ t i - γ₂ t i) ^ 2) =
      (fun t : ℝ≥0 ↦ ∑ i, max (γ₁ t i - γ₂ t i) 0 ^ 2) +
        fun t : ℝ≥0 ↦ ∑ i, max (γ₂ t i - γ₁ t i) 0 ^ 2 := by
    ext t
    rw [Pi.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rcases le_total (γ₁ t i) (γ₂ t i) with hle | hge
    · rw [max_eq_right (sub_nonpos.2 hle), max_eq_left (sub_nonneg.2 hle)]
      ring
    · rw [max_eq_left (sub_nonneg.2 hge), max_eq_right (sub_nonpos.2 hge)]
      ring
  rw [hsplit]
  exact (h₁.antitone_sum_max_sub_zero_sq h₂).add (h₂.antitone_sum_max_sub_zero_sq h₁)

/-- **Continuous dependence on initial data in `ℓ²`** (AGZ Proposition 4.3.5). For any two Dyson
trajectories driven by the same path `w`, `∑ᵢ (γ₁ t i - γ₂ t i)² ≤ ∑ᵢ (xᵢ - yᵢ)²` at every `t`. -/
theorem sum_sq_sub_le (h₁ : IsDysonPath n x w γ₁) (h₂ : IsDysonPath n y w γ₂) (t : ℝ≥0) :
    ∑ i, (γ₁ t i - γ₂ t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  have hle := h₁.antitone_sum_sq_sub h₂ (zero_le : 0 ≤ t)
  simpa only [h₁.eval_zero, h₂.eval_zero, Pi.add_apply, add_sub_add_right_eq_sub] using hle

/-- **Pathwise uniqueness for Dyson trajectories.** Two Dyson trajectories from the same initial
configuration `x` and driven by the same path `w` are equal at all times. -/
protected theorem eq {γ₁ γ₂ : ℝ≥0 → Fin n → ℝ} (h₁ : IsDysonPath n x w γ₁)
    (h₂ : IsDysonPath n x w γ₂) : γ₁ = γ₂ := by
  ext t i
  have hle : (γ₁ t i - γ₂ t i) ^ 2 ≤ 0 := by
    calc (γ₁ t i - γ₂ t i) ^ 2
        ≤ ∑ k, (γ₁ t k - γ₂ t k) ^ 2 :=
          single_le_sum (f := fun k ↦ (γ₁ t k - γ₂ t k) ^ 2) (fun k _ ↦ sq_nonneg _) (mem_univ i)
      _ ≤ ∑ k, (x k - x k) ^ 2 := h₁.sum_sq_sub_le h₂ t
      _ = 0 := by simp
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 ((sq_nonneg _).antisymm' hle))

end Comparison

end IsDysonPath

/-! ### Stochastic Dyson particle system `IsDysonSolution` -/

section Stochastic

variable {Ω : Type*}

/-- A continuous process, in the open chamber at positive times, solving the Dyson system of size
`n` and parameter `β` from `x`, driven by `B`, as a pathwise integral identity with integrable
drift (AGZ §4.3.1). Adaptedness to the filtration of `B` is not part of this predicate. -/
def IsDysonSolution [MeasurableSpace Ω] (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧ (∀ t, 0 < t → StrictAnti (X t ω)) ∧
    ∀ (t : ℝ≥0) (i : Fin n),
      IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
        (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹) volume 0 t ∧
      X t ω i = x i + Real.sqrt (2 / (β * n)) * B i t ω +
        ∫ s in (0 : ℝ)..t, (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
          (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹

/-- Defining equivalence for `IsDysonSolution`. -/
theorem isDysonSolution_iff [MeasurableSpace Ω] {β : ℝ} {n : ℕ} {x : Fin n → ℝ} {P : Measure Ω}
    {B : Fin n → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧ (∀ t, 0 < t → StrictAnti (X t ω)) ∧
        ∀ (t : ℝ≥0) (i : Fin n),
          IntervalIntegrable (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
            (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹) volume 0 t ∧
          X t ω i = x i + Real.sqrt (2 / (β * n)) * B i t ω +
            ∫ s in (0 : ℝ)..t, (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
              (X s.toNNReal ω i - X s.toNNReal ω j)⁻¹ :=
  Iff.rfl

/-- `IsDysonSolution` is equivalent to `P`-almost-sure `IsDysonPath` driven by
`t i ↦ √(2 / (β * n)) * B i t ω`. -/
theorem isDysonSolution_iff_ae_isDysonPath [MeasurableSpace Ω] {β : ℝ} {n : ℕ} {x : Fin n → ℝ}
    {P : Measure Ω} {B : Fin n → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, IsDysonPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ X t ω) := by
  simp only [isDysonSolution_iff, isDysonPath_iff, dysonDrift_apply]

namespace IsDysonSolution

variable [MeasurableSpace Ω] {β : ℝ} {n : ℕ} {x y : Fin n → ℝ} {P : Measure Ω}
  {B : Fin n → ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → Fin n → ℝ}

/-- `IsDysonSolution` yields `P`-almost-sure `IsDysonPath` trajectories. -/
theorem ae_isDysonPath (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, IsDysonPath n x (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (fun t ↦ X t ω) :=
  isDysonSolution_iff_ae_isDysonPath.1 hX

/-- Almost surely, the sample path `t ↦ X t ω` is continuous on `ℝ≥0`. -/
theorem ae_continuous (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) :=
  hX.ae_isDysonPath.mono fun _ hω ↦ hω.continuous

/-- Almost surely, every positive-time slice `X t ω` (`0 < t`) lies in the open decreasing
chamber. -/
theorem ae_strictAnti (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t, 0 < t → StrictAnti (X t ω) :=
  hX.ae_isDysonPath.mono fun _ hω _ ht ↦ hω.strictAnti ht

/-- Almost surely, every time slice `X t ω` lies in the closed decreasing chamber. -/
theorem ae_antitone (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t, Antitone (X t ω) :=
  hX.ae_isDysonPath.mono fun _ hω ↦ hω.antitone

/-- Congruence for `IsDysonSolution` under almost-sure pathwise equality of the driving family `B`
and the solution process `X`. -/
theorem congr_ae {B' : Fin n → ℝ≥0 → Ω → ℝ} (hX : IsDysonSolution β n x P B X)
    (hB : ∀ i, ∀ᵐ ω ∂P, ∀ t, B i t ω = B' i t ω) (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    IsDysonSolution β n x P B' Y := by
  rw [isDysonSolution_iff_ae_isDysonPath]
  rw [← ae_all_iff] at hB
  filter_upwards [hX.ae_isDysonPath, hB, hXY] with ω hω hωB hωX
  have heqB : (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) =
      fun t i ↦ Real.sqrt (2 / (β * n)) * B' i t ω := by
    ext t i
    rw [hωB i t]
  have heqX : (fun t ↦ X t ω) = fun t ↦ Y t ω := funext hωX
  rwa [heqB, heqX] at hω

/-- Almost-sure center-of-mass formula for `IsDysonSolution`. -/
theorem ae_sum_apply (hX : IsDysonSolution β n x P B X) :
    ∀ᵐ ω ∂P, ∀ t, ∑ i, X t ω i = (∑ i, x i) + Real.sqrt (2 / (β * n)) * ∑ i, B i t ω := by
  refine hX.ae_isDysonPath.mono fun ω hω t ↦ ?_
  rw [hω.sum_apply t, mul_sum]

/-- Almost-sure coordinatewise comparison for `IsDysonSolution` (AGZ Lemma 4.3.6). -/
theorem ae_le_of_le (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n y P B Y)
    (hxy : x ≤ y) : ∀ᵐ ω ∂P, ∀ t, X t ω ≤ Y t ω := by
  filter_upwards [hX.ae_isDysonPath, hY.ae_isDysonPath] with ω hωX hωY t
  exact hωX.le_of_le hωY hxy t

/-- Almost-sure `ℓ²`-contraction for `IsDysonSolution` (AGZ Proposition 4.3.5). -/
theorem ae_antitone_sum_sq_sub (hX : IsDysonSolution β n x P B X)
    (hY : IsDysonSolution β n y P B Y) :
    ∀ᵐ ω ∂P, Antitone (fun t ↦ ∑ i, (X t ω i - Y t ω i) ^ 2) := by
  filter_upwards [hX.ae_isDysonPath, hY.ae_isDysonPath] with ω hωX hωY
  exact hωX.antitone_sum_sq_sub hωY

/-- Almost-sure `ℓ²` continuous-dependence bound for `IsDysonSolution`. -/
theorem ae_sum_sq_sub_le (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n y P B Y) :
    ∀ᵐ ω ∂P, ∀ t, ∑ i, (X t ω i - Y t ω i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  filter_upwards [hX.ae_isDysonPath, hY.ae_isDysonPath] with ω hωX hωY t
  exact hωX.sum_sq_sub_le hωY t

/-- **Almost-sure pathwise uniqueness for `IsDysonSolution`.** Any two solutions started at `x`
and driven by the same process `B` agree at all times `P`-almost surely, with no sign or ordering
assumptions on `β` or `x` and no distributional assumptions on `B`. -/
theorem ae_eq (hX : IsDysonSolution β n x P B X) (hY : IsDysonSolution β n x P B Y) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [hX.ae_isDysonPath, hY.ae_isDysonPath] with ω hωX hωY t
  exact congr_fun (hωX.eq hωY) t

end IsDysonSolution

end Stochastic

/-! ### Explicit existence witnesses (`n ≤ 1` and two-particle zero-noise Bessel trajectory) -/

/-- For `n ≤ 1`, the Dyson drift vanishes and `t i ↦ x i + w t i` solves `IsDysonPath` for every
continuous driving path `w`. -/
theorem isDysonPath_of_subsingleton {n : ℕ} [Subsingleton (Fin n)] (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    IsDysonPath n x w (fun t i ↦ x i + w t i) := by
  refine ⟨continuous_const.add hw, fun t _ i j hij ↦ (hij.ne (Subsingleton.elim i j)).elim,
    fun t i ↦ ?_⟩
  have hempty : (univ : Finset (Fin n)).erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp [hempty, dysonDrift_of_subsingleton]

/-- For `n ≤ 1`, `X t ω i = x i + √(2 / (β * n)) * B i t ω` solves `IsDysonSolution` whenever each
coordinate `B i` has `P`-almost-surely continuous paths (for example `(hB i).cont` when `B i` is
`ProbabilityTheory.IsBrownianReal`). -/
theorem isDysonSolution_of_subsingleton {Ω : Type*} [MeasurableSpace Ω] (β : ℝ) {n : ℕ}
    [Subsingleton (Fin n)] (x : Fin n → ℝ) (P : Measure Ω) {B : Fin n → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, ∀ᵐ ω ∂P, Continuous (B i · ω)) :
    IsDysonSolution β n x P B (fun t ω i ↦ x i + Real.sqrt (2 / (β * n)) * B i t ω) := by
  rw [isDysonSolution_iff_ae_isDysonPath, ← ae_all_iff] at *
  refine hB.mono fun ω hω ↦ isDysonPath_of_subsingleton x ?_
  exact continuous_pi fun i ↦ continuous_const.mul (hω i)

/-- **Explicit two-particle zero-noise Dyson trajectory** from initial configuration
`x : Fin 2 → ℝ`:
`t ↦ ![(x 0 + x 1) / 2 + √(((x 0 - x 1) / 2)² + t / 2),
       (x 0 + x 1) / 2 - √(((x 0 - x 1) / 2)² + t / 2)]`. -/
noncomputable def dysonZeroNoiseTwo (x : Fin 2 → ℝ) (t : ℝ≥0) : Fin 2 → ℝ :=
  ![(x 0 + x 1) / 2 + Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2),
    (x 0 + x 1) / 2 - Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2)]

/-- First coordinate of `dysonZeroNoiseTwo`. -/
@[simp]
theorem dysonZeroNoiseTwo_apply_zero (x : Fin 2 → ℝ) (t : ℝ≥0) :
    dysonZeroNoiseTwo x t 0 =
      (x 0 + x 1) / 2 + Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2) :=
  (rfl)

/-- Second coordinate of `dysonZeroNoiseTwo`. -/
@[simp]
theorem dysonZeroNoiseTwo_apply_one (x : Fin 2 → ℝ) (t : ℝ≥0) :
    dysonZeroNoiseTwo x t 1 =
      (x 0 + x 1) / 2 - Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2) :=
  (rfl)

/-- For `Antitone x`, `dysonZeroNoiseTwo x 0 = x`. -/
theorem dysonZeroNoiseTwo_zero {x : Fin 2 → ℝ} (hx : Antitone x) :
    dysonZeroNoiseTwo x 0 = x := by
  have hr : 0 ≤ (x 0 - x 1) / 2 := div_nonneg (sub_nonneg.2 (hx (by decide))) zero_le_two
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, dysonZeroNoiseTwo_apply_zero, NNReal.coe_zero, zero_div, add_zero,
      Real.sqrt_sq hr]
    ring
  · simp only [Fin.mk_one, dysonZeroNoiseTwo_apply_one, NNReal.coe_zero, zero_div, add_zero,
      Real.sqrt_sq hr]
    ring

/-- Gap between the two coordinates of `dysonZeroNoiseTwo`. -/
theorem dysonZeroNoiseTwo_sub (x : Fin 2 → ℝ) (t : ℝ≥0) :
    dysonZeroNoiseTwo x t 0 - dysonZeroNoiseTwo x t 1 =
      2 * Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2) := by
  simp only [dysonZeroNoiseTwo_apply_zero, dysonZeroNoiseTwo_apply_one]
  ring

/-- Continuity of `dysonZeroNoiseTwo x`. -/
theorem continuous_dysonZeroNoiseTwo (x : Fin 2 → ℝ) : Continuous (dysonZeroNoiseTwo x) := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · dsimp only
    rw [Fin.zero_eta]
    simp only [dysonZeroNoiseTwo_apply_zero]
    fun_prop
  · dsimp only
    rw [Fin.mk_one]
    simp only [dysonZeroNoiseTwo_apply_one]
    fun_prop

/-- Integrability of the inverse gap `(dysonZeroNoiseTwo x s 0 - dysonZeroNoiseTwo x s 1)⁻¹` on
`[0, t]` for every `x : Fin 2 → ℝ` (including the coincident start `x 0 = x 1` where on `(0, t]`
the inverse gap is `(√(2 s))⁻¹`), together with the integral of
`dysonDrift 2 (dysonZeroNoiseTwo x s.toNNReal) 0` on `[0, t]`. -/
private theorem intervalIntegrable_and_integral_dysonZeroNoiseTwo (x : Fin 2 → ℝ) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ ↦
      (dysonZeroNoiseTwo x s.toNNReal 0 - dysonZeroNoiseTwo x s.toNNReal 1)⁻¹) volume 0 t ∧
    ∫ s in (0 : ℝ)..t, dysonDrift 2 (dysonZeroNoiseTwo x s.toNNReal) 0 =
      Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2) - |(x 0 - x 1) / 2| := by
  set r₀ : ℝ := (x 0 - x 1) / 2
  set F : ℝ → ℝ := fun s ↦ Real.sqrt (r₀ ^ 2 + max s 0 / 2)
  have hF_cont : ContinuousOn F (Icc 0 (t : ℝ)) := by dsimp only [F]; fun_prop
  have hF_deriv : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt F ((4 * F s)⁻¹) s := fun s hs ↦ by
    have hrad : 0 < r₀ ^ 2 + s / 2 := add_pos_of_nonneg_of_pos (sq_nonneg r₀) (half_pos hs.1)
    have hd : HasDerivAt (fun u : ℝ ↦ Real.sqrt (r₀ ^ 2 + u / 2)) ((4 * F s)⁻¹) s := by
      convert ((hasDerivAt_id' s).div_const (2 : ℝ) |>.const_add (r₀ ^ 2)).sqrt hrad.ne' using 1
      have hFs : F s = Real.sqrt (r₀ ^ 2 + s / 2) := by simp [F, max_eq_left hs.1.le]
      rw [hFs]
      have : Real.sqrt (r₀ ^ 2 + s / 2) ≠ 0 := (Real.sqrt_pos.2 hrad).ne'
      field_simp; ring
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs.1] with u (hu : 0 < u)
    simp [F, max_eq_left hu.le]
  have hf_nn : ∀ s ∈ Ioo (0 : ℝ) t, 0 ≤ (4 * F s)⁻¹ := fun _ _ ↦ inv_nonneg.2 (by positivity)
  have hintF : IntervalIntegrable (fun s : ℝ ↦ (4 * F s)⁻¹) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF_cont hF_deriv hf_nn)
  have hgap : ∀ s : ℝ, dysonZeroNoiseTwo x s.toNNReal 0 - dysonZeroNoiseTwo x s.toNNReal 1 =
      2 * F s := fun s ↦ by simp only [dysonZeroNoiseTwo_sub, F, Real.coe_toNNReal', r₀]
  have hfun : (fun s : ℝ ↦
      (dysonZeroNoiseTwo x s.toNNReal 0 - dysonZeroNoiseTwo x s.toNNReal 1)⁻¹) =
      fun s ↦ 2 * (4 * F s)⁻¹ := by
    ext s; rw [hgap s]
    rcases eq_or_ne (F s) 0 with h0 | hne
    · simp [h0]
    · field_simp; ring
  have hdr : (fun s : ℝ ↦ dysonDrift 2 (dysonZeroNoiseTwo x s.toNNReal) 0) =
      fun s ↦ (4 * F s)⁻¹ := funext fun s ↦ by rw [dysonDrift_two_zero, hgap s]; ring
  refine ⟨hfun ▸ hintF.const_mul 2, ?_⟩
  rw [hdr, TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg
    (NNReal.coe_nonneg t) hF_cont hF_deriv hf_nn]
  simp [F, Real.sqrt_sq_eq_abs, r₀]

/-- **Zero-noise two-particle existence from any closed-chamber configuration** (including the
coincident boundary `x 0 = x 1`, where the drift `(2 √(2 s))⁻¹` has an integrable endpoint
singularity at `s = 0`). -/
theorem isDysonPath_dysonZeroNoiseTwo {x : Fin 2 → ℝ} (hx : Antitone x) :
    IsDysonPath 2 x 0 (dysonZeroNoiseTwo x) := by
  have hr₀ : 0 ≤ (x 0 - x 1) / 2 := div_nonneg (sub_nonneg.2 (hx (by decide))) zero_le_two
  have hstrict : ∀ t : ℝ≥0, 0 < t → StrictAnti (dysonZeroNoiseTwo x t) := by
    intro t ht i j hij
    have hij' : i = 0 ∧ j = 1 := by omega
    rcases hij' with ⟨rfl, rfl⟩
    have hpos : 0 < Real.sqrt (((x 0 - x 1) / 2) ^ 2 + (t : ℝ) / 2) :=
      Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) (half_pos (NNReal.coe_pos.2 ht)))
    simp only [dysonZeroNoiseTwo_apply_zero, dysonZeroNoiseTwo_apply_one]
    linarith
  refine ⟨continuous_dysonZeroNoiseTwo x, hstrict, fun t i ↦ ?_⟩
  obtain ⟨hint, hval⟩ := intervalIntegrable_and_integral_dysonZeroNoiseTwo x t
  rw [abs_of_nonneg hr₀] at hval
  fin_cases i
  · dsimp only
    rw [Fin.zero_eta]
    have herase : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
    refine ⟨by simpa only [herase, sum_singleton] using hint, ?_⟩
    rw [hval]
    simp only [dysonZeroNoiseTwo_apply_zero, Pi.zero_apply, add_zero]
    ring
  · dsimp only
    rw [Fin.mk_one]
    have herase : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
    have hneg : (fun s : ℝ ↦
        (dysonZeroNoiseTwo x s.toNNReal 1 - dysonZeroNoiseTwo x s.toNNReal 0)⁻¹) =
        -(fun s : ℝ ↦ (dysonZeroNoiseTwo x s.toNNReal 0 - dysonZeroNoiseTwo x s.toNNReal 1)⁻¹) := by
      ext s
      rw [Pi.neg_apply, ← neg_sub (dysonZeroNoiseTwo x s.toNNReal 0), inv_neg]
    have hdr : (fun s : ℝ ↦ dysonDrift 2 (dysonZeroNoiseTwo x s.toNNReal) 1) =
        fun s ↦ -dysonDrift 2 (dysonZeroNoiseTwo x s.toNNReal) 0 := by
      ext s
      rw [dysonDrift_two_one, dysonDrift_two_zero]
    refine ⟨by simpa only [herase, sum_singleton, hneg] using hint.neg, ?_⟩
    rw [_root_.intervalIntegral.integral_congr fun s _ ↦ congr_fun hdr s,
      _root_.intervalIntegral.integral_neg, hval]
    simp only [dysonZeroNoiseTwo_apply_one, Pi.zero_apply, add_zero]
    ring

/-- Zero-noise `IsDysonSolution` witness for `n = 2` from any `Antitone x` (including `x 0 = x 1`),
for `B = 0`. -/
theorem isDysonSolution_dysonZeroNoiseTwo {Ω : Type*} [MeasurableSpace Ω] (β : ℝ)
    {x : Fin 2 → ℝ} (hx : Antitone x) (P : Measure Ω) :
    IsDysonSolution β 2 x P 0 (fun t _ ↦ dysonZeroNoiseTwo x t) := by
  rw [isDysonSolution_iff_ae_isDysonPath]
  refine Eventually.of_forall fun ω ↦ ?_
  have h0 : (fun (t : ℝ≥0) (i : Fin 2) ↦
      Real.sqrt (2 / (β * (2 : ℕ))) * (0 : Fin 2 → ℝ≥0 → Ω → ℝ) i t ω) = 0 := by
    ext t i
    simp
  rw [h0]
  exact isDysonPath_dysonZeroNoiseTwo hx

end TauCeti.Probability
