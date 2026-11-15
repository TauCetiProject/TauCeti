/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.DysonBrownianMotion.Drift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Solutions of the Dyson system and their pathwise uniqueness

The Dyson system of size `n` and parameter `β` is
`dλᵢ = √(2/(βn)) dBᵢ + n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹ dt`. Its noise is additive, so a solution
driven by a path `b` is a solution of the integral identity
`λᵢ(t) = xᵢ + √(2/(βn)) bᵢ(t) + ∫₀ᵗ Fᵢ(λ(s)) ds`, with `F = TauCeti.Probability.dysonDrift`,
and no stochastic integral is needed. This file states that identity, for continuous paths in the
open chamber `{x₁ > ⋯ > xₙ}` at positive times with integrable drift, as
`TauCeti.Probability.IsDysonPath`, and its almost sure version for a random driving process as
`TauCeti.Probability.IsDysonSolution`.

Solutions are pathwise unique: two solutions driven by the same path from the same start agree.
For two solutions `X` and `Y`, the difference `D = X - Y` is the integral of `F(X) - F(Y)`, which
is continuous at positive times, so `|D|²` is differentiable there with derivative
`2 ⟨D, F(X) - F(Y)⟩ ≤ 0` by the monotonicity of the drift; as `D(0) = 0`, it follows that
`D = 0`. This needs neither adaptedness nor any property of the driving path, and it covers
starts with coincident coordinates. In size `1` the system is `dλ = √(2/β) dB`, solved by
`x + √(2/β) b`.

## Main declarations

* `TauCeti.Probability.IsDysonPath`: a solution of the Dyson system driven by a path.
* `TauCeti.Probability.IsDysonPath.unique`: pathwise uniqueness.
* `TauCeti.Probability.IsDysonSolution`: an almost sure solution driven by a random process.
* `TauCeti.Probability.IsDysonSolution.indist`: two such solutions are indistinguishable.
* `TauCeti.Probability.isDysonPath_one`: the solution in size `1`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1, Lemma 4.3.3 and Proposition 4.3.5.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal Topology

namespace TauCeti.Probability

variable {β : ℝ} {n : ℕ} {x : Fin n → ℝ} {b : Fin n → ℝ≥0 → ℝ} {X Y : ℝ≥0 → Fin n → ℝ}

/-- `X` solves the Dyson system of size `n` and parameter `β` from `x`, driven by the path `b`:
`X` is continuous, lies in the open chamber `{X₁(t) > ⋯ > Xₙ(t)}` at every positive time, its
drift `F(X(s)) = TauCeti.Probability.dysonDrift n (X s)` is integrable on every `[0, t]`, and
`Xᵢ(t) = xᵢ + √(2/(βn)) bᵢ(t) + ∫₀ᵗ Fᵢ(X(s)) ds` for all `t` and `i`. The start `x` may have
coincident coordinates. -/
structure IsDysonPath (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (b : Fin n → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Fin n → ℝ) : Prop where
  /-- The solution has continuous paths. -/
  continuous : Continuous X
  /-- At positive times the solution lies in the open chamber. -/
  strictAnti : ∀ t, 0 < t → StrictAnti (X t)
  /-- The drift along the solution is integrable on every interval `[0, t]`. -/
  intervalIntegrable : ∀ (t : ℝ≥0) (i : Fin n),
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift n (X s.toNNReal) i) volume 0 t
  /-- The integral form of the Dyson system. -/
  apply_eq : ∀ (t : ℝ≥0) (i : Fin n), X t i =
    x i + Real.sqrt (2 / (β * n)) * b i t + ∫ s in (0 : ℝ)..t, dysonDrift n (X s.toNNReal) i

namespace IsDysonPath

/-- At a positive time, the drift along a solution is continuous in time. -/
private theorem continuousAt_dysonDrift_comp (hX : IsDysonPath β n x b X) (i : Fin n) {u : ℝ}
    (hu : 0 < u) : ContinuousAt (fun v : ℝ ↦ dysonDrift n (X v.toNNReal) i) u :=
  (continuousAt_dysonDrift (hX.strictAnti _ (Real.toNNReal_pos.2 hu)).injective i).comp_of_eq
    (hX.continuous.comp continuous_real_toNNReal).continuousAt rfl

/-- The difference of two solutions driven by the same path is the integral of the difference
of their drifts. -/
private theorem sub_eq_integral (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y)
    (t : ℝ≥0) (i : Fin n) :
    X t i - Y t i = ∫ s in (0 : ℝ)..t,
      (dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i) := by
  rw [intervalIntegral.integral_sub (hX.intervalIntegrable t i) (hY.intervalIntegrable t i),
    hX.apply_eq, hY.apply_eq]
  ring

/-- At a positive time, the difference of two solutions driven by the same path is
differentiable, with derivative the difference of their drifts. -/
private theorem hasDerivAt_sub (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y)
    (i : Fin n) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u : ℝ ↦ X u.toNNReal i - Y u.toNNReal i)
      (dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i) s := by
  set g : ℝ → ℝ := fun u ↦ dysonDrift n (X u.toNNReal) i - dysonDrift n (Y u.toNNReal) i
  -- The drift difference is continuous on `(0, ∞)`, where both paths are in the open chamber.
  have hg : ContinuousOn g (Ioi 0) := fun u hu ↦
    ((continuousAt_dysonDrift_comp hX i hu).sub
      (continuousAt_dysonDrift_comp hY i hu)).continuousWithinAt
  have hint : IntervalIntegrable g volume 0 s := by
    simpa [Real.coe_toNNReal _ hs.le] using
      (hX.intervalIntegrable s.toNNReal i).sub (hY.intervalIntegrable s.toNNReal i)
  refine (intervalIntegral.integral_hasDerivAt_right hint
    (hg.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hg.continuousAt (isOpen_Ioi.mem_nhds hs))).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
  rw [sub_eq_integral hX hY, Real.coe_toNNReal _ (le_of_lt hu)]

/-- **Pathwise uniqueness for the Dyson system** (the uniqueness part of AGZ Lemma 4.3.3 and
Proposition 4.3.5). Two solutions driven by the same path from the same start agree, whether or
not the start has coincident coordinates. -/
theorem unique (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y) : X = Y := by
  set φ : ℝ → ℝ := fun u ↦ ∑ i, (X u.toNNReal i - Y u.toNNReal i) ^ 2
  have hφc : Continuous φ := by
    have hXc : Continuous fun u : ℝ ↦ X u.toNNReal := hX.continuous.comp continuous_real_toNNReal
    have hYc : Continuous fun u : ℝ ↦ Y u.toNNReal := hY.continuous.comp continuous_real_toNNReal
    exact continuous_finsetSum _ fun i _ ↦
      (((continuous_apply i).comp hXc).sub ((continuous_apply i).comp hYc)).pow 2
  -- `φ = |X - Y|²` is antitone on `[0, ∞)`, since its derivative at positive times is
  -- `2 ⟨X - Y, F(X) - F(Y)⟩ ≤ 0`.
  have hφ : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hφc.continuousOn
      (f' := fun s ↦ 2 * ∑ i, (dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i) *
        (X s.toNNReal i - Y s.toNNReal i))
      (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    · rw [interior_Ici] at hs
      refine ((HasDerivAt.fun_sum fun i _ ↦
        (hasDerivAt_sub hX hY i hs).fun_pow 2).congr_deriv ?_).hasDerivWithinAt
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by push_cast; ring
    · rw [interior_Ici] at hs
      have hs' : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
      exact mul_nonpos_of_nonneg_of_nonpos zero_le_two <|
        sum_dysonDrift_sub_mul_sub_nonpos (hX.strictAnti _ hs').injective
          (hY.strictAnti _ hs').injective
          ((hX.strictAnti _ hs').antitone.monovary (hY.strictAnti _ hs').antitone)
  have hφ0 : φ 0 = 0 := by
    simp [φ, sub_eq_integral hX hY 0]
  funext t i
  have ht : φ t ≤ 0 := hφ0 ▸ hφ self_mem_Ici (mem_Ici.2 t.2) t.2
  have := (sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (X t j - Y t j)).1
    (le_antisymm (by simpa [φ] using ht) (sum_nonneg fun j _ ↦ sq_nonneg _)) i (mem_univ i)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

end IsDysonPath

/-- In size `1` the Dyson system `dλ = √(2/β) dB` has no drift, and `x + √(2/β) b` solves it
for every continuous driving path `b`. -/
theorem isDysonPath_one (β : ℝ) (x : Fin 1 → ℝ) {b : Fin 1 → ℝ≥0 → ℝ}
    (hb : ∀ i, Continuous (b i)) :
    IsDysonPath β 1 x b (fun t i ↦ x i + Real.sqrt (2 / β) * b i t) where
  continuous := continuous_pi fun i ↦ continuous_const.add (continuous_const.mul (hb i))
  strictAnti _ _ := Subsingleton.strictAnti _
  intervalIntegrable _ _ := by simp
  apply_eq _ _ := by simp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `X` is almost surely a solution of the Dyson system of size `n` and parameter `β` from `x`,
driven by the process `B`: for `P`-almost every `ω`, the path `t ↦ X t ω` solves the system
driven by the path `t ↦ B · t ω` (`TauCeti.Probability.IsDysonPath`). Adaptedness of `X` to a
filtration of `B` is not part of this notion. -/
def IsDysonSolution (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω) (B : Fin n → ℝ≥0 → Ω → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsDysonPath β n x (fun i t ↦ B i t ω) (fun t ↦ X t ω)

/-- The defining property of an almost sure solution of the Dyson system. -/
theorem isDysonSolution_iff {P : Measure Ω} {B : Fin n → ℝ≥0 → Ω → ℝ}
    {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, IsDysonPath β n x (fun i t ↦ B i t ω) (fun t ↦ X t ω) :=
  (Iff.rfl)

/-- **Pathwise uniqueness for the Dyson system**, almost sure form. Two solutions driven by the
same process from the same start are indistinguishable. No property of `B` and no adaptedness is
needed. -/
theorem IsDysonSolution.indist {P : Measure Ω} {B : Fin n → ℝ≥0 → Ω → ℝ}
    {X Y : ℝ≥0 → Ω → Fin n → ℝ} (hX : IsDysonSolution β n x P B X)
    (hY : IsDysonSolution β n x P B Y) : X ≡ᵐ[P] Y := by
  filter_upwards [isDysonSolution_iff.1 hX, isDysonSolution_iff.1 hY] with ω hXω hYω t
  exact congrFun (hXω.unique hYω) t

end TauCeti.Probability
