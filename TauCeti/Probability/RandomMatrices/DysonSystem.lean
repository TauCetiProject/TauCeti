/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Dyson system and its pathwise uniqueness

The Dyson system of size `n` and parameter `β` is the system of stochastic differential equations
`dλᵢ = √(2/(βn)) dBᵢ + n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹ dt`, `i = 1, …, n`, satisfied by the ordered
eigenvalues of symmetric (`β = 1`) and Hermitian (`β = 2`) matrix Brownian motion. Its noise is
additive, so a solution in the open chamber `{x₁ > ⋯ > xₙ}` at positive times is a pathwise
integral identity
`λᵢ(t) = xᵢ + √(2/(βn)) Bᵢ(t) + ∫₀ᵗ n⁻¹ ∑_{j ≠ i} (λᵢ(s) - λⱼ(s))⁻¹ ds`,
with no stochastic integral.

The drift `F = dysonDrift n` is monotone (dissipative) on the open chamber: for `x` and `y` in it,
`∑ᵢ (Fᵢ(x) - Fᵢ(y)) (xᵢ - yᵢ) = -n⁻¹ ∑_{i<j} (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ) ≤ 0`, where
`aᵢⱼ = xᵢ - xⱼ` and `bᵢⱼ = yᵢ - yⱼ`. Two solutions driven by the same path therefore have
`|X(t) - Y(t)|²` nonincreasing in `t`, and since they start together they agree. This is pathwise
uniqueness; it needs neither adaptedness nor any property of the driving path, and holds for
every real `β`. Existence, for which the constraint `β ≥ 1` is needed, is not proved here.

## Main definitions

* `TauCeti.Probability.dysonDrift`: the drift `x ↦ (n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹)ᵢ`.
* `TauCeti.Probability.IsDysonPath`: a deterministic path solving the Dyson system driven by a
  given path.
* `TauCeti.Probability.IsDysonSolution`: a process whose paths almost surely solve the Dyson
  system driven by the paths of `B`.

## Main results

* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub`: the monotonicity identity for the drift.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos`: the drift is monotone on each open
  Weyl chamber.
* `TauCeti.Probability.IsDysonPath.eq`: pathwise uniqueness for a fixed driving path.
* `TauCeti.Probability.IsDysonSolution.ae_eq`: two solutions driven by the same processes agree
  almost surely at all times.
* `TauCeti.Probability.isDysonPath_one`, `TauCeti.Probability.isDysonSolution_one`: for `n = 1`
  the drift vanishes and the solution is the scaled driving path.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Lemma 4.3.3 and Proposition 4.3.5.
* E. Cépa, D. Lépingle, *Diffusing particles with electrostatic repulsion*, Probab. Theory
  Related Fields 107 (1997), 429–449, for the monotonicity of the drift.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped NNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} {n : ℕ}

/-! ### The drift -/

/-- The **Dyson drift** of size `n` at `x`: its `i`-th coordinate is `n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹`,
the interaction of particle `i` with all the others. -/
def dysonDrift (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹

/-- Unfolding `dysonDrift`. -/
theorem dysonDrift_apply (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹ := (rfl)

/-- For a single particle there is no interaction: the drift vanishes. -/
@[simp]
theorem dysonDrift_one (x : Fin 1 → ℝ) : dysonDrift 1 x = 0 := by
  funext i
  simp [dysonDrift_apply, Subsingleton.elim i 0]

/-- The drift is continuous at every configuration of distinct particles. -/
theorem continuousAt_dysonDrift {x : Fin n → ℝ} (hx : Function.Injective x) :
    ContinuousAt (dysonDrift n) x := by
  refine continuousAt_pi.2 fun i ↦ continuousAt_const.mul (tendsto_finsetSum _ fun j hj ↦ ?_)
  exact ((continuous_apply i).sub (continuous_apply j)).continuousAt.inv₀
    (sub_ne_zero.2 (hx.ne (ne_of_mem_erase hj).symm))

/-- **The monotonicity identity for the Dyson drift.** For configurations `x` and `y` of distinct
particles, with `aᵢⱼ = xᵢ - xⱼ` and `bᵢⱼ = yᵢ - yⱼ`,
`∑ᵢ (Fᵢ(x) - Fᵢ(y)) (xᵢ - yᵢ) = -n⁻¹ ∑_{i<j} (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ)`. -/
theorem sum_dysonDrift_sub_mul_sub {x y : Fin n → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      -((n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i,
        ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j))) := by
  have hsym := sum_sum_Ioi_add_eq_sum_sum_off_diag
    fun j i ↦ ((x i - x j)⁻¹ - (y i - y j)⁻¹) * (x i - y i)
  simp only [compl_singleton] at hsym
  calc ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i)
      = (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ univ.erase i,
          ((x i - x j)⁻¹ - (y i - y j)⁻¹) * (x i - y i) := by
        simp only [dysonDrift_apply, ← mul_sub, ← sum_sub_distrib, mul_assoc, sum_mul, mul_sum]
    _ = -((n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i,
          ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j))) := by
        rw [← hsym, ← mul_neg, ← sum_neg_distrib]
        congr 1
        refine sum_congr rfl fun i _ ↦ ?_
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun j hj ↦ ?_
        have hij : i ≠ j := (mem_Ioi.1 hj).ne
        have ha : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne hij)
        have hb : y i - y j ≠ 0 := sub_ne_zero.2 (hy.ne hij)
        have ha' : x j - x i ≠ 0 := sub_ne_zero.2 (hx.ne hij.symm)
        have hb' : y j - y i ≠ 0 := sub_ne_zero.2 (hy.ne hij.symm)
        field_simp
        ring

/-- **The Dyson drift is monotone on each open Weyl chamber.** If `x` and `y` order their
particles in the same way, that is `(xᵢ - xⱼ) (yᵢ - yⱼ) > 0` whenever `i ≠ j`, then
`∑ᵢ (Fᵢ(x) - Fᵢ(y)) (xᵢ - yᵢ) ≤ 0`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos {x y : Fin n → ℝ}
    (h : Pairwise fun i j ↦ 0 < (x i - x j) * (y i - y j)) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  have hx : Function.Injective x := fun i j hij ↦ by
    by_contra hne
    simpa [hij] using h hne
  have hy : Function.Injective y := fun i j hij ↦ by
    by_contra hne
    simpa [hij] using h hne
  rw [sum_dysonDrift_sub_mul_sub hx hy, neg_nonpos]
  exact mul_nonneg (by positivity) (sum_nonneg fun i _ ↦ sum_nonneg fun j hj ↦
    div_nonneg (sq_nonneg _) (h (mem_Ioi.1 hj).ne).le)

/-! ### Solutions -/

/-- A path `X` **solving the Dyson system** of size `n` and parameter `β` from `x`, driven by the
path `b`: `X` is continuous, lies in the open chamber `{x₁ > ⋯ > xₙ}` at positive times, its drift
is integrable on every `[0, t]`, and
`Xᵢ(t) = xᵢ + √(2/(βn)) bᵢ(t) + ∫₀ᵗ n⁻¹ ∑_{j ≠ i} (Xᵢ(s) - Xⱼ(s))⁻¹ ds`. -/
structure IsDysonPath (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (b : Fin n → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Fin n → ℝ) : Prop where
  /-- The path is continuous. -/
  continuous : Continuous X
  /-- At positive times the particles are distinct and strictly decreasing. -/
  strictAnti : ∀ t, 0 < t → StrictAnti (X t)
  /-- The drift along the path is integrable on every `[0, t]`. -/
  intervalIntegrable (t : ℝ≥0) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift n (X s.toNNReal) i) volume 0 t
  /-- The integral form of the Dyson system. -/
  eq_add_integral (t : ℝ≥0) (i : Fin n) :
    X t i = x i + √(2 / (β * n)) * b i t + ∫ s in (0 : ℝ)..t, dysonDrift n (X s.toNNReal) i

/-- A process `X` **solving the Dyson system** of size `n` and parameter `β` from `x`, driven by
the processes `B`: almost surely its path solves the Dyson system driven by the paths of `B`.
Adaptedness of `X` to a filtration of `B` is not part of it. -/
def IsDysonSolution [MeasurableSpace Ω] (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsDysonPath β n x (fun i t ↦ B i t ω) (fun t ↦ X t ω)

/-- Unfolding `IsDysonSolution`: almost every path is an `IsDysonPath`. -/
theorem isDysonSolution_iff [MeasurableSpace Ω] {β : ℝ} {x : Fin n → ℝ} {P : Measure Ω}
    {B : Fin n → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, IsDysonPath β n x (fun i t ↦ B i t ω) (fun t ↦ X t ω) := Iff.rfl

namespace IsDysonPath

variable {β : ℝ} {x : Fin n → ℝ} {b : Fin n → ℝ≥0 → ℝ} {X Y : ℝ≥0 → Fin n → ℝ}

/-- At positive times the drift along a solution is continuous. -/
theorem continuousAt_dysonDrift (hX : IsDysonPath β n x b X) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ ↦ dysonDrift n (X s.toNNReal)) t :=
  ContinuousAt.comp (f := fun s : ℝ ↦ X s.toNNReal)
    (TauCeti.Probability.continuousAt_dysonDrift
      (hX.strictAnti _ (Real.toNNReal_pos.2 ht)).injective)
    (hX.continuous.comp continuous_real_toNNReal).continuousAt

/-- Two solutions driven by the same path differ by the integral of the difference of their
drifts. -/
theorem sub_eq_integral (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y) (t : ℝ≥0)
    (i : Fin n) :
    X t i - Y t i = ∫ s in (0 : ℝ)..t,
      (dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i) := by
  rw [intervalIntegral.integral_sub (hX.intervalIntegrable t i) (hY.intervalIntegrable t i),
    hX.eq_add_integral, hY.eq_add_integral]
  ring

/-- At a positive time, the difference of two solutions driven by the same path is differentiable,
with derivative the difference of their drifts. -/
theorem hasDerivAt_sub (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y) {t : ℝ}
    (ht : 0 < t) (i : Fin n) :
    HasDerivAt (fun s : ℝ ↦ X s.toNNReal i - Y s.toNNReal i)
      (dysonDrift n (X t.toNNReal) i - dysonDrift n (Y t.toNNReal) i) t := by
  have hcont : ContinuousOn
      (fun s : ℝ ↦ dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i)
      (Set.Ioi 0) := fun s hs ↦
    (((continuous_apply i).continuousAt.comp (hX.continuousAt_dysonDrift hs)).sub
      ((continuous_apply i).continuousAt.comp (hY.continuousAt_dysonDrift hs))).continuousWithinAt
  have hint := (hX.intervalIntegrable t.toNNReal i).sub (hY.intervalIntegrable t.toNNReal i)
  rw [Real.coe_toNNReal _ ht.le] at hint
  refine (intervalIntegral.integral_hasDerivAt_right hint
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi t ht)
    (hcont.continuousAt (isOpen_Ioi.mem_nhds ht))).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [hX.sub_eq_integral hY, Real.coe_toNNReal _ hs.le]

/-- **Pathwise uniqueness for the Dyson system.** Two solutions from the same start driven by the
same path coincide. No assumption on `β` or on the driving path is needed: the squared distance
`|X(t) - Y(t)|²` vanishes at `0` and is nonincreasing because the drift is monotone on the open
chamber. -/
theorem eq (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y) : X = Y := by
  set φ : ℝ → ℝ := fun s ↦ ∑ i, (X s.toNNReal i - Y s.toNNReal i) ^ 2
  have hφ' (t : ℝ) (ht : 0 < t) : HasDerivAt φ (2 * ∑ i,
      (dysonDrift n (X t.toNNReal) i - dysonDrift n (Y t.toNNReal) i) *
        (X t.toNNReal i - Y t.toNNReal i)) t := by
    convert HasDerivAt.fun_sum fun i _ ↦ (hX.hasDerivAt_sub hY ht i).pow 2 using 1
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    push_cast
    ring
  have hcont : Continuous φ := by
    have hXc := hX.continuous.comp continuous_real_toNNReal
    have hYc := hY.continuous.comp continuous_real_toNNReal
    exact continuous_finsetSum _ fun i _ ↦
      (((continuous_apply i).comp hXc).sub ((continuous_apply i).comp hYc)).pow 2
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
      (fun t ht ↦ (hφ' t (by simpa using ht)).differentiableAt.differentiableWithinAt)
      fun t ht ↦ ?_
    have ht : 0 < t := by simpa using ht
    rw [(hφ' t ht).deriv]
    have hXt := hX.strictAnti _ (Real.toNNReal_pos.2 ht)
    have hYt := hY.strictAnti _ (Real.toNNReal_pos.2 ht)
    -- both configurations are strictly decreasing, so they lie in the same open Weyl chamber
    refine mul_nonpos_of_nonneg_of_nonpos zero_le_two
      (sum_dysonDrift_sub_mul_sub_nonpos fun i j hij ↦ ?_)
    rcases hij.lt_or_gt with h | h
    · exact mul_pos (sub_pos.2 (hXt h)) (sub_pos.2 (hYt h))
    · exact mul_pos_of_neg_of_neg (sub_neg.2 (hXt h)) (sub_neg.2 (hYt h))
  have hφ0 : φ 0 = 0 := by
    refine sum_eq_zero fun i _ ↦ ?_
    simp [hX.sub_eq_integral hY]
  funext t
  have hle : φ t ≤ 0 := hφ0 ▸ hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 t.2) t.2
  have hsq := (sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg _).1
    (le_antisymm hle (sum_nonneg fun i _ ↦ sq_nonneg _))
  funext i
  simpa [sub_eq_zero] using hsq i (mem_univ i)

end IsDysonPath

/-- **Almost sure uniqueness for the Dyson system.** Two solutions from the same start driven by
the same processes agree almost surely at all times. -/
theorem IsDysonSolution.ae_eq [MeasurableSpace Ω] {β : ℝ} {x : Fin n → ℝ} {P : Measure Ω}
    {B : Fin n → ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → Fin n → ℝ} (hX : IsDysonSolution β n x P B X)
    (hY : IsDysonSolution β n x P B Y) : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [hX, hY] with ω hXω hYω t
  exact congrFun (hXω.eq hYω) t

/-- For a single particle the Dyson system is `dλ = √(2/β) db`: its solution is the start plus
the scaled driving path, for any continuous driving path. -/
theorem isDysonPath_one {β : ℝ} (x : Fin 1 → ℝ) {b : Fin 1 → ℝ≥0 → ℝ}
    (hb : ∀ i, Continuous (b i)) :
    IsDysonPath β 1 x b fun t i ↦ x i + √(2 / β) * b i t where
  continuous := continuous_pi fun i ↦ continuous_const.add (continuous_const.mul (hb i))
  strictAnti _ _ := Subsingleton.strictAnti _
  intervalIntegrable t i := by simp
  eq_add_integral t i := by simp

/-- For a single particle, the start plus the scaled driving processes solves the Dyson system
whenever the driving processes have almost surely continuous paths. -/
theorem isDysonSolution_one [MeasurableSpace Ω] {β : ℝ} (x : Fin 1 → ℝ) {P : Measure Ω}
    {B : Fin 1 → ℝ≥0 → Ω → ℝ} (hB : ∀ᵐ ω ∂P, ∀ i, Continuous (B i · ω)) :
    IsDysonSolution β 1 x P B fun t ω i ↦ x i + √(2 / β) * B i t ω := by
  filter_upwards [hB] with ω hω
  exact isDysonPath_one x hω

end Probability

end TauCeti
