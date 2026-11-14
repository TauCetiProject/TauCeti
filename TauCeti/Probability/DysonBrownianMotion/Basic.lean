/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# The Dyson system and its pathwise uniqueness

The **Dyson system** of size `n` and parameter `β`, driven by real processes `B₁, …, Bₙ`, is

`dλᵢ = √(2 / (β n)) dBᵢ + n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹ dt`, `i = 1, …, n`.

For `β = 1, 2` and Brownian `B` it is the equation of the ordered eigenvalues of real symmetric or
complex Hermitian matrix Brownian motion. Its noise is additive, so a solution is a pathwise
integral identity and needs no stochastic integral. This file states that identity for one path
(`TauCeti.Probability.IsDysonPath`) and almost surely
(`TauCeti.Probability.IsDysonSolution`): a continuous path, in the open chamber
`{x₁ > ⋯ > xₙ}` at positive times, whose drift is integrable on bounded time intervals.

The drift `F(x)ᵢ = n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹` is monotone (dissipative) on each open Weyl
chamber: writing `aᵢⱼ = xᵢ - xⱼ` and `bᵢⱼ = yᵢ - yⱼ`,

`⟨F(x) - F(y), x - y⟩ = -(2n)⁻¹ ∑_{i ≠ j} (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ) ≤ 0`.

Two solutions driven by the same path therefore have a difference `D` with
`d|D|² / dt = 2 ⟨D, F(X) - F(Y)⟩ ≤ 0` at positive times, and `D(0) = 0`; so they coincide. This
is pathwise uniqueness, and it needs neither adaptedness nor any property of the driving path,
nor the restriction `β ≥ 1` under which solutions exist.

## Main declarations

* `TauCeti.Probability.dysonDrift`: the drift `n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹`.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub`: the monotonicity identity.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos`: the drift is monotone on each open
  Weyl chamber.
* `TauCeti.Probability.IsDysonPath`, `TauCeti.Probability.IsDysonSolution`: solutions of the
  Dyson system along one path, and almost surely.
* `TauCeti.Probability.IsDysonPath.unique`, `TauCeti.Probability.IsDysonSolution.ae_eq`: pathwise
  uniqueness.
* `TauCeti.Probability.isDysonSolution_one`: for `n = 1` and Brownian `B`, the process
  `x + √(2 / β) B` is the solution.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1 (Lemma 4.3.3 and Proposition 4.3.5).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace TauCeti.Probability

variable {n : ℕ}

/-- The **Dyson drift** `F(x)ᵢ = n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹`, the drift of the Dyson system of
size `n`. -/
def dysonDrift (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹

/-- The defining formula of the Dyson drift. -/
theorem dysonDrift_apply (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ := by
  rw [dysonDrift]

/-- The diagonal term `(xᵢ - xᵢ)⁻¹` vanishes, so the Dyson drift is also a sum over all `j`. -/
theorem dysonDrift_eq_sum (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j, (x i - x j)⁻¹ := by
  rw [dysonDrift_apply, Finset.sum_erase _ (by simp)]

/-- The Dyson drift is continuous at every point with distinct coordinates. -/
theorem continuousAt_dysonDrift {x : Fin n → ℝ} (hx : Function.Injective x) :
    ContinuousAt (dysonDrift n) x := by
  refine continuousAt_pi.2 fun i ↦ ?_
  simp only [dysonDrift_apply]
  refine continuousAt_const.mul <| tendsto_finsetSum _ fun j hj ↦ ?_
  refine ((continuous_apply i).sub (continuous_apply j)).continuousAt.inv₀ ?_
  exact sub_ne_zero.2 (hx.ne (Finset.ne_of_mem_erase hj).symm)

/-- **The monotonicity identity for the Dyson drift.** For `x` and `y` with distinct
coordinates, `⟨F(x) - F(y), x - y⟩ = -(2n)⁻¹ ∑_{i, j} (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ)`, where
`aᵢⱼ = xᵢ - xⱼ` and `bᵢⱼ = yᵢ - yⱼ` (the diagonal terms vanish). -/
theorem sum_dysonDrift_sub_mul_sub {x y : Fin n → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      -(2 * n : ℝ)⁻¹ * ∑ i, ∑ j,
        ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) := by
  -- `f i j = aᵢⱼ⁻¹ - bᵢⱼ⁻¹` is antisymmetric, so swapping `i` and `j` symmetrizes the sum.
  obtain ⟨f, hf⟩ : ∃ f : Fin n → Fin n → ℝ, ∀ i j, f i j = (x i - x j)⁻¹ - (y i - y j)⁻¹ :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hS : ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      (n : ℝ)⁻¹ * ∑ i, ∑ j, f i j * (x i - y i) := by
    simp only [dysonDrift_eq_sum, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul, hf, mul_assoc]
  have hanti (i j : Fin n) : f j i = -f i j := by
    rw [hf, hf, ← neg_sub (x i), ← neg_sub (y i), inv_neg, inv_neg]
    ring
  have hterm (i j : Fin n) : ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) =
      f i j * (x j - y j) - f i j * (x i - y i) := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    rw [hf, inv_sub_inv (sub_ne_zero.2 (hx.ne hij)) (sub_ne_zero.2 (hy.ne hij))]
    ring
  have hswap : ∑ i, ∑ j, f i j * (x i - y i) = -∑ i, ∑ j, f i j * (x j - y j) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hanti i j, neg_mul]
  rw [hS]
  simp only [hterm, Finset.sum_sub_distrib]
  rw [hswap]
  ring

/-- **The Dyson drift is monotone on each open Weyl chamber**: if every pair of coordinates of
`x` is ordered as the corresponding pair of `y`, then `⟨F(x) - F(y), x - y⟩ ≤ 0`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos {x y : Fin n → ℝ}
    (hxy : ∀ i j, i ≠ j → 0 < (x i - x j) * (y i - y j)) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  have hx : Function.Injective x := fun i j h ↦ by_contra fun hij ↦ by simpa [h] using hxy i j hij
  have hy : Function.Injective y := fun i j h ↦ by_contra fun hij ↦ by simpa [h] using hxy i j hij
  rw [sum_dysonDrift_sub_mul_sub hx hy, neg_mul]
  refine neg_nonpos.2 (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ ?_))
  rcases eq_or_ne i j with rfl | hij
  · simp
  · exact div_nonneg (sq_nonneg _) (hxy i j hij).le

/-- Two strictly decreasing vectors lie in the same open Weyl chamber, so the Dyson drift is
monotone on `{x₁ > ⋯ > xₙ}`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos_of_strictAnti {x y : Fin n → ℝ} (hx : StrictAnti x)
    (hy : StrictAnti y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  refine sum_dysonDrift_sub_mul_sub_nonpos fun i j hij ↦ ?_
  rcases hij.lt_or_gt with h | h
  · exact mul_pos (sub_pos.2 (hx h)) (sub_pos.2 (hy h))
  · exact mul_pos_of_neg_of_neg (sub_neg.2 (hx h)) (sub_neg.2 (hy h))

/-- A path `X` solves the **Dyson system** of size `n` and parameter `β` from `x`, driven by the
path `b`: `X` is continuous, lies in the open chamber `{x₁ > ⋯ > xₙ}` at every positive time,
its drift is integrable on every interval `[0, t]`, and for every time `t` and index `i`

`Xᵢ(t) = xᵢ + √(2 / (β n)) bᵢ(t) + ∫₀ᵗ n⁻¹ ∑_{j ≠ i} (Xᵢ(s) - Xⱼ(s))⁻¹ ds`. -/
structure IsDysonPath (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (b : Fin n → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Fin n → ℝ) : Prop where
  /-- The path is continuous. -/
  continuous : Continuous X
  /-- At positive times the path lies in the open chamber `{x₁ > ⋯ > xₙ}`. -/
  strictAnti : ∀ t, 0 < t → StrictAnti (X t)
  /-- The drift along the path is integrable on every interval `[0, t]`. -/
  intervalIntegrable : ∀ (t : ℝ≥0) (i : Fin n),
    IntervalIntegrable (fun s : ℝ ↦ dysonDrift n (X s.toNNReal) i) volume 0 t
  /-- The integral form of the Dyson system. -/
  apply_eq : ∀ (t : ℝ≥0) (i : Fin n), X t i = x i + √(2 / (β * n)) * b i t +
    ∫ s in (0 : ℝ)..t, dysonDrift n (X s.toNNReal) i

namespace IsDysonPath

variable {β : ℝ} {x : Fin n → ℝ} {b : Fin n → ℝ≥0 → ℝ} {X Y : ℝ≥0 → Fin n → ℝ}

/-- A solution of the Dyson system starts at its initial condition. -/
theorem apply_zero (hX : IsDysonPath β n x b X) : X 0 = x + √(2 / (β * n)) • fun i ↦ b i 0 := by
  ext i
  simp [hX.apply_eq 0 i]

/-- The drift of a solution of the Dyson system is continuous at positive times. -/
theorem continuousOn_dysonDrift (hX : IsDysonPath β n x b X) (i : Fin n) :
    ContinuousOn (fun s : ℝ ↦ dysonDrift n (X s.toNNReal) i) (Ioi 0) := fun s hs ↦ by
  have h : ContinuousAt (fun r : ℝ ↦ X r.toNNReal) s :=
    (hX.continuous.comp continuous_real_toNNReal).continuousAt
  exact ((continuous_apply i).continuousAt.comp ((continuousAt_dysonDrift
    (hX.strictAnti _ (Real.toNNReal_pos.2 hs)).injective).comp (x := s) h)).continuousWithinAt

/-- The difference of two solutions of the Dyson system driven by the same path is
differentiable at positive times, with derivative the difference of their drifts. -/
theorem hasDerivAt_sub (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y) (i : Fin n)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ ↦ X r.toNNReal i - Y r.toNNReal i)
      (dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i) s := by
  have hFTC {Z : ℝ≥0 → Fin n → ℝ} (hZ : IsDysonPath β n x b Z) :
      HasDerivAt (fun r ↦ ∫ u in (0 : ℝ)..r, dysonDrift n (Z u.toNNReal) i)
        (dysonDrift n (Z s.toNNReal) i) s := by
    have h := hZ.intervalIntegrable s.toNNReal i
    rw [Real.coe_toNNReal _ hs.le] at h
    exact intervalIntegral.integral_hasDerivAt_right h
      ((hZ.continuousOn_dysonDrift i).stronglyMeasurableAtFilter isOpen_Ioi s hs)
      ((hZ.continuousOn_dysonDrift i).continuousAt (isOpen_Ioi.mem_nhds hs))
  refine ((hFTC hX).fun_sub (hFTC hY)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with r (hr : 0 < r)
  rw [hX.apply_eq, hY.apply_eq, Real.coe_toNNReal _ hr.le]
  ring

/-- **Pathwise uniqueness for the Dyson system.** Two solutions of the Dyson system from the same
start, driven by the same path, coincide. -/
theorem unique (hX : IsDysonPath β n x b X) (hY : IsDysonPath β n x b Y) : X = Y := by
  -- The squared distance `φ(r) = ‖X(r) - Y(r)‖²` is continuous, vanishes at `0` and has
  -- derivative `2 ⟨X - Y, F(X) - F(Y)⟩ ≤ 0` at positive times, so it vanishes identically.
  set φ : ℝ → ℝ := fun r ↦ ∑ i, (X r.toNNReal i - Y r.toNNReal i) ^ 2 with hφ
  have hcont : Continuous φ := continuous_finsetSum _ fun i _ ↦
    (((continuous_apply i).comp hX.continuous).sub ((continuous_apply i).comp hY.continuous)).comp
      continuous_real_toNNReal |>.pow 2
  have hanti : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hcont.continuousOn
      (f' := fun s ↦ 2 * ∑ i, (dysonDrift n (X s.toNNReal) i - dysonDrift n (Y s.toNNReal) i) *
        (X s.toNNReal i - Y s.toNNReal i)) (fun s hs ↦ ?_) fun s hs ↦ ?_
    · rw [interior_Ici] at hs
      refine HasDerivAt.hasDerivWithinAt ?_
      convert HasDerivAt.fun_sum fun i _ ↦ (hX.hasDerivAt_sub hY i hs).pow 2 using 1
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
    · rw [interior_Ici] at hs
      exact mul_nonpos_of_nonneg_of_nonpos zero_le_two
        (sum_dysonDrift_sub_mul_sub_nonpos_of_strictAnti (hX.strictAnti _ (Real.toNNReal_pos.2 hs))
          (hY.strictAnti _ (Real.toNNReal_pos.2 hs)))
  have h0 : φ 0 = 0 := by simp [hφ, hX.apply_zero, hY.apply_zero]
  funext t
  have ht : φ t = 0 := le_antisymm (h0 ▸ hanti self_mem_Ici t.2 t.2)
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  simp only [hφ, Real.toNNReal_coe] at ht
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg _] at ht
  funext i
  simpa [sub_eq_zero] using ht i (Finset.mem_univ i)

end IsDysonPath

/-- For `n = 1` the Dyson system has no drift: `x + √(2 / β) b` is its solution driven by a
continuous path `b`. -/
theorem isDysonPath_one {β : ℝ} {x : Fin 1 → ℝ} {b : Fin 1 → ℝ≥0 → ℝ}
    (hb : ∀ i, Continuous (b i)) :
    IsDysonPath β 1 x b (fun t i ↦ x i + √(2 / β) * b i t) where
  continuous := continuous_pi fun i ↦ continuous_const.add (continuous_const.mul (hb i))
  strictAnti _ _ := Subsingleton.strictAnti _
  intervalIntegrable _ i := by
    obtain rfl := Subsingleton.elim i 0
    simp [dysonDrift_apply]
  apply_eq _ i := by
    obtain rfl := Subsingleton.elim i 0
    simp [dysonDrift_apply]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A process `X` solves the **Dyson system** of size `n` and parameter `β` from `x`, driven by
the processes `B`, if almost every path of `X` solves it driven by the corresponding path of `B`
(`IsDysonPath`). Adaptedness to a filtration of `B` is not part of it. -/
def IsDysonSolution (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω)
    (B : Fin n → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsDysonPath β n x (fun i t ↦ B i t ω) (fun t ↦ X t ω)

/-- A solution of the Dyson system is a process almost every path of which solves it. -/
theorem isDysonSolution_iff {β : ℝ} {x : Fin n → ℝ} {P : Measure Ω} {B : Fin n → ℝ≥0 → Ω → ℝ}
    {X : ℝ≥0 → Ω → Fin n → ℝ} :
    IsDysonSolution β n x P B X ↔
      ∀ᵐ ω ∂P, IsDysonPath β n x (fun i t ↦ B i t ω) (fun t ↦ X t ω) := by
  rw [IsDysonSolution]

/-- **Pathwise uniqueness for the Dyson system** (the uniqueness part of
Anderson–Guionnet–Zeitouni, Lemma 4.3.3 and Proposition 4.3.5). Two solutions of the Dyson system
from the same start, driven by the same processes, are almost surely equal at all times. No
adaptedness or Brownian hypothesis is needed. -/
theorem IsDysonSolution.ae_eq {β : ℝ} {x : Fin n → ℝ} {P : Measure Ω}
    {B : Fin n → ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → Fin n → ℝ} (hX : IsDysonSolution β n x P B X)
    (hY : IsDysonSolution β n x P B Y) : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  filter_upwards [hX, hY] with ω hXω hYω t
  exact congrFun (hXω.unique hYω) t

/-- For `n = 1` and Brownian `B`, the process `x + √(2 / β) B` solves the Dyson system. -/
theorem isDysonSolution_one {β : ℝ} {x : Fin 1 → ℝ} {P : Measure Ω} {B : Fin 1 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) :
    IsDysonSolution β 1 x P B (fun t ω i ↦ x i + √(2 / β) * B i t ω) := by
  filter_upwards [ae_all_iff.2 fun i ↦ (hB i).cont] with ω hω
  exact isDysonPath_one hω

end TauCeti.Probability
