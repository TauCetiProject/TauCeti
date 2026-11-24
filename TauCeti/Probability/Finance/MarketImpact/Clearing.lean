/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.Deriv.Inverse
import TauCeti.Order.Monotone.InvFunOn

/-!
# Global market clearing with program-trader demand

A market with total asset supply one, reference demand `D(x, y) = c(y) / x` at asset price
`x > 0` and income `y`, and program-trader demand `H(x)` clears when `D(x, y) + H(x) = 1`. For
positive `x` this is the equation

`x (1 - H(x)) = c(y)`,

so equilibrium prices are the positive solutions of `clearingMap H x = c(y)`, where
`clearingMap H x = x (1 - H(x))` (`clearingMap_eq_iff_div_add_eq_one`). In the linear-demand
model `c(y) = d₀ y^γ`; for a single claim with price `C`, the program-trader demand is
`H = ρ ∂ₓC`.

The derivative of the clearing map is `1 - H(x) - x H'(x)`. Suppose `H` is differentiable on the
positive half-line, this derivative is bounded below by `δ > 0` there, and the clearing map
tends to zero as `x ↓ 0`. Then:

* the clearing map grows at rate at least `δ`: `δ (x₂ - x₁) ≤ x₂(1 - H(x₂)) - x₁(1 - H(x₁))`
  for `0 < x₁ ≤ x₂` (`mul_sub_le_clearingMap_sub`), so it is strictly increasing and tends to
  infinity;
* the inverse (the equilibrium price as a function of `c(y)`) is strictly increasing and
  Lipschitz with constant `δ⁻¹` on the range of the clearing map, and differentiable with
  derivative the reciprocal of the clearing derivative;
* `δ x ≤ x (1 - H(x))`, hence `δ ≤ 1 - H(x)`;
* the clearing map is a bijection of `(0, ∞)` onto itself (`bijOn_clearingMap`): every positive
  value of `c(y)` has exactly one positive equilibrium price (`existsUnique_clearingMap_eq`).

Only the last two items use the limit at zero; the others need only the margin. Strict
monotonicity of the clearing map and of its inverse, and the derivative of the inverse, need only
that the clearing derivative is positive at each positive price (`strictMonoOn_clearingMap`,
`hasDerivAt_invFunOn_clearingMap`).

Without the margin, strict monotonicity and the endpoint limits do not give a differentiable
inverse: `x (1 - H(x)) = 1 + (x - 1)³` has a critical point at `x = 1`.

## Main declarations

* `TauCeti.Finance.clearingMap`: the clearing map `x (1 - H(x))`.
* `TauCeti.Finance.existsUnique_clearingMap_eq`: global clearing, a unique positive equilibrium
  price for each positive right-hand side.
* `TauCeti.Finance.bijOn_clearingMap`: the clearing map is a bijection of `(0, ∞)`.
* `TauCeti.Finance.lipschitzOnWith_invFunOn_clearingMap`,
  `TauCeti.Finance.hasDerivAt_invFunOn_clearingMap`: Lipschitz bound and derivative of the
  equilibrium price.

## References

* R. Sircar, G. Papanicolaou, *General Black–Scholes models accounting for increased market
  volatility from hedging strategies*, Applied Mathematical Finance 5 (1998), 45–82, §2.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.Finance

variable {H : ℝ → ℝ} {δ x y : ℝ}

/-- The clearing map `x ↦ x (1 - H(x))` for a program-trader demand `H`. With reference demand
`c / x`, a positive price `x` clears the market exactly when `clearingMap H x = c`. -/
def clearingMap (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (1 - H x)

/-- Unfold the clearing map. -/
theorem clearingMap_def (H : ℝ → ℝ) (x : ℝ) : clearingMap H x = x * (1 - H x) :=
  (rfl)

/-- For a nonzero price `x`, the clearing equation `c / x + H(x) = 1` for reference demand
`c / x` is the equation `clearingMap H x = c`. -/
theorem clearingMap_eq_iff_div_add_eq_one (hx : x ≠ 0) (c : ℝ) :
    clearingMap H x = c ↔ c / x + H x = 1 := by
  rw [clearingMap_def]
  field_simp
  constructor <;> intro h <;> linarith

/-- The derivative of the clearing map `x (1 - H(x))` is `1 - H(x) - x H'(x)`. -/
theorem _root_.HasDerivAt.clearingMap {h : ℝ} (hH : HasDerivAt H h x) :
    HasDerivAt (clearingMap H) (1 - H x - x * h) x := by
  convert (hasDerivAt_id x).mul (hH.const_sub 1) using 1
  · exact funext fun y ↦ clearingMap_def H y
  · simp only [id_eq]
    ring

/-- If the program-trader demand `H` is differentiable at `x`, the clearing map has derivative
`1 - H(x) - x H'(x)` there. -/
theorem hasDerivAt_clearingMap (hH : DifferentiableAt ℝ H x) :
    HasDerivAt (clearingMap H) (1 - H x - x * deriv H x) x :=
  hH.hasDerivAt.clearingMap

/-- If the program-trader demand `H` is differentiable at `x`, the derivative of the clearing map
there is `1 - H(x) - x H'(x)`. -/
theorem deriv_clearingMap (hH : DifferentiableAt ℝ H x) :
    deriv (clearingMap H) x = 1 - H x - x * deriv H x :=
  (hasDerivAt_clearingMap hH).deriv

/-- The clearing map is continuous wherever the program-trader demand is. -/
theorem continuousOn_clearingMap {s : Set ℝ} (hH : ContinuousOn H s) :
    ContinuousOn (clearingMap H) s :=
  continuousOn_id.mul (continuousOn_const.sub hH)

section Pos

variable (hH : DifferentiableOn ℝ H (Ioi 0)) (hpos : ∀ x, 0 < x → 0 < 1 - H x - x * deriv H x)
include hH hpos

/-- A positive clearing derivative `1 - H(x) - x H'(x)` makes the clearing map strictly
increasing on the positive half-line. -/
theorem strictMonoOn_clearingMap : StrictMonoOn (clearingMap H) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (continuousOn_clearingMap hH.continuousOn)
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  exact (deriv_clearingMap ((hH x hx).differentiableAt (Ioi_mem_nhds hx))).symm ▸ hpos x hx

/-- Under a positive clearing derivative, the equilibrium price recovers every positive price
from its clearing value. -/
theorem invFunOn_clearingMap (hx : 0 < x) :
    invFunOn (clearingMap H) (Ioi 0) (clearingMap H x) = x :=
  (strictMonoOn_clearingMap hH hpos).injOn.leftInvOn_invFunOn hx

/-- Under a positive clearing derivative, the equilibrium price is strictly increasing on the
range of the clearing map. -/
theorem strictMonoOn_invFunOn_clearingMap :
    StrictMonoOn (invFunOn (clearingMap H) (Ioi 0)) (clearingMap H '' Ioi 0) :=
  (strictMonoOn_clearingMap hH hpos).invFunOn

/-- Under a positive clearing derivative, the equilibrium price is differentiable: at the
clearing value of a positive price `x`, its derivative is the reciprocal of the clearing
derivative `1 - H(x) - x H'(x)`. -/
theorem hasDerivAt_invFunOn_clearingMap (hx : 0 < x) :
    HasDerivAt (invFunOn (clearingMap H) (Ioi 0)) (1 - H x - x * deriv H x)⁻¹
      (clearingMap H x) :=
  (strictMonoOn_clearingMap hH hpos).hasDerivAt_invFunOn
    (continuousOn_clearingMap hH.continuousOn) (Ioi_mem_nhds hx)
    (hasDerivAt_clearingMap ((hH x hx).differentiableAt (Ioi_mem_nhds hx))) (hpos x hx).ne'

end Pos

section Margin

variable (hH : DifferentiableOn ℝ H (Ioi 0)) (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
include hH hmargin

/-- A lower bound `δ` on the clearing derivative `1 - H(x) - x H'(x)` makes the clearing map
grow at rate at least `δ` on the positive half-line. -/
theorem mul_sub_le_clearingMap_sub {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) :
    δ * (x₂ - x₁) ≤ clearingMap H x₂ - clearingMap H x₁ := by
  refine (convex_Ioi 0).mul_sub_le_image_sub_of_le_deriv (continuousOn_clearingMap hH.continuousOn)
    (fun x hx ↦ (hasDerivAt_clearingMap ((hH x (interior_subset hx)).differentiableAt
      (mem_interior_iff_mem_nhds.1 hx))).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ ?_) x₁ hx₁ x₂ (hx₁.trans_le hx) hx
  rw [interior_Ioi] at hx
  exact (deriv_clearingMap ((hH x hx).differentiableAt (Ioi_mem_nhds hx))).symm ▸ hmargin x hx

/-- Under a lower bound `δ` on the clearing derivative, positive prices at distance `d` have
clearing values at distance at least `δ d`. -/
theorem mul_abs_sub_le_abs_clearingMap_sub {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    δ * |x₂ - x₁| ≤ |clearingMap H x₂ - clearingMap H x₁| := by
  rcases le_total x₁ x₂ with hx | hx
  · rw [abs_of_nonneg (sub_nonneg.2 hx)]
    exact (mul_sub_le_clearingMap_sub hH hmargin hx₁ hx).trans (le_abs_self _)
  · rw [abs_sub_comm x₂, abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm]
    exact (mul_sub_le_clearingMap_sub hH hmargin hx₂ hx).trans (le_abs_self _)

/-- A lower bound `δ > 0` on the clearing derivative makes the equilibrium price Lipschitz with
constant `δ⁻¹` on the range of the clearing map. -/
theorem lipschitzOnWith_invFunOn_clearingMap (hδ : 0 < δ) :
    LipschitzOnWith (Real.toNNReal δ⁻¹) (invFunOn (clearingMap H) (Ioi 0))
      (clearingMap H '' Ioi 0) := by
  refine lipschitzOnWith_iff_restrict.2 (AntilipschitzWith.to_rightInvOn' ?_
    (surjOn_image _ _).mapsTo_invFunOn (surjOn_image _ _).rightInvOn_invFunOn)
  refine AntilipschitzWith.of_le_mul_dist fun x₁ x₂ ↦ ?_
  simp only [Real.coe_toNNReal _ (inv_nonneg.2 hδ.le), Subtype.dist_eq, domRestrict_apply,
    Real.dist_eq]
  exact (le_inv_mul_iff₀ hδ).2 (mul_abs_sub_le_abs_clearingMap_sub hH hmargin x₂.property
      x₁.property)

/-- Under a strictly positive clearing-derivative margin, the clearing map tends to infinity with
the price. -/
theorem tendsto_clearingMap_atTop (hδ : 0 < δ) : Tendsto (clearingMap H) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (clearingMap H 1 - δ)
    (tendsto_id.const_mul_atTop hδ))
  filter_upwards [eventually_ge_atTop 1] with x hx
  dsimp only [id]
  linarith [mul_sub_le_clearingMap_sub hH hmargin one_pos hx]

variable (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0))
include hzero

/-- If the clearing map tends to zero at zero price, a lower bound `δ` on the clearing
derivative gives the lower bound `δ x ≤ x (1 - H(x))` for positive `x`. -/
theorem mul_le_clearingMap (hx : 0 < x) : δ * x ≤ clearingMap H x := by
  have hlim : Tendsto (fun x₁ ↦ δ * (x - x₁) + clearingMap H x₁) (𝓝[>] 0) (𝓝 (δ * x)) := by
    simpa using ((tendsto_const_nhds.sub
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).const_mul δ).add hzero
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with x₁ hx₁
  linarith [mul_sub_le_clearingMap_sub hH hmargin hx₁.1 hx₁.2.le]

/-- If the clearing map tends to zero at zero price, a lower bound `δ` on the clearing
derivative also bounds the clearing factor: `δ ≤ 1 - H(x)` for positive `x`. -/
theorem le_one_sub_of_tendsto_clearingMap (hx : 0 < x) : δ ≤ 1 - H x := by
  have := mul_le_clearingMap hH hmargin hzero hx
  rw [clearingMap_def, mul_comm δ] at this
  exact le_of_mul_le_mul_left this hx

/-- Under a strictly positive clearing-derivative margin and the zero limit at zero price, the
clearing map is a bijection of the positive half-line onto itself. -/
theorem bijOn_clearingMap (hδ : 0 < δ) : BijOn (clearingMap H) (Ioi 0) (Ioi 0) := by
  refine ⟨fun x hx ↦ ?_,
    (strictMonoOn_clearingMap hH fun x hx ↦ hδ.trans_le (hmargin x hx)).injOn, fun y hy ↦ ?_⟩
  · exact (mul_pos hδ hx).trans_le (mul_le_clearingMap hH hmargin hzero hx)
  obtain ⟨a, hay, ha⟩ :=
    ((hzero.eventually (gt_mem_nhds hy)).and self_mem_nhdsWithin).exists
  obtain ⟨b, hby, hab⟩ := ((tendsto_clearingMap_atTop hH hmargin hδ).eventually_gt_atTop y
    |>.and (eventually_ge_atTop a)).exists
  have hcont : ContinuousOn (clearingMap H) (Icc a b) :=
    (continuousOn_clearingMap hH.continuousOn).mono fun x hx ↦ ha.trans_le hx.1
  obtain ⟨x, hx, rfl⟩ := intermediate_value_Icc hab hcont ⟨hay.le, hby.le⟩
  exact ⟨x, ha.trans_le hx.1, rfl⟩

/-- **Global clearing.** If the program-trader demand `H` is differentiable on the positive
half-line with clearing derivative `1 - H(x) - x H'(x) ≥ δ > 0` there, and `x (1 - H(x)) → 0`
as `x ↓ 0`, then for every `y > 0` there is exactly one positive price `x` with
`x (1 - H(x)) = y`. -/
theorem existsUnique_clearingMap_eq (hδ : 0 < δ) (hy : 0 < y) :
    ∃! x, 0 < x ∧ clearingMap H x = y := by
  have h := bijOn_clearingMap hH hmargin hzero hδ
  obtain ⟨x, hx, rfl⟩ := h.surjOn hy
  exact ⟨x, ⟨hx, rfl⟩, fun x' hx' ↦ h.injOn hx'.1 hx hx'.2⟩

/-- The equilibrium price `invFunOn (clearingMap H) (Ioi 0)` maps positive right-hand sides
bijectively onto positive prices. -/
theorem bijOn_invFunOn_clearingMap (hδ : 0 < δ) :
    BijOn (invFunOn (clearingMap H) (Ioi 0)) (Ioi 0) (Ioi 0) :=
  (bijOn_clearingMap hH hmargin hzero hδ).symm
    (bijOn_clearingMap hH hmargin hzero hδ).invOn_invFunOn.symm

/-- The equilibrium price solves the clearing equation: for `y > 0`,
`clearingMap H (invFunOn (clearingMap H) (Ioi 0) y) = y`. -/
theorem clearingMap_invFunOn (hδ : 0 < δ) (hy : 0 < y) :
    clearingMap H (invFunOn (clearingMap H) (Ioi 0) y) = y :=
  (bijOn_clearingMap hH hmargin hzero hδ).invOn_invFunOn.2 hy

/-- The equilibrium price is strictly increasing in the positive right-hand side of the
clearing equation. -/
theorem strictMonoOn_invFunOn_clearingMap_Ioi (hδ : 0 < δ) :
    StrictMonoOn (invFunOn (clearingMap H) (Ioi 0)) (Ioi 0) :=
  (strictMonoOn_invFunOn_clearingMap hH fun x hx ↦ hδ.trans_le (hmargin x hx)).mono
    (bijOn_clearingMap hH hmargin hzero hδ).surjOn

/-- The equilibrium price is Lipschitz with constant `δ⁻¹` in the positive right-hand side of the
clearing equation. -/
theorem lipschitzOnWith_invFunOn_clearingMap_Ioi (hδ : 0 < δ) :
    LipschitzOnWith (Real.toNNReal δ⁻¹) (invFunOn (clearingMap H) (Ioi 0)) (Ioi 0) :=
  (lipschitzOnWith_invFunOn_clearingMap hH hmargin hδ).mono
    (bijOn_clearingMap hH hmargin hzero hδ).surjOn

end Margin

end TauCeti.Finance
