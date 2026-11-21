/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Global market clearing with program-trader demand

When program traders hold `H(x)` shares of an asset at price `x` and reference traders demand
`c / x` shares, clearing against a total supply of one share means `c / x + H(x) = 1`. For
`x > 0` this is the equation `clearingMap H x = c` for the *clearing map*

`clearingMap H x = x (1 - H(x))`.

In the linear-consistency model of feedback hedging the reference demand is `d₀ y^γ / x` for
income `y > 0`, so `c = d₀ y^γ`. The equilibrium asset price is then the positive root of
`x (1 - H(x)) = d₀ y^γ`.

This file proves that the root exists and is unique under two conditions:

* a uniform derivative margin `δ ≤ 1 - H x - x H'(x)` with `δ > 0` for all `x > 0`; the right
  side is the derivative of the clearing map (`deriv_clearingMap`);
* the zero limit `x (1 - H(x)) → 0` as `x ↓ 0`.

The margin makes the clearing map grow at least at rate `δ` (`mul_sub_le_clearingMap_sub`), and
together with the zero limit it gives `δ x ≤ x (1 - H(x))` (`mul_le_clearingMap`). In
particular the residual reference demand `1 - H(x)` is at least `δ`
(`le_one_sub_of_clearing_margin`). The margin alone makes the clearing map tend to infinity
(`tendsto_clearingMap_atTop`). The intermediate value theorem then shows that the clearing map
is a bijection of `(0, ∞)` onto itself (`bijOn_clearingMap`), so every positive income level
has exactly one positive equilibrium price (`existsUnique_clearingMap_eq`, and
`existsUnique_div_add_eq_one` in the market form `c / x + H x = 1`).

The equilibrium price as a function of `c` is packaged as the order isomorphism
`clearingOrderIso` of `(0, ∞)`. Its inverse is monotone and Lipschitz with constant `1 / δ`
(`lipschitzWith_clearingOrderIso_symm`).

A pointwise positive derivative already makes the clearing map strictly increasing
(`strictMonoOn_clearingMap`), but it does not give a root for every level: `1 - e^{-x}` has
positive derivative and zero limit at `0`, yet never reaches `1`. Hence the uniform margin.

## References

* R. Sircar and G. Papanicolaou, *General Black–Scholes models accounting for increased market
  volatility from hedging strategies*, Appl. Math. Finance 5 (1998), 45–82, §2.3.
-/

public section

noncomputable section

open Filter Set
open scoped Topology NNReal

namespace TauCeti.Finance

variable {H : ℝ → ℝ} {δ x x' c : ℝ}

/-- The **clearing map** `x ↦ x (1 - H(x))` of a program-trader demand `H`. A positive price `x`
clears the market against the reference demand `c / x` exactly when `clearingMap H x = c`
(`div_add_eq_one_iff_clearingMap_eq`). -/
def clearingMap (H : ℝ → ℝ) (x : ℝ) : ℝ := x * (1 - H x)

/-- Unfolding equation for `clearingMap`. -/
theorem clearingMap_def (H : ℝ → ℝ) (x : ℝ) : clearingMap H x = x * (1 - H x) := (rfl)

/-- A positive price clears the market against the reference demand `c / x` exactly when the
clearing map takes the value `c` there. -/
theorem div_add_eq_one_iff_clearingMap_eq (hx : x ≠ 0) :
    c / x + H x = 1 ↔ clearingMap H x = c := by
  rw [← eq_sub_iff_add_eq, div_eq_iff hx, clearingMap_def]
  exact ⟨fun h ↦ by rw [h]; ring, fun h ↦ by rw [← h]; ring⟩

/-- The derivative of the clearing map is the clearing margin `1 - H x - x H'(x)`. -/
theorem hasDerivAt_clearingMap {H' : ℝ} (hH : HasDerivAt H H' x) :
    HasDerivAt (clearingMap H) (1 - H x - x * H') x := by
  exact ((hasDerivAt_id' x).fun_mul (hH.const_sub 1)).congr_deriv (by ring)

/-- The derivative of the clearing map at a point where the demand is differentiable. -/
theorem deriv_clearingMap (hH : DifferentiableAt ℝ H x) :
    deriv (clearingMap H) x = 1 - H x - x * deriv H x :=
  (hasDerivAt_clearingMap hH.hasDerivAt).deriv

/-- The clearing map is differentiable wherever the demand is. -/
theorem differentiableOn_clearingMap {s : Set ℝ} (hH : DifferentiableOn ℝ H s) :
    DifferentiableOn ℝ (clearingMap H) s :=
  differentiableOn_id.fun_mul (hH.const_sub 1)

/-- A positive clearing margin at every positive price makes the clearing map strictly
increasing on the positive prices. -/
theorem strictMonoOn_clearingMap (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → 0 < 1 - H x - x * deriv H x) :
    StrictMonoOn (clearingMap H) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (differentiableOn_clearingMap hH).continuousOn
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [deriv_clearingMap (hH.differentiableAt (Ioi_mem_nhds hx))]
  exact hmargin x hx

/-- A clearing margin of at least `δ` makes the clearing map grow at rate at least `δ` on the
positive prices. -/
theorem mul_sub_le_clearingMap_sub (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x) (hx : 0 < x) (hxx' : x ≤ x') :
    δ * (x' - x) ≤ clearingMap H x' - clearingMap H x := by
  refine (convex_Ioi 0).mul_sub_le_image_sub_of_le_deriv
    (differentiableOn_clearingMap hH).continuousOn (by simpa using differentiableOn_clearingMap hH)
    (fun y hy ↦ ?_) x hx x' (hx.trans_le hxx') hxx'
  rw [interior_Ioi] at hy
  rw [deriv_clearingMap (hH.differentiableAt (Ioi_mem_nhds hy))]
  exact hmargin y hy

/-- A clearing margin of at least `δ` and the zero limit at zero price bound the clearing map
below by `δ x`. -/
theorem mul_le_clearingMap (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) (hx : 0 < x) :
    δ * x ≤ clearingMap H x := by
  have hlim : Tendsto (fun y ↦ δ * (x - y) + clearingMap H y) (𝓝[>] 0) (𝓝 (δ * x)) := by
    have hcont : Tendsto (fun y : ℝ ↦ δ * (x - y)) (𝓝[>] 0) (𝓝 (δ * (x - 0))) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simpa using hcont.add hzero
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with y hy
  linarith [mul_sub_le_clearingMap_sub hH hmargin hy.1 hy.2.le]

/-- Under a clearing margin of at least `δ` and the zero limit at zero price, program traders
leave at least `δ` shares of residual demand at every positive price: `δ ≤ 1 - H x`. -/
theorem le_one_sub_of_clearing_margin (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) (hx : 0 < x) :
    δ ≤ 1 - H x := by
  have := mul_le_clearingMap hH hmargin hzero hx
  rw [clearingMap_def, mul_comm] at this
  exact le_of_mul_le_mul_left this hx

/-- A positive uniform clearing margin makes the clearing map tend to infinity. -/
theorem tendsto_clearingMap_atTop (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x) :
    Tendsto (clearingMap H) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (clearingMap H 1)
    ((tendsto_atTop_add_const_right _ (-1) tendsto_id).const_mul_atTop hδ))
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [id_eq]
  linarith [mul_sub_le_clearingMap_sub hH hmargin one_pos hx]

/-- A positive uniform clearing margin and the zero limit at zero price make the clearing map a
bijection of the positive prices onto the positive levels. -/
theorem bijOn_clearingMap (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) :
    BijOn (clearingMap H) (Ioi 0) (Ioi 0) := by
  refine ⟨fun x hx ↦ (mul_pos hδ hx).trans_le (mul_le_clearingMap hH hmargin hzero hx),
    (strictMonoOn_clearingMap hH fun x hx ↦ hδ.trans_le (hmargin x hx)).injOn,
    fun y (hy : 0 < y) ↦ ?_⟩
  -- The level `y` is reached below at `y / δ`, and is exceeded near zero by the zero limit.
  have hx₂ : 0 < y / δ := div_pos hy hδ
  have hyx₂ : y ≤ clearingMap H (y / δ) := by
    simpa [mul_div_cancel₀ y hδ.ne'] using mul_le_clearingMap hH hmargin hzero hx₂
  exact isPreconnected_Ioi.intermediate_value_Ioc hx₂ (l := 𝓝[>] 0) inf_le_right
    (differentiableOn_clearingMap hH).continuousOn hzero ⟨hy, hyx₂⟩

/-- **Global clearing.** Under a positive uniform clearing margin and the zero limit at zero
price, every positive level `y` is the value of the clearing map at exactly one positive
price. -/
theorem existsUnique_clearingMap_eq (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) {y : ℝ} (hy : 0 < y) :
    ∃! x, 0 < x ∧ clearingMap H x = y := by
  have hbij := bijOn_clearingMap hδ hH hmargin hzero
  obtain ⟨x, hx, hxy⟩ := hbij.surjOn hy
  exact ⟨x, ⟨hx, hxy⟩, fun x' ⟨hx', hx'y⟩ ↦ hbij.injOn hx' hx (hx'y.trans hxy.symm)⟩

/-- **Global clearing against reference demand `c / x`.** Under a positive uniform clearing
margin and the zero limit at zero price, for every `c > 0` the market
`c / x + H x = 1` clears at exactly one positive price. -/
theorem existsUnique_div_add_eq_one (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) (hc : 0 < c) :
    ∃! x, 0 < x ∧ c / x + H x = 1 := by
  obtain ⟨x, ⟨hx, hxc⟩, huniq⟩ := existsUnique_clearingMap_eq hδ hH hmargin hzero hc
  exact ⟨x, ⟨hx, (div_add_eq_one_iff_clearingMap_eq hx.ne').2 hxc⟩,
    fun x' ⟨hx', h⟩ ↦ huniq x' ⟨hx', (div_add_eq_one_iff_clearingMap_eq hx'.ne').1 h⟩⟩

/-- The clearing map as an order isomorphism of the positive reals, under a positive uniform
clearing margin and the zero limit at zero price. Its inverse sends a positive level to the
unique positive equilibrium price. -/
def clearingOrderIso (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) : Ioi (0 : ℝ) ≃o Ioi (0 : ℝ) :=
  have hbij := bijOn_clearingMap hδ hH hmargin hzero
  StrictMono.orderIsoOfSurjective (hbij.mapsTo.restrict _ _ _)
    (fun a b hab ↦
      strictMonoOn_clearingMap hH (fun x hx ↦ hδ.trans_le (hmargin x hx)) a.2 b.2 hab)
    (hbij.mapsTo.restrict_surjective_iff.2 hbij.surjOn)

/-- `clearingOrderIso` acts on positive prices by the clearing map. -/
@[simp]
theorem coe_clearingOrderIso_apply (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) (x : Ioi (0 : ℝ)) :
    (clearingOrderIso hδ hH hmargin hzero x : ℝ) = clearingMap H x := (rfl)

/-- The inverse of `clearingOrderIso` returns the equilibrium price of each level. -/
@[simp]
theorem clearingMap_clearingOrderIso_symm_apply (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) (y : Ioi (0 : ℝ)) :
    clearingMap H ((clearingOrderIso hδ hH hmargin hzero).symm y) = y := by
  rw [← coe_clearingOrderIso_apply hδ hH hmargin hzero, OrderIso.apply_symm_apply]

/-- The equilibrium price depends on the level in a `δ⁻¹`-Lipschitz way. -/
theorem lipschitzWith_clearingOrderIso_symm (hδ : 0 < δ) (hH : DifferentiableOn ℝ H (Ioi 0))
    (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
    (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) :
    LipschitzWith (Real.toNNReal δ⁻¹) (clearingOrderIso hδ hH hmargin hzero).symm := by
  refine LipschitzWith.of_dist_le_mul fun y y' ↦ ?_
  set e := clearingOrderIso hδ hH hmargin hzero
  rw [Real.coe_toNNReal _ (inv_nonneg.2 hδ.le), Subtype.dist_eq, Subtype.dist_eq,
    ← clearingMap_clearingOrderIso_symm_apply hδ hH hmargin hzero y,
    ← clearingMap_clearingOrderIso_symm_apply hδ hH hmargin hzero y',
    Real.dist_eq, Real.dist_eq, le_inv_mul_iff₀ hδ]
  -- The margin bounds the growth of the clearing map from below, in either order.
  rcases le_total ((e.symm y : ℝ)) (e.symm y') with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
    exact (mul_sub_le_clearingMap_sub hH hmargin (e.symm y).2 h).trans (le_abs_self _)
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact (mul_sub_le_clearingMap_sub hH hmargin (e.symm y').2 h).trans (le_abs_self _)

end TauCeti.Finance
