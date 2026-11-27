/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Linear growth from a convergent derivative

If the derivative of a function `f` of one real variable tends to `c` at `+∞`, then `f` grows like
`x • c`: `x⁻¹ • f x → c` (`TauCeti.tendsto_inv_smul_atTop_of_tendsto_deriv`). This is the `∞ / ∞`
form of l'Hôpital's rule with denominator `x`, which Mathlib's `HasDerivAt.lhopital_zero_atTop`
(a `0 / 0` statement) does not cover. The local counterpart at a point, integrating a little-o
bound on the derivative, is Mathlib's `Convex.isLittleO_pow_succ_real`.

In particular a function which converges at `+∞` and whose derivative converges there has
derivative tending to `0` (`TauCeti.eq_zero_of_tendsto_of_tendsto_deriv`). For a solution of an
autonomous equation `x' = F x` with continuous `F`, this says that a limit of the solution at `+∞`
or at `-∞` is a zero of `F` (`TauCeti.apply_eq_zero_of_tendsto_atTop_of_hasDerivAt`,
`TauCeti.apply_eq_zero_of_tendsto_atBot_of_hasDerivAt`).

More generally, the comparison form of the `∞ / ∞` rule holds for any real denominator: if
`g → +∞` with `g' ≥ 0` eventually, and `f' = o(g')`, then `f = o(g)`
(`TauCeti.isLittleO_atTop_of_hasDerivAt`). It compares a function with an explicit primitive of
a dominant integrand, as in the asymptotics of `∫ˣ e^{2ξ} ξ' (1 + o(1))`, where only the
derivatives are known in closed form. The proof is the mean value inequality with variable bound
(`image_norm_le_of_norm_deriv_right_le_deriv_boundary'`). The linear-growth statement above is
derived from it with `g x = x`, applied to `f x - x • c`.
-/

public section

open Filter Topology Set Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}

namespace TauCeti

/-- **L'Hôpital's rule for little-o at `+∞`.** Let `f` take values in a real normed space and let
`g` be real, with derivatives `f'` and `g'` eventually. If `g → +∞`, `g' ≥ 0` eventually and
`f' = o(g')`, then `f = o(g)`. -/
theorem isLittleO_atTop_of_hasDerivAt {g g' : ℝ → ℝ} (hf : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hg₀ : ∀ᶠ x in atTop, 0 ≤ g' x)
    (hgt : Tendsto g atTop atTop) (hfg : f' =o[atTop] g') : f =o[atTop] g := by
  refine IsLittleO.of_bound fun c hc ↦ ?_
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 <|
    (hf.and hg).and (hg₀.and (hfg.bound (half_pos hc)))
  -- the mean value inequality on `[x₀, x]`: `‖f x - f x₀‖ ≤ c / 2 (g x - g x₀)`
  have hmv (x : ℝ) (hx : x₀ ≤ x) : ‖f x - f x₀‖ ≤ c / 2 * (g x - g x₀) := by
    have hd (y : ℝ) (hy : y ∈ Icc x₀ x) := hx₀ y hy.1
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := fun y ↦ f y - f x₀)
      (f' := f') (B := fun y ↦ c / 2 * (g y - g x₀)) (B' := fun y ↦ c / 2 * g' y)
      (fun y hy ↦ ((hd y hy).1.1.continuousAt.sub continuousAt_const).continuousWithinAt)
      (fun y hy ↦ ((hd y (Ico_subset_Icc_self hy)).1.1.sub_const (f x₀)).hasDerivWithinAt)
      (by simp) (fun y hy ↦ (((hd y hy).1.2.continuousAt.sub
        continuousAt_const).const_mul _).continuousWithinAt)
      (fun y hy ↦ (((hd y (Ico_subset_Icc_self hy)).1.2.sub_const (g x₀)).const_mul
        (c / 2)).hasDerivWithinAt) (fun y hy ↦ ?_) ⟨hx, le_rfl⟩
    obtain ⟨h0, h⟩ := (hd y (Ico_subset_Icc_self hy)).2
    rwa [Real.norm_of_nonneg h0] at h
  filter_upwards [eventually_ge_atTop x₀,
    hgt.eventually_ge_atTop (2 / c * ‖f x₀‖ + |g x₀|), hgt.eventually_ge_atTop 0] with x hx hgx hg0
  rw [Real.norm_of_nonneg hg0]
  have h1 := norm_sub_norm_le (f x) (f x₀)
  have h2 := hmv x hx
  have h3 := neg_le_abs (g x₀)
  have h4 : c / 2 * (2 / c * ‖f x₀‖ + |g x₀|) ≤ c / 2 * g x :=
    mul_le_mul_of_nonneg_left hgx (by positivity)
  have h5 : c / 2 * (2 / c * ‖f x₀‖) = ‖f x₀‖ := by field_simp
  nlinarith [h1, h2, h3, h4, h5, abs_nonneg (g x₀)]

/-- **Linear growth from a convergent derivative.** If the derivative of `f` tends to `c` at
`+∞`, then `x⁻¹ • f x` tends to `c`. -/
theorem tendsto_inv_smul_atTop_of_tendsto_deriv {c : E}
    (hf : ∀ᶠ x in atTop, HasDerivAt f (f' x) x) (hf' : Tendsto f' atTop (𝓝 c)) :
    Tendsto (fun x ↦ x⁻¹ • f x) atTop (𝓝 c) := by
  -- Subtract the linear function `x • c`: by l'Hôpital's rule with denominator `x`, the
  -- remainder is `o(x)`, as its derivative `f' - c` tends to `0`.
  have ho : (fun x ↦ f x - x • c) =o[atTop] id :=
    isLittleO_atTop_of_hasDerivAt (f' := fun x ↦ f' x - c) (g' := fun _ ↦ 1)
      (hf.mono fun x hx ↦ by
        convert hx.sub ((hasDerivAt_id x).smul_const c) using 1 <;> first | rfl | simp)
      (Eventually.of_forall hasDerivAt_id) (Eventually.of_forall fun _ ↦ zero_le_one) tendsto_id
      ((isLittleO_one_iff ℝ).2 (by simpa using hf'.sub_const c))
  refine (by simpa using ho.tendsto_inv_smul_nhds_zero.add_const c :
    Tendsto (fun x ↦ x⁻¹ • (f x - x • c) + c) atTop (𝓝 c)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp [smul_sub, smul_smul, inv_mul_cancel₀ hx.ne']

/-- **A convergent function has derivative tending to `0`, if the derivative converges.** If `f`
converges at `+∞` and its derivative tends to `c`, then `c = 0`: otherwise `f` would grow like
`x • c`. -/
theorem eq_zero_of_tendsto_of_tendsto_deriv {c L : E}
    (hf : ∀ᶠ x in atTop, HasDerivAt f (f' x) x) (hf' : Tendsto f' atTop (𝓝 c))
    (hL : Tendsto f atTop (𝓝 L)) : c = 0 := by
  have h0 : Tendsto (fun x ↦ x⁻¹ • f x) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.smul hL
  exact tendsto_nhds_unique (tendsto_inv_smul_atTop_of_tendsto_deriv hf hf') h0

/-- **A limit at `+∞` of a solution of an autonomous equation is an equilibrium.** If `x' = F x`
near `+∞` and `x` tends to `L` at `+∞`, where `F` is continuous at `L`, then `F L = 0`. -/
theorem apply_eq_zero_of_tendsto_atTop_of_hasDerivAt {F : E → E} {x : ℝ → E} {L : E}
    (hF : ContinuousAt F L) (hx : ∀ᶠ t in atTop, HasDerivAt x (F (x t)) t)
    (hL : Tendsto x atTop (𝓝 L)) : F L = 0 :=
  eq_zero_of_tendsto_of_tendsto_deriv hx (hF.tendsto.comp hL) hL

/-- **A limit at `-∞` of a solution of an autonomous equation is an equilibrium.** If `x' = F x`
near `-∞` and `x` tends to `L` at `-∞`, where `F` is continuous at `L`, then `F L = 0`. -/
theorem apply_eq_zero_of_tendsto_atBot_of_hasDerivAt {F : E → E} {x : ℝ → E} {L : E}
    (hF : ContinuousAt F L) (hx : ∀ᶠ t in atBot, HasDerivAt x (F (x t)) t)
    (hL : Tendsto x atBot (𝓝 L)) : F L = 0 := by
  have hL' := hL.comp tendsto_neg_atTop_atBot
  refine neg_eq_zero.1 (eq_zero_of_tendsto_of_tendsto_deriv (f := fun t ↦ x (-t)) ?_
    (hF.tendsto.comp hL').neg hL')
  filter_upwards [tendsto_neg_atTop_atBot.eventually hx] with t ht
  simpa [Function.comp_def] using ht.scomp t (hasDerivAt_neg t)

end TauCeti
