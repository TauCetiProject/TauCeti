/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Second-order Sobolev regularity of a norm power

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure, and let `u(x) = ‖x‖ ^ γ`. Away from the origin its classical Hessian is

`D²u(x) v = γ ‖x‖ ^ (γ - 2) v + γ (γ - 2) ‖x‖ ^ (γ - 4) ⟪x, v⟫ x`

(`TauCeti.iteratedGradientChain_one_norm_rpow_apply`), of size comparable to `‖x‖ ^ (γ - 2)`.
For `n + γ > 2` this Hessian is locally integrable, and it is the weak derivative of the gradient
of `u` across the origin (`TauCeti.hasWeakFDerivOn_gradient_norm_rpow`), while the gradient is the
weak derivative of `u` itself (`TauCeti.hasWeakFDerivOn_norm_rpow`). Consequently, for
`0 < γ < 2` and `n + γ > 2`, on a bounded open set containing the origin,

`u ∈ W^{2,p}` exactly when `p < n / (2 - γ)`

(`TauCeti.exists_wkp_two_value_ae_eq_norm_rpow_iff`), including `p = ∞`, which never qualifies.
For `n ≥ 2` and `0 < γ < 1` the threshold `n / (2 - γ)` lies strictly between `n / 2` and `n`:
`u` is then a `W^{2,p}` function for some `p > n / 2`, hence continuous, but it is not in
`W^{2,n}`. Such power singularities are the standard witnesses for the sharpness of `W^{2,p}`
regularity statements for elliptic equations with discontinuous coefficients.

## The argument

For `γ > 2` the function `u` is `C²` and there is nothing to prove. For `γ ≤ 2`, the fields
`G_ε(x) = γ (‖x‖² + ε) ^ (γ / 2 - 1) x` are, for `ε > 0`, the smooth gradients of
`(‖x‖² + ε) ^ (γ / 2)`, and their classical derivatives `H_ε` are given by the same formula as
`D²u` with `‖x‖²` replaced by `‖x‖² + ε`. For `γ ≤ 2` the exponent `γ / 2 - 1` is nonpositive,
so `‖G_ε(x)‖ ≤ |γ| ‖x‖ ^ (γ - 1)` and `‖H_ε(x)‖ ≤ |γ| (3 - γ) ‖x‖ ^ (γ - 2)` uniformly in `ε`.
Both bounds are locally integrable when `n + γ > 2`, so by dominated convergence `G_ε → ∇u` and
`H_ε → D²u` in `L¹` on every ball as `ε → 0`, and the weak derivative identity passes to the
limit (`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`). For the converse integrability
bound, the trace of `D²u(x)` in an orthonormal basis is `γ (n + γ - 2) ‖x‖ ^ (γ - 2)`, so the
operator norm of `D²u(x)` is at least `|γ (n + γ - 2)| / n · ‖x‖ ^ (γ - 2)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.3, Example 2, for the first-order
  analogue: `‖x‖ ^ (-α)` lies in `W^{1,p}` of the unit ball exactly when `α < (n - p) / p`.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace Module
open scoped ENNReal NNReal Topology InnerProductSpace Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ}

/-! ### The regularized gradient and Hessian fields -/

/-- The field `γ (‖x‖² + ε) ^ (γ / 2 - 1) x`: for `ε > 0` the gradient of `(‖x‖² + ε) ^ (γ / 2)`,
and for `ε = 0` the gradient of `‖x‖ ^ γ` away from the origin. -/
private def gradField (γ ε : ℝ) (x : E) : E :=
  (γ * (‖x‖ ^ 2 + ε) ^ (γ / 2 - 1)) • x

/-- The derivative of `TauCeti.gradField γ ε` at `x`. -/
private def hessField (γ ε : ℝ) (x : E) : E →L[ℝ] E :=
  (γ * (‖x‖ ^ 2 + ε) ^ (γ / 2 - 1)) • ContinuousLinearMap.id ℝ E +
    (γ * (γ - 2) * (‖x‖ ^ 2 + ε) ^ (γ / 2 - 2)) • (innerSL ℝ x).smulRight x

private theorem hessField_apply (γ ε : ℝ) (x v : E) :
    hessField γ ε x v = (γ * (‖x‖ ^ 2 + ε) ^ (γ / 2 - 1)) • v +
      (γ * (γ - 2) * (‖x‖ ^ 2 + ε) ^ (γ / 2 - 2) * ⟪x, v⟫_ℝ) • x := by
  simp only [hessField, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_smul]

private theorem hasFDerivAt_gradField (γ ε : ℝ) {x : E} (hx : ‖x‖ ^ 2 + ε ≠ 0) :
    HasFDerivAt (gradField γ ε) (hessField γ ε x) x := by
  have hs : HasFDerivAt (fun y : E => ‖y‖ ^ 2 + ε) (2 • innerSL ℝ x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).add_const ε
  have hc := ((hs.rpow_const (p := γ / 2 - 1) (Or.inl hx)).const_mul γ).smul
    (hasFDerivAt_id x)
  refine hc.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, hessField_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, id_eq]
  rw [show γ / 2 - 1 - 1 = γ / 2 - 2 by ring, add_right_inj]
  congr 1
  ring

omit [InnerProductSpace ℝ E] in
/-- `(‖x‖ ^ 2) ^ a = ‖x‖ ^ (2 a)`. -/
private theorem norm_sq_rpow (x : E) (a : ℝ) : (‖x‖ ^ 2) ^ a = ‖x‖ ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x), Nat.cast_ofNat]

private theorem gradField_zero (γ : ℝ) (x : E) :
    gradField γ 0 x = (γ * ‖x‖ ^ (γ - 2)) • x := by
  rw [gradField, add_zero, norm_sq_rpow]
  congr 3
  ring

private theorem hessField_zero_apply (γ : ℝ) (x v : E) :
    hessField γ 0 x v = (γ * ‖x‖ ^ (γ - 2)) • v +
      (γ * (γ - 2) * ‖x‖ ^ (γ - 4) * ⟪x, v⟫_ℝ) • x := by
  rw [hessField_apply, add_zero, norm_sq_rpow, norm_sq_rpow]
  congr 5 <;> ring

omit [InnerProductSpace ℝ E] in
/-- `(‖x‖² + ε) ^ (γ / 2 - 1) ≤ ‖x‖ ^ (γ - 2)` for `x ≠ 0`, `ε ≥ 0` and `γ ≤ 2`. -/
private theorem rpow_norm_sq_add_le {x : E} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) (hγ : γ ≤ 2) :
    (‖x‖ ^ 2 + ε) ^ (γ / 2 - 1) ≤ ‖x‖ ^ (γ - 2) := by
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  calc (‖x‖ ^ 2 + ε) ^ (γ / 2 - 1) ≤ (‖x‖ ^ 2) ^ (γ / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos hx2 (le_add_of_nonneg_right hε) (by linarith)
    _ = ‖x‖ ^ (γ - 2) := by rw [norm_sq_rpow]; congr 1; ring

private theorem norm_gradField_le {x : E} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) (hγ : γ ≤ 2) :
    ‖gradField γ ε x‖ ≤ |γ| * ‖x‖ ^ (γ - 1) := by
  have hN : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [gradField, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (by positivity) _), mul_assoc,
    show γ - 1 = (γ - 2) + 1 by ring, Real.rpow_add_one hN.ne']
  gcongr
  exact rpow_norm_sq_add_le hx hε hγ

private theorem norm_hessField_le {x : E} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) (hγ : γ ≤ 2) :
    ‖hessField γ ε x‖ ≤ |γ| * (3 - γ) * ‖x‖ ^ (γ - 2) := by
  have hs : 0 < ‖x‖ ^ 2 + ε := by positivity
  set s := ‖x‖ ^ 2 + ε
  -- `s ^ (γ / 2 - 2) ‖x‖² ≤ s ^ (γ / 2 - 1)`, since `‖x‖² ≤ s`.
  have hpow : s ^ (γ / 2 - 2) * ‖x‖ ^ 2 ≤ s ^ (γ / 2 - 1) := by
    calc s ^ (γ / 2 - 2) * ‖x‖ ^ 2 ≤ s ^ (γ / 2 - 2) * s := by
          gcongr
          exact le_add_of_nonneg_right hε
      _ = s ^ (γ / 2 - 1) := by
          rw [← Real.rpow_add_one hs.ne']
          congr 1
          ring
  have hK : ‖(innerSL ℝ x).smulRight x‖ = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, sq]
  calc ‖hessField γ ε x‖
      ≤ |γ| * s ^ (γ / 2 - 1) * ‖ContinuousLinearMap.id ℝ E‖ +
          |γ| * (2 - γ) * s ^ (γ / 2 - 2) * ‖(innerSL ℝ x).smulRight x‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
        · rw [abs_of_pos (Real.rpow_pos_of_pos hs _)]
        · rw [abs_mul, abs_of_nonpos (by linarith : γ - 2 ≤ 0),
            abs_of_pos (Real.rpow_pos_of_pos hs _), neg_sub]
    _ ≤ |γ| * s ^ (γ / 2 - 1) * 1 + |γ| * (2 - γ) * s ^ (γ / 2 - 1) := by
        rw [hK, mul_assoc (|γ| * (2 - γ))]
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = |γ| * (3 - γ) * s ^ (γ / 2 - 1) := by ring
    _ ≤ |γ| * (3 - γ) * ‖x‖ ^ (γ - 2) := by
        have : 0 ≤ |γ| * (3 - γ) := mul_nonneg (abs_nonneg γ) (by linarith)
        gcongr
        exact rpow_norm_sq_add_le hx hε hγ

/-! ### Continuity in the regularization parameter -/

private theorem continuous_gradField {ε : ℝ} (hε : 0 < ε) : Continuous (gradField (E := E) γ ε) :=
  (continuous_const.mul (((continuous_norm.pow 2).add continuous_const).rpow_const
    fun _ => Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne')).smul continuous_id

private theorem continuous_hessField {ε : ℝ} (hε : 0 < ε) :
    Continuous (hessField (E := E) γ ε) := by
  have h : ∀ a : ℝ, Continuous fun x : E => (‖x‖ ^ 2 + ε) ^ a := fun a =>
    ((continuous_norm.pow 2).add continuous_const).rpow_const fun _ =>
      Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'
  have hK : Continuous fun x : E => (innerSL ℝ x).smulRight x :=
    (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
      ((innerSL ℝ).continuous.prodMk continuous_id)
  exact ((continuous_const.mul (h _)).smul continuous_const).add
    ((continuous_const.mul (h _)).smul hK)

private theorem continuousAt_gradField {x : E} (hx : x ≠ 0) :
    ContinuousAt (fun ε : ℝ => gradField γ ε x) 0 := by
  have h : ContinuousAt (fun ε : ℝ => ‖x‖ ^ 2 + ε) 0 := by fun_prop
  exact ((h.rpow_const (Or.inl (by simpa using hx))).const_mul γ).smul continuousAt_const

private theorem continuousAt_hessField {x : E} (hx : x ≠ 0) :
    ContinuousAt (fun ε : ℝ => hessField γ ε x) 0 := by
  have h : ContinuousAt (fun ε : ℝ => ‖x‖ ^ 2 + ε) 0 := by fun_prop
  have hx' : ‖x‖ ^ 2 + 0 ≠ 0 := by simpa using hx
  exact (((h.rpow_const (Or.inl hx')).const_mul γ).smul continuousAt_const).add
    (((h.rpow_const (Or.inl hx')).const_mul (γ * (γ - 2))).smul continuousAt_const)

/-! ### The classical derivatives away from the origin -/

variable [FiniteDimensional ℝ E]

private theorem gradient_norm_rpow_eq_gradField {x : E} (hx : x ≠ 0) :
    ∇ (fun y : E => ‖y‖ ^ γ) x = gradField γ 0 x := by
  rw [gradient_norm_rpow hx, gradField_zero]

private theorem iteratedGradientChain_one_norm_rpow_eq_hessField {x : E} (hx : x ≠ 0) :
    iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1 x = hessField γ 0 x := by
  rw [iteratedGradientChain_succ, iteratedGradientChain_zero]
  have hev : (∇ fun y : E => ‖y‖ ^ γ) =ᶠ[𝓝 x] gradField γ 0 :=
    (eventually_ne_nhds hx).mono fun y hy => gradient_norm_rpow_eq_gradField hy
  rw [hev.fderiv_eq]
  exact (hasFDerivAt_gradField γ 0
    (by rw [add_zero]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hx))).fderiv

/-- Away from the origin, the classical Hessian of `‖x‖ ^ γ`, the derivative of its gradient, is
`v ↦ γ ‖x‖ ^ (γ - 2) v + γ (γ - 2) ‖x‖ ^ (γ - 4) ⟪x, v⟫ x`. -/
theorem iteratedGradientChain_one_norm_rpow_apply {x : E} (hx : x ≠ 0) (v : E) :
    iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1 x v =
      (γ * ‖x‖ ^ (γ - 2)) • v + (γ * (γ - 2) * ‖x‖ ^ (γ - 4) * ⟪x, v⟫_ℝ) • x := by
  rw [iteratedGradientChain_one_norm_rpow_eq_hessField hx, hessField_zero_apply]

/-! ### Passing to the limit -/

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem measurable_gradField (ε : ℝ) : Measurable (gradField (E := E) γ ε) := by
  unfold gradField
  fun_prop


private theorem tendsto_eps : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem eps_pos (k : ℕ) : 0 < (1 : ℝ) / (k + 1) := by positivity

/-- On a ball centred at the origin, the derivative of the gradient field `γ ‖x‖ ^ (γ - 2) x`
across the origin is its classical derivative. -/
private theorem hasWeakFDerivOn_ball_gradField [Nontrivial E] (hγ : γ ≤ 2)
    (hn : 2 < finrank ℝ E + γ) (R : ℝ) :
    HasWeakFDerivOn μ ⟨ball 0 R, isOpen_ball⟩ (gradField γ 0) (hessField γ 0) := by
  have hs1 : -(finrank ℝ E : ℝ) < γ - 1 := by linarith
  have hs2 : -(finrank ℝ E : ℝ) < γ - 2 := by linarith
  have hae : ∀ᵐ x ∂μ.restrict (ball 0 R), x ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton 0))
  -- The limit fields are integrable on the ball.
  have hG : IntegrableOn (gradField γ 0) (ball 0 R) μ :=
    ((integrableOn_norm_rpow_ball (mu := μ) hs1).const_mul |γ|).mono'
      (measurable_gradField 0).aestronglyMeasurable
      (hae.mono fun x hx => norm_gradField_le hx le_rfl hγ)
  have hH : ∀ v : E, IntegrableOn (fun x => hessField γ 0 x v) (ball 0 R) μ := fun v => by
    refine ((integrableOn_norm_rpow_ball (mu := μ) hs2).const_mul (|γ| * (3 - γ) * ‖v‖)).mono'
      ?_ (hae.mono fun x hx => ?_)
    · simp only [hessField_apply]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · calc ‖hessField γ 0 x v‖ ≤ ‖hessField γ 0 x‖ * ‖v‖ := (hessField γ 0 x).le_opNorm v
        _ ≤ |γ| * (3 - γ) * ‖x‖ ^ (γ - 2) * ‖v‖ := by
          gcongr
          exact norm_hessField_le hx le_rfl hγ
        _ = |γ| * (3 - γ) * ‖v‖ * ‖x‖ ^ (γ - 2) := by ring
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    (u := fun k : ℕ => gradField γ (1 / (k + 1)))
    (U := fun k : ℕ => hessField γ (1 / (k + 1)))
    (hG.locallyIntegrableOn) (fun v => (hH v).locallyIntegrableOn) (fun k => ?_) ?_ ?_
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_gradField (eps_pos k)).continuousOn
      ((continuous_hessField (eps_pos k)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ => hasFDerivAt_gradField γ _ (by positivity [eps_pos k])
  · exact tendsto_setLIntegral_ball_enorm_sub_of_norm_le_mul_norm_rpow hs1
      (fun k => (continuous_gradField (eps_pos k)).aestronglyMeasurable)
      (fun k x hx => norm_gradField_le hx (eps_pos k).le hγ)
      fun x hx => (continuousAt_gradField hx).tendsto.comp tendsto_eps
  · exact tendsto_setLIntegral_ball_enorm_sub_of_norm_le_mul_norm_rpow hs2
      (fun k => (continuous_hessField (eps_pos k)).aestronglyMeasurable)
      (fun k x hx => norm_hessField_le hx (eps_pos k).le hγ)
      fun x hx => (continuousAt_hessField hx).tendsto.comp tendsto_eps

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem nontrivial_of_two_lt (hγ : γ ≤ 2) (hn : 2 < finrank ℝ E + γ) : Nontrivial E :=
  Module.nontrivial_of_finrank_pos (R := ℝ)
    (by exact_mod_cast (by linarith : (0 : ℝ) < finrank ℝ E))

private theorem hasWeakFDerivOn_gradField (hγ : γ ≤ 2) (hn : 2 < finrank ℝ E + γ) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (gradField γ 0) (hessField γ 0) :=
  have := nontrivial_of_two_lt hγ hn
  hasWeakFDerivOn_iff_locally.2 fun x _ => ⟨⟨ball 0 (‖x‖ + 1), isOpen_ball⟩,
    mem_ball_zero_iff.2 (lt_add_one _), hasWeakFDerivOn_ball_gradField hγ hn _⟩

/-! ### Weak derivatives across the origin -/

/-- For `γ > 0`, the classical gradient of `‖x‖ ^ γ` is its weak gradient on every open set; this
restates `TauCeti.hasWeakFDerivOn_norm_rpow` in terms of the gradient. -/
private theorem hasWeakFDerivOn_norm_rpow_innerSL_gradient [Nontrivial E] (hγ : 0 < γ)
    (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun y : E => ‖y‖ ^ γ)
      (fun x => innerSL ℝ (∇ (fun y : E => ‖y‖ ^ γ) x)) := by
  have hs : 1 - (finrank ℝ E : ℝ) < γ := by
    have : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos (R := ℝ) (M := E)
    linarith
  refine (hasWeakFDerivOn_norm_rpow hs Ω).congr_ae_deriv ?_
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := μ) (0 : E)))]
    with x hx
  rw [gradient_norm_rpow hx, map_smul]

/-- **The weak Hessian of a norm power.** Let `n + γ > 2`, where `n` is the dimension. On every
open set, the classical Hessian of `‖x‖ ^ γ`, of size comparable to `‖x‖ ^ (γ - 2)`, is the weak
derivative of its gradient across the origin. For `γ > 2` the function is `C²` and the Hessian is
continuous; for `γ ≤ 2` it is singular at the origin but locally integrable. -/
theorem hasWeakFDerivOn_gradient_norm_rpow (hn : 2 < finrank ℝ E + γ) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (∇ fun y : E => ‖y‖ ^ γ)
      (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) := by
  rcases le_or_gt γ 2 with hγ | hγ
  · have := nontrivial_of_two_lt hγ hn
    have hae : ∀ᵐ x ∂μ.restrict Ω, x ≠ 0 :=
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton 0))
    exact ((hasWeakFDerivOn_gradField hγ hn Ω).congr_ae
      (hae.mono fun x hx => (gradient_norm_rpow_eq_gradField hx).symm)).congr_ae_deriv
      (hae.mono fun x hx => (iteratedGradientChain_one_norm_rpow_eq_hessField hx).symm)
  · -- For `γ > 2` the function is `C²`, so its gradient is `C¹` with continuous derivative.
    have hC : ContDiff ℝ 2 (fun y : E => ‖y‖ ^ γ) :=
      contDiff_norm_rpow_of_lt (k := 2) (by exact_mod_cast hγ)
    have h1 : ∀ x, ContDiffAt ℝ 1 (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 0) x :=
      fun x => contDiffAt_iteratedGradientChain hC.contDiffAt 0 (by norm_num)
    have h0 : Continuous (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) :=
      continuous_iff_continuousAt.2 fun x =>
        (contDiffAt_iteratedGradientChain hC.contDiffAt 1 (m := 0) (by norm_num)).continuousAt
    rw [← iteratedGradientChain_zero, iteratedGradientChain_succ]
    exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt).continuousOn
      (by simpa only [iteratedGradientChain_succ] using h0.locallyIntegrable.locallyIntegrableOn _)
      fun x _ => ((h1 x).differentiableAt (by norm_num)).hasFDerivAt

/-- The weak Hessian of an element of `W^{2,p}(Ω)` equal to `‖x‖ ^ γ`, for `γ > 0` and
`n + γ > 2`, is its classical Hessian. -/
theorem Wkp.iteratedGradient_one_ae_eq_norm_rpow (hγ0 : 0 < γ) (hn : 2 < finrank ℝ E + γ)
    {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Wkp μ Ω p 2)
    (hw : (Wkp.value 2 w : E → ℝ) =ᵐ[μ.restrict Ω] fun y => ‖y‖ ^ γ) :
    (Wkp.iteratedGradient 1 w : E → IteratedGradient E 1) =ᵐ[μ.restrict Ω]
      iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1 := by
  -- On the zero space both fields vanish.
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ae_of_all _ fun _ => Subsingleton.elim _ _
  -- The weak gradient of the first-order part is the classical gradient.
  have hv : (Wkp.value 1 (Wkp.lowerOrder 1 w) : E → ℝ) =ᵐ[μ.restrict Ω]
      fun y => ‖y‖ ^ γ := by
    rw [← Wkp.value_succ]
    exact hw
  have h1 := (Wkp.hasWeakFDerivOn_value (Wkp.lowerOrder 1 w)).congr_ae hv
  have hg : (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w) : E → E) =ᵐ[μ.restrict Ω]
      ∇ fun y : E => ‖y‖ ^ γ := by
    filter_upwards [h1.ae_eq (hasWeakFDerivOn_norm_rpow_innerSL_gradient hγ0 Ω)] with x hx
    exact ext_inner_right ℝ fun v => by simpa using congrArg (· v) hx
  exact ((Wkp.hasWeakFDerivOn_iteratedGradient 0 w).congr_ae hg).ae_eq
    (hasWeakFDerivOn_gradient_norm_rpow hn Ω)

/-! ### Membership in `W^{2,p}` -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The trace of the Hessian of `‖x‖ ^ γ` in an orthonormal basis is `γ (n + γ - 2) ‖x‖ ^ (γ - 2)`,
so its operator norm is at least `|γ (n + γ - 2)| / n · ‖x‖ ^ (γ - 2)`. -/
private theorem abs_mul_rpow_le_norm_hessField {x : E} (hx : x ≠ 0) :
    |γ * (finrank ℝ E + γ - 2)| * ‖x‖ ^ (γ - 2) ≤ finrank ℝ E * ‖hessField γ 0 x‖ := by
  set b := stdOrthonormalBasis ℝ E
  have hN : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h42 : ‖x‖ ^ (γ - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (γ - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN]
    norm_num
    ring_nf
  have htr : ∑ i, ⟪hessField γ 0 x (b i), b i⟫_ℝ =
      γ * (finrank ℝ E + γ - 2) * ‖x‖ ^ (γ - 2) := by
    have hterm : ∀ i, ⟪hessField γ 0 x (b i), b i⟫_ℝ =
        γ * ‖x‖ ^ (γ - 2) + γ * (γ - 2) * ‖x‖ ^ (γ - 4) * (⟪x, b i⟫_ℝ * ⟪b i, x⟫_ℝ) := by
      intro i
      rw [hessField_zero_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, b.norm_eq_one, real_inner_comm (b i) x]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_const,
      ← Finset.mul_sum, b.sum_inner_mul_inner, real_inner_self_eq_norm_sq, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_assoc (γ * (γ - 2)), h42]
    ring
  have hle : |∑ i, ⟪hessField γ 0 x (b i), b i⟫_ℝ| ≤ finrank ℝ E * ‖hessField γ 0 x‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |⟪hessField γ 0 x (b i), b i⟫_ℝ| ≤ ∑ _i : Fin (finrank ℝ E), ‖hessField γ 0 x‖ :=
          Finset.sum_le_sum fun i _ => (abs_real_inner_le_norm _ _).trans <| by
            simpa [b.norm_eq_one] using (hessField γ 0 x).le_opNorm (b i)
      _ = finrank ℝ E * ‖hessField γ 0 x‖ := by simp
  rwa [htr, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN _)] at hle

private theorem aestronglyMeasurable_iteratedGradientChain_one_norm_rpow [Nontrivial E] :
    AEStronglyMeasurable (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) μ := by
  have hae : ∀ᵐ x ∂μ, x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  exact (aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => (continuous_hessField (E := E) (γ := γ) (eps_pos k)).aestronglyMeasurable)
    (hae.mono fun x hx => (continuousAt_hessField hx).tendsto.comp tendsto_eps)).congr
    (hae.mono fun x hx => (iteratedGradientChain_one_norm_rpow_eq_hessField hx).symm)

/-- If the Hessian of `‖x‖ ^ γ`, `0 < γ < 2`, is `p`-integrable near the origin, then
`p < n / (2 - γ)`: its norm is at least a multiple of `‖x‖ ^ (γ - 2)`. -/
private theorem lt_ofReal_of_memLp_iteratedGradientChain_one_norm_rpow (hγ0 : 0 < γ)
    (hγ : γ < 2) (hn : 2 < finrank ℝ E + γ) {Ω : Set E} (hΩ : Ω ∈ 𝓝 0) {p : ℝ≥0∞}
    (hH : MemLp (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) p (μ.restrict Ω)) :
    p < ENNReal.ofReal (finrank ℝ E / (2 - γ)) := by
  have := nontrivial_of_two_lt hγ.le hn
  have h2γ : 0 < 2 - γ := by linarith
  have hnpos : (0 : ℝ) < finrank ℝ E := by linarith
  by_contra hq
  rw [not_lt] at hq
  set q := ENNReal.ofReal (finrank ℝ E / (2 - γ)) with hq_def
  have hqr : q.toReal = finrank ℝ E / (2 - γ) := ENNReal.toReal_ofReal (by positivity)
  have hq0 : q ≠ 0 := by rw [hq_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hΩ
  have : IsFiniteMeasure (μ.restrict (ball (0 : E) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The Hessian would be `q`-integrable on a ball about the origin.
  have hint := ((hH.mono_measure (Measure.restrict_mono hball le_rfl)).mono_exponent
    hq).integrable_norm_rpow hq0 ENNReal.ofReal_ne_top
  -- Its norm is at least `c ‖x‖ ^ (γ - 2)`, so `‖x‖ ^ ((γ - 2) q)` would be integrable there.
  set c := |γ * (finrank ℝ E + γ - 2)| / finrank ℝ E
  have hc : 0 < c := div_pos (abs_pos.2 (mul_ne_zero hγ0.ne' (by linarith))) hnpos
  have hpow : IntegrableOn (fun x : E => ‖x‖ ^ ((γ - 2) * q.toReal)) (ball 0 r) μ := by
    refine (hint.const_mul (c ^ (-q.toReal))).mono'
      (by fun_prop : Measurable fun x : E => ‖x‖ ^ ((γ - 2) * q.toReal)).aestronglyMeasurable
      ?_
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := μ) 0))]
      with x hx
    have hlow : c * ‖x‖ ^ (γ - 2) ≤ ‖iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1 x‖ := by
      rw [iteratedGradientChain_one_norm_rpow_eq_hessField hx, div_mul_eq_mul_div,
        div_le_iff₀ hnpos, mul_comm _ (finrank ℝ E : ℝ)]
      exact abs_mul_rpow_le_norm_hessField hx
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_mul (norm_nonneg x),
      Real.rpow_neg hc.le, le_inv_mul_iff₀ (by positivity),
      ← Real.mul_rpow hc.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hlow ENNReal.toReal_nonneg
  have := (integrableOn_norm_rpow_ball_iff hr).1 hpow
  rw [hqr, show (γ - 2) * (finrank ℝ E / (2 - γ)) = -finrank ℝ E by field_simp; ring] at this
  exact lt_irrefl _ this

/-- For `0 < γ < 2` and `p < n / (2 - γ)`, `‖x‖ ^ γ` lies in `W^{2,p}` of a bounded open set. -/
private theorem exists_wkp_two_value_ae_eq_norm_rpow (hγ0 : 0 < γ) (hγ : γ < 2)
    (hn : 2 < finrank ℝ E + γ) {Ω : Opens E} (hb : Bornology.IsBounded (Ω : Set E))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p < ENNReal.ofReal (finrank ℝ E / (2 - γ))) :
    ∃ w : Wkp μ Ω p 2, (Wkp.value 2 w : E → ℝ) =ᵐ[μ.restrict Ω] fun y => ‖y‖ ^ γ := by
  have := nontrivial_of_two_lt hγ.le hn
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have h2γ : 0 < 2 - γ := by linarith
  have hpt : p ≠ ∞ := ne_top_of_lt hp
  have hpr : p.toReal * (2 - γ) < finrank ℝ E := by
    have := (ENNReal.toReal_lt_toReal hpt ENNReal.ofReal_ne_top).2 hp
    rwa [ENNReal.toReal_ofReal (by positivity), lt_div_iff₀ h2γ] at this
  have hp1r : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpt hp1
  have hu : MemLp (fun y : E => ‖y‖ ^ γ) p (μ.restrict Ω) :=
    memLp_restrict_of_norm_le_mul_norm_rpow (C := 1) hp0 hpt hb
      (continuous_norm.rpow_const fun _ => Or.inr hγ0.le).aestronglyMeasurable
      (fun x _ => by rw [one_mul, Real.norm_of_nonneg (by positivity)])
      (by nlinarith)
  have hg : MemLp (∇ fun y : E => ‖y‖ ^ γ) p (μ.restrict Ω) :=
    memLp_restrict_of_norm_le_mul_norm_rpow hp0 hpt hb
      (measurable_gradient _).aestronglyMeasurable (fun x hx => (norm_gradient_norm_rpow hx).le)
      (by nlinarith)
  have hH : MemLp (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) p (μ.restrict Ω) :=
    memLp_restrict_of_norm_le_mul_norm_rpow hp0 hpt hb
      (aestronglyMeasurable_iteratedGradientChain_one_norm_rpow (μ := μ)).restrict
      (fun x hx => by
        rw [iteratedGradientChain_one_norm_rpow_eq_hessField hx]
        exact norm_hessField_le hx le_rfl hγ.le)
      (by nlinarith)
  have h1 : HasWeakFDerivOn μ Ω hu.toLp (fun x => innerSL ℝ (⇑hg.toLp x)) :=
    ((hasWeakFDerivOn_norm_rpow_innerSL_gradient hγ0 Ω).congr_ae hu.coeFn_toLp.symm).congr_ae_deriv
      (hg.coeFn_toLp.mono fun x hx => by simp only [hx])
  obtain ⟨v, hv, hgv⟩ : ∃ v : Wkp μ Ω p 1,
      W1p.value v = hu.toLp ∧ Wkp.iteratedGradient 0 v = hg.toLp :=
    ⟨W1p.mk hu.toLp hg.toLp h1, W1p.value_mk _ _ h1,
      (Wkp.iteratedGradient_zero _).trans (W1p.gradient_mk _ _ h1)⟩
  have h2 : HasWeakFDerivOn μ Ω (Wkp.iteratedGradient 0 v) hH.toLp := by
    rw [hgv]
    exact ((hasWeakFDerivOn_gradient_norm_rpow hn Ω).congr_ae
      hg.coeFn_toLp.symm).congr_ae_deriv hH.coeFn_toLp.symm
  refine ⟨Wkp.mk 0 v hH.toLp h2, ?_⟩
  rw [Wkp.value_mk, Wkp.value_one, hv]
  exact hu.coeFn_toLp

/-- **`W^{2,p}` regularity of a norm power.** Let `0 < γ < 2` with `n + γ > 2`, where `n` is the
dimension, and let `Ω` be a bounded open set containing the origin. Then `‖x‖ ^ γ` lies in
`W^{2,p}(Ω)` exactly when `p < n / (2 - γ)`. The Hessian has size comparable to
`‖x‖ ^ (γ - 2)`, which is `p`-integrable near the origin exactly in this range; the case
`p = ∞` is included and never occurs. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow_iff (hγ0 : 0 < γ) (hγ : γ < 2)
    (hn : 2 < finrank ℝ E + γ) {Ω : Opens E} (hb : Bornology.IsBounded (Ω : Set E))
    (h0 : (0 : E) ∈ Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (∃ w : Wkp μ Ω p 2, (Wkp.value 2 w : E → ℝ) =ᵐ[μ.restrict Ω] fun y => ‖y‖ ^ γ) ↔
      p < ENNReal.ofReal (finrank ℝ E / (2 - γ)) :=
  ⟨fun ⟨w, hw⟩ => lt_ofReal_of_memLp_iteratedGradientChain_one_norm_rpow hγ0 hγ hn
      (Ω.isOpen.mem_nhds h0) ((Lp.memLp (Wkp.iteratedGradient 1 w)).ae_eq
        (Wkp.iteratedGradient_one_ae_eq_norm_rpow hγ0 hn w hw)),
    exists_wkp_two_value_ae_eq_norm_rpow hγ0 hγ hn hb⟩

end TauCeti
