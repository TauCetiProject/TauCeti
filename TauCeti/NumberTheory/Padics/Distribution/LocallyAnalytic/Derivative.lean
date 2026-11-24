/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic
import Mathlib.Algebra.Polynomial.Identities

/-!
# The derivative of locally analytic functions

On the disc `a + pʰℤ_p` the coordinate is `x = a + pʰ w`, and a locally analytic function is the
power series `∑ₙ c(a, n) wⁿ`. Its derivative in the disc coordinate `w` has coefficients
`(n + 1) • c(a, n + 1)`. This coefficient operator is `TauCeti.AnalyticStage.discDerivative`, a
continuous linear endomorphism of the analytic stage `LA_h(E)` which does not increase norms, for
every ultrametric normed group `E` with a semiring action.

When `E` is moreover a complete `ℤ_p`-module with contractive `ℤ_p`-action
(`‖r • v‖ ≤ ‖r‖ ‖v‖`), `discDerivative` is the derivative of the evaluated function: it evaluates
to the series of termwise derivatives (`hasSum_eval_discDerivative`), and on each disc the Taylor
remainder of order two is quadratic,

`‖f(a + pʰ (w + d)) - f(a + pʰ w) - d • (d f / d w)(a + pʰ w)‖ ≤ ‖d‖² ‖c‖`

(`norm_eval_add_sub_sub_smul_eval_discDerivative_le`).

Since `d/dx = p⁻ʰ d/dw` on the discs of level `h`, the derivative in `x` requires `p` to be
invertible on the coefficients. For a field `𝕜` acting on `E` in which `p ≠ 0`, it is
`TauCeti.AnalyticStage.derivative 𝕜 = (pʰ)⁻¹ • discDerivative 𝕜`. On the subdiscs of level `h + 1`,
`w = b + p v`, so the derivative in `v` is `p` times the re-expanded derivative in `w`
(`discDerivative_transition`), and the derivative in `x` commutes with re-expansion
(`transition_derivative`). It therefore induces the derivative
`TauCeti.LocallyAnalytic.derivative 𝕜` of locally analytic functions `LA(ℤ_p, E)`, which is the
derivative of the evaluated functions with a quadratic remainder
(`LocallyAnalytic.exists_norm_eval_sub_sub_smul_eval_derivative_le`). It vanishes on stage vectors
whose coefficients of positive degree vanish (`LocallyAnalytic.derivative_ofStage_eq_zero`).

The transpose derivative of distributions is in
`TauCeti.NumberTheory.Padics.Distribution.Derivative`, and the Leibniz rules for multiplication by
the coordinate are in `TauCeti.NumberTheory.Padics.Distribution.MulCoord`.

## Main definitions

* `TauCeti.AnalyticStage.discDerivative S`: the derivative in the disc coordinate on `LA_h(E)`.
* `TauCeti.AnalyticStage.derivative 𝕜`: the derivative `d/dx = p⁻ʰ d/dw` on `LA_h(E)`.
* `TauCeti.LocallyAnalytic.derivative 𝕜`: the derivative on `LA(ℤ_p, E)`.

## Main results

* `TauCeti.AnalyticStage.hasSum_eval_discDerivative`: the derivative in the disc coordinate
  evaluates to the series of termwise derivatives.
* `TauCeti.AnalyticStage.norm_eval_add_sub_sub_smul_eval_discDerivative_le` and
  `TauCeti.LocallyAnalytic.exists_norm_eval_sub_sub_smul_eval_derivative_le`: the derivatives
  differentiate the evaluated functions, with a quadratic remainder.
* `TauCeti.AnalyticStage.transition_derivative`: the derivative commutes with re-expansion.
* `TauCeti.LocallyAnalytic.derivative_ofStage_eq_zero`: the derivative vanishes on stage vectors
  whose coefficients of positive degree vanish.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ}

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]

/-! ### The derivative in the disc coordinate -/

/-- The coefficients `(n + 1) • c(a, n + 1)` of the derivative in `w` of `∑ₙ c(a, n) wⁿ`. -/
private noncomputable def discDerivativeCoeff (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) :
    E :=
  (i.2 + 1) • c (i.1, i.2 + 1)

private theorem norm_discDerivativeCoeff_le (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) :
    ‖discDerivativeCoeff c i‖ ≤ ‖c (i.1, i.2 + 1)‖ :=
  IsUltrametricDist.norm_nsmul_le _ _

private theorem tendsto_discDerivativeCoeff (c : AnalyticStage p h E) :
    Tendsto (discDerivativeCoeff c) cofinite (𝓝 0) := by
  have hinj : Function.Injective fun i : ZMod (p ^ h) × ℕ ↦ (i.1, i.2 + 1) :=
    Function.injective_id.prodMap Nat.succ_injective
  exact squeeze_zero_norm (norm_discDerivativeCoeff_le c)
    ((tendsto_zero_iff_norm_tendsto_zero.mp c.tendsto_cofinite).comp hinj.tendsto_cofinite)

/-- The coefficient vector of the derivative in `w` has norm at most `‖c‖`. -/
private theorem norm_mkOfDiscrete_discDerivativeCoeff_le (c : AnalyticStage p h E) :
    ‖ZeroAtInftyContinuousMap.mkOfDiscrete (discDerivativeCoeff c)
      (tendsto_discDerivativeCoeff c)‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦ by
    rw [ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
    exact (norm_discDerivativeCoeff_le c i).trans (c.norm_coe_le_norm _)

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

/-- The derivative in the disc coordinate on the analytic stage `LA_h(E)`: on the disc of `a`,
where `x = a.val + pʰ w`, it differentiates `∑ₙ c(a, n) wⁿ` in `w`, so the coefficient of `wⁿ`
becomes `(n + 1) • c(a, n + 1)`. -/
noncomputable def discDerivative : AnalyticStage p h E →L[S] AnalyticStage p h E :=
  let L : AnalyticStage p h E →ₗ[S] AnalyticStage p h E :=
    { toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete (discDerivativeCoeff c)
        (tendsto_discDerivativeCoeff c)
      map_add' c d := by
        ext i
        simp [discDerivativeCoeff, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, smul_add]
      map_smul' s c := by
        ext i
        simp [discDerivativeCoeff, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, smul_comm _ s] }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      exact norm_mkOfDiscrete_discDerivativeCoeff_le c }

/-- The coefficient of `wⁿ` in the derivative in `w` on the disc of `a` is `(n + 1) • c(a, n + 1)`.
-/
@[simp]
theorem discDerivative_apply (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (n : ℕ) :
    discDerivative S c (a, n) = (n + 1) • c (a, n + 1) :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete (discDerivativeCoeff c)
    (tendsto_discDerivativeCoeff c)) (a, n)

/-- The derivative in the disc coordinate does not increase norms. -/
theorem norm_discDerivative_le (c : AnalyticStage p h E) : ‖discDerivative S c‖ ≤ ‖c‖ :=
  norm_mkOfDiscrete_discDerivativeCoeff_le c

/-- The derivative in the disc coordinate has operator norm at most `1`. -/
theorem opNorm_discDerivative_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖discDerivative (p := p) (h := h) (E := E) 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_discDerivative_le 𝕜 c

/-! ### The derivative in the coordinate `x` -/

section Derivative

variable (𝕜 : Type*) [Field 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]

/-- The derivative `d/dx = p⁻ʰ d/dw` on the analytic stage `LA_h(E)`, as a coefficient operator:
on the disc of `a`, where `w = (x - a) / pʰ`, it multiplies the derivative in `w`
(`discDerivative`) by the inverse of `pʰ` in the field `𝕜` acting on the coefficients.

When moreover `p ≠ 0` in `𝕜` and `E` is a complete `ℤ_p`-module with contractive `ℤ_p`-action on
which `AnalyticStage.eval` is defined, it is the derivative of the evaluated function: see
`LocallyAnalytic.exists_norm_eval_sub_sub_smul_eval_derivative_le` for the quadratic remainder
bound. -/
noncomputable def derivative : AnalyticStage p h E →L[𝕜] AnalyticStage p h E :=
  ((p : 𝕜) ^ h)⁻¹ • discDerivative 𝕜

/-- The derivative in `x` is `p⁻ʰ` times the derivative in the disc coordinate. -/
theorem derivative_def (c : AnalyticStage p h E) :
    derivative 𝕜 c = ((p : 𝕜) ^ h)⁻¹ • discDerivative 𝕜 c :=
  (rfl)

/-- The coefficient of `wⁿ` in the derivative in `x` on the disc of `a` is
`p⁻ʰ (n + 1) • c(a, n + 1)`. -/
@[simp]
theorem derivative_apply (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (n : ℕ) :
    derivative 𝕜 c (a, n) = ((p : 𝕜) ^ h)⁻¹ • ((n + 1) • c (a, n + 1)) := by
  rw [derivative_def, smul_apply, discDerivative_apply]

end Derivative

/-- The derivative in `x` multiplies norms by at most `‖p⁻ʰ‖`. -/
theorem norm_derivative_le (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : AnalyticStage p h E) :
    ‖derivative 𝕜 c‖ ≤ ‖((p : 𝕜) ^ h)⁻¹‖ * ‖c‖ := by
  rw [derivative_def]
  exact (norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_discDerivative_le 𝕜 c) (norm_nonneg _))

/-- The derivative in `x` has operator norm at most `‖p⁻ʰ‖`. -/
theorem opNorm_derivative_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖derivative (p := p) (h := h) (E := E) 𝕜‖ ≤ ‖((p : 𝕜) ^ h)⁻¹‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_derivative_le 𝕜)

variable [hp : Fact p.Prime] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [SMulCommClass ℤ_[p] S E]
  [CompleteSpace E]

/-- **The derivative in `v` of the re-expansion.** On the disc of level `h + 1` where
`w = b + p v`, differentiating in `v` is `p` times the re-expansion of the derivative in `w`. -/
theorem discDerivative_transition (c : AnalyticStage p h E) :
    discDerivative S (transition S c) = (p : ℤ_[p]) • transition S (discDerivative S c) := by
  ext ⟨a', j⟩
  rw [discDerivative_apply, smul_apply]
  -- Pascal-type identity `(j + 1) R(m + 1, j + 1) = p (m + 1) R(m, j)` for the re-expansion
  -- scalars `R(m, j) = (m choose j) b^(m - j) pʲ`.
  have hscalar (b : ℤ_[p]) (m : ℕ) : ((j + 1 : ℕ) : ℤ_[p]) * reexpandScalar b p (m + 1) (j + 1) =
      (p : ℤ_[p]) * (reexpandScalar b p m j * ((m + 1 : ℕ) : ℤ_[p])) := by
    have hchoose : ((m + 1 : ℕ) : ℤ_[p]) * (m.choose j : ℤ_[p]) =
        ((m + 1).choose (j + 1) : ℤ_[p]) * ((j + 1 : ℕ) : ℤ_[p]) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    simp only [reexpandScalar_def, Nat.add_sub_add_right]
    linear_combination (-(b ^ (m - j) * (p : ℤ_[p]) ^ (j + 1))) * hchoose
  -- Both sides are sums over the degrees `m + 1` on the disc of level `h`; the degree `0` term of
  -- the left side vanishes.
  have hD := (hasSum_transition_apply S (discDerivative S c) a' j).const_smul (p : ℤ_[p])
  have hT := (hasSum_transition_apply S c a' (j + 1)).const_smul (((j + 1 : ℕ) : ℤ_[p]))
  have hT' := (hasSum_nat_add_iff' 1).mpr hT
  simp only [Finset.range_one, Finset.sum_singleton, reexpandScalar_of_lt _ _ (Nat.succ_pos j),
    zero_smul, smul_zero, sub_zero] at hT'
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], hT'.unique (hD.congr_fun fun m ↦ ?_)]
  simp only [discDerivative_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, hscalar]

/-- **The derivative in the disc coordinate evaluates to the termwise derivative.** On the disc of
`a`, the derivative in `w` of `f = eval c` is `∑ₙ (n wⁿ⁻¹) • c(a, n)`. -/
theorem hasSum_eval_discDerivative (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    HasSum (fun n : ℕ ↦ ((n : ℤ_[p]) * w ^ (n - 1)) • c (a, n))
      (eval S (discDerivative S c) ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w)) := by
  -- Shift the series `∑ₙ wⁿ • (n + 1) • c(a, n + 1)` by one degree; its degree `0` term vanishes.
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
  refine (hasSum_eval_natCast_val_add_mul S (discDerivative S c) a w).congr_fun fun n ↦ ?_
  rw [discDerivative_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, Nat.add_sub_cancel,
    mul_comm]

/-- **The derivative in the disc coordinate differentiates the evaluated function.** On the disc
of `a`, the Taylor remainder of order two of `f = eval c` in the disc coordinate is bounded by
`‖d‖² ‖c‖`:

`‖f(a + pʰ (w + d)) - f(a + pʰ w) - d • (d f / d w)(a + pʰ w)‖ ≤ ‖d‖² ‖c‖`. -/
theorem norm_eval_add_sub_sub_smul_eval_discDerivative_le (c : AnalyticStage p h E)
    (a : ZMod (p ^ h)) (w d : ℤ_[p]) :
    ‖eval S c ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (w + d)) -
        eval S c ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) -
        d • eval S (discDerivative S c) ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w)‖ ≤
      ‖d‖ ^ 2 * ‖c‖ := by
  have hsum := ((hasSum_eval_natCast_val_add_mul S c a (w + d)).sub
    (hasSum_eval_natCast_val_add_mul S c a w)).sub
    ((hasSum_eval_discDerivative S c a w).const_smul d)
  rw [← hsum.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦ ?_
  -- By the binomial expansion, `(w + d)ⁿ - wⁿ - d (n wⁿ⁻¹) = k d²` with `k ∈ ℤ_p`.
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ n) w d
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  have hrem : (w + d) ^ n - w ^ n - d * ((n : ℤ_[p]) * w ^ (n - 1)) = k * d ^ 2 := by
    linear_combination hk
  rw [smul_smul, ← sub_smul, ← sub_smul, hrem]
  refine (norm_smul_le _ _).trans ?_
  rw [norm_mul, norm_pow]
  calc ‖k‖ * ‖d‖ ^ 2 * ‖c (a, n)‖ ≤ 1 * ‖d‖ ^ 2 * ‖c‖ := by
        gcongr
        exacts [PadicInt.norm_le_one k, c.norm_coe_le_norm _]
    _ = ‖d‖ ^ 2 * ‖c‖ := by rw [one_mul]

/-! ### Re-expansion of the derivative in `x` -/

section Derivative

variable (𝕜 : Type*) [Field 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
variable [NeZero (p : 𝕜)] [SMulCommClass ℤ_[p] 𝕜 E]

/-- **The derivative commutes with re-expansion** to the discs of the next level. -/
theorem transition_derivative (c : AnalyticStage p h E) :
    transition 𝕜 (derivative 𝕜 c) = derivative 𝕜 (transition 𝕜 c) := by
  -- The levels differ by one factor `p`: `p⁻ʰ = p⁻⁽ʰ⁺¹⁾ p`.
  have hinv : ((p : 𝕜) ^ h)⁻¹ = ((p : 𝕜) ^ (h + 1))⁻¹ * p := by
    field_simp [NeZero.ne (p : 𝕜)]
    ring
  rw [derivative_def, derivative_def, map_smul, discDerivative_transition,
    Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, hinv]

/-- The derivative commutes with re-expansion between any two levels. -/
theorem transitionLE_derivative {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transitionLE 𝕜 hhk (derivative 𝕜 c) = derivative 𝕜 (transitionLE 𝕜 hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ 𝕜 hhk, ContinuousLinearMap.comp_apply, ih, transition_derivative,
      ContinuousLinearMap.comp_apply]

end Derivative

end AnalyticStage

variable [hp : Fact p.Prime]

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (𝕜 : Type*) [Field 𝕜] [NeZero (p : 𝕜)] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
  [SMulCommClass ℤ_[p] 𝕜 E]

/-- The derivative of locally analytic functions `LA(ℤ_p, E)`, induced by
`AnalyticStage.derivative` on each stage. It is defined when `p` is invertible in a field `𝕜`
acting on the coefficients. -/
noncomputable def derivative : LocallyAnalytic p 𝕜 E →ₗ[𝕜] LocallyAnalytic p 𝕜 E :=
  Module.DirectLimit.map (fun _ ↦ (AnalyticStage.derivative 𝕜).toLinearMap)
    fun _ _ hhk ↦ LinearMap.ext fun c ↦ (transitionLE_derivative 𝕜 hhk c).symm

/-- The derivative is computed on any stage. -/
@[simp]
theorem derivative_ofStage (h : ℕ) (c : AnalyticStage p h E) :
    derivative 𝕜 (ofStage 𝕜 h c) = ofStage 𝕜 h (AnalyticStage.derivative 𝕜 c) := by
  rw [derivative, ofStage_def, Module.DirectLimit.map_apply_of, ContinuousLinearMap.coe_coe]

/-- **The derivative vanishes on a stage vector with no coefficients of positive degree.** -/
theorem derivative_ofStage_eq_zero {h : ℕ} {c : AnalyticStage p h E}
    (hc : ∀ a n, c (a, n + 1) = 0) : derivative 𝕜 (ofStage 𝕜 h c) = 0 := by
  have hc' : AnalyticStage.derivative 𝕜 c = 0 := by
    ext ⟨a, n⟩
    simp [hc]
  rw [derivative_ofStage, hc', map_zero]

/-- **The derivative differentiates the evaluated function.** For every locally analytic `f` there
are a level `h` and a constant `C` such that the Taylor remainder of order two is quadratic on the
discs of level `h`:

`‖f(y) - f(x) - (y - x) • f'(x)‖ ≤ C ‖y - x‖²` whenever `‖y - x‖ ≤ p⁻ʰ`. -/
theorem exists_norm_eval_sub_sub_smul_eval_derivative_le (f : LocallyAnalytic p 𝕜 E) :
    ∃ (h : ℕ) (C : ℝ), ∀ x y : ℤ_[p], ‖y - x‖ ≤ (p : ℝ) ^ (-(h : ℤ)) →
      ‖eval 𝕜 f y - eval 𝕜 f x - (y - x) • eval 𝕜 (derivative 𝕜 f) x‖ ≤ C * ‖y - x‖ ^ 2 := by
  obtain ⟨h, c, rfl⟩ := exists_ofStage 𝕜 f
  have hp𝕜 : ((p : 𝕜) ^ h) ≠ 0 := pow_ne_zero h (NeZero.ne _)
  have hpℤ : ‖(p : ℤ_[p]) ^ h‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (pow_ne_zero h (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  refine ⟨h, ‖c‖ / ‖(p : ℤ_[p]) ^ h‖ ^ 2, fun x y hxy ↦ ?_⟩
  simp only [derivative_ofStage, eval_ofStage, AnalyticStage.derivative_def, map_smul,
    ContinuousMap.smul_apply]
  -- Write `x = a + pʰ w` and `y - x = d pʰ`.
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨d, hd⟩ :=
    Ideal.mem_span_singleton'.mp ((PadicInt.norm_le_pow_iff_mem_span_pow _ h).mp hxy)
  simp only [PadicInt.discHomeomorph_apply] at hd ⊢
  have hy : y = (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (w + d) := by
    linear_combination -hd
  -- The scalar `d pʰ` acting on `p⁻ʰ v` is `d` acting on `v`.
  have hsmul (v : E) : (d * (p : ℤ_[p]) ^ h) • (((p : 𝕜) ^ h)⁻¹ • v) = d • v := by
    have hp' : ((p ^ h : ℕ) : 𝕜) ≠ 0 := by rwa [Nat.cast_pow]
    simp only [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_inv_smul₀ hp']
  rw [← hd, hsmul, hy]
  refine (norm_eval_add_sub_sub_smul_eval_discDerivative_le 𝕜 c a w d).trans_eq ?_
  rw [norm_mul, mul_pow]
  field_simp

end LocallyAnalytic

end TauCeti
