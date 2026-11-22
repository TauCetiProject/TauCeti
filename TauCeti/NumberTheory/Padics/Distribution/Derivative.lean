/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Convolution
public import TauCeti.NumberTheory.Padics.Distribution.MulCoord
import Mathlib.Algebra.Polynomial.Identities

/-!
# The derivative of locally analytic functions and the transpose derivative of distributions

On the disc `a + pʰℤ_p` the coordinate is `x = a + pʰ w`, and a locally analytic function is the
power series `∑ₙ c(a, n) wⁿ`. Its derivative in the disc coordinate `w` has coefficients
`(n + 1) • c(a, n + 1)`. This is `TauCeti.AnalyticStage.discDerivative`, a continuous linear
endomorphism of the analytic stage `LA_h(E)` which does not increase norms, for every complete
ultrametric `ℤ_p`-module `E`. It is the derivative of the evaluated function in the strong sense
of a quadratic Taylor remainder: on each disc,

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
(`LocallyAnalytic.exists_norm_eval_sub_sub_smul_eval_derivative_le`). It kills the constants
(`derivative_mahlerTerm_zero`) and satisfies the Leibniz rule for multiplication by the coordinate,
`(x f)' = f + x f'` (`derivative_mulCoord`).

The transpose is the derivative of a distribution, `TauCeti.LocallyAnalyticDistribution.derivative`,
with the sign convention `(d μ)(f) = μ(f')`. Over a field `K` of characteristic zero, it acts on the
Amice transform as multiplication by `log (1 + T)` (`amiceTransform_derivative`):

`A_{d μ} = log (1 + T) · A_μ`.

The proof needs no formula for the derivatives of the binomial polynomials. By the Leibniz rule,
`x (d μ) = μ + d (x μ)`, and multiplication by `x` acts on Amice transforms as the derivation
`∂ = (1 + T) d/dT` (`amiceTransform_mulCoord`). Since `∂ log (1 + T) = 1`, the difference
`A_{d μ} - log (1 + T) A_μ` intertwines multiplication by `x` with `∂`; its constant coefficient
vanishes because the derivative kills the constant `1`, and the coefficient formula
`∂ (∑ₙ aₙ Tⁿ) = ∑ₙ ((n + 1) aₙ₊₁ + n aₙ) Tⁿ` then kills all its coefficients by induction. In
particular the derivative at `0`, `f ↦ f'(0)`, has Amice transform `log (1 + T)`
(`amiceTransform_derivative_one`).

## Main definitions

* `TauCeti.AnalyticStage.discDerivative S`: the derivative in the disc coordinate on `LA_h(E)`.
* `TauCeti.AnalyticStage.derivative 𝕜`: the derivative `d/dx = p⁻ʰ d/dw` on `LA_h(E)`.
* `TauCeti.LocallyAnalytic.derivative 𝕜`: the derivative on `LA(ℤ_p, E)`.
* `TauCeti.LocallyAnalyticDistribution.derivative`: the transpose derivative `(d μ)(f) = μ(f')`.

## Main results

* `TauCeti.AnalyticStage.norm_eval_add_sub_sub_smul_eval_discDerivative_le` and
  `TauCeti.LocallyAnalytic.exists_norm_eval_sub_sub_smul_eval_derivative_le`: the derivatives
  differentiate the evaluated functions, with a quadratic remainder.
* `TauCeti.AnalyticStage.transition_derivative`: the derivative commutes with re-expansion.
* `TauCeti.LocallyAnalytic.derivative_mulCoord`: the Leibniz rule `(x f)' = f + x f'`.
* `TauCeti.LocallyAnalytic.derivative_mahlerTerm_zero`: the derivative of a constant is zero.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_derivative_le`: the derivative multiplies the
  stage seminorm of level `h` by at most `‖p‖⁻ʰ`.
* `TauCeti.LocallyAnalyticDistribution.mulCoord_derivative`: `x (d μ) = μ + d (x μ)`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_derivative`: `A_{d μ} = log (1 + T) · A_μ`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ}

/-- Multiplication by `pⁿ` is the same through `ℤ_p` and through any semiring `𝕜` acting on `E`. -/
private theorem natCast_pow_smul_eq [Fact p.Prime] {E : Type*} [AddCommMonoid E] [Module ℤ_[p] E]
    (𝕜 : Type*) [Semiring 𝕜] [Module 𝕜 E] (n : ℕ) (v : E) :
    (p : ℤ_[p]) ^ n • v = ((p : 𝕜) ^ n) • v := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

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
  have hinj : Function.Injective fun i : ZMod (p ^ h) × ℕ ↦ (i.1, i.2 + 1) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hi
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hi
    rw [hi.1, hi.2]
  exact squeeze_zero_norm (norm_discDerivativeCoeff_le c)
    ((tendsto_zero_iff_norm_tendsto_zero.mp c.tendsto_cofinite).comp hinj.tendsto_cofinite)

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
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦ ?_
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact (norm_discDerivativeCoeff_le c i).trans (c.norm_coe_le_norm _) }

private theorem coe_discDerivative (c : AnalyticStage p h E) :
    ⇑(discDerivative S c) = discDerivativeCoeff c :=
  ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _

/-- The coefficient of `wⁿ` in the derivative in `w` on the disc of `a` is `(n + 1) • c(a, n + 1)`.
-/
@[simp]
theorem discDerivative_apply (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (n : ℕ) :
    discDerivative S c (a, n) = (n + 1) • c (a, n + 1) := by
  rw [coe_discDerivative, discDerivativeCoeff]

/-- The derivative in the disc coordinate does not increase norms. -/
theorem norm_discDerivative_le (c : AnalyticStage p h E) : ‖discDerivative S c‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦
    coe_discDerivative S c ▸ (norm_discDerivativeCoeff_le c i).trans (c.norm_coe_le_norm _)

/-- The derivative in the disc coordinate has operator norm at most `1`. -/
theorem opNorm_discDerivative_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖discDerivative (p := p) (h := h) (E := E) 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_discDerivative_le 𝕜 c

/-! ### The derivative in the coordinate `x` -/

section Derivative

variable (𝕜 : Type*) [Field 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]

/-- The derivative `d/dx = p⁻ʰ d/dw` on the analytic stage `LA_h(E)`, where `w = (x - a) / pʰ` is
the coordinate of the disc of `a`. It is the derivative of the evaluated functions when `p` is
invertible in the field `𝕜` acting on the coefficients. -/
noncomputable def derivative : AnalyticStage p h E →L[𝕜] AnalyticStage p h E :=
  ((p : 𝕜) ^ h)⁻¹ • discDerivative 𝕜

/-- The derivative in `x` is `p⁻ʰ` times the derivative in the disc coordinate. -/
theorem derivative_apply (c : AnalyticStage p h E) :
    derivative 𝕜 c = ((p : 𝕜) ^ h)⁻¹ • discDerivative 𝕜 c :=
  (rfl)

end Derivative

variable [hp : Fact p.Prime] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [SMulCommClass ℤ_[p] S E]

/-- **The Leibniz rule for the coordinate.** Differentiating `x f = (a + pʰ w) f` in `w` gives
`pʰ f + x (d f / d w)`. -/
theorem discDerivative_mulCoord (c : AnalyticStage p h E) :
    discDerivative S (mulCoord S c) = (p : ℤ_[p]) ^ h • c + mulCoord S (discDerivative S c) := by
  ext ⟨a, _ | n⟩ <;>
  · simp only [discDerivative_apply, mulCoord_apply_zero, mulCoord_apply_succ, FunLike.coe_add,
      Pi.add_apply, smul_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p]]
    push_cast
    module

variable [CompleteSpace E]

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
  rw [discDerivative_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, smul_smul, smul_smul,
    hscalar, mul_assoc]

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
  -- The derivative series, shifted by one degree, is `∑ₙ (n wⁿ⁻¹ d) • c(a, n)`.
  have hD := ((hasSum_eval_natCast_val_add_mul S (discDerivative S c) a w).const_smul d)
  have hD' : HasSum (fun n : ℕ ↦ ((n : ℤ_[p]) * w ^ (n - 1) * d) • c (a, n))
      (d • eval S (discDerivative S c) ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, zero_smul,
      sub_zero]
    refine hD.congr_fun fun n ↦ ?_
    rw [discDerivative_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, smul_smul,
      Nat.add_sub_cancel]
    congr 1
    push_cast
    ring
  have hsum := ((hasSum_eval_natCast_val_add_mul S c a (w + d)).sub
    (hasSum_eval_natCast_val_add_mul S c a w)).sub hD'
  rw [← hsum.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦ ?_
  -- By the binomial expansion, `(w + d)ⁿ - wⁿ - n wⁿ⁻¹ d = k d²` with `k ∈ ℤ_p`.
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ n) w d
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  rw [← sub_smul, ← sub_smul, hk, show (w ^ n + (n : ℤ_[p]) * w ^ (n - 1) * d + k * d ^ 2 - w ^ n -
    (n : ℤ_[p]) * w ^ (n - 1) * d) = k * d ^ 2 by ring]
  refine (norm_smul_le _ _).trans ?_
  rw [norm_mul, norm_pow]
  calc ‖k‖ * ‖d‖ ^ 2 * ‖c (a, n)‖ ≤ 1 * ‖d‖ ^ 2 * ‖c‖ := by
        gcongr
        exacts [PadicInt.norm_le_one k, c.norm_coe_le_norm _]
    _ = ‖d‖ ^ 2 * ‖c‖ := by rw [one_mul]

/-! ### Re-expansion and the Leibniz rule for the derivative in `x` -/

section Derivative

variable (𝕜 : Type*) [Field 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
variable [NeZero (p : 𝕜)] [SMulCommClass ℤ_[p] 𝕜 E]

/-- **The derivative commutes with re-expansion** to the discs of the next level. -/
theorem transition_derivative (c : AnalyticStage p h E) :
    transition 𝕜 (derivative 𝕜 c) = derivative 𝕜 (transition 𝕜 c) := by
  have hp : (p : 𝕜) ≠ 0 := NeZero.ne _
  rw [derivative_apply, derivative_apply, map_smul, discDerivative_transition,
    ← pow_one (p : ℤ_[p]), natCast_pow_smul_eq 𝕜, smul_smul]
  congr 1
  rw [pow_succ, pow_one, mul_inv, mul_assoc, inv_mul_cancel₀ hp, mul_one]

/-- The derivative commutes with re-expansion between any two levels. -/
theorem transitionLE_derivative {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transitionLE 𝕜 hhk (derivative 𝕜 c) = derivative 𝕜 (transitionLE 𝕜 hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ 𝕜 hhk, ContinuousLinearMap.comp_apply, ih, transition_derivative,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
/-- **The Leibniz rule for the coordinate**: `(x f)' = f + x f'`. -/
theorem derivative_mulCoord (c : AnalyticStage p h E) :
    derivative 𝕜 (mulCoord 𝕜 c) = c + mulCoord 𝕜 (derivative 𝕜 c) := by
  have hp : ((p : 𝕜) ^ h) ≠ 0 := pow_ne_zero h (NeZero.ne _)
  rw [derivative_apply, derivative_apply, discDerivative_mulCoord, natCast_pow_smul_eq 𝕜, smul_add,
    inv_smul_smul₀ hp, map_smul]

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

/-- **The Leibniz rule for the coordinate**: `(x f)' = f + x f'`. -/
theorem derivative_mulCoord (f : LocallyAnalytic p 𝕜 E) :
    derivative 𝕜 (mulCoord 𝕜 f) = f + mulCoord 𝕜 (derivative 𝕜 f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, mulCoord_ofStage, derivative_ofStage, derivative_ofStage, mulCoord_ofStage,
    AnalyticStage.derivative_mulCoord, map_add]

/-- **The derivative of a constant is zero**: `mahlerTerm p 𝕜 e 0` is the constant function `e`. -/
@[simp]
theorem derivative_mahlerTerm_zero (e : E) : derivative 𝕜 (mahlerTerm p 𝕜 e 0) = 0 := by
  have hc : discDerivative 𝕜 (amiceTerm p 0 0 e) = 0 := by
    ext ⟨a, n⟩
    simp only [discDerivative_apply, amiceTerm_apply,
      coeff_amicePolynomial_eq_zero _ (Nat.succ_pos n), zero_smul, smul_zero, zero_apply]
  rw [mahlerTerm_def, derivative_ofStage, AnalyticStage.derivative_apply, hc, smul_zero, map_zero]

/-- **The derivative differentiates the evaluated function.** For every locally analytic `f` there
are a level `h` and a constant `C` such that the Taylor remainder of order two is quadratic on the
discs of level `h`:

`‖f(y) - f(x) - (y - x) • f'(x)‖ ≤ C ‖y - x‖²` whenever `‖y - x‖ ≤ p⁻ʰ`. -/
theorem exists_norm_eval_sub_sub_smul_eval_derivative_le (f : LocallyAnalytic p 𝕜 E) :
    ∃ (h : ℕ) (C : ℝ), ∀ x y : ℤ_[p], ‖y - x‖ ≤ (p : ℝ) ^ (-(h : ℤ)) →
      ‖eval 𝕜 f y - eval 𝕜 f x - (y - x) • eval 𝕜 (derivative 𝕜 f) x‖ ≤ C * ‖y - x‖ ^ 2 := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  have hp𝕜 : ((p : 𝕜) ^ h) ≠ 0 := pow_ne_zero h (NeZero.ne _)
  have hpℤ : ‖(p : ℤ_[p]) ^ h‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (pow_ne_zero h (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  refine ⟨h, ‖c‖ / ‖(p : ℤ_[p]) ^ h‖ ^ 2, fun x y hxy ↦ ?_⟩
  rw [← ofStage_def, derivative_ofStage, eval_ofStage, eval_ofStage,
    AnalyticStage.derivative_apply, map_smul, ContinuousMap.smul_apply]
  -- Write `x = a + pʰ w` and `y - x = d pʰ`.
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨d, hd⟩ :=
    Ideal.mem_span_singleton'.mp ((PadicInt.norm_le_pow_iff_mem_span_pow _ h).mp hxy)
  simp only [PadicInt.discHomeomorph_apply] at hd ⊢
  have hy : y = (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (w + d) := by
    linear_combination -hd
  -- The scalar `d pʰ` acting on `p⁻ʰ v` is `d` acting on `v`.
  have hsmul (v : E) : (d * (p : ℤ_[p]) ^ h) • (((p : 𝕜) ^ h)⁻¹ • v) = d • v := by
    rw [mul_smul, natCast_pow_smul_eq 𝕜, smul_inv_smul₀ hp𝕜]
  rw [← hd, hsmul, hy]
  refine (norm_eval_add_sub_sub_smul_eval_discDerivative_le 𝕜 c a w d).trans_eq ?_
  rw [norm_mul, mul_pow]
  field_simp

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

section NeZero

variable [NeZero (p : K)]

/-- The transpose derivative of a locally analytic distribution: `(d μ)(f) = μ(f')`. -/
noncomputable def derivative :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K where
  toFun μ := ⟨(μ : Module.Dual K (LocallyAnalytic p K K)) ∘ₗ LocallyAnalytic.derivative K,
    mem_iff.mpr fun h ↦ by
      convert (stage h μ ∘L AnalyticStage.derivative K).continuous using 1
      ext c
      simp⟩
  map_add' μ ν := rfl
  map_smul' a μ := rfl

/-- The distribution `d μ` takes the value `μ(f')` on `f`. -/
@[simp]
theorem coe_derivative_apply (μ : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    (derivative μ : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.derivative K f) :=
  (rfl)

/-- The restriction of `d μ` to a stage is the restriction of `μ` composed with the derivative on
that stage. -/
@[simp]
theorem stage_derivative (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stage h (derivative μ) = stage h μ ∘L AnalyticStage.derivative K := by
  ext c
  simp

/-- The derivative multiplies the stage seminorm of level `h` by at most `‖p‖⁻ʰ`. -/
theorem stageSeminorm_derivative_le (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h (derivative μ) ≤ ‖((p : K) ^ h)⁻¹‖ * stageSeminorm h μ := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stage_derivative, mul_comm]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_
    (norm_nonneg _))
  exact (norm_smul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
    opNorm_discDerivative_le_one)

/-- **The Leibniz rule for distributions**: `x (d μ) = μ + d (x μ)`. -/
theorem mulCoord_derivative (μ : LocallyAnalyticDistribution p K) :
    mulCoord (derivative μ) = μ + derivative (mulCoord μ) := by
  refine Subtype.ext <| LinearMap.ext fun f ↦ ?_
  simp [LocallyAnalytic.derivative_mulCoord]

end NeZero

section CharZero

variable [CharZero K]

/-- **The Amice transform of the transpose derivative.** With the convention `(d μ)(f) = μ(f')`,
the Amice transform of `d μ` is `log (1 + T)` times the Amice transform of `μ`. -/
@[simp]
theorem amiceTransform_derivative (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (derivative μ) = PowerSeries.log K * amiceTransform μ := by
  set L := PowerSeries.log K
  set D := PowerSeries.mahlerDerivation K
  -- `∂ log (1 + T) = (1 + T) d/dT log (1 + T) = 1`.
  have hL : D L = 1 := by
    rw [PowerSeries.mahlerDerivation_apply, mul_comm, PowerSeries.derivative_log_mul_one_add_X]
  -- The difference `A_{d ν} - L A_ν` intertwines multiplication by `x` with `∂`.
  have hstep (ν : LocallyAnalyticDistribution p K) :
      D (amiceTransform (derivative ν)) - D (L * amiceTransform ν) =
        amiceTransform (derivative (mulCoord ν)) - L * amiceTransform (mulCoord ν) := by
    rw [← amiceTransform_mulCoord, mulCoord_derivative, map_add, Derivation.leibniz, hL,
      amiceTransform_mulCoord, smul_eq_mul, smul_eq_mul, mul_one]
    ring
  ext n
  induction n generalizing μ with
  | zero =>
    -- The constant coefficients vanish: the derivative kills the constant `1`.
    simp [L, PowerSeries.coeff_mul]
  | succ n ih =>
    have hn := congrArg (PowerSeries.coeff n) (hstep μ)
    simp only [map_sub, D, PowerSeries.coeff_mahlerDerivation, ih μ, ih (mulCoord μ),
      sub_self] at hn
    refine mul_left_cancel₀ (Nat.cast_add_one_ne_zero n : ((n : K) + 1) ≠ 0) ?_
    linear_combination hn

/-- Iterating, the transpose derivative `dᵏ` acts on the Amice transform as multiplication by
`log (1 + T) ^ k`. -/
theorem amiceTransform_iterate_derivative (μ : LocallyAnalyticDistribution p K) (k : ℕ) :
    amiceTransform (derivative^[k] μ) = PowerSeries.log K ^ k * amiceTransform μ := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', amiceTransform_derivative, ih, pow_succ',
      mul_assoc]

/-- The transpose derivative of the unit `1 = δ_0` of the convolution algebra is the derivative at
`0`, `f ↦ f'(0)`; its Amice transform is `log (1 + T)`. -/
theorem amiceTransform_derivative_one :
    amiceTransform (derivative (1 : LocallyAnalyticDistribution p K)) = PowerSeries.log K := by
  rw [amiceTransform_derivative, amiceTransform_one, mul_one]

end CharZero

end LocallyAnalyticDistribution

end TauCeti
