/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.Analysis.MvPolynomial.L1Norm
import TauCeti.Analysis.Normed.Group.Pi
import TauCeti.Analysis.SpecialFunctions.Gaussian.Reproducing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Polynomial vectors in the Fock model

For signs `ε : ι → ℤˣ` and a complex polynomial `P` in variables indexed by `ι`, the function
`v_P(x) = P(ζ(x)) e(x)`, with `ζ` the holomorphic coordinates and `e` the Gaussian, is a vector of
the Fock space `𝓕(ε)`. The map
`P ↦ v_P` is injective, and the Heisenberg operators differentiate polynomial vectors into
polynomial vectors: `t ↦ ϱ(t x) v_P` (`t ∈ ℝ`) is differentiable at `0` in `𝓕(ε)` with derivative
`v_{D_x P}`, where `D_x = ∑ i, (x i • A_i - conj (x i * ε i) • B_i)` and `A_i`, `B_i` are the
raising and lowering operators (`X_i` and `∂_i` for `ε i = 1`, `-∂_i` and `X_i` for `ε i = -1`).

The proof shows both statements together, by induction on `P`. If `u = v_P` lies in `𝓕(ε)`, then
`ϱ(t x) u = ∫ (ϱ(t x) u)(y) • ϱ(y) e dy` (superposition), and `(ϱ(t x) u)(y)` is
`e(y) P(ζ(y) - t ζ(x)) exp (t S(x, y) - t² |x|² / 2)` with `S(x, y) = ∑ i, conj (ζ(x) i) ζ(y) i`.
Its `t`-derivative is bounded by `K exp (k ‖y‖) |e(y)|` for `|t| < 1`, which is integrable, so the
integral may be differentiated under the integral sign in `𝓕(ε)`; evaluating at points identifies
the derivative with `v_{D_x P}`, which therefore lies in `𝓕(ε)`. Taking `x = ζ(eᵢ)` and
`x = ζ(I eᵢ)` gives `v_{Xᵢ P}`.

## Main definitions

* `TauCeti.Fock.raiseOp`, `TauCeti.Fock.lowerOp`, `TauCeti.Fock.heisenbergDeriv`: `A_i`, `B_i` and
  `D_x`.
* `TauCeti.Fock.polyVector`: the linear map `P ↦ v_P`.

## Main results

* `TauCeti.Fock.polyVector_apply`, `TauCeti.Fock.polyVector_injective`: `v_P(x) = P(ζ(x)) e(x)`,
  and `P ↦ v_P` is injective.
* `TauCeti.Fock.hasDerivAt_heisenbergRep_polyVector`: the Heisenberg operators differentiate
  `v_P` into `v_{D_x P}`.
* `TauCeti.Fock.integrable_exp_mul_norm_gaussian`: the exponential bound behind the domination,
  which together with the polynomial growth bound
  `MvPolynomial.norm_eval_le_l1Norm_mul_max_one_pow` controls the integrand.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Weil/Fock/Basic.lean` (`New.Fock.raiseOp`, `New.Fock.lowerOp`,
`New.Fock.heisenbergDeriv`, `New.Fock.exists_norm_eval_le_exp` (here the polynomial growth bound
`MvPolynomial.norm_eval_le_l1Norm_mul_max_one_pow`),
`New.Fock.integrable_exp_mul_realVac`, `New.Fock.exists_hasDerivAt_realHeisenbergOp`,
`New.Fock.polyVector`, `New.Fock.polyVector_injective`, `New.Fock.hasDerivAt_realHeisenbergOp`).
The source differentiates in a complex parameter with Cauchy estimates; here the derivative is
bounded directly and Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is used.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform,
  part I*, Comm. Pure Appl. Math. 14 (1961), 187–214.
* G. B. Folland, *Harmonic analysis in phase space*, Ann. of Math. Stud. 122 (1989), Chapter 1.
-/

public noncomputable section

open MeasureTheory Complex Finset MvPolynomial
open scoped ComplexConjugate

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### Raising and lowering operators -/

variable (ε) in
/-- The raising operator `A_i` on polynomials: multiplication by `X i` if `ε i = 1`, and `-∂_i`
if `ε i = -1`. -/
def raiseOp (i : ι) : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  if ε i = 1 then LinearMap.mulLeft ℂ (X i) else -(pderiv i).toLinearMap

variable (ε) in
/-- The lowering operator `B_i` on polynomials: `∂_i` if `ε i = 1`, and multiplication by `X i`
if `ε i = -1`. -/
def lowerOp (i : ι) : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  if ε i = 1 then (pderiv i).toLinearMap else LinearMap.mulLeft ℂ (X i)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem raiseOp_apply_of_eq_one {i : ι} (h : ε i = 1) (P : MvPolynomial ι ℂ) :
    raiseOp ε i P = X i * P := by
  simp [raiseOp, h]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem raiseOp_apply_of_eq_neg_one {i : ι} (h : ε i = -1) (P : MvPolynomial ι ℂ) :
    raiseOp ε i P = -pderiv i P := by
  simp [raiseOp, h]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem lowerOp_apply_of_eq_one {i : ι} (h : ε i = 1) (P : MvPolynomial ι ℂ) :
    lowerOp ε i P = pderiv i P := by
  simp [lowerOp, h]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem lowerOp_apply_of_eq_neg_one {i : ι} (h : ε i = -1) (P : MvPolynomial ι ℂ) :
    lowerOp ε i P = X i * P := by
  simp [lowerOp, h]

variable (ε) in
/-- The derivative `D_x = ∑ i, (x i • A_i - conj (x i * ε i) • B_i)` of the Heisenberg operators
along `x` on polynomial vectors (`TauCeti.Fock.hasDerivAt_heisenbergRep_polyVector`). -/
def heisenbergDeriv (x : ι → ℂ) : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  ∑ i, (x i • raiseOp ε i - conj (x i * ((ε i : ℤ) : ℂ)) • lowerOp ε i)

omit [DecidableEq ι] in
theorem heisenbergDeriv_apply (x : ι → ℂ) (P : MvPolynomial ι ℂ) :
    heisenbergDeriv ε x P =
      ∑ i, (x i • raiseOp ε i P - conj (x i * ((ε i : ℤ) : ℂ)) • lowerOp ε i P) := by
  simp [heisenbergDeriv]

omit [DecidableEq ι] in
/-- The value of `D_v P` at `l`: `(∑ i, conj (ζ(v) i) * l i) P(l) - ∑ i, ζ(v) i (∂_i P)(l)`. -/
theorem eval_heisenbergDeriv (v l : ι → ℂ) (P : MvPolynomial ι ℂ) :
    eval l (heisenbergDeriv ε v P) =
      (∑ i, conj (holomorphicCoord ε v i) * l i) * eval l P -
        ∑ i, holomorphicCoord ε v i * eval l (pderiv i P) := by
  simp only [heisenbergDeriv, LinearMap.sum_apply, map_sum, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases Int.units_eq_one_or (ε i) with h | h <;>
    simp [h] <;> ring

/-! ### Growth estimates -/

omit [DecidableEq ι] in
theorem norm_gaussian (x : ι → ℂ) : ‖gaussian ι x‖ = Real.exp (-(∑ i, ‖x i‖ ^ 2) / 2) := by
  rw [gaussian_apply, Complex.norm_exp]
  congr 1
  simp [← ofReal_pow, -ofReal_sum]

omit [DecidableEq ι] in
/-- For every real `C`, the function `exp (C ‖x‖) |e(x)|` is integrable. -/
theorem integrable_exp_mul_norm_gaussian (C : ℝ) :
    Integrable (fun x : ι → ℂ ↦ Real.exp (C * ‖x‖) * ‖gaussian ι x‖) (measure ι) := by
  -- It is at most `exp (C ^ 2)` times the wider Gaussian `exp (-|x|² / 4)`.
  have h_int := (integrable_cexp_neg_sum_mul_norm_sq_add (ι := ι) (a := fun _ ↦ 1 / 4)
    (fun _ ↦ by norm_num) 0 0).norm.const_mul (Real.exp (C ^ 2))
  rw [measure_def]
  refine (h_int.smul_measure ENNReal.ofReal_ne_top).mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have h_le : C * ‖x‖ - (∑ i, ‖x i‖ ^ 2) / 2 ≤ C ^ 2 - (∑ i, ‖x i‖ ^ 2) / 4 := by
    nlinarith [Pi.norm_pow_le_sum_norm_pow x two_ne_zero, sq_nonneg (‖x‖ - 2 * C)]
  have h_norm : ‖cexp (-∑ i, (1 / 4 : ℂ) * (‖x i‖ : ℂ) ^ 2 + ∑ i, (0 : ι → ℂ) i * x i +
      ∑ i, (0 : ι → ℂ) i * conj (x i))‖ = Real.exp (-(∑ i, ‖x i‖ ^ 2) / 4) := by
    rw [Complex.norm_exp]
    congr 1
    simp [← mul_sum, ← ofReal_pow, -ofReal_sum, div_eq_inv_mul]
  rw [Real.norm_of_nonneg (by positivity), norm_gaussian, ← Real.exp_add, h_norm, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

omit [Fintype ι] [DecidableEq ι] in
theorem holomorphicCoord_real_smul (t : ℝ) (x : ι → ℂ) :
    holomorphicCoord ε (t • x) = (t : ℂ) • holomorphicCoord ε x := by
  ext i
  simp only [holomorphicCoord_apply, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

omit [DecidableEq ι] in
@[simp]
theorem norm_holomorphicCoord (x : ι → ℂ) : ‖holomorphicCoord ε x‖ = ‖x‖ := by
  have h (i : ι) : ‖holomorphicCoord ε x i‖₊ = ‖x i‖₊ := NNReal.eq (norm_holomorphicCoord_apply x i)
  simp [Pi.norm_def, h]

/-! ### The Heisenberg operators on polynomial vectors -/

section ExpBounded

omit [DecidableEq ι]

/-- A family `f t y` (`|t| < 1`, `y : ι → ℂ`) is bounded by `K exp (k ‖y‖)`. -/
private def ExpBounded (f : ℝ → (ι → ℂ) → ℂ) : Prop :=
  ∃ K k : ℝ, 0 ≤ K ∧ 0 ≤ k ∧ ∀ t : ℝ, |t| < 1 → ∀ y, ‖f t y‖ ≤ K * Real.exp (k * ‖y‖)

private theorem ExpBounded.add {f g : ℝ → (ι → ℂ) → ℂ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun t y ↦ f t y + g t y) := by
  obtain ⟨K₁, k₁, hK₁, hk₁, h₁⟩ := hf
  obtain ⟨K₂, k₂, hK₂, -, h₂⟩ := hg
  refine ⟨K₁ + K₂, max k₁ k₂, by positivity, le_max_of_le_left hk₁, fun t ht y ↦ ?_⟩
  have e₁ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left k₁ k₂) (norm_nonneg y))
  have e₂ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right k₁ k₂) (norm_nonneg y))
  calc ‖f t y + g t y‖ ≤ K₁ * Real.exp (k₁ * ‖y‖) + K₂ * Real.exp (k₂ * ‖y‖) :=
        (norm_add_le _ _).trans (add_le_add (h₁ t ht y) (h₂ t ht y))
    _ ≤ (K₁ + K₂) * Real.exp (max k₁ k₂ * ‖y‖) := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left e₁ hK₁) (mul_le_mul_of_nonneg_left e₂ hK₂)

private theorem ExpBounded.mul {f g : ℝ → (ι → ℂ) → ℂ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun t y ↦ f t y * g t y) := by
  obtain ⟨K₁, k₁, hK₁, hk₁, h₁⟩ := hf
  obtain ⟨K₂, k₂, hK₂, hk₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, k₁ + k₂, by positivity, by positivity, fun t ht y ↦ ?_⟩
  rw [norm_mul, add_mul, Real.exp_add, mul_mul_mul_comm]
  exact mul_le_mul (h₁ t ht y) (h₂ t ht y) (norm_nonneg _) (by positivity)

/-- A polynomial evaluated on the line `ζ(y) - t ζ(v)` is exponentially bounded. -/
private theorem ExpBounded.eval (P : MvPolynomial ι ℂ) (v : ι → ℂ) :
    ExpBounded fun t y ↦ eval (holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v) P := by
  have hP := P.l1Norm_nonneg
  refine ⟨P.l1Norm * Real.exp (P.totalDegree * ‖v‖), P.totalDegree, by positivity, by positivity,
    fun t ht y ↦ ?_⟩
  have h_norm : ‖holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v‖ ≤ ‖y‖ + ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_holomorphicCoord, norm_smul, norm_holomorphicCoord, Complex.norm_real,
      Real.norm_eq_abs]
    exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) ht.le)
  have h_max : max 1 ‖holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v‖ ≤
      Real.exp (‖y‖ + ‖v‖) :=
    max_le (Real.one_le_exp (by positivity))
      (h_norm.trans (by linarith [Real.add_one_le_exp (‖y‖ + ‖v‖)]))
  refine (P.norm_eval_le_l1Norm_mul_max_one_pow _).trans ?_
  calc P.l1Norm * max 1 ‖holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v‖ ^ P.totalDegree
      ≤ P.l1Norm * Real.exp (‖y‖ + ‖v‖) ^ P.totalDegree := by gcongr
    _ = P.l1Norm * Real.exp (P.totalDegree * ‖v‖) * Real.exp (P.totalDegree * ‖y‖) := by
        rw [← Real.exp_natCast_mul, mul_assoc, ← Real.exp_add, mul_add, add_comm]

omit [DecidableEq ι] in
private theorem norm_phase_le (v y : ι → ℂ) :
    ‖∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i‖ ≤
      Fintype.card ι * ‖v‖ * ‖y‖ :=
  calc ‖∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i‖
      ≤ ∑ _i : ι, ‖v‖ * ‖y‖ := (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ by
        rw [norm_mul, RCLike.norm_conj, norm_holomorphicCoord_apply, norm_holomorphicCoord_apply]
        exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm y i) (norm_nonneg _)
          (norm_nonneg _))
    _ = Fintype.card ι * ‖v‖ * ‖y‖ := by simp [mul_assoc]

/-- The phase `S(v, y) = ∑ i, conj (ζ(v) i) * ζ(y) i` is exponentially bounded. -/
private theorem ExpBounded.phase (v : ι → ℂ) :
    ExpBounded (ι := ι) fun _ y ↦ ∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i := by
  refine ⟨Fintype.card ι * ‖v‖, 1, by positivity, zero_le_one, fun _ _ y ↦ ?_⟩
  refine (norm_phase_le v y).trans ?_
  gcongr
  rw [one_mul]
  linarith [Real.add_one_le_exp ‖y‖]

variable (ε) in
/-- The Gaussian factor `exp (t S(v, y) - t² |v|² / 2)` of a Heisenberg translate of a polynomial
vector, with the phase `S(v, y) = ∑ i, conj (ζ(v) i) * ζ(y) i`. -/
private def phaseFactor (v : ι → ℂ) (t : ℝ) (y : ι → ℂ) : ℂ :=
  cexp (t * ∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i -
    t ^ 2 * (∑ i, (‖v i‖ : ℂ) ^ 2) / 2)

/-- The Gaussian factor is exponentially bounded. -/
private theorem expBounded_phaseFactor (v : ι → ℂ) : ExpBounded (phaseFactor ε v) := by
  refine ⟨1, Fintype.card ι * ‖v‖, zero_le_one, by positivity, fun t ht y ↦ ?_⟩
  rw [phaseFactor, Complex.norm_exp, one_mul, Real.exp_le_exp]
  have h_re : (t ^ 2 * (∑ i, (‖v i‖ : ℂ) ^ 2) / 2 : ℂ).re = t ^ 2 * (∑ i, ‖v i‖ ^ 2) / 2 := by
    simp [← ofReal_pow, -ofReal_sum]
  rw [sub_re, h_re]
  have h₁ := (re_le_norm ((t : ℂ) * ∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h₁
  have h₂ := norm_phase_le (ε := ε) v y
  nlinarith [abs_nonneg t, sq_nonneg t, sum_nonneg fun i (_ : i ∈ univ) ↦ sq_nonneg ‖v i‖,
    norm_nonneg (∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i)]

private theorem ExpBounded.real_mul (c : ℂ) : ExpBounded (ι := ι) fun t _ ↦ (t : ℂ) * c := by
  refine ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun t ht _ ↦ ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, zero_mul, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.le

variable (ε) in
/-- The `t`-derivative of `P(ζ(y) - t ζ(v))` times the Gaussian factor `phaseFactor ε v t y`. -/
private def derivIntegrand (P : MvPolynomial ι ℂ) (v : ι → ℂ) (t : ℝ) (y : ι → ℂ) : ℂ :=
  eval (holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v)
      (∑ i, C (-holomorphicCoord ε v i) * pderiv i P) * phaseFactor ε v t y +
    eval (holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v) P *
      ((∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i -
        t * ∑ i, (‖v i‖ : ℂ) ^ 2) * phaseFactor ε v t y)

/-- The derivative of `hasDerivAt_eval_mul_phaseFactor` is exponentially bounded. -/
private theorem expBounded_derivIntegrand (P : MvPolynomial ι ℂ) (v : ι → ℂ) :
    ExpBounded (derivIntegrand ε P v) := by
  refine ((ExpBounded.eval _ v).mul (expBounded_phaseFactor v)).add
    ((ExpBounded.eval P v).mul (ExpBounded.mul ?_ (expBounded_phaseFactor v)))
  simpa [sub_eq_add_neg] using (ExpBounded.phase (ε := ε) v).add
    ((ExpBounded.real_mul (-∑ i, (‖v i‖ : ℂ) ^ 2)))

/-- The derivative along `t ↦ ζ(y) - t ζ(v)` of `P` times the Gaussian factor. -/
private theorem hasDerivAt_eval_mul_phaseFactor (P : MvPolynomial ι ℂ) (v y : ι → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ eval (holomorphicCoord ε y - (s : ℂ) • holomorphicCoord ε v) P *
      phaseFactor ε v s y) (derivIntegrand ε P v t y) t := by
  simp only [derivIntegrand, phaseFactor]
  set S := ∑ i, conj (holomorphicCoord ε v i) * holomorphicCoord ε y i
  set N := ∑ i, (‖v i‖ : ℂ) ^ 2
  have h_line : HasDerivAt (fun s : ℝ ↦ holomorphicCoord ε y - (s : ℂ) • holomorphicCoord ε v)
      (-holomorphicCoord ε v) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.smul_const (holomorphicCoord ε v)).const_sub
      (holomorphicCoord ε y)
  have h_poly := ((P.hasFDerivAt_eval (holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v)
    ).restrictScalars ℝ).comp_hasDerivAt t h_line
  have h_inner : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * S - (s : ℂ) ^ 2 * N / 2) (S - t * N) t := by
    have h : HasDerivAt (fun w : ℂ ↦ w * S - w ^ 2 * N / 2) (S - t * N) (t : ℂ) :=
      (((hasDerivAt_id (t : ℂ)).mul_const S).sub
        (((hasDerivAt_pow 2 (t : ℂ)).mul_const N).div_const 2)).congr_deriv (by simp; ring)
    exact h.comp_ofReal
  convert h_poly.mul h_inner.cexp using 1
  · rfl
  simp only [ContinuousLinearMap.coe_restrictScalars', sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Pi.neg_apply, smul_eq_mul, Function.comp_apply,
    map_sum, eval_mul, eval_C, sum_mul]
  ring_nf
  congr 1
  exact sum_congr rfl fun i _ ↦ by ring

end ExpBounded

/-- The value of a Heisenberg translate of a polynomial vector `u = v_P` at `y`:
`e(y) P(ζ(y) - t ζ(v)) exp (t S(v, y) - t² |v|² / 2)`. -/
private theorem heisenbergRep_real_smul_apply {u : FockSpace ε} {P : MvPolynomial ι ℂ}
    (hu : ∀ x, u x = eval (holomorphicCoord ε x) P * gaussian ι x) (v : ι → ℂ) (t : ℝ)
    (y : ι → ℂ) :
    ReproducingModel.heisenbergRep (t • v) u y = gaussian ι y *
      (eval (holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v) P * phaseFactor ε v t y) := by
  have hk := heisenbergDatum_mul_gaussian (ε := ε) y (t • v)
  have h_exp : gaussian ι (t • v) *
      cexp (∑ i, conj (holomorphicCoord ε (t • v) i) * holomorphicCoord ε y i) =
      phaseFactor ε v t y := by
    simp only [phaseFactor, gaussian_apply, ← Complex.exp_add, holomorphicCoord_real_smul,
      Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, norm_smul, Real.norm_eq_abs, ofReal_mul,
      mul_pow, ← mul_sum, mul_assoc]
    congr 1
    rw [← ofReal_pow, sq_abs, ofReal_pow]
    ring
  rw [ReproducingModel.heisenbergRep_apply, hu, holomorphicCoord_sub, holomorphicCoord_real_smul,
    ← h_exp]
  linear_combination (eval (holomorphicCoord ε y - (t : ℂ) • holomorphicCoord ε v) P) * hk

/-- The pointwise derivative of the Heisenberg translates of `u = v_P`. -/
private theorem hasDerivAt_heisenbergRep_apply {u : FockSpace ε} {P : MvPolynomial ι ℂ}
    (hu : ∀ x, u x = eval (holomorphicCoord ε x) P * gaussian ι x) (v y : ι → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ReproducingModel.heisenbergRep (s • v) u y)
      (gaussian ι y * derivIntegrand ε P v t y) t := by
  simp_rw [heisenbergRep_real_smul_apply hu]
  exact (hasDerivAt_eval_mul_phaseFactor P v y t).const_mul _

/-- The candidate derivative of `t ↦ ϱ(t v) u` at `0` is a continuous superposition of the
translates of the vacuum. -/
private theorem continuous_derivIntegrand_smul (P : MvPolynomial ι ℂ) (v : ι → ℂ) :
    Continuous fun y ↦ (gaussian ι y * derivIntegrand ε P v 0 y) •
      ReproducingModel.heisenbergRep y (ReproducingModel.vacuum : FockSpace ε) := by
  refine Continuous.smul (f := fun y ↦ gaussian ι y * derivIntegrand ε P v 0 y) ?_
    (HeisenbergDatum.Representation.continuous_apply_apply _ continuous_id continuous_const)
  have := MvPolynomial.continuous_eval (∑ i, C (-holomorphicCoord ε v i) * pderiv i P)
  have := MvPolynomial.continuous_eval P
  simp only [derivIntegrand, phaseFactor]
  fun_prop

/-- **The derivative of the Heisenberg operators on a polynomial vector.** If `u = v_P`, then
`t ↦ ϱ(t v) u` is differentiable at `0` in the Fock space, with derivative the function
`v_{D_v P}`. -/
private theorem exists_hasDerivAt_heisenbergRep {u : FockSpace ε} {P : MvPolynomial ι ℂ}
    (hu : ∀ x, u x = eval (holomorphicCoord ε x) P * gaussian ι x) (v : ι → ℂ) :
    ∃ D : FockSpace ε, HasDerivAt (fun t : ℝ ↦ ReproducingModel.heisenbergRep (t • v) u) D 0 ∧
      ∀ x, D x = eval (holomorphicCoord ε x) (heisenbergDeriv ε v P) * gaussian ι x := by
  set ϱ := ReproducingModel.heisenbergRep (β := heisenbergDatum ε) (μ := measure ι)
    (e := gaussian ι)
  set vac : FockSpace ε := ReproducingModel.vacuum
  -- The curve is the superposition of the translates of the vacuum, weighted by its values.
  have h_curve (t : ℝ) : ϱ (t • v) u = ∫ y, ϱ (t • v) u y • ϱ y vac ∂measure ι := by
    conv_lhs => rw [← ReproducingModel.integrated_vacuum (ϱ (t • v) u)]
    exact HeisenbergDatum.Representation.integrated_apply _ _ _
  obtain ⟨K, k, -, -, h_bound⟩ := expBounded_derivIntegrand (ε := ε) P v
  have h_cont (t : ℝ) : Continuous fun y ↦ ϱ (t • v) u y • ϱ y vac :=
    (ReproducingModel.continuous _).smul
      (HeisenbergDatum.Representation.continuous_apply_apply ϱ continuous_id continuous_const)
  have h_deriv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := measure ι)
    (F := fun t y ↦ ϱ (t • v) u y • ϱ y vac) (x₀ := (0 : ℝ))
    (F' := fun t y ↦ (gaussian ι y * derivIntegrand ε P v t y) • ϱ y vac)
    (bound := fun y ↦ K * (Real.exp (k * ‖y‖) * ‖gaussian ι y‖) * ‖vac‖)
    (Metric.ball_mem_nhds 0 one_pos) (.of_forall fun t ↦ (h_cont t).aestronglyMeasurable)
    (HeisenbergDatum.Representation.integrable_smul_apply ϱ _ vac)
    (continuous_derivIntegrand_smul P v).aestronglyMeasurable (.of_forall fun y t ht ↦ ?_)
    (((integrable_exp_mul_norm_gaussian k).const_mul K).mul_const _)
    (.of_forall fun y t _ ↦ (hasDerivAt_heisenbergRep_apply hu v y t).smul_const (ϱ y vac))
  · set D := ∫ y, (gaussian ι y * derivIntegrand ε P v 0 y) • ϱ y vac ∂measure ι
    have hD : HasDerivAt (fun t : ℝ ↦ ϱ (t • v) u) D 0 := by
      simpa only [← h_curve] using h_deriv.2
    refine ⟨D, hD, fun x ↦ ?_⟩
    have h₁ : HasDerivAt (fun s : ℝ ↦ ϱ (s • v) u x) (D x) 0 := by
      simpa [Function.comp_def] using ((ReproducingModel.evalCLM (β := heisenbergDatum ε)
        (μ := measure ι) (e := gaussian ι) x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) hD
    rw [← (hasDerivAt_heisenbergRep_apply hu v x 0).unique h₁, eval_heisenbergDeriv]
    simp only [derivIntegrand, phaseFactor, ofReal_zero, zero_smul, sub_zero, zero_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_self, Complex.exp_zero,
      mul_one, eval_sum, eval_mul, eval_C, neg_mul, sum_neg_distrib]
    ring
  · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    rw [norm_smul, HeisenbergDatum.Representation.norm_apply, norm_mul]
    calc ‖gaussian ι y‖ * ‖derivIntegrand ε P v t y‖ * ‖vac‖
        ≤ ‖gaussian ι y‖ * (K * Real.exp (k * ‖y‖)) * ‖vac‖ := by gcongr; exact h_bound t ht y
      _ = K * (Real.exp (k * ‖y‖) * ‖gaussian ι y‖) * ‖vac‖ := by ring

/-- Every polynomial `P` gives a vector `v_P(x) = P(ζ(x)) e(x)` of the Fock space: the constants
are multiples of the vacuum, and `v_{X_i P}` is a combination of derivatives of Heisenberg
translates of `v_P`. -/
private theorem exists_polyVector (P : MvPolynomial ι ℂ) :
    ∃ u : FockSpace ε, ∀ x, u x = eval (holomorphicCoord ε x) P * gaussian ι x := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨c • ReproducingModel.vacuum, fun x ↦ by simp⟩
  | add P Q hP hQ =>
    obtain ⟨u, hu⟩ := hP
    obtain ⟨w, hw⟩ := hQ
    exact ⟨u + w, fun x ↦ by simp [hu, hw, add_mul]⟩
  | mul_X P i hP =>
    obtain ⟨u, hu⟩ := hP
    -- The derivatives along `ζ(c eᵢ)` are the vectors of `conj c Xᵢ P - c ∂ᵢ P`; take `c = 1, I`.
    obtain ⟨D₁, -, hD₁⟩ := exists_hasDerivAt_heisenbergRep hu (holomorphicCoord ε (Pi.single i 1))
    obtain ⟨D₂, -, hD₂⟩ := exists_hasDerivAt_heisenbergRep hu (holomorphicCoord ε (Pi.single i I))
    refine ⟨(1 / 2 : ℂ) • D₁ + (I / 2) • D₂, fun x ↦ ?_⟩
    simp only [ReproducingModel.add_apply, ReproducingModel.smul_apply, hD₁, hD₂,
      eval_heisenbergDeriv, holomorphicCoord_holomorphicCoord, Pi.single_apply, apply_ite,
      map_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, eval_mul, eval_X, map_one,
      Complex.conj_I]
    linear_combination (-(1 / 2) * eval (holomorphicCoord ε x) P * holomorphicCoord ε x i *
      gaussian ι x - (1 / 2) * eval (holomorphicCoord ε x) (pderiv i P) * gaussian ι x) * I_sq

variable (ε) in
/-- The *polynomial vectors*: the linear map `P ↦ v_P` to the Fock space, with
`v_P(x) = P(ζ(x)) e(x)` (`TauCeti.Fock.polyVector_apply`). -/
def polyVector : MvPolynomial ι ℂ →ₗ[ℂ] FockSpace ε where
  toFun P := (exists_polyVector P).choose
  map_add' P Q := ReproducingModel.ext fun x ↦ by
    rw [ReproducingModel.add_apply, (exists_polyVector (P + Q)).choose_spec,
      (exists_polyVector P).choose_spec, (exists_polyVector Q).choose_spec, map_add, add_mul]
  map_smul' c P := ReproducingModel.ext fun x ↦ by
    rw [ReproducingModel.smul_apply, (exists_polyVector (c • P)).choose_spec,
      (exists_polyVector P).choose_spec, RingHom.id_apply, smul_eval, mul_assoc]

/-- `v_P(x) = P(ζ(x)) e(x)`. -/
@[simp]
theorem polyVector_apply (P : MvPolynomial ι ℂ) (x : ι → ℂ) :
    polyVector ε P x = eval (holomorphicCoord ε x) P * gaussian ι x :=
  (exists_polyVector P).choose_spec x

@[simp]
theorem polyVector_one : polyVector ε 1 = ReproducingModel.vacuum :=
  ReproducingModel.ext fun x ↦ by simp

/-- `P ↦ v_P` is injective. -/
theorem polyVector_injective : Function.Injective (polyVector ε) := by
  refine fun P Q h ↦ MvPolynomial.funext fun x ↦ ?_
  have h_ne : gaussian ι (holomorphicCoord ε x) ≠ 0 := by
    rw [gaussian_apply]; exact Complex.exp_ne_zero _
  have := congr($h (holomorphicCoord ε x))
  simpa [polyVector_apply, h_ne] using this

/-- **Heisenberg derivatives of polynomial vectors**: `t ↦ ϱ(t x) v_P` (`t ∈ ℝ`) is
differentiable at `0` in the Fock space, with derivative `v_{D_x P}`. -/
theorem hasDerivAt_heisenbergRep_polyVector (v : ι → ℂ) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t : ℝ ↦ ReproducingModel.heisenbergRep (t • v) (polyVector ε P))
      (polyVector ε (heisenbergDeriv ε v P)) 0 := by
  obtain ⟨D, hD, hDx⟩ := exists_hasDerivAt_heisenbergRep (polyVector_apply P) v
  convert hD
  exact ReproducingModel.ext fun x ↦ by rw [polyVector_apply, hDx]

end TauCeti.Fock
