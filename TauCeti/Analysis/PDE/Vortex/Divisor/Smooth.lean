/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Family
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction
import TauCeti.Analysis.PDE.Vortex.Reduced.HigherSmoothness
import TauCeti.Analysis.Polynomial.AtInfinity
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Smooth dependence of the plane vortices on the divisor

For `c ∈ ℂᵐ` let `P_c = TauCeti.Polynomial.monicOfCoeff c`, the monic polynomial of degree `m`
with lower coefficients `c`; the coefficients are symmetric coordinates on the divisor space
`Sym^m ℂ`, collisions of zeros included. Taubes's plane vortex with zero divisor `P_c` is the field
`TauCeti.Vortex.polynomialVortex P_c` of the amplitude `u₀ + w_c` and the section `P_c`, where
`u₀ = -log (1 + ‖P_c‖²) / 2` is the background amplitude and `w_c` the reduced solution. This file
proves that its `L∞` class `TauCeti.Vortex.polynomialVortexLp P_c` is a smooth function of `c`
(`TauCeti.Vortex.contDiff_polynomialVortexLp_monicOfCoeff`), and so `C^n` along every family of
monic polynomials of degree `m` with `C^n` coefficients
(`TauCeti.Vortex.contDiff_polynomialVortexLp`). Composed with the smoothness of the orthogonal
kernel projections and right inverses of the realization `L_P : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` along smooth
families of coefficients
(`TauCeti.Vortex.contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator`), this makes the
projection of `H¹(ℂ)⁴` onto the kernel of `L_P` along its `L²`-orthogonal complement, and the
right inverse of `L_P` with values in that complement, `C^n` along such families for `m ≥ 1`, in
operator norm; for `P = P_c` they are smooth functions of `c`:

* `TauCeti.Vortex.contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp`,
* `TauCeti.Vortex.contDiff_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp`.

They are therefore smooth over every compact window of divisors, including its collision locus;
their continuity is `TauCeti.Analysis.PDE.Vortex.Divisor.Family`.

**The proof.** Fix `c₀`, put `P₀ = P_{c₀}` and `a = √(1 + ‖P₀‖²)`. The vortex of `P_c` is read
off six bounded continuous parts

`x = (a⁻¹, P_c a⁻¹, P_c' a⁻¹, w_c, ∂₁ w_c, ∂₂ w_c)`.

With `N = ‖x 0‖² + ‖x 1‖² = (1 + ‖P_c‖²) a⁻²`, the derivative `Du₀(v) = -Re (v P_c' conj P_c) /
(1 + ‖P_c‖²)` and the background section `exp (u₀) P_c = P_c / √(1 + ‖P_c‖²)` are
`-Re (v x 2 conj (x 1)) / N` and `x 1 / √N`, so the vortex is `G ∘ x` for one map `G`, smooth where
`N > 0`. Each part is a smooth function of `c` with values in the bounded continuous functions.
The first three are affine in the coefficients of `P_c`, with the fixed bounded functions
`z ^ k / a` for `k ≤ m` as coefficients, since `‖z‖ ^ k ≤ C (1 + ‖P₀ z‖)`. The last three are
images of the reduced solution, smooth in `c` in every Sobolev space
(`TauCeti.Vortex.contDiff_ofRealSobolevFunction_reducedSolution`), under the derivatives
`H³(ℂ) → H²(ℂ)` and the Sobolev embedding of `H²(ℂ)` into bounded continuous functions
(`BesselPotentialSpace.toZeroAtInfty`), both continuous linear.

At `c = c₀` the parts satisfy `N = 1` everywhere, so the parts within `1 / 8` of them, in the sup
norm, take values in a compact set on which `N ≥ 1 / 2`. On that set `G` is uniformly smooth, so
the superposition operator `f ↦ G ∘ f` on bounded continuous functions is smooth at the parts of
`c₀` (`BoundedContinuousFunction.contDiffAt_of_forall_apply_eq`). Composing with the parts and the
inclusion of bounded continuous functions into `L∞` (`BoundedContinuousFunction.toLpTop`) gives the
`L∞` class of the vortex near `c₀`, since the Sobolev parts agree with `w_c` and its derivatives
almost everywhere.

## Main results

* `TauCeti.Vortex.contDiff_polynomialVortexLp_monicOfCoeff`: the `L∞` class of the vortex of
  `P_c` is smooth in `c`.
* `TauCeti.Vortex.contDiff_polynomialVortexLp`: the same along families of monic polynomials of a
  fixed degree with `C^n` coefficients.
* `TauCeti.Vortex.contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp`,
  `TauCeti.Vortex.contDiff_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp`:
  the orthogonal kernel projections and right inverses at the vortices of such a family are `C^n`
  in the parameter.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* J. Appell and P. P. Zabrejko, *Nonlinear Superposition Operators*, Cambridge Tracts in
  Mathematics **95**, Cambridge University Press, 1990.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Metric Set Topology TopologicalSpace Module
  BesselPotentialSpace BoundedContinuousFunction TauCeti.Polynomial
open scoped ContDiff ENNReal BesselPotentialSpace ComplexConjugate RealInnerProductSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

namespace TauCeti.Vortex

/-! ### The vortex field as a function of six parts -/

/-- The squared length `‖x 0‖² + ‖x 1‖²` of the first two parts. -/
private def partsNormSq (x : Fin 6 → ℂ) : ℝ :=
  ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2

/-- The field read off six parts `x = (a⁻¹, P a⁻¹, P' a⁻¹, w, ∂₁ w, ∂₂ w)`: with
`N = ‖x 0‖² + ‖x 1‖² = (1 + ‖P‖²) a⁻²` it is the plane-vortex field of the amplitude
`u₀ + w` and the section `P` (`fieldOfParts_eq`). -/
private def fieldOfParts (x : Fin 6 → ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[-(conj (x 1) * x 2).im / partsNormSq x - (x 5).re,
    -(conj (x 1) * x 2).re / partsNormSq x + (x 4).re,
    Real.exp (x 3).re * (x 1).re / (2 * √(partsNormSq x)),
    Real.exp (x 3).re * (x 1).im / (2 * √(partsNormSq x))]

private theorem contDiff_partsNormSq : ContDiff ℝ ∞ partsNormSq :=
  ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ : Fin 6 ↦ ℂ) 0)).add
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ : Fin 6 ↦ ℂ) 1))

/-- The field is smooth in its parts where `‖x 0‖² + ‖x 1‖² > 0`. -/
private theorem contDiffAt_fieldOfParts {x : Fin 6 → ℂ} (hx : 0 < partsNormSq x) :
    ContDiffAt ℝ ∞ fieldOfParts x := by
  have hN := contDiff_partsNormSq.contDiffAt (x := x)
  have hc (j : Fin 6) : ContDiffAt ℝ ∞ (fun x : Fin 6 → ℂ ↦ x j) x :=
    (contDiff_apply ℝ (fun _ : Fin 6 ↦ ℂ) j).contDiffAt
  have hre (j : Fin 6) : ContDiffAt ℝ ∞ (fun x : Fin 6 → ℂ ↦ (x j).re) x :=
    reCLM.contDiff.contDiffAt.comp x (hc j)
  have him (j : Fin 6) : ContDiffAt ℝ ∞ (fun x : Fin 6 → ℂ ↦ (x j).im) x :=
    imCLM.contDiff.contDiffAt.comp x (hc j)
  have hprod : ContDiffAt ℝ ∞ (fun x : Fin 6 → ℂ ↦ conj (x 1) * x 2) x :=
    ((conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp x
      (hc 1)).mul (hc 2)
  have hsqrt : ContDiffAt ℝ ∞ (fun x ↦ 2 * √(partsNormSq x)) x :=
    contDiffAt_const.mul (hN.sqrt hx.ne')
  have hsqrt0 : 2 * √(partsNormSq x) ≠ 0 := by positivity
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · exact ((imCLM.contDiff.contDiffAt.comp x hprod).neg.div hN hx.ne').sub (hre 5)
  · exact ((reCLM.contDiff.contDiffAt.comp x hprod).neg.div hN hx.ne').add (hre 4)
  · exact (((hre 3).exp).mul (hre 1)).div hsqrt hsqrt0
  · exact (((hre 3).exp).mul (him 1)).div hsqrt hsqrt0

/-- **The field of the parts of a vortex.** For `a > 0`, the parts
`(a⁻¹, P a⁻¹, P' a⁻¹, w, ∂₁ w, ∂₂ w)` give the field of the amplitude `u₀ + w`, with `u₀` the
background amplitude of `P`, and the section `P`. -/
private theorem fieldOfParts_eq (P : _root_.Polynomial ℂ) {w : ℂ → ℝ} {z : ℂ}
    (hw : DifferentiableAt ℝ w z) {a : ℝ} (ha : 0 < a) {x : Fin 6 → ℂ}
    (h0 : x 0 = (a⁻¹ : ℝ)) (h1 : x 1 = P.eval z * (a⁻¹ : ℝ))
    (h2 : x 2 = P.derivative.eval z * (a⁻¹ : ℝ)) (h3 : (x 3).re = w z)
    (h4 : (x 4).re = fderiv ℝ w z 1) (h5 : (x 5).re = fderiv ℝ w z I) :
    fieldOfParts x = amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval z := by
  have hu₀ : DifferentiableAt ℝ (backgroundAmplitude P.eval) z :=
    ((contDiff_backgroundAmplitude ((P.differentiable.contDiff (n := 1)).restrict_scalars ℝ)
      ).differentiable one_ne_zero) z
  have hD (v : ℂ) : fderiv ℝ (fun z ↦ backgroundAmplitude P.eval z + w z) z v =
      -((1 + ‖P.eval z‖ ^ 2)⁻¹ * (conj (P.eval z) * (v * P.derivative.eval z)).re) +
        fderiv ℝ w z v := by
    rw [fderiv_fun_add hu₀ hw, add_apply,
      fderiv_backgroundAmplitude_apply (P.differentiable z), _root_.Polynomial.deriv,
      Complex.inner]
    ring_nf
  have hN : partsNormSq x = (1 + ‖P.eval z‖ ^ 2) * (a⁻¹) ^ 2 := by
    rw [partsNormSq, h0, h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have hpos : 0 < 1 + ‖P.eval z‖ ^ 2 := by positivity
  have hsqrt : √(partsNormSq x) = √(1 + ‖P.eval z‖ ^ 2) * a⁻¹ := by
    rw [hN, Real.sqrt_mul hpos.le, Real.sqrt_sq (inv_nonneg.2 ha.le)]
  have hconj : conj (x 1) * x 2 = conj (P.eval z) * P.derivative.eval z * ((a⁻¹) ^ 2 : ℝ) := by
    rw [h1, h2, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hI : (conj (P.eval z) * (I * P.derivative.eval z)).re =
      -(conj (P.eval z) * P.derivative.eval z).im := by
    rw [mul_left_comm, Complex.I_mul_re]
  ext i
  fin_cases i
  · simp only [fieldOfParts, Fin.zero_eta, amplitudeField_apply_zero, hD, h5, hconj, hN, hI,
      Complex.im_mul_ofReal, PiLp.toLp_apply, Matrix.cons_val_zero]
    field_simp
    ring
  · simp only [fieldOfParts, Fin.mk_one, amplitudeField_apply_one, hD, h4, hconj, hN, one_mul,
      Complex.re_mul_ofReal, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
  · simp only [fieldOfParts, Fin.reduceFinMk, h3, h1, hsqrt, Complex.re_mul_ofReal, PiLp.toLp_apply,
      Matrix.cons_val, amplitudeField_apply_two, Real.exp_add, exp_backgroundAmplitude]
    field_simp
  · simp only [fieldOfParts, Fin.reduceFinMk, h3, h1, hsqrt, Complex.im_mul_ofReal, PiLp.toLp_apply,
      Matrix.cons_val, amplitudeField_apply_three, Real.exp_add, exp_backgroundAmplitude]
    field_simp

/-! ### The background parts -/

section Background

variable (P₀ : _root_.Polynomial ℂ)

/-- `1 + a ≤ 2 √(1 + a²)`. -/
private theorem one_add_le_two_mul_sqrt (a : ℝ) : 1 + a ≤ 2 * √(1 + a ^ 2) := by
  have h1 : 1 ≤ √(1 + a ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : a ≤ √(1 + a ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- For `k ≤ deg P₀`, the function `z ^ k / √(1 + ‖P₀ z‖²)` is bounded. -/
private theorem exists_norm_pow_mul_inv_sqrt_le (hP₀ : P₀ ≠ 0) {k : ℕ} (hk : k ≤ P₀.natDegree) :
    ∃ C, ∀ z : ℂ, ‖z ^ k * (((√(1 + ‖P₀.eval z‖ ^ 2))⁻¹ : ℝ) : ℂ)‖ ≤ C := by
  have hdeg : ((_root_.Polynomial.X : _root_.Polynomial ℂ) ^ k).degree ≤ P₀.degree := by
    rw [_root_.Polynomial.degree_X_pow, _root_.Polynomial.degree_eq_natDegree hP₀]
    exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := _root_.Polynomial.exists_norm_eval_le_mul_one_add_norm_eval hdeg
  refine ⟨2 * C, fun z ↦ ?_⟩
  have hs : 0 < √(1 + ‖P₀.eval z‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hz : ‖z‖ ^ k ≤ C * (1 + ‖P₀.eval z‖) := by simpa using hC z
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs.le),
    ← div_eq_mul_inv, div_le_iff₀ hs]
  calc ‖z‖ ^ k ≤ C * (1 + ‖P₀.eval z‖) := hz
    _ ≤ C * (2 * √(1 + ‖P₀.eval z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (one_add_le_two_mul_sqrt _) hC0
    _ = 2 * C * √(1 + ‖P₀.eval z‖ ^ 2) := by ring

/-- `z ↦ (√(1 + ‖P₀ z‖²))⁻¹` is continuous. -/
private theorem continuous_inv_sqrt_one_add_norm_eval_sq :
    Continuous fun z : ℂ ↦ (((√(1 + ‖P₀.eval z‖ ^ 2))⁻¹ : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp
    (continuous_const.add (P₀.continuous.norm.pow 2))).inv₀
      fun z ↦ (Real.sqrt_pos.2 (show (0 : ℝ) < 1 + ‖P₀.eval z‖ ^ 2 by positivity)).ne')

/-- The bounded continuous function `z ^ k / √(1 + ‖P₀ z‖²)` for `k ≤ n ≤ deg P₀`. -/
private def monomialSqrtWeight (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree) (k : Fin (n + 1)) :
    ℂ →ᵇ ℂ :=
  .ofNormedAddCommGroup (fun z ↦ z ^ (k : ℕ) * (((√(1 + ‖P₀.eval z‖ ^ 2))⁻¹ : ℝ) : ℂ))
    ((continuous_pow _).mul (continuous_inv_sqrt_one_add_norm_eval_sq P₀)) _
    (exists_norm_pow_mul_inv_sqrt_le P₀ hP₀ (k.is_le.trans hn)).choose_spec

/-- The bounded continuous function `Q / √(1 + ‖P₀‖²)` of a polynomial `Q` with coefficients
`a`, linear in `a`. -/
private def polySqrtWeight (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree) (a : Fin (n + 1) → ℂ) :
    ℂ →ᵇ ℂ :=
  ∑ k, a k • monomialSqrtWeight P₀ hP₀ hn k

private theorem polySqrtWeight_apply (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree)
    {Q : _root_.Polynomial ℂ} (hQ : Q.natDegree < n + 1) (z : ℂ) :
    polySqrtWeight P₀ hP₀ hn (fun k ↦ Q.coeff k) z =
      Q.eval z * (((√(1 + ‖P₀.eval z‖ ^ 2))⁻¹ : ℝ) : ℂ) := by
  rw [_root_.Polynomial.eval_eq_sum_range' hQ, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range,
    polySqrtWeight]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_apply, smul_eq_mul, monomialSqrtWeight,
    coe_ofNormedAddCommGroup]
  ring

/-- `polySqrtWeight` depends smoothly on coefficients that depend smoothly on a parameter. -/
private theorem contDiff_polySqrtWeight (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {a : Y → Fin (n + 1) → ℂ}
    (ha : ∀ k, ContDiff ℝ ∞ fun y ↦ a y k) :
    ContDiff ℝ ∞ fun y ↦ polySqrtWeight P₀ hP₀ hn (a y) := by
  unfold polySqrtWeight
  exact ContDiff.sum fun k _ ↦ (ha k).smul contDiff_const

end Background

/-! ### The parts from the reduced solution -/

/-- The Sobolev embedding of `H^s(ℂ)`, `s > 1`, into the bounded continuous functions. -/
private def sobolevBCF {s : ℝ} (hs : 1 < s) : H^{s}(ℂ) →L[ℝ] ℂ →ᵇ ℂ :=
  (ZeroAtInftyContinuousMap.toBCFₗᵢ ℝ).toContinuousLinearMap.comp
    ((toZeroAtInfty (finrank_real_complex_lt_two_mul hs)).restrictScalars ℝ)

private theorem coeFn_sobolevBCF {s : ℝ} (hs : 1 < s) (u : H^{s}(ℂ)) :
    ⇑(sobolevBCF hs u) = ⇑(toZeroAtInfty (finrank_real_complex_lt_two_mul hs) u) := by
  ext z
  simp [sobolevBCF]

/-- The Sobolev embedding of `u` is a representative of its `L²` function. -/
private theorem sobolevBCF_ae_eq {s : ℝ} (hs : 1 < s) {u : H^{s}(ℂ)} {f : ℂ → ℂ}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] f) : ⇑(sobolevBCF hs u) =ᵐ[volume] f := by
  rw [coeFn_sobolevBCF]
  exact (coeFn_inclusionLp_ae_eq_toZeroAtInfty _ u).symm.trans hu

variable {m : ℕ}

/-- The reduced solution `w_c` of `P_c` as an element of `H³(ℂ)`. -/
private def reducedSolutionH3 (c : Fin m → ℂ) : H^{(2 : ℝ) + 1}(ℂ) :=
  ofRealSobolevFunction (by norm_num)
    (reducedSolution_mem_realSobolevFunctions (monicOfCoeff c) ((2 : ℝ) + 1))

/-- The derivative `∂_v w_c` of the reduced solution, as a bounded continuous function. -/
private def reducedSolutionDeriv (v : ℂ) (c : Fin m → ℂ) : ℂ →ᵇ ℂ :=
  sobolevBCF one_lt_two (lineDerivCLM (by norm_num) (by simp) v (reducedSolutionH3 c))

private theorem contDiff_reducedSolutionDeriv (v : ℂ) :
    ContDiff ℝ ∞ (reducedSolutionDeriv (m := m) v) :=
  (sobolevBCF one_lt_two).contDiff.comp
    (((lineDerivCLM (by norm_num) (by simp) v).restrictScalars ℝ).contDiff.comp
      (contDiff_ofRealSobolevFunction_reducedSolution _))

private theorem reducedSolutionDeriv_ae_eq (v : ℂ) (c : Fin m → ℂ) :
    ⇑(reducedSolutionDeriv v c) =ᵐ[volume]
      fun z ↦ (fderiv ℝ (reducedSolution (monicOfCoeff c)) z v : ℂ) :=
  sobolevBCF_ae_eq one_lt_two (coeFn_inclusionLp_lineDerivCLM_ae_eq (by norm_num) (by simp)
    zero_le_two ((contDiff_reducedSolution _).of_le (by simp))
    (coeFn_inclusionLp_ofRealSobolevFunction _ _) v)

/-! ### The six parts of the vortex of `P_c` -/

/-- The six parts `((1 + ‖P₀‖²)^(-1/2), P_c (1 + ‖P₀‖²)^(-1/2), P_c' (1 + ‖P₀‖²)^(-1/2), w_c,
∂₁ w_c, ∂₂ w_c)` of the vortex of `P_c`, normalized by the polynomial `P₀ = P_{c₀}`, as bounded
continuous functions. -/
private def partsEntry (c₀ c : Fin m → ℂ) : Fin 6 → ℂ →ᵇ ℂ :=
  ![monomialSqrtWeight (monicOfCoeff c₀) (monic_monicOfCoeff c₀).ne_zero
      (natDegree_monicOfCoeff c₀).ge 0,
    polySqrtWeight (monicOfCoeff c₀) (monic_monicOfCoeff c₀).ne_zero
      (natDegree_monicOfCoeff c₀).ge fun k ↦ (monicOfCoeff c).coeff k,
    polySqrtWeight (monicOfCoeff c₀) (monic_monicOfCoeff c₀).ne_zero
      (natDegree_monicOfCoeff c₀).ge fun k ↦ (monicOfCoeff c).derivative.coeff k,
    sobolevBCF one_lt_two (sobolevReducedSolution c),
    reducedSolutionDeriv 1 c,
    reducedSolutionDeriv I c]

private theorem contDiff_partsEntry (c₀ : Fin m → ℂ) (j : Fin 6) :
    ContDiff ℝ ∞ fun c ↦ partsEntry c₀ c j := by
  fin_cases j
  · exact contDiff_const
  · exact contDiff_polySqrtWeight _ _ _ fun k ↦ (contDiff_coeff_monicOfCoeff k).restrict_scalars ℝ
  · exact contDiff_polySqrtWeight _ _ _ fun k ↦
      (contDiff_coeff_derivative_monicOfCoeff k).restrict_scalars ℝ
  · exact (sobolevBCF one_lt_two).contDiff.comp contDiff_sobolevReducedSolution
  · exact contDiff_reducedSolutionDeriv 1
  · exact contDiff_reducedSolutionDeriv I

/-- The six parts of the vortex of `P_c` as one bounded continuous function. -/
private def vortexParts (c₀ c : Fin m → ℂ) : ℂ →ᵇ (Fin 6 → ℂ) :=
  ∑ j, (ContinuousLinearMap.single ℝ (fun _ : Fin 6 ↦ ℂ) j).compLeftContinuousBounded ℂ
    (partsEntry c₀ c j)

private theorem vortexParts_apply (c₀ c : Fin m → ℂ) (z : ℂ) (j : Fin 6) :
    vortexParts c₀ c z j = partsEntry c₀ c j z := by
  simp [vortexParts, Pi.single_apply]

private theorem contDiff_vortexParts (c₀ : Fin m → ℂ) : ContDiff ℝ ∞ (vortexParts c₀) :=
  ContDiff.sum fun j _ ↦ ((ContinuousLinearMap.single ℝ (fun _ : Fin 6 ↦ ℂ) j
    ).compLeftContinuousBounded ℂ).contDiff.comp (contDiff_partsEntry c₀ j)

private theorem vortexParts_apply_zero (c₀ c : Fin m → ℂ) (z : ℂ) :
    vortexParts c₀ c z 0 = (((√(1 + ‖(monicOfCoeff c₀).eval z‖ ^ 2))⁻¹ : ℝ) : ℂ) := by
  simp [vortexParts_apply, partsEntry, monomialSqrtWeight]

private theorem vortexParts_apply_one (c₀ c : Fin m → ℂ) (z : ℂ) :
    vortexParts c₀ c z 1 =
      (monicOfCoeff c).eval z * (((√(1 + ‖(monicOfCoeff c₀).eval z‖ ^ 2))⁻¹ : ℝ) : ℂ) := by
  simp only [vortexParts_apply, partsEntry, Matrix.cons_val]
  rw [polySqrtWeight_apply _ _ _ (by rw [natDegree_monicOfCoeff]; exact Nat.lt_succ_self m)]

private theorem vortexParts_apply_two (c₀ c : Fin m → ℂ) (z : ℂ) :
    vortexParts c₀ c z 2 = (monicOfCoeff c).derivative.eval z *
      (((√(1 + ‖(monicOfCoeff c₀).eval z‖ ^ 2))⁻¹ : ℝ) : ℂ) := by
  simp only [vortexParts_apply, partsEntry, Matrix.cons_val]
  rw [polySqrtWeight_apply _ _ _
      ((_root_.Polynomial.natDegree_derivative_le _).trans_lt
        (by rw [natDegree_monicOfCoeff]; omega))]

/-- At `c = c₀` the first two parts have `‖x 0‖² + ‖x 1‖² = 1`. -/
private theorem partsNormSq_vortexParts_self (c₀ : Fin m → ℂ) (z : ℂ) :
    partsNormSq (vortexParts c₀ c₀ z) = 1 := by
  have hpos : (0 : ℝ) < 1 + ‖(monicOfCoeff c₀).eval z‖ ^ 2 := by positivity
  rw [partsNormSq, vortexParts_apply_zero, vortexParts_apply_one, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have hs := Real.sq_sqrt hpos.le
  field_simp
  linarith

/-- **The parts read off the vortex.** Almost everywhere, the field of the six parts of the vortex
of `P_c` is the vortex of `P_c`. -/
private theorem ae_fieldOfParts_vortexParts (c₀ c : Fin m → ℂ) :
    ∀ᵐ z, fieldOfParts (vortexParts c₀ c z) = polynomialVortex (monicOfCoeff c) z := by
  have h3 := sobolevBCF_ae_eq one_lt_two (coeFn_inclusionLp_sobolevReducedSolution c)
  filter_upwards [h3, reducedSolutionDeriv_ae_eq 1 c, reducedSolutionDeriv_ae_eq I c]
    with z h3 h4 h5
  rw [polynomialVortex_def]
  refine fieldOfParts_eq _ ((contDiff_reducedSolution _).differentiable (by simp) z)
    (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + ‖(monicOfCoeff c₀).eval z‖ ^ 2))
    (vortexParts_apply_zero c₀ c z) (vortexParts_apply_one c₀ c z)
    (vortexParts_apply_two c₀ c z) ?_ ?_ ?_
  · rw [vortexParts_apply]
    simp [partsEntry, h3]
  · rw [vortexParts_apply]
    simp [partsEntry, h4]
  · rw [vortexParts_apply]
    simp [partsEntry, h5]

/-! ### The superposition operator of the field of the parts -/

/-- A compact set of parts on which the field is smooth. -/
private def partsWindow (R : ℝ) : Set (Fin 6 → ℂ) :=
  {x | ‖x‖ ≤ R ∧ 1 / 2 ≤ partsNormSq x}

private theorem isCompact_partsWindow (R : ℝ) : IsCompact (partsWindow R) :=
  Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const contDiff_partsNormSq.continuous))
    (isBounded_closedBall.subset fun _ hx ↦ mem_closedBall_zero_iff.2 hx.1)

private theorem partsWindow_subset (R : ℝ) : partsWindow R ⊆ {x | 0 < partsNormSq x} :=
  fun _ hx ↦ lt_of_lt_of_le (by norm_num) hx.2

private theorem continuousOn_fieldOfParts (R : ℝ) : ContinuousOn fieldOfParts (partsWindow R) :=
  fun _ hx ↦ (contDiffAt_fieldOfParts (partsWindow_subset R hx)).continuousAt.continuousWithinAt

/-- If `u² + v² = 1` and `p, q` are within `1 / 8` of `u, v`, then `p² + q² ≥ 1 / 2`. -/
private theorem one_half_le_sq_add_sq {u v p q : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (h : u ^ 2 + v ^ 2 = 1) (hpu : u ≤ p + 1 / 8) (hqv : v ≤ q + 1 / 8) :
    1 / 2 ≤ p ^ 2 + q ^ 2 := by
  have hp2 : u ^ 2 - u / 4 ≤ p ^ 2 := by
    rcases le_total u (1 / 8) with h' | h'
    · nlinarith
    · nlinarith
  have hq2 : v ^ 2 - v / 4 ≤ q ^ 2 := by
    rcases le_total v (1 / 8) with h' | h'
    · nlinarith
    · nlinarith
  have hu1 : u ≤ 1 := by nlinarith
  have hv1 : v ≤ 1 := by nlinarith
  linarith

/-- Parts within `1 / 8` of parts with `‖x 0‖² + ‖x 1‖² = 1` lie in the window. -/
private theorem ball_subset_partsWindow {x₀ : Fin 6 → ℂ} (h₀ : partsNormSq x₀ = 1) {R : ℝ}
    (hR : ‖x₀‖ + 1 ≤ R) : ball x₀ (1 / 8) ⊆ partsWindow R := by
  intro x hx
  rw [mem_ball, dist_eq_norm] at hx
  have he (j : Fin 6) : ‖x₀ j‖ ≤ ‖x j‖ + 1 / 8 := by
    have := (norm_le_pi_norm (x - x₀) j).trans hx.le
    rw [Pi.sub_apply] at this
    linarith [norm_le_norm_add_norm_sub' (x₀ j) (x j), norm_sub_rev (x j) (x₀ j)]
  refine ⟨?_, ?_⟩
  · linarith [norm_le_norm_add_norm_sub' x x₀]
  · exact one_half_le_sq_add_sq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      h₀ (he 0) (he 1)

/-- Parts within `1 / 8` of the parts of the vortex of `P_{c₀}` at a point lie in the window. -/
private theorem ball_vortexParts_subset_partsWindow (c₀ : Fin m → ℂ) (z : ℂ) :
    ball (vortexParts c₀ c₀ z) (1 / 8) ⊆ partsWindow (‖vortexParts c₀ c₀‖ + 1) :=
  ball_subset_partsWindow (partsNormSq_vortexParts_self c₀ z)
    (by linarith [norm_coe_le_norm (vortexParts c₀ c₀) z])

/-- Bounded parts within `1 / 8` of the parts of the vortex of `P_{c₀}` take values in the
window. -/
private theorem vortexParts_mem_partsWindow {c₀ : Fin m → ℂ} {f : ℂ →ᵇ (Fin 6 → ℂ)}
    (hf : f ∈ ball (vortexParts c₀ c₀) (1 / 8)) (z : ℂ) :
    f z ∈ partsWindow (‖vortexParts c₀ c₀‖ + 1) :=
  ball_vortexParts_subset_partsWindow c₀ z ((dist_coe_le_dist z).trans_lt hf)

open scoped Classical in
/-- The superposition operator `f ↦ fieldOfParts ∘ f`, on parts with values in the window, and
`0` otherwise. -/
private def fieldOfPartsBCF (R : ℝ) (f : ℂ →ᵇ (Fin 6 → ℂ)) : ℂ →ᵇ EuclideanSpace ℝ (Fin 4) :=
  if h : ∀ z, f z ∈ partsWindow R then
    .ofNormedAddCommGroup (fun z ↦ fieldOfParts (f z))
      ((continuousOn_fieldOfParts R).comp_continuous f.continuous h) _ fun z ↦
        ((isCompact_partsWindow R).exists_bound_of_continuousOn
          (continuousOn_fieldOfParts R)).choose_spec _ (h z)
  else 0

private theorem fieldOfPartsBCF_apply {R : ℝ} {f : ℂ →ᵇ (Fin 6 → ℂ)}
    (h : ∀ z, f z ∈ partsWindow R) (z : ℂ) : fieldOfPartsBCF R f z = fieldOfParts (f z) := by
  rw [fieldOfPartsBCF, dite_eq_left h, coe_ofNormedAddCommGroup]

/-- The superposition operator is smooth at the parts of the vortex of `P_{c₀}`. -/
private theorem contDiffAt_fieldOfPartsBCF (c₀ : Fin m → ℂ) :
    ContDiffAt ℝ ∞ (fieldOfPartsBCF (‖vortexParts c₀ c₀‖ + 1)) (vortexParts c₀ c₀) := by
  set R := ‖vortexParts c₀ c₀‖ + 1
  have hopen : IsOpen {x : Fin 6 → ℂ | 0 < partsNormSq x} :=
    isOpen_lt continuous_const contDiff_partsNormSq.continuous
  refine contDiffAt_infty.2 fun n ↦ contDiffAt_of_forall_apply_eq
    (ContDiffOn.uniformContDiffOn hopen (partsWindow_subset R) (isCompact_partsWindow R)
      fun x hx ↦ (contDiffAt_infty.1 (contDiffAt_fieldOfParts hx) n).contDiffWithinAt)
    (by norm_num) (ball_vortexParts_subset_partsWindow c₀) fun f hf z ↦
      fieldOfPartsBCF_apply (vortexParts_mem_partsWindow hf) z

/-! ### Smooth dependence on the divisor -/

/-- **The vortices depend smoothly on the divisor.** For `c ∈ ℂᵐ`, the symmetric coordinates of
the divisor of `P_c = TauCeti.Polynomial.monicOfCoeff c` in `Sym^m ℂ`, collisions of zeros
included, the `L∞` class of the plane vortex with zero divisor `P_c` is a smooth function of
`c`. -/
theorem contDiff_polynomialVortexLp_monicOfCoeff :
    ContDiff ℝ ∞ fun c : Fin m → ℂ ↦ polynomialVortexLp (monicOfCoeff c) := by
  refine contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  set R := ‖vortexParts c₀ c₀‖ + 1
  have hF := contDiff_vortexParts c₀
  have hcomp : ContDiffAt ℝ ∞
      (fun c ↦ toLpTop μ⊤ ℝ (fieldOfPartsBCF R (vortexParts c₀ c))) c₀ :=
    (toLpTop μ⊤ ℝ : (ℂ →ᵇ EuclideanSpace ℝ (Fin 4)) →L[ℝ] _).contDiff.contDiffAt.comp c₀
      ((contDiffAt_fieldOfPartsBCF c₀).comp c₀ hF.contDiffAt)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds
    (ball_mem_nhds (vortexParts c₀ c₀) (by norm_num : (0 : ℝ) < 1 / 8))] with c hc
  refine Lp.ext ?_
  filter_upwards [polynomialVortexLp_ae_eq (monicOfCoeff c),
    coeFn_toLpTop μ⊤ (𝕜 := ℝ) (fieldOfPartsBCF R (vortexParts c₀ c)),
    ae_restrict_of_ae (ae_fieldOfParts_vortexParts c₀ c)] with z h₁ h₂ h₃
  rw [h₁, h₂, fieldOfPartsBCF_apply (vortexParts_mem_partsWindow hc), h₃]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {P : X → _root_.Polynomial ℂ}
  {n : ℕ∞}

/-- **Smoothness of the vortices along a family of polynomials.** For a family of monic
polynomials of degree `m` whose coefficients are `C^n` functions of a parameter, the `L∞` classes
of their vortices are a `C^n` function of the parameter. -/
theorem contDiff_polynomialVortexLp (hmonic : ∀ x, (P x).Monic) (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, ContDiff ℝ n fun x ↦ (P x).coeff k) :
    ContDiff ℝ n fun x ↦ polynomialVortexLp (P x) := by
  have h : (fun x ↦ polynomialVortexLp (P x)) =
      (fun c : Fin m → ℂ ↦ polynomialVortexLp (monicOfCoeff c)) ∘ fun x i ↦ (P x).coeff i :=
    funext fun x ↦ by rw [Function.comp_apply, monicOfCoeff_coeff (hmonic x) (hdeg x)]
  rw [h]
  exact (contDiff_polynomialVortexLp_monicOfCoeff.of_le (WithTop.coe_le_coe.2 le_top)).comp
    (contDiff_pi.2 fun i ↦ hcoeff i)

variable (hm : 0 < m) (hmonic : ∀ x, (P x).Monic) (hdeg : ∀ x, (P x).natDegree = m)
  (hcoeff : ∀ k, ContDiff ℝ n fun x ↦ (P x).coeff k)
include hm hmonic hdeg hcoeff

/-- **Smoothness of the kernel projections along the vortex family.** For a family of monic
polynomials of a fixed degree `m ≥ 1` whose coefficients are `C^n` functions of a parameter, the
projection of `H¹(ℂ)⁴` onto the kernel of `L_P : H¹ → L²` along its `L²`-orthogonal complement is
a `C^n` function of the parameter, in operator norm. For `P = P_c` the parameter is the tuple
`c ∈ ℂᵐ` of symmetric coordinates of the divisor, and the projections are smooth in `c`,
collisions of zeros included. -/
theorem contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp :
    ContDiff ℝ n fun x ↦ ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (polynomialVortexLp (P x))) :=
  contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator
    (contDiff_polynomialVortexLp hmonic hdeg hcoeff)
    (fun x ↦ sobolevGaugeFixedOperator_polynomialVortexLp_surjective (hmonic x)
      ((hdeg x).symm ▸ hm))
    fun x ↦ finiteDimensional_ker_sobolevGaugeFixedOperator_polynomialVortexLp (hmonic x)
      ((hdeg x).symm ▸ hm)

/-- **Smoothness of the right inverses along the vortex family.** For a family of monic
polynomials of a fixed degree `m ≥ 1` whose coefficients are `C^n` functions of a parameter, the
right inverse of `L_P : H¹ → L²` with values `L²`-orthogonal to its kernel is a `C^n` function of
the parameter, in operator norm. For `P = P_c` the parameter is the tuple `c ∈ ℂᵐ` of symmetric
coordinates of the divisor, and the right inverses are smooth in `c`, collisions of zeros
included. -/
theorem contDiff_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp :
    ContDiff ℝ n fun x ↦ ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (polynomialVortexLp (P x))) :=
  contDiff_orthogonalRightInverse_sobolevGaugeFixedOperator
    (contDiff_polynomialVortexLp hmonic hdeg hcoeff)
    (fun x ↦ sobolevGaugeFixedOperator_polynomialVortexLp_surjective (hmonic x)
      ((hdeg x).symm ▸ hm))
    fun x ↦ finiteDimensional_ker_sobolevGaugeFixedOperator_polynomialVortexLp (hmonic x)
      ((hdeg x).symm ▸ hm)

end TauCeti.Vortex
