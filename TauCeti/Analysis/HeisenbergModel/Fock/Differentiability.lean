/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.PolynomialVector
public import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.MvPolynomial.L1Norm
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.Analysis.Normed.Group.Pi
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Differentiability of polynomial Fock orbits

Polynomial vectors have differentiable orbits under the Weil representation: a differentiable
curve of matrices in the indefinite unitary group gives a differentiable curve in the Banach
Fock space. The assertion concerns the `L¹` norm, rather than only pointwise derivatives.

The analytic input is holomorphic dependence of superpositions of polynomial times Gaussian
functions. Homogeneity and compactness give a uniform integrable majorant near the undeformed
Gaussian. The inverse matrix and its conjugate transpose are then treated as independent complex
parameters before restricting to a real curve of unitary matrices.

The argument follows the Gaussian deformation method of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC),
`src/Lib/Weil/Fock/Basic.lean`, `differentiableAt_integral_smul_realHeisenbergOp`, and
`src/Lib/Weil/Fock/PolynomialVectors.lean`, `differentiableAt_realWeil_polyVector`.
Here the existing holomorphic parametric integral theorem and polynomial `l1Norm` bound are used.
-/

public noncomputable section

open MeasureTheory Complex Matrix MvPolynomial Filter Topology Metric Set
open scoped ComplexConjugate Matrix.Norms.L2Operator

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Uniform control on the unit ball extends to all integration variables by homogeneity. -/
private theorem deformation_bounds
    (f : E → ℂ × (ι → ℂ) → (ι → ℂ) × ℂ) (z : E)
    (hf : ∀ (r : ℝ) y, f z (r • y) = (r • (f z y).1, r ^ 2 • (f z y).2))
    (hsmall : ∀ y ∈ closedBall (0 : ℂ × (ι → ℂ)) 1,
      ‖(f z y).1‖ < 2 ∧ (f z y).2.re + (∑ i, ‖y.2 i‖ ^ 2) / 2 < 1 / 4)
    (x : ι → ℂ) :
    ‖(f z (1, x)).1‖ ≤ 2 * (1 + ‖x‖) ∧
      (f z (1, x)).2.re ≤ 1 - (∑ i, ‖x i‖ ^ 2) / 8 := by
  let r : ℝ := max 1 ‖x‖
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hnorm : ‖((1, x) : ℂ × (ι → ℂ))‖ = r := by simp [r, Prod.norm_def]
  have hy : r⁻¹ • ((1 : ℂ), x) ∈ closedBall 0 1 := by
    simp only [mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      hnorm, inv_mul_cancel₀ hr.ne', le_refl]
  obtain ⟨h₁, h₂⟩ := hsmall _ hy
  rw [hf] at h₁ h₂
  have hsum : ∑ i, ‖(r⁻¹ • x) i‖ ^ 2 = r⁻¹ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    simp [Pi.smul_apply, Real.norm_of_nonneg hr.le, mul_pow, Finset.mul_sum]
  simp only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at h₁
  have h₁' : ‖(f z (1, x)).1‖ < 2 * r := by simpa [mul_comm] using (inv_mul_lt_iff₀ hr).mp h₁
  have h₂' : (f z (1, x)).2.re + (∑ i, ‖x i‖ ^ 2) / 2 < r ^ 2 / 4 := by
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Prod.smul_snd, hsum] at h₂
    have := (mul_lt_mul_iff_right₀ (sq_pos_of_pos hr)).mpr h₂
    field_simp at this
    nlinarith
  have hr_bound : r ≤ 1 + ‖x‖ := max_le (by linarith [norm_nonneg x]) (by linarith)
  have hr_sq : r ^ 2 ≤ 1 + ∑ i, ‖x i‖ ^ 2 := by
    have h := Pi.norm_pow_le_sum_norm_pow x two_ne_zero
    rcases le_total 1 ‖x‖ with hx | hx <;> simp only [r, max_eq_right hx, max_eq_left hx] <;>
      nlinarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ sq_nonneg ‖x i‖)]
  exact ⟨h₁'.le.trans (by linarith), by
    nlinarith [Finset.sum_nonneg (s := Finset.univ) (fun i : ι ↦ fun _ ↦ sq_nonneg ‖x i‖)]⟩

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- The polynomial times deformed Gaussian has an integrable bound independent of the parameter. -/
private theorem norm_deformed_integrand_le (P : MvPolynomial ι ℂ)
    (f : E → ℂ × (ι → ℂ) → (ι → ℂ) × ℂ) (z : E)
    (hb : ∀ x : ι → ℂ, ‖(f z (1, x)).1‖ ≤ 2 * (1 + ‖x‖) ∧
      (f z (1, x)).2.re ≤ 1 - (∑ i, ‖x i‖ ^ 2) / 8) (x : ι → ℂ) :
    ‖(eval (f z (1, x)).1 P * cexp (f z (1, x)).2) •
      ReproducingModel.heisenbergRep x (ReproducingModel.vacuum : FockSpace ε)‖ ≤
      P.l1Norm * Real.exp (2 * P.totalDegree + 1) *
        ‖(ReproducingModel.vacuum : FockSpace ε)‖ *
        (Real.exp (4 * P.totalDegree * ‖(1 / 2 : ℝ) • x‖) *
          ‖gaussian ι ((1 / 2 : ℝ) • x)‖) := by
  have hP := P.l1Norm_nonneg
  have hmax : max 1 ‖(f z (1, x)).1‖ ≤ Real.exp (2 * (1 + ‖x‖)) := by
    exact max_le (Real.one_le_exp (by positivity))
      ((hb x).1.trans (by linarith [Real.add_one_le_exp (2 * (1 + ‖x‖))]))
  have hpoly : ‖eval (f z (1, x)).1 P‖ ≤
      P.l1Norm * Real.exp (P.totalDegree * (2 * (1 + ‖x‖))) := by
    refine (P.norm_eval_le_l1Norm_mul_max_one_pow _).trans ?_
    rw [Real.exp_natCast_mul]
    gcongr
  rw [norm_smul, norm_mul, HeisenbergDatum.Representation.norm_apply, Complex.norm_exp]
  calc
    _ ≤ P.l1Norm * Real.exp (P.totalDegree * (2 * (1 + ‖x‖))) *
        Real.exp (1 - (∑ i, ‖x i‖ ^ 2) / 8) * ‖(ReproducingModel.vacuum : FockSpace ε)‖ := by
      gcongr
      exact (hb x).2
    _ = _ := by
      rw [norm_gaussian]
      simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        mul_pow, ← Finset.mul_sum, ← Real.exp_add]
      rw [mul_assoc P.l1Norm, ← Real.exp_add]
      have hexp : (P.totalDegree : ℝ) * (2 * (1 + ‖x‖)) +
          (1 - (∑ i, ‖x i‖ ^ 2) / 8) =
          (2 * P.totalDegree + 1) +
            (4 * P.totalDegree * (1 / 2 * ‖x‖) -
              ((1 / 2 : ℝ) ^ 2 * ∑ i, ‖x i‖ ^ 2) / 2) := by ring
      rw [hexp]
      ring_nf
      simp only [Real.exp_add]
      ring

/-- Superpositions of holomorphic homogeneous deformations of a polynomial times the Gaussian
are analytic near the undeformed parameter. The two components have real degrees one and two
in the homogenized integration variable `(s, x)`. -/
theorem analyticAt_integral_smul_heisenbergRep (P : MvPolynomial ι ℂ)
    (f : E → ℂ × (ι → ℂ) → (ι → ℂ) × ℂ) {a : E}
    (hd : ∀ y, Differentiable ℂ (f · y)) (hc : Continuous f.uncurry)
    (ha : ∀ y, f a y = (holomorphicCoord ε y.2, -(∑ i, (‖y.2 i‖ : ℂ) ^ 2) / 2))
    (hh : ∀ z (r : ℝ) y, f z (r • y) = (r • (f z y).1, r ^ 2 • (f z y).2)) :
    AnalyticAt ℂ (fun z ↦ ∫ x : ι → ℂ,
      (eval (f z (1, x)).1 P * cexp (f z (1, x)).2) •
        ReproducingModel.heisenbergRep x (ReproducingModel.vacuum : FockSpace ε) ∂measure ι) a := by
  have hsmall : ∀ᶠ z in 𝓝 a, ∀ y ∈ closedBall (0 : ℂ × (ι → ℂ)) 1,
      ‖(f z y).1‖ < 2 ∧ (f z y).2.re + (∑ i, ‖y.2 i‖ ^ 2) / 2 < 1 / 4 := by
    apply (isCompact_closedBall _ _).eventually_forall_of_forall_eventually
    intro y hy
    have h₁ : ‖(f a y).1‖ < 2 := by
      rw [ha, norm_holomorphicCoord]
      have : ‖y.2‖ ≤ 1 := (norm_snd_le y).trans (by simpa using hy)
      linarith
    have h₂ : (f a y).2.re + (∑ i, ‖y.2 i‖ ^ 2) / 2 < 1 / 4 := by
      simp [ha, ← Complex.ofReal_pow, -Complex.ofReal_sum]
      linarith
    exact ((hc.fst.norm.continuousAt.eventually_lt continuous_const.continuousAt h₁).and
      ((by fun_prop : Continuous fun p : E × (ℂ × (ι → ℂ)) ↦
        (f p.1 p.2).2.re + (∑ i, ‖p.2.2 i‖ ^ 2) / 2).continuousAt.eventually_lt
          continuous_const.continuousAt h₂))
  obtain ⟨U, hU, hUa, hUs⟩ := _root_.mem_nhds_iff.mp hsmall
  let bound := fun x : ι → ℂ ↦ P.l1Norm * Real.exp (2 * P.totalDegree + 1) *
    ‖(ReproducingModel.vacuum : FockSpace ε)‖ *
      (Real.exp (4 * P.totalDegree * ‖(1 / 2 : ℝ) • x‖) *
        ‖gaussian ι ((1 / 2 : ℝ) • x)‖)
  have hi : Integrable bound (measure ι) :=
    ((integrable_exp_mul_norm_gaussian (4 * P.totalDegree)).comp_smul (by norm_num)).const_mul _
  refine analyticOnNhd_integral_of_dominated hUa (fun z _ ↦ ?_)
    (fun z hz ↦ ⟨U, hUa.mem_nhds hz, bound, hi, .of_forall fun x w hw ↦ ?_⟩)
    (.of_forall fun x ↦ ?_) a hUs
  · have hcont : Continuous (f z) := hc.comp (continuous_const.prodMk continuous_id)
    have hp := P.continuous_eval
    fun_prop
  · exact norm_deformed_integrand_le P f w (deformation_bounds f w (hh w) (hU hw)) x
  · have hp : Differentiable ℂ (fun l : ι → ℂ ↦ eval l P) :=
      fun l ↦ (P.hasFDerivAt_eval l).differentiableAt
    exact (by fun_prop : Differentiable ℂ fun z ↦
      (eval (f z (1, x)).1 P * cexp (f z (1, x)).2) •
        ReproducingModel.heisenbergRep x (ReproducingModel.vacuum : FockSpace ε)).differentiableOn

/-! ### Matrix curves in the unitary group -/

/-- Independent complex variables for the inverse matrix and its conjugate transpose. -/
private def matrixDeformation (ε : ι → ℤˣ)
    (z : Matrix ι ι ℂ × Matrix ι ι ℂ) (y : ℂ × (ι → ℂ)) : (ι → ℂ) × ℂ :=
  ((fun i ↦ if ε i = 1 then (star y.2 ᵥ* z.2) i else (z.1 *ᵥ y.2) i),
    -(star y.2 ᵥ* z.2 ⬝ᵥ z.1 *ᵥ y.2) / 2)

private theorem matrixDeformation_one (y : ℂ × (ι → ℂ)) :
    matrixDeformation ε (1, 1) y =
      (holomorphicCoord ε y.2, -(∑ i, (‖y.2 i‖ : ℂ) ^ 2) / 2) := by
  have hnorm (w : ℂ) : conj w * w = (‖w‖ : ℂ) ^ 2 := (Complex.conj_mul' w)
  apply Prod.ext
  · funext i
    simp [matrixDeformation, holomorphicCoord_apply]
  · simp [matrixDeformation, dotProduct, hnorm]

omit [DecidableEq ι] in
private theorem matrixDeformation_real_smul (z : Matrix ι ι ℂ × Matrix ι ι ℂ)
    (r : ℝ) (y : ℂ × (ι → ℂ)) :
    matrixDeformation ε z (r • y) =
      (r • (matrixDeformation ε z y).1, r ^ 2 • (matrixDeformation ε z y).2) := by
  ext i
  · simp only [matrixDeformation, Prod.smul_snd, star_smul, star_trivial,
      smul_vecMul, mulVec_smul, Pi.smul_apply]
    split_ifs <;> rfl
  · simp [matrixDeformation, star_smul, star_trivial, smul_vecMul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, Complex.real_smul]
    ring

/-- The parameterized superposition used to differentiate the Weil action. -/
private def matrixSuperposition (ε : ι → ℤˣ) (P : MvPolynomial ι ℂ)
    (z : Matrix ι ι ℂ × Matrix ι ι ℂ) : FockSpace ε :=
  ∫ x : ι → ℂ,
    (eval (matrixDeformation ε z (1, x)).1 P * cexp (matrixDeformation ε z (1, x)).2) •
      ReproducingModel.heisenbergRep x (ReproducingModel.vacuum : FockSpace ε) ∂measure ι

/-- The matrix superposition is holomorphic at the identity pair of matrices. -/
private theorem analyticAt_matrixSuperposition (P : MvPolynomial ι ℂ) :
    AnalyticAt ℂ (matrixSuperposition ε P) (1, 1) := by
  apply analyticAt_integral_smul_heisenbergRep P (matrixDeformation ε)
  · intro y
    dsimp only [matrixDeformation]
    apply Differentiable.prodMk
    · apply differentiable_pi.2
      intro i
      split_ifs <;> fun_prop [mulVec, vecMul, dotProduct]
    · fun_prop [mulVec, vecMul, dotProduct]
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      split_ifs <;> fun_prop [mulVec, vecMul, dotProduct]
    · fun_prop [mulVec, vecMul, dotProduct]
  · exact matrixDeformation_one
  · exact matrixDeformation_real_smul

/-- Change variables in superposition to obtain the holomorphic matrix expression. -/
private theorem weilRep_polyVector_eq_matrixSuperposition (g : unitaryGroup ε)
    (P : MvPolynomial ι ℂ) :
    weilRep ε g (polyVector ε P) = multiplier ε g • matrixSuperposition ε P
      ((((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ),
        (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)ᴴ) := by
  rw [matrixSuperposition]
  rw [ReproducingModel.weilRep_apply_eq, ReproducingModel.weilOp_apply_eq,
    HeisenbergDatum.Representation.integrated_apply]
  congr 1
  rw [← ((multiplier ε).measurePreserving_smul g⁻¹).integral_comp' (f := .smul g⁻¹)]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    have hcoord (M : Matrix ι ι ℂ) : holomorphicCoord ε (M *ᵥ x) =
        fun i ↦ if ε i = 1 then (star x ᵥ* Mᴴ) i else (M *ᵥ x) i := by
      rw [← star_mulVec]
      funext i
      exact holomorphicCoord_apply _ _
    simp [matrixDeformation, polyVector_apply, hcoord, smul_def,
      HeisenbergDatum.Representation.twist_apply, star_mulVec,
      gaussian_eq_exp_star_dotProduct]

/-- A curve through the identity acts differentiably on every polynomial vector. -/
private theorem differentiableAt_weilRep_polyVector_of_eq_one {γ : ℝ → unitaryGroup ε}
    {t : ℝ} (h₀ : γ t = 1)
    (hγ : DifferentiableAt ℝ (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) t)
    (P : MvPolynomial ι ℂ) :
    DifferentiableAt ℝ (fun s ↦ weilRep ε (γ s) (polyVector ε P)) t := by
  let A (s : ℝ) : Matrix ι ι ℂ := ((γ s : GL ι ℂ) : Matrix ι ι ℂ)
  let B (s : ℝ) : Matrix ι ι ℂ := ((γ s)⁻¹ : GL ι ℂ)
  have hB : DifferentiableAt ℝ B t := by
    have heq (s : ℝ) : B s = (signMatrix ε) * (A s)ᴴ * signMatrix ε := by
      dsimp only [B]
      rw [val_inv_of_mem_unitaryGroupOf isUnit_signMatrix (γ s).property, inv_signMatrix,
        star_eq_conjTranspose]
    rw [funext heq]
    exact (hγ.star.const_mul (signMatrix ε)).mul_const (signMatrix ε)
  have hi := analyticAt_matrixSuperposition (ε := ε) P
  have hparam : (B t, (B t)ᴴ) = (1, 1) := by simp [B, h₀]
  rw [← hparam] at hi
  have hBstar : DifferentiableAt ℝ (fun s ↦ (B s)ᴴ) t := by
    simpa only [star_eq_conjTranspose] using hB.star
  have hint := (hi.differentiableAt.restrictScalars ℝ).comp t (hB.prodMk hBstar)
  have hdelta : DifferentiableAt ℝ (fun s ↦ multiplier ε (γ s)) t := by
    have hdet : DifferentiableAt ℝ
        (fun s ↦ (negBlock ε ((γ s : GL ι ℂ) : Matrix ι ι ℂ)).det) t := by
      have hentry (i j : ι) : DifferentiableAt ℝ
          (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ) i j) t :=
        differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
      simp only [Matrix.det_apply', negBlock_apply]
      fun_prop
    simp only [multiplier_apply]
    exact hdet.star
  -- The integral keeps the vacuum translates fixed; only its scalar coefficients move.
  convert hdelta.smul hint using 1
  funext s
  exact weilRep_polyVector_eq_matrixSuperposition (γ s) P

/-- Every polynomial Fock vector has a differentiable Weil orbit along any differentiable curve
of unitary matrices, at any point of the curve. Differentiability is in the Banach Fock norm. -/
theorem differentiableAt_weilRep_polyVector {γ : ℝ → unitaryGroup ε} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun s ↦ ((γ s : GL ι ℂ) : Matrix ι ι ℂ)) t)
    (P : MvPolynomial ι ℂ) :
    DifferentiableAt ℝ (fun s ↦ weilRep ε (γ s) (polyVector ε P)) t := by
  let η (s : ℝ) := (γ t)⁻¹ * γ s
  have hη : DifferentiableAt ℝ (fun s ↦ ((η s : GL ι ℂ) : Matrix ι ι ℂ)) t := by
    simpa [η] using hγ.const_mul (((γ t)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)
  have hd := differentiableAt_weilRep_polyVector_of_eq_one (γ := η) (by simp [η]) hη P
  have h := ((weilRep ε (γ t)).restrictScalars ℝ).differentiableAt.comp t hd
  simpa [Function.comp_def, η, ← mul_apply_eq_comp, ← map_mul] using h

end TauCeti.Fock
