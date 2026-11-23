/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Fredholm
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# A saddle connection on the upright torus and its removal by tilting

The torus of revolution `((2 + cos y) cos x, (2 + cos y) sin x, sin y)` standing upright has the
height function `(2 + cos y) cos x`. Tilting the direction of measurement to `(1, 0, ε)` gives

`f_ε(x, y) = (2 + cos y) cos x + ε sin y`

(`TauCeti.tiltedTorusHeight`), which we study on the Euclidean plane, the universal cover of the
torus. Its gradient is globally Lipschitz. Its critical points are the points with `sin x = 0` and
`sin y cos x = ε cos y`, all nondegenerate. Among them, those with `cos y < 0` are saddles, of
Morse index `1`; the others are maxima, where `cos x = 1`, and minima, where `cos x = -1`.

* **The upright torus is not Morse–Smale.** For `ε = 0` the line `y = π` is invariant, and on it the
  flow is `x' = sin x`, solved by `x = 2 arctan eᵗ`. This trajectory runs from the saddle `(0, π)`
  to the saddle `(π, π)`, of the same Morse index, so the flow is not Morse–Smale
  (`TauCeti.not_isMorseSmale_tiltedTorusHeight_zero`).
* **The tilted torus is Morse–Smale** for every `ε ≠ 0` (`TauCeti.isMorseSmale_tiltedTorusHeight`).
  By `TauCeti.IsMorseSmale.of_forall_ne_of_morseIndex_ne` only trajectories between distinct
  saddles need to be excluded. Along the flow `cos x` is nonincreasing, with derivative
  `-(2 + cos y) sin² x`, and at a saddle `f_ε = (cos x) (2 - √(1 + ε²))` depends only on `cos x`.
  Since `f_ε` strictly decreases along such a trajectory, it runs from a saddle with `cos x = 1` to
  one with `cos x = -1`. These have `ε sin y < 0` and `ε sin y > 0` respectively, while along the
  flow `ε sin y` can cross `0` only downwards: where `sin y = 0` its derivative is `-ε²`.

This is the classical picture of the nongeneric saddle connection of the upright torus and of its
perturbation into a Morse–Smale flow.

## Main results

* `TauCeti.lipschitzWith_gradient_tiltedTorusHeight`: the gradient is `(4 + |ε|)`-Lipschitz.
* `TauCeti.fderiv_tiltedTorusHeight_eq_zero_iff`,
  `TauCeti.isNondegenerateCriticalPoint_tiltedTorusHeight`,
  `TauCeti.morseIndex_tiltedTorusHeight_of_cos_lt_zero`,
  `TauCeti.morseIndex_tiltedTorusHeight_of_cos_eq_one_of_cos_pos`,
  `TauCeti.morseIndex_tiltedTorusHeight_of_cos_eq_neg_one_of_cos_pos`: the critical points, their
  nondegeneracy and their Morse indices.
* `TauCeti.mem_unstableSet_inter_stableSet_tiltedTorusHeight_zero`: the saddle connection of the
  upright torus.
* `TauCeti.not_isMorseSmale_tiltedTorusHeight_zero`: the upright torus is not Morse–Smale.
* `TauCeti.isMorseSmale_tiltedTorusHeight`: the tilted torus is Morse–Smale.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the upright torus and its tilt).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (the Morse–Smale condition).
-/

public section

open Set Filter Topology InnerProductSpace
open scoped Gradient NNReal RealInnerProductSpace

namespace TauCeti

/-- The height `(2 + cos y) cos x + ε sin y` of the torus of revolution
`((2 + cos y) cos x, (2 + cos y) sin x, sin y)` in the direction `(1, 0, ε)`, as a function on the
Euclidean plane. For `ε = 0` it is the height function of the upright torus. -/
noncomputable def tiltedTorusHeight (ε : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (2 + Real.cos (z 1)) * Real.cos (z 0) + ε * Real.sin (z 1)

variable {ε : ℝ}

private theorem two_add_cos_pos (y : ℝ) : 0 < 2 + Real.cos y := by
  linarith [Real.neg_one_le_cos y]

@[simp]
theorem tiltedTorusHeight_apply (z : EuclideanSpace ℝ (Fin 2)) :
    tiltedTorusHeight ε z = (2 + Real.cos (z 1)) * Real.cos (z 0) + ε * Real.sin (z 1) :=
  (rfl)

/-- The tilted torus height is smooth. -/
theorem contDiff_tiltedTorusHeight {n : WithTop ℕ∞} : ContDiff ℝ n (tiltedTorusHeight ε) := by
  have h0 := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff (n := n)
  have h1 := (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff (n := n)
  exact ((contDiff_const.add (Real.contDiff_cos.comp h1)).mul (Real.contDiff_cos.comp h0)).add
    (contDiff_const.mul (Real.contDiff_sin.comp h1))

/-- The basis vectors of the plane. -/
private noncomputable abbrev e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

private noncomputable abbrev e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

private theorem smul_e₀_add_smul_e₁_apply_zero (a b : ℝ) : (a • e₀ + b • e₁) 0 = a := by
  simp

private theorem smul_e₀_add_smul_e₁_apply_one (a b : ℝ) : (a • e₀ + b • e₁) 1 = b := by
  simp

/-- The gradient field `(-(2 + cos y) sin x, -sin y cos x + ε cos y)`. -/
private noncomputable def gradField (ε : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (-((2 + Real.cos (z 1)) * Real.sin (z 0))) • e₀ +
    (-(Real.sin (z 1) * Real.cos (z 0)) + ε * Real.cos (z 1)) • e₁

@[simp]
private theorem gradField_apply_zero (z : EuclideanSpace ℝ (Fin 2)) :
    gradField ε z 0 = -((2 + Real.cos (z 1)) * Real.sin (z 0)) := by
  simp [gradField]

@[simp]
private theorem gradField_apply_one (z : EuclideanSpace ℝ (Fin 2)) :
    gradField ε z 1 = -(Real.sin (z 1) * Real.cos (z 0)) + ε * Real.cos (z 1) := by
  simp [gradField]

private theorem hasGradientAt_tiltedTorusHeight (z : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (tiltedTorusHeight ε) (gradField ε z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hp0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z 0
  have hp1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z 1
  have hc0 := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z hp0
  have hc1 := (Real.hasDerivAt_cos (z 1)).comp_hasFDerivAt z hp1
  have hs1 := (Real.hasDerivAt_sin (z 1)).comp_hasFDerivAt z hp1
  refine ((((hasFDerivAt_const (2 : ℝ) z).add hc1).mul hc0).add (hs1.const_mul ε)).congr_fderiv ?_
  ext u
  simp only [add_apply, smul_apply, zero_apply, PiLp.proj_apply, Pi.add_apply,
    Function.comp_apply, smul_eq_mul, toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial, gradField_apply_zero, gradField_apply_one]
  ring

/-- The gradient of the tilted torus height. -/
private theorem gradient_tiltedTorusHeight : ∇ (tiltedTorusHeight ε) = gradField ε :=
  funext fun z ↦ (hasGradientAt_tiltedTorusHeight z).gradient

/-- The first coordinate of the gradient is `-(2 + cos y) sin x`. -/
@[simp]
theorem gradient_tiltedTorusHeight_apply_zero (z : EuclideanSpace ℝ (Fin 2)) :
    ∇ (tiltedTorusHeight ε) z 0 = -((2 + Real.cos (z 1)) * Real.sin (z 0)) := by
  rw [gradient_tiltedTorusHeight, gradField_apply_zero]

/-- The second coordinate of the gradient is `-sin y cos x + ε cos y`. -/
@[simp]
theorem gradient_tiltedTorusHeight_apply_one (z : EuclideanSpace ℝ (Fin 2)) :
    ∇ (tiltedTorusHeight ε) z 1 = -(Real.sin (z 1) * Real.cos (z 0)) + ε * Real.cos (z 1) := by
  rw [gradient_tiltedTorusHeight, gradField_apply_one]

/-- The entries `a = -(2 + cos y) cos x`, `b = sin x sin y` and `d = -(cos y cos x + ε sin y)` of
the Hessian matrix. -/
private noncomputable def hessA (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  -((2 + Real.cos (z 1)) * Real.cos (z 0))

private noncomputable def hessB (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sin (z 0) * Real.sin (z 1)

private noncomputable def hessD (ε : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  -(Real.cos (z 1) * Real.cos (z 0) + ε * Real.sin (z 1))

/-- The derivative of the gradient field, `u ↦ (a u₀ + b u₁, b u₀ + d u₁)`. -/
private noncomputable def hessField (ε : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (hessA z • (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
      hessB z • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).smulRight
    e₀ +
  (hessB z • (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) +
      hessD ε z • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).smulRight
    e₁

private theorem hessField_apply (z u : EuclideanSpace ℝ (Fin 2)) :
    hessField ε z u = (hessA z * u 0 + hessB z * u 1) • e₀ +
      (hessB z * u 0 + hessD ε z * u 1) • e₁ := by
  simp [hessField]

private theorem hasFDerivAt_gradField (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (gradField ε) (hessField ε z) z := by
  have hp0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z 0
  have hp1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z 1
  have hc0 := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z hp0
  have hs0 := (Real.hasDerivAt_sin (z 0)).comp_hasFDerivAt z hp0
  have hc1 := (Real.hasDerivAt_cos (z 1)).comp_hasFDerivAt z hp1
  have hs1 := (Real.hasDerivAt_sin (z 1)).comp_hasFDerivAt z hp1
  have g0 := (((hasFDerivAt_const (2 : ℝ) z).add hc1).mul hs0).neg.smul_const e₀
  have g1 := ((hs1.mul hc0).neg.add (hc1.const_mul ε)).smul_const e₁
  refine (g0.add g1).congr_fderiv ?_
  rw [hessField]
  congr 2 <;> ext u <;>
    simp only [add_apply, neg_apply, smul_apply, zero_apply, PiLp.proj_apply, Pi.add_apply,
      Function.comp_apply, smul_eq_mul, hessA, hessB, hessD] <;>
    ring

/-- The Hessian operator of the tilted torus height. -/
private theorem hessianOperator_tiltedTorusHeight (z : EuclideanSpace ℝ (Fin 2)) :
    hessianOperator (tiltedTorusHeight ε) z = hessField ε z := by
  rw [← fderiv_gradient, gradient_tiltedTorusHeight]
  exact (hasFDerivAt_gradField z).fderiv

/-- The Hessian quadratic form: `a u₀² + 2 b u₀ u₁ + d u₁²`. -/
private theorem hessianQuadraticForm_tiltedTorusHeight (z u : EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (tiltedTorusHeight ε) z u =
      hessA z * u 0 ^ 2 + 2 * hessB z * u 0 * u 1 + hessD ε z * u 1 ^ 2 := by
  rw [hessianQuadraticForm_apply, ← inner_hessianOperator_left,
    hessianOperator_tiltedTorusHeight, hessField_apply, PiLp.inner_apply, Fin.sum_univ_two,
    smul_e₀_add_smul_e₁_apply_zero, smul_e₀_add_smul_e₁_apply_one]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem abs_hessA_le (z : EuclideanSpace ℝ (Fin 2)) : |hessA z| ≤ 3 := by
  rw [hessA, abs_neg, abs_mul, abs_of_pos (two_add_cos_pos (z 1))]
  nlinarith [Real.abs_cos_le_one (z 0), Real.cos_le_one (z 1), abs_nonneg (Real.cos (z 0))]

private theorem abs_hessB_le (z : EuclideanSpace ℝ (Fin 2)) : |hessB z| ≤ 1 := by
  rw [hessB, abs_mul]
  nlinarith [Real.abs_sin_le_one (z 0), Real.abs_sin_le_one (z 1),
    abs_nonneg (Real.sin (z 0)), abs_nonneg (Real.sin (z 1))]

private theorem abs_hessD_le (z : EuclideanSpace ℝ (Fin 2)) : |hessD ε z| ≤ 1 + |ε| := by
  rw [hessD, abs_neg]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    nlinarith [Real.abs_cos_le_one (z 0), Real.abs_cos_le_one (z 1),
      abs_nonneg (Real.cos (z 0)), abs_nonneg (Real.cos (z 1))]
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- The operator norm of the derivative of the gradient field is at most `4 + |ε|`. -/
private theorem norm_hessField_le (z : EuclideanSpace ℝ (Fin 2)) :
    ‖hessField ε z‖ ≤ 4 + |ε| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  have ha := abs_hessA_le z
  have hb := abs_hessB_le z
  have hd := abs_hessD_le (ε := ε) z
  have hu : ‖u‖ = √(u 0 ^ 2 + u 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have hv : ‖hessField ε z u‖ = √((hessA z * u 0 + hessB z * u 1) ^ 2 +
      (hessB z * u 0 + hessD ε z * u 1) ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, hessField_apply]
    simp
  set a := hessA z
  set b := hessB z
  set d := hessD ε z
  -- Cauchy–Schwarz in each row, then the bounds on the entries.
  have hrow0 : (a * u 0 + b * u 1) ^ 2 ≤ (a ^ 2 + b ^ 2) * (u 0 ^ 2 + u 1 ^ 2) := by
    nlinarith [sq_nonneg (a * u 1 - b * u 0)]
  have hrow1 : (b * u 0 + d * u 1) ^ 2 ≤ (b ^ 2 + d ^ 2) * (u 0 ^ 2 + u 1 ^ 2) := by
    nlinarith [sq_nonneg (b * u 1 - d * u 0)]
  have ha2 : a ^ 2 ≤ 9 := by nlinarith [sq_abs a, abs_nonneg a]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_abs b, abs_nonneg b]
  have hd2 : d ^ 2 ≤ (1 + |ε|) ^ 2 := by nlinarith [sq_abs d, abs_nonneg d]
  have hsum : (a * u 0 + b * u 1) ^ 2 + (b * u 0 + d * u 1) ^ 2 ≤
      ((4 + |ε|) * √(u 0 ^ 2 + u 1 ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [abs_nonneg ε, (by positivity : 0 ≤ u 0 ^ 2 + u 1 ^ 2)]
  rw [hv, hu]
  exact (Real.sqrt_le_sqrt hsum).trans_eq (Real.sqrt_sq (by positivity))

/-- **The gradient is `(4 + |ε|)`-Lipschitz.** -/
theorem lipschitzWith_gradient_tiltedTorusHeight (ε : ℝ) :
    LipschitzWith (4 + ‖ε‖₊) (∇ (tiltedTorusHeight ε)) := by
  rw [gradient_tiltedTorusHeight]
  refine lipschitzWith_of_nnNorm_fderiv_le (fun z ↦ (hasFDerivAt_gradField z).differentiableAt)
    fun z ↦ ?_
  rw [(hasFDerivAt_gradField z).fderiv, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_add,
    coe_nnNorm, Real.norm_eq_abs]
  exact norm_hessField_le z

/-! ### Critical points and their Morse indices -/

/-- The critical points of the tilted torus height are the points with `sin x = 0` and
`sin y cos x = ε cos y`. -/
@[simp]
theorem fderiv_tiltedTorusHeight_eq_zero_iff {z : EuclideanSpace ℝ (Fin 2)} :
    fderiv ℝ (tiltedTorusHeight ε) z = 0 ↔
      Real.sin (z 0) = 0 ∧ Real.sin (z 1) * Real.cos (z 0) = ε * Real.cos (z 1) := by
  have h : fderiv ℝ (tiltedTorusHeight ε) z = 0 ↔ ∇ (tiltedTorusHeight ε) z = 0 := by
    simp [gradient]
  rw [h]
  constructor
  · intro h0
    have h0' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h0
    have h1' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) h0
    simp only [gradient_tiltedTorusHeight_apply_zero, gradient_tiltedTorusHeight_apply_one,
      PiLp.zero_apply, neg_eq_zero] at h0' h1'
    exact ⟨(mul_eq_zero.1 h0').resolve_left (two_add_cos_pos (z 1)).ne', by linarith⟩
  · rintro ⟨h0, h1⟩
    exact PiLp.ext <| Fin.forall_fin_two.2 ⟨by simp [h0], by simp [h1]⟩

variable {z : EuclideanSpace ℝ (Fin 2)}

/-- At a critical point `cos² x = 1`. -/
private theorem cos_sq_eq_one_of_fderiv_eq_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    Real.cos (z 0) ^ 2 = 1 := by
  have := (fderiv_tiltedTorusHeight_eq_zero_iff.1 hz).1
  nlinarith [Real.sin_sq_add_cos_sq (z 0)]

/-- At a critical point `cos y ≠ 0`: otherwise `sin y cos x = 0` would force `sin y = 0` too. -/
private theorem cos_ne_zero_of_fderiv_eq_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    Real.cos (z 1) ≠ 0 := by
  intro hc
  have h1 := (fderiv_tiltedTorusHeight_eq_zero_iff.1 hz).2
  have hx := cos_sq_eq_one_of_fderiv_eq_zero hz
  rw [hc, mul_zero] at h1
  have hs : Real.sin (z 1) = 0 :=
    (mul_eq_zero.1 h1).resolve_right fun h ↦ by rw [h] at hx; norm_num at hx
  nlinarith [Real.sin_sq_add_cos_sq (z 1), hs]

/-- At a critical point, `a cos x = -(2 + cos y)`, `b = 0` and `d cos x = -(1 + ε²) cos y` for the
entries of the Hessian matrix. -/
private theorem hess_of_fderiv_eq_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    hessA z * Real.cos (z 0) = -(2 + Real.cos (z 1)) ∧ hessB z = 0 ∧
      hessD ε z * Real.cos (z 0) = -((1 + ε ^ 2) * Real.cos (z 1)) := by
  obtain ⟨h0, h1⟩ := fderiv_tiltedTorusHeight_eq_zero_iff.1 hz
  have hx := cos_sq_eq_one_of_fderiv_eq_zero hz
  refine ⟨?_, by simp [hessB, h0], ?_⟩
  · rw [hessA]
    linear_combination -(2 + Real.cos (z 1)) * hx
  · rw [hessD]
    linear_combination -Real.cos (z 1) * hx - ε * h1

/-- At a critical point the Hessian quadratic form is diagonal: `a u₀² + d u₁²`. -/
private theorem hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero
    (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) (u : EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (tiltedTorusHeight ε) z u = ∑ i, ![hessA z, hessD ε z] i * u i ^ 2 := by
  rw [hessianQuadraticForm_tiltedTorusHeight, (hess_of_fderiv_eq_zero hz).2.1, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- At a critical point the negated Hessian quadratic form is `(-a) u₀² + (-d) u₁²`. -/
private theorem neg_hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero
    (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) (u : EuclideanSpace ℝ (Fin 2)) :
    (-hessianQuadraticForm (tiltedTorusHeight ε) z) u =
      ∑ i, -![hessA z, hessD ε z] i * u i ^ 2 := by
  simp only [neg_apply, hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero hz, neg_mul,
    Finset.sum_neg_distrib]

private theorem hessA_ne_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) : hessA z ≠ 0 := by
  intro h
  have := (hess_of_fderiv_eq_zero hz).1
  rw [h, zero_mul] at this
  linarith [two_add_cos_pos (z 1)]

private theorem hessD_ne_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) : hessD ε z ≠ 0 := by
  intro h
  have := (hess_of_fderiv_eq_zero hz).2.2
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact cos_ne_zero_of_fderiv_eq_zero hz
    ((mul_eq_zero.1 this).resolve_left (by positivity))

/-- **The critical points are nondegenerate.** -/
theorem isNondegenerateCriticalPoint_tiltedTorusHeight
    (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    IsNondegenerateCriticalPoint (tiltedTorusHeight ε) z := by
  refine isNondegenerateCriticalPoint_iff_separatingLeft.2
    ⟨contDiff_tiltedTorusHeight.contDiffAt, hz,
      (ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective _).2 fun v w hvw ↦ ?_⟩
  -- The Hessian bilinear form is `⟪hessField z v, w⟫`, and `hessField z` is injective.
  rw [← sub_eq_zero]
  have hB : fderiv ℝ (fderiv ℝ (tiltedTorusHeight ε)) z (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hD : hessField ε z (v - w) = 0 := by
    have h2 : fderiv ℝ (fderiv ℝ (tiltedTorusHeight ε)) z (v - w) (hessField ε z (v - w)) = 0 := by
      simp [hB]
    rw [← inner_hessianOperator_left, hessianOperator_tiltedTorusHeight] at h2
    exact inner_self_eq_zero.1 h2
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hD
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hD
  simp only [hessField_apply, (hess_of_fderiv_eq_zero hz).2.1] at h0 h1
  exact PiLp.ext <| Fin.forall_fin_two.2
    ⟨by simpa [hessA_ne_zero hz] using h0, by simpa [hessD_ne_zero hz] using h1⟩

/-- **The tilted torus height is a Morse function**: every critical point is nondegenerate. -/
theorem hasNondegenerateCriticalPointsOn_tiltedTorusHeight :
    HasNondegenerateCriticalPointsOn (tiltedTorusHeight ε) univ :=
  hasNondegenerateCriticalPointsOn_iff.2 fun _ _ hz ↦
    isNondegenerateCriticalPoint_tiltedTorusHeight hz

/-- **The saddles.** A critical point with `cos y < 0` has Morse index `1`. -/
theorem morseIndex_tiltedTorusHeight_of_cos_lt_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0)
    (hy : Real.cos (z 1) < 0) : morseIndex (tiltedTorusHeight ε) z = 1 := by
  have hnd := isNondegenerateCriticalPoint_tiltedTorusHeight hz
  obtain ⟨ha, -, hd⟩ := hess_of_fderiv_eq_zero hz
  have hx := cos_sq_eq_one_of_fderiv_eq_zero hz
  -- The diagonal entries `a` and `d` of the Hessian have opposite signs.
  have had : hessA z * hessD ε z < 0 := by
    have hprod : (hessA z * Real.cos (z 0)) * (hessD ε z * Real.cos (z 0)) < 0 := by
      rw [ha, hd, neg_mul_neg]
      exact mul_neg_of_pos_of_neg (two_add_cos_pos (z 1))
        (mul_neg_of_pos_of_neg (by positivity) hy)
    have heq : hessA z * hessD ε z =
        (hessA z * Real.cos (z 0)) * (hessD ε z * Real.cos (z 0)) := by
      linear_combination (-(hessA z * hessD ε z)) * hx
    rw [heq]
    exact hprod
  have h0 : morseIndex (tiltedTorusHeight ε) z ≠ 0 := fun h ↦ by
    obtain ⟨ha, hd⟩ : 0 < hessA z ∧ 0 < hessD ε z := by
      simpa [Fin.forall_fin_two] using (EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq
        (hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero hz)).1
          (hnd.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero.2 h)
    linarith [mul_pos ha hd]
  have h2 : morseIndex (tiltedTorusHeight ε) z ≠ 2 := fun h ↦ by
    obtain ⟨ha, hd⟩ : hessA z < 0 ∧ hessD ε z < 0 := by
      simpa [Fin.forall_fin_two] using (EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq
        (neg_hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero hz)).1
          ((neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank
            (f := tiltedTorusHeight ε) (x := z)).2 (by rw [h, finrank_euclideanSpace_fin]))
    linarith [mul_pos_of_neg_of_neg ha hd]
  have hle : morseIndex (tiltedTorusHeight ε) z ≤ 2 := by
    simpa using morseIndex_le_finrank (f := tiltedTorusHeight ε) (x := z)
  omega

/-- **The maxima.** A critical point with `cos x = 1` and `cos y > 0` has Morse index `2`. -/
theorem morseIndex_tiltedTorusHeight_of_cos_eq_one_of_cos_pos
    (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) (hx : Real.cos (z 0) = 1)
    (hy : 0 < Real.cos (z 1)) : morseIndex (tiltedTorusHeight ε) z = 2 := by
  obtain ⟨ha, -, hd⟩ := hess_of_fderiv_eq_zero hz
  rw [hx, mul_one] at ha hd
  have hd' : hessD ε z < 0 := by rw [hd]; nlinarith [sq_nonneg ε]
  have ha' : hessA z < 0 := by rw [ha]; linarith
  have hpd : (-hessianQuadraticForm (tiltedTorusHeight ε) z).PosDef :=
    (EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq
      (neg_hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero hz)).2
        (by simp [Fin.forall_fin_two, ha', hd'])
  simpa using neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank.1 hpd

/-- **The minima.** A critical point with `cos x = -1` and `cos y > 0` has Morse index `0`. -/
theorem morseIndex_tiltedTorusHeight_of_cos_eq_neg_one_of_cos_pos
    (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) (hx : Real.cos (z 0) = -1)
    (hy : 0 < Real.cos (z 1)) : morseIndex (tiltedTorusHeight ε) z = 0 := by
  obtain ⟨ha, -, hd⟩ := hess_of_fderiv_eq_zero hz
  rw [hx, mul_neg_one, neg_inj] at ha hd
  have hd' : 0 < hessD ε z := by rw [hd]; positivity
  have ha' : 0 < hessA z := by rw [ha]; linarith
  exact morseIndex_eq_zero_of_posDef
    ((EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq
      (hessianQuadraticForm_tiltedTorusHeight_of_fderiv_eq_zero hz)).2
        (by simp [Fin.forall_fin_two, ha', hd']))

/-! ### The saddle connection of the upright torus -/

/-- The trajectory `(2 arctan eᵗ, π)` of the upright torus height, along the invariant line
`y = π`. -/
private noncomputable def saddleConnection (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (2 * Real.arctan (Real.exp t)) • e₀ + Real.pi • e₁

@[simp]
private theorem saddleConnection_apply_zero (t : ℝ) :
    saddleConnection t 0 = 2 * Real.arctan (Real.exp t) :=
  smul_e₀_add_smul_e₁_apply_zero _ _

@[simp]
private theorem saddleConnection_apply_one (t : ℝ) : saddleConnection t 1 = Real.pi :=
  smul_e₀_add_smul_e₁_apply_one _ _

private theorem saddleConnection_eq_comp :
    saddleConnection = (fun a : ℝ ↦ (2 * a) • e₀ + Real.pi • e₁) ∘ (Real.arctan ∘ Real.exp) := by
  funext t
  simp only [saddleConnection, Function.comp_apply]

private theorem isIntegralCurve_saddleConnection :
    IsIntegralCurve saddleConnection fun _ w ↦ -∇ (tiltedTorusHeight 0) w := by
  intro t
  rw [gradient_tiltedTorusHeight]
  have hA := ((Real.hasDerivAt_arctan (Real.exp t)).comp t (Real.hasDerivAt_exp t)).const_mul 2
  refine ((hA.smul_const e₀).add_const (Real.pi • e₁)).congr_deriv ?_
  refine PiLp.ext <| Fin.forall_fin_two.2 ⟨?_, by simp⟩
  simp only [PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one, PiLp.neg_apply,
    gradField_apply_zero, saddleConnection_apply_zero, saddleConnection_apply_one,
    Real.sin_two_mul_arctan, Real.cos_pi]
  field_simp
  norm_num

/-- **The saddle connection of the upright torus.** For the height function
`(2 + cos y) cos x` of the upright torus, the point `(π / 2, π)` lies on the trajectory
`(2 arctan eᵗ, π)` from the saddle `(0, π)` to the saddle `(π, π)`. -/
theorem mem_unstableSet_inter_stableSet_tiltedTorusHeight_zero :
    !₂[Real.pi / 2, Real.pi] ∈
      Flow.unstableSet (negativeGradientFlow (tiltedTorusHeight 0)
          (lipschitzWith_gradient_tiltedTorusHeight 0)) !₂[0, Real.pi] ∩
        Flow.stableSet (negativeGradientFlow (tiltedTorusHeight 0)
          (lipschitzWith_gradient_tiltedTorusHeight 0)) !₂[Real.pi, Real.pi] := by
  have hflow := eq_negativeGradientFlow (tiltedTorusHeight 0)
    (lipschitzWith_gradient_tiltedTorusHeight 0) isIntegralCurve_saddleConnection
  have h0 : saddleConnection 0 = !₂[Real.pi / 2, Real.pi] := by
    refine PiLp.ext <| Fin.forall_fin_two.2 ⟨?_, by simp⟩
    rw [saddleConnection_apply_zero, Real.exp_zero, Real.arctan_one]
    simp only [Matrix.cons_val_zero]
    ring
  rw [← h0]
  have hc : Continuous fun a : ℝ ↦ (2 * a) • e₀ + Real.pi • e₁ := by fun_prop
  refine ⟨Flow.mem_unstableSet.2 (Tendsto.congr hflow ?_),
    Flow.mem_stableSet.2 (Tendsto.congr hflow ?_)⟩
  · have harc : Tendsto (Real.arctan ∘ Real.exp) atBot (𝓝 0) := by
      have h := (Real.continuous_arctan.tendsto 0).comp Real.tendsto_exp_atBot
      rwa [Real.arctan_zero] at h
    rw [saddleConnection_eq_comp]
    convert (hc.tendsto 0).comp harc using 2
    exact PiLp.ext <| Fin.forall_fin_two.2 ⟨by simp, by simp⟩
  · have harc : Tendsto (Real.arctan ∘ Real.exp) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp Real.tendsto_exp_atTop
    rw [saddleConnection_eq_comp]
    convert (hc.tendsto (Real.pi / 2)).comp harc using 2
    refine PiLp.ext <| Fin.forall_fin_two.2 ⟨?_, by simp⟩
    rw [smul_e₀_add_smul_e₁_apply_zero]
    simp only [Matrix.cons_val_zero]
    ring

/-- **The upright torus is not Morse–Smale.** The negative gradient flow of the height function
`(2 + cos y) cos x` has a trajectory between the saddles `(0, π)` and `(π, π)`, both of Morse
index `1`. -/
theorem not_isMorseSmale_tiltedTorusHeight_zero :
    ¬IsMorseSmale (tiltedTorusHeight 0) (lipschitzWith_gradient_tiltedTorusHeight 0) := by
  intro h
  have hp : fderiv ℝ (tiltedTorusHeight 0) !₂[0, Real.pi] = 0 :=
    fderiv_tiltedTorusHeight_eq_zero_iff.2 (by simp)
  have hq : fderiv ℝ (tiltedTorusHeight 0) !₂[Real.pi, Real.pi] = 0 :=
    fderiv_tiltedTorusHeight_eq_zero_iff.2 (by simp)
  have hind : morseIndex (tiltedTorusHeight 0) !₂[0, Real.pi] ≤
      morseIndex (tiltedTorusHeight 0) !₂[Real.pi, Real.pi] := by
    rw [morseIndex_tiltedTorusHeight_of_cos_lt_zero hp (by simp),
      morseIndex_tiltedTorusHeight_of_cos_lt_zero hq (by simp)]
  have hpq : (!₂[0, Real.pi] : EuclideanSpace ℝ (Fin 2)) ≠ !₂[Real.pi, Real.pi] := fun he ↦ by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) he
    simp only [Matrix.cons_val_zero] at this
    exact Real.pi_ne_zero this.symm
  have := h.unstableSet_inter_stableSet_eq_empty
    (isNondegenerateCriticalPoint_tiltedTorusHeight hp)
    (isNondegenerateCriticalPoint_tiltedTorusHeight hq) contDiff_tiltedTorusHeight hpq hind
  rw [Set.eq_empty_iff_forall_notMem] at this
  exact this _ mem_unstableSet_inter_stableSet_tiltedTorusHeight_zero

/-! ### The tilted torus is Morse–Smale -/

/-- At a critical point `sin y = ε cos x cos y`. -/
private theorem sin_eq_of_fderiv_eq_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    Real.sin (z 1) = ε * Real.cos (z 0) * Real.cos (z 1) := by
  have h1 := (fderiv_tiltedTorusHeight_eq_zero_iff.1 hz).2
  have hx := cos_sq_eq_one_of_fderiv_eq_zero hz
  linear_combination Real.cos (z 0) * h1 - Real.sin (z 1) * hx

/-- At a critical point `w = (1 + ε²) cos y` satisfies `w² = 1 + ε²`. -/
private theorem sq_eq_of_fderiv_eq_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    ((1 + ε ^ 2) * Real.cos (z 1)) ^ 2 = 1 + ε ^ 2 := by
  have hs := sin_eq_of_fderiv_eq_zero hz
  have hx := cos_sq_eq_one_of_fderiv_eq_zero hz
  have hsc := Real.sin_sq_add_cos_sq (z 1)
  linear_combination (1 + ε ^ 2) * hsc -
    (1 + ε ^ 2) * (Real.sin (z 1) + ε * Real.cos (z 0) * Real.cos (z 1)) * hs -
    (1 + ε ^ 2) * ε ^ 2 * Real.cos (z 1) ^ 2 * hx

/-- At a critical point the value is `cos x (2 + (1 + ε²) cos y)`. -/
private theorem tiltedTorusHeight_eq_of_fderiv_eq_zero (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0) :
    tiltedTorusHeight ε z = Real.cos (z 0) * (2 + (1 + ε ^ 2) * Real.cos (z 1)) := by
  rw [tiltedTorusHeight_apply, sin_eq_of_fderiv_eq_zero hz]
  ring

/-- A critical point whose Morse index is neither `0` nor `2` has `cos y < 0`. -/
private theorem cos_lt_zero_of_morseIndex_ne (hz : fderiv ℝ (tiltedTorusHeight ε) z = 0)
    (h0 : morseIndex (tiltedTorusHeight ε) z ≠ 0) (h2 : morseIndex (tiltedTorusHeight ε) z ≠ 2) :
    Real.cos (z 1) < 0 := by
  by_contra hy
  have hy' : 0 < Real.cos (z 1) :=
    lt_of_le_of_ne (not_lt.1 hy) (cos_ne_zero_of_fderiv_eq_zero hz).symm
  rcases Real.sin_eq_zero_iff_cos_eq.1 (fderiv_tiltedTorusHeight_eq_zero_iff.1 hz).1 with hx | hx
  · exact h2 (morseIndex_tiltedTorusHeight_of_cos_eq_one_of_cos_pos hz hx hy')
  · exact h0 (morseIndex_tiltedTorusHeight_of_cos_eq_neg_one_of_cos_pos hz hx hy')

/-- **Comparing two saddles.** Both saddles have the value `cos x (2 + w)` with the same
`w = (1 + ε²) cos y = -√(1 + ε²)`, so their values agree when their values of `cos x` do. Hence if
`cos x` at `q` is at most that at `p` and the value at `q` is below that at `p`, then `cos x = 1` at
`p` and `cos x = -1` at `q`. -/
private theorem cos_eq_one_and_cos_eq_neg_one_of_lt {p q : EuclideanSpace ℝ (Fin 2)}
    (hpc : fderiv ℝ (tiltedTorusHeight ε) p = 0) (hqc : fderiv ℝ (tiltedTorusHeight ε) q = 0)
    (hpy : Real.cos (p 1) < 0) (hqy : Real.cos (q 1) < 0)
    (hcos : Real.cos (q 0) ≤ Real.cos (p 0))
    (hlt : tiltedTorusHeight ε q < tiltedTorusHeight ε p) :
    Real.cos (p 0) = 1 ∧ Real.cos (q 0) = -1 := by
  have hwp := sq_eq_of_fderiv_eq_zero hpc
  have hwq := sq_eq_of_fderiv_eq_zero hqc
  have hwp0 : (1 + ε ^ 2) * Real.cos (p 1) < 0 := mul_neg_of_pos_of_neg (by positivity) hpy
  have hwq0 : (1 + ε ^ 2) * Real.cos (q 1) < 0 := mul_neg_of_pos_of_neg (by positivity) hqy
  have hw : (1 + ε ^ 2) * Real.cos (p 1) = (1 + ε ^ 2) * Real.cos (q 1) := by nlinarith
  have hcpq : Real.cos (q 0) < Real.cos (p 0) := hcos.lt_of_ne fun h ↦ by
    rw [tiltedTorusHeight_eq_of_fderiv_eq_zero hpc, tiltedTorusHeight_eq_of_fderiv_eq_zero hqc,
      ← hw, h] at hlt
    exact lt_irrefl _ hlt
  constructor
  · rcases Real.sin_eq_zero_iff_cos_eq.1 (fderiv_tiltedTorusHeight_eq_zero_iff.1 hpc).1 with h | h
    · exact h
    · linarith [Real.neg_one_le_cos (q 0)]
  · rcases Real.sin_eq_zero_iff_cos_eq.1 (fderiv_tiltedTorusHeight_eq_zero_iff.1 hqc).1 with h | h
    · linarith [Real.cos_le_one (p 0)]
    · exact h

/-- Along the negative gradient flow of `f_ε` the function `cos x` is antitone: its derivative is
`-sin x · (2 + cos y) sin x = -(2 + cos y) sin² x`. -/
private theorem antitone_cos_negativeGradientFlow (y : EuclideanSpace ℝ (Fin 2)) :
    Antitone fun t ↦ Real.cos (negativeGradientFlow (tiltedTorusHeight ε)
      (lipschitzWith_gradient_tiltedTorusHeight ε) t y 0) := by
  set Φ := negativeGradientFlow (tiltedTorusHeight ε) (lipschitzWith_gradient_tiltedTorusHeight ε)
  refine antitone_of_hasDerivAt_nonpos (f' := fun s ↦
    -Real.sin (Φ s y 0) * ((2 + Real.cos (Φ s y 1)) * Real.sin (Φ s y 0))) (fun s ↦ ?_) fun s ↦ ?_
  · have hx : HasDerivAt (fun s ↦ Φ s y 0) ((2 + Real.cos (Φ s y 1)) * Real.sin (Φ s y 0)) s :=
      (hasDerivAt_negativeGradientFlow_apply _ _ y 0 s).congr_deriv (by
        rw [gradient_tiltedTorusHeight_apply_zero, neg_neg])
    exact (Real.hasDerivAt_cos _).comp s hx
  · rw [Pi.zero_apply]
    nlinarith [mul_nonneg (two_add_cos_pos (Φ s y 1)).le (sq_nonneg (Real.sin (Φ s y 0)))]

/-- Along the negative gradient flow of `f_ε`, `ε ≠ 0`, the function `ε sin y` can cross `0` only
downwards: once it is at most `0`, it stays at most `0`. Where `sin y = 0` its derivative is
`ε cos y (sin y cos x - ε cos y) = -ε²`. -/
private theorem mul_sin_negativeGradientFlow_nonpos (hε : ε ≠ 0) (y : EuclideanSpace ℝ (Fin 2))
    {t₀ t : ℝ} (ht : t₀ ≤ t)
    (h₀ : ε * Real.sin (negativeGradientFlow (tiltedTorusHeight ε)
      (lipschitzWith_gradient_tiltedTorusHeight ε) t₀ y 1) ≤ 0) :
    ε * Real.sin (negativeGradientFlow (tiltedTorusHeight ε)
      (lipschitzWith_gradient_tiltedTorusHeight ε) t y 1) ≤ 0 := by
  set Φ := negativeGradientFlow (tiltedTorusHeight ε) (lipschitzWith_gradient_tiltedTorusHeight ε)
  have hγ (s : ℝ) : HasDerivAt (fun s ↦ Φ s y 1)
      (Real.sin (Φ s y 1) * Real.cos (Φ s y 0) - ε * Real.cos (Φ s y 1)) s :=
    (hasDerivAt_negativeGradientFlow_apply _ _ y 1 s).congr_deriv (by
      rw [gradient_tiltedTorusHeight_apply_one]
      ring)
  have hg (s : ℝ) : HasDerivAt (fun s ↦ ε * Real.sin (Φ s y 1))
      (ε * (Real.cos (Φ s y 1) *
        (Real.sin (Φ s y 1) * Real.cos (Φ s y 0) - ε * Real.cos (Φ s y 1)))) s :=
    ((Real.hasDerivAt_sin _).comp s (hγ s)).const_mul ε
  refine image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ ↦ 0) (B' := fun _ ↦ 0)
    (fun s _ ↦ (hg s).continuousAt.continuousWithinAt) (fun s _ ↦ (hg s).hasDerivWithinAt) h₀
    continuousOn_const (fun _ _ ↦ hasDerivWithinAt_const _ _ _) (fun s _ hs ↦ ?_) ⟨ht, le_rfl⟩
  -- Where `ε sin y = 0`, `sin y = 0`, `cos² y = 1` and the derivative is `-ε²`.
  have hsin : Real.sin (Φ s y 1) = 0 := (mul_eq_zero.1 hs).resolve_left hε
  have hcos : Real.cos (Φ s y 1) ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq (Φ s y 1)]
  rw [hsin]
  nlinarith [sq_pos_of_ne_zero hε]

/-- **The tilted torus is Morse–Smale.** For `ε ≠ 0`, the negative gradient flow of
`(2 + cos y) cos x + ε sin y` is Morse–Smale. Only trajectories between distinct saddles need to be
excluded. Along the flow `cos x` does not increase, and at a saddle the value is
`cos x (2 - √(1 + ε²))`, so as the value strictly decreases such a trajectory would run from a
saddle with `cos x = 1`, where `ε sin y < 0`, to one with `cos x = -1`, where `ε sin y > 0`; but
`ε sin y` crosses `0` only downwards. -/
theorem isMorseSmale_tiltedTorusHeight (hε : ε ≠ 0) :
    IsMorseSmale (tiltedTorusHeight ε) (lipschitzWith_gradient_tiltedTorusHeight ε) := by
  refine IsMorseSmale.of_forall_ne_of_morseIndex_ne contDiff_tiltedTorusHeight
    fun p q y hp hq hpq hp0 hp2 hq0 hq2 hy ↦ (?_ : False).elim
  rw [finrank_euclideanSpace_fin] at hp2 hq2
  have hpc := hp.fderiv_eq_zero
  have hqc := hq.fderiv_eq_zero
  have hpy := cos_lt_zero_of_morseIndex_ne hpc hp0 hp2
  have hqy := cos_lt_zero_of_morseIndex_ne hqc hq0 hq2
  set Φ := negativeGradientFlow (tiltedTorusHeight ε) (lipschitzWith_gradient_tiltedTorusHeight ε)
  -- `cos x` does not increase and the value decreases strictly from `p` to `q`, so
  -- `cos (p 0) = 1` and `cos (q 0) = -1`.
  have hC : Continuous fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.cos (w 0) := by fun_prop
  have hanti := antitone_cos_negativeGradientFlow (ε := ε) y
  have hcos : Real.cos (q 0) ≤ Real.cos (p 0) :=
    (le_of_tendsto ((hC.tendsto q).comp (Flow.mem_stableSet.1 hy.2))
      (eventually_atTop.2 ⟨0, fun _ ht ↦ hanti ht⟩)).trans
      (ge_of_tendsto ((hC.tendsto p).comp (Flow.mem_unstableSet.1 hy.1))
        (eventually_atBot.2 ⟨0, fun _ ht ↦ hanti ht⟩))
  have hd : Differentiable ℝ (tiltedTorusHeight ε) :=
    (contDiff_tiltedTorusHeight (n := 1)).differentiable one_ne_zero
  have hlt := (isNegativeGradient_negativeGradientFlow (tiltedTorusHeight ε)
    (lipschitzWith_gradient_tiltedTorusHeight ε)).value_lt_of_mem_unstableSet_inter_stableSet
    (fun _ ↦ hd.differentiableAt) hd.continuous.continuousAt hd.continuous.continuousAt hpq hy
  obtain ⟨hcp, hcq⟩ := cos_eq_one_and_cos_eq_neg_one_of_lt hpc hqc hpy hqy hcos hlt
  -- So `ε sin y` is negative at `p` and positive at `q`.
  have hVp : ε * Real.sin (p 1) < 0 := by
    rw [sin_eq_of_fderiv_eq_zero hpc, hcp]
    nlinarith [sq_pos_of_ne_zero hε]
  have hVq : 0 < ε * Real.sin (q 1) := by
    rw [sin_eq_of_fderiv_eq_zero hqc, hcq]
    nlinarith [sq_pos_of_ne_zero hε]
  have hV : Continuous fun w : EuclideanSpace ℝ (Fin 2) ↦ ε * Real.sin (w 1) := by fun_prop
  have hbot : Tendsto (fun t ↦ ε * Real.sin (Φ t y 1)) atBot (𝓝 (ε * Real.sin (p 1))) :=
    (hV.tendsto p).comp (Flow.mem_unstableSet.1 hy.1)
  have htop : Tendsto (fun t ↦ ε * Real.sin (Φ t y 1)) atTop (𝓝 (ε * Real.sin (q 1))) :=
    (hV.tendsto q).comp (Flow.mem_stableSet.1 hy.2)
  obtain ⟨t₀, ht₀⟩ := (hbot.eventually (gt_mem_nhds hVp)).exists
  have hle : ε * Real.sin (q 1) ≤ 0 :=
    le_of_tendsto htop (eventually_atTop.2 ⟨t₀, fun t ht ↦
      mul_sin_negativeGradientFlow_nonpos hε y ht ht₀.le⟩)
  linarith

end TauCeti
