/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# A saddle connection on the torus and its perturbation

The torus of revolution with radii `R > r > 0`, standing upright, has the height function
`(R + r cos φ) cos θ` in the angles `θ` and `φ`. Its four critical points are a maximum `(0, 0)`,
a minimum `(π, 0)` and two saddles `(0, π)` and `(π, π)`, of index `1`. Along the circle `φ = π`
the negative-gradient flow runs from one saddle to the other: this is the standard example of a
gradient flow which is not Morse–Smale, since a trajectory between two critical points of the same
index has expected dimension `-1`. Tilting the torus slightly breaks the saddle connection. This
file works this example out for the flat metric `dθ² + dφ²` on the doubly periodic functions

`torusHeight R r ε (θ, φ) = (R + r cos φ) cos θ + ε sin φ`

on the plane `ℝ²` covering the torus, where the negative-gradient flow is defined by the
Euclidean framework of `TauCeti.Analysis.Calculus.Morse` (the gradient is globally Lipschitz,
`TauCeti.lipschitzWith_gradient_torusHeight`).

* **Critical points.** For `|r| < R` the critical points are the points with `sin θ = 0` and
  `ε cos φ = r sin φ cos θ`. With `ρ = √(r² + ε²) > 0` every one of them is nondegenerate, and there
  are four kinds, up to the period lattice: a maximum of value `R + ρ`, saddles of values `R - ρ`
  and `ρ - R`, and a minimum of value `-R - ρ`.
* **The saddle connection.** For `ε = 0`, on a circle `φ = φ₀` with `sin φ₀ = 0` and
  `R + r cos φ₀ > 0`, the point `(π / 2, φ₀)` lies on the trajectory
  `t ↦ (2 arctan (e^{(R + r cos φ₀) t}), φ₀)` from `(0, φ₀)` to `(π, φ₀)`. For `|r| < R` and
  `r ≠ 0`, choosing `φ₀ = π` if `r > 0` and `φ₀ = 0` if `r < 0` makes both endpoints saddles, so
  the flow is not Morse–Smale (`TauCeti.not_isMorseSmale_torusHeight_zero`).
* **The perturbation.** For `ε ≠ 0` and `ρ < R` the flow is Morse–Smale
  (`TauCeti.isMorseSmale_torusHeight`); in particular no trajectory joins two saddles
  (`TauCeti.IsMorseSmale.unstableSet_inter_stableSet_eq_empty`). By
  `TauCeti.IsMorseSmale.of_forall_ne_of_morseIndex_ne` only trajectories between distinct saddles
  need to be examined, and a trajectory between distinct critical points lowers the value. This
  leaves only trajectories from a saddle of value `R - ρ`, where `ρ sin φ = -ε`, to a saddle of
  value `ρ - R`, where `ρ sin φ = ε`. Along such a trajectory `ε sin φ` would pass from negative to
  positive values, but wherever it vanishes its derivative is `-ε² < 0`, so it cannot.

## Main results

* `TauCeti.torusHeight`: the perturbed height function of the torus of revolution.
* `TauCeti.fderiv_torusHeight_eq_zero_iff`, `TauCeti.fderiv_torusHeight_eq_zero_iff_cos_eq`: its
  critical points.
* `TauCeti.isNondegenerateCriticalPoint_torusHeight`: they are nondegenerate.
* `TauCeti.morseIndex_torusHeight_eq_two`, `TauCeti.morseIndex_torusHeight_eq_one`,
  `TauCeti.morseIndex_torusHeight_eq_zero`: Morse indices.
* `TauCeti.morseIndex_torusHeight_of_fderiv_eq_zero`: the index and value of each critical point.
* `TauCeti.mem_unstableSet_inter_stableSet_torusHeight_zero`: the saddle connection for `ε = 0`.
* `TauCeti.not_isMorseSmale_torusHeight_zero`: for `ε = 0` the flow is not Morse–Smale.
* `TauCeti.isMorseSmale_torusHeight`: for small `ε ≠ 0` it is.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002 (the upright torus, whose height function has trajectories
  between its two saddles and is not Morse–Smale, and its perturbation by tilting).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (the Morse–Smale condition, with the height function of the upright torus as the
  example of a pseudo-gradient that does not satisfy it).
-/

public section

open Filter Set Topology Real
open scoped Gradient NNReal RealInnerProductSpace

namespace TauCeti

local notation "𝔼" => EuclideanSpace ℝ (Fin 2)

local notation "pr₀" => (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

local notation "pr₁" => (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

local notation "e₀" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

local notation "e₁" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- The height function `(R + r cos φ) cos θ + ε sin φ` of a torus of revolution with radii `R`
and `r`, perturbed by `ε sin φ`, in the angles `θ = z 0` and `φ = z 1`. It is `2π`-periodic in
both angles. -/
noncomputable def torusHeight (R r ε : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (R + r * cos (z 1)) * cos (z 0) + ε * sin (z 1)

variable {R r ε : ℝ}

/-- The value of the perturbed torus height. -/
@[simp]
theorem torusHeight_apply (z : EuclideanSpace ℝ (Fin 2)) :
    torusHeight R r ε z = (R + r * cos (z 1)) * cos (z 0) + ε * sin (z 1) :=
  (rfl)

/-- The perturbed torus height is smooth. -/
theorem contDiff_torusHeight {n : WithTop ℕ∞} : ContDiff ℝ n (torusHeight R r ε) := by
  have h0 : ContDiff ℝ n fun z : 𝔼 ↦ z 0 := ContinuousLinearMap.contDiff pr₀
  have h1 : ContDiff ℝ n fun z : 𝔼 ↦ z 1 := ContinuousLinearMap.contDiff pr₁
  exact ((contDiff_const.add (contDiff_const.mul (contDiff_cos.comp h1))).mul
    (contDiff_cos.comp h0)).add (contDiff_const.mul (contDiff_sin.comp h1))

private theorem hasFDerivAt_cos_apply (i : Fin 2) (z : 𝔼) :
    HasFDerivAt (fun w : 𝔼 ↦ cos (w i)) (-sin (z i) • (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ)) z := by
  simpa [Function.comp_def] using (hasDerivAt_cos (z i)).comp_hasFDerivAt z
    (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).hasFDerivAt

private theorem hasFDerivAt_sin_apply (i : Fin 2) (z : 𝔼) :
    HasFDerivAt (fun w : 𝔼 ↦ sin (w i)) (cos (z i) • (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ)) z := by
  simpa [Function.comp_def] using (hasDerivAt_sin (z i)).comp_hasFDerivAt z
    (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).hasFDerivAt

/-- The gradient field `(-(R + r cos φ) sin θ, ε cos φ - r sin φ cos θ)`. -/
private noncomputable def gradField (R r ε : ℝ) (z : 𝔼) : 𝔼 :=
  (-((R + r * cos (z 1)) * sin (z 0))) • e₀ + (ε * cos (z 1) - r * sin (z 1) * cos (z 0)) • e₁

private theorem hasGradientAt_torusHeight (z : 𝔼) :
    HasGradientAt (torusHeight R r ε) (gradField R r ε z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((((hasFDerivAt_cos_apply 1 z).const_mul r).const_add R).mul
    (hasFDerivAt_cos_apply 0 z)).add ((hasFDerivAt_sin_apply 1 z).const_mul ε)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u ↦ ?_)
  simp [gradField, PiLp.inner_apply]
  ring

private theorem gradient_torusHeight : ∇ (torusHeight R r ε) = gradField R r ε :=
  funext fun z ↦ (hasGradientAt_torusHeight z).gradient

/-- The first coordinate of the gradient is `-(R + r cos φ) sin θ`. -/
@[simp]
theorem gradient_torusHeight_apply_zero (z : EuclideanSpace ℝ (Fin 2)) :
    ∇ (torusHeight R r ε) z 0 = -((R + r * cos (z 1)) * sin (z 0)) := by
  simp [gradient_torusHeight, gradField]

/-- The second coordinate of the gradient is `ε cos φ - r sin φ cos θ`. -/
@[simp]
theorem gradient_torusHeight_apply_one (z : EuclideanSpace ℝ (Fin 2)) :
    ∇ (torusHeight R r ε) z 1 = ε * cos (z 1) - r * sin (z 1) * cos (z 0) := by
  simp [gradient_torusHeight, gradField]

/-- The derivative of the gradient field, the Hessian of the perturbed torus height:
`u ↦ (a u₀ + b u₁, b u₀ + c u₁)` with `a = -(R + r cos φ) cos θ`, `b = r sin φ sin θ` and
`c = -ε sin φ - r cos φ cos θ`. -/
private noncomputable def hessField (R r ε : ℝ) (z : 𝔼) : 𝔼 →L[ℝ] 𝔼 :=
  ((-((R + r * cos (z 1)) * cos (z 0))) • pr₀ + (r * sin (z 1) * sin (z 0)) • pr₁).smulRight e₀ +
    ((r * sin (z 1) * sin (z 0)) • pr₀ +
      (-(ε * sin (z 1)) - r * cos (z 1) * cos (z 0)) • pr₁).smulRight e₁

private theorem hessField_apply (z u : 𝔼) :
    hessField R r ε z u =
      (-((R + r * cos (z 1)) * cos (z 0)) * u 0 + r * sin (z 1) * sin (z 0) * u 1) • e₀ +
        (r * sin (z 1) * sin (z 0) * u 0 +
          (-(ε * sin (z 1)) - r * cos (z 1) * cos (z 0)) * u 1) • e₁ := by
  simp [hessField]

private theorem hasFDerivAt_gradField (z : 𝔼) :
    HasFDerivAt (gradField R r ε) (hessField R r ε z) z := by
  have h₀ := ((((hasFDerivAt_cos_apply 1 z).const_mul r).const_add R).mul
    (hasFDerivAt_sin_apply 0 z)).neg
  have h₁ := ((hasFDerivAt_cos_apply 1 z).const_mul ε).sub
    (((hasFDerivAt_sin_apply 1 z).const_mul r).mul (hasFDerivAt_cos_apply 0 z))
  refine ((h₀.smul_const e₀).add (h₁.smul_const e₁)).congr_fderiv
    (ContinuousLinearMap.ext fun u ↦ ?_)
  ext i
  fin_cases i <;> simp [hessField] <;> ring

private theorem hessianOperator_torusHeight (z : 𝔼) :
    hessianOperator (torusHeight R r ε) z = hessField R r ε z := by
  rw [← fderiv_gradient, gradient_torusHeight]
  exact (hasFDerivAt_gradField z).fderiv

/-- The Hessian quadratic form of the perturbed torus height:
`a u₀² + 2 b u₀ u₁ + c u₁²` with `a = -(R + r cos φ) cos θ`, `b = r sin φ sin θ` and
`c = -ε sin φ - r cos φ cos θ`. -/
theorem hessianQuadraticForm_torusHeight (z u : EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (torusHeight R r ε) z u =
      -((R + r * cos (z 1)) * cos (z 0)) * u 0 ^ 2 + 2 * (r * sin (z 1) * sin (z 0)) * u 0 * u 1 +
        (-(ε * sin (z 1)) - r * cos (z 1) * cos (z 0)) * u 1 ^ 2 := by
  rw [hessianQuadraticForm_apply, ← inner_hessianOperator_left, hessianOperator_torusHeight,
    hessField_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **The gradient is Lipschitz**, with constant `|R| + 4 |r| + |ε|`. -/
theorem lipschitzWith_gradient_torusHeight (R r ε : ℝ) :
    LipschitzWith (‖R‖₊ + 4 * ‖r‖₊ + ‖ε‖₊) (∇ (torusHeight R r ε)) := by
  rw [gradient_torusHeight]
  refine lipschitzWith_of_nnNorm_fderiv_le
    (fun z ↦ (hasFDerivAt_gradField z).differentiableAt) fun z ↦ ?_
  rw [(hasFDerivAt_gradField z).fderiv, ← NNReal.coe_le_coe, coe_nnNorm]
  push_cast
  simp only [Real.norm_eq_abs]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  have hu₀ : |u 0| ≤ ‖u‖ := by simpa using PiLp.norm_apply_le u 0
  have hu₁ : |u 1| ≤ ‖u‖ := by simpa using PiLp.norm_apply_le u 1
  have hu := norm_nonneg u
  have abs_mul_le_of_abs_le_one {x c : ℝ} (hc : |c| ≤ 1) : |x * c| ≤ |x| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hc
  -- The entries of the Hessian are bounded by `|R| + |r|`, `|r|` and `|ε| + |r|`.
  have ha : |-((R + r * cos (z 1)) * cos (z 0))| ≤ |R| + |r| := by
    rw [abs_neg]
    refine (abs_mul_le_of_abs_le_one (abs_cos_le_one _)).trans ((abs_add_le _ _).trans ?_)
    exact add_le_add_right (abs_mul_le_of_abs_le_one (abs_cos_le_one _)) _
  have hb : |r * sin (z 1) * sin (z 0)| ≤ |r| :=
    (abs_mul_le_of_abs_le_one (abs_sin_le_one _)).trans
      (abs_mul_le_of_abs_le_one (abs_sin_le_one _))
  have hc : |-(ε * sin (z 1)) - r * cos (z 1) * cos (z 0)| ≤ |ε| + |r| := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg]
      exact abs_mul_le_of_abs_le_one (abs_sin_le_one _)
    · exact (abs_mul_le_of_abs_le_one (abs_cos_le_one _)).trans
        (abs_mul_le_of_abs_le_one (abs_cos_le_one _))
  have hrow {a b : ℝ} : |a * u 0 + b * u 1| ≤ |a| * ‖u‖ + |b| * ‖u‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
  rw [hessField_apply]
  refine (norm_add_le _ _).trans ?_
  have he₀ : ‖e₀‖ = 1 := by simp
  have he₁ : ‖e₁‖ = 1 := by simp
  rw [norm_smul, norm_smul, he₀, he₁, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [@hrow (-((R + r * cos (z 1)) * cos (z 0))) (r * sin (z 1) * sin (z 0)),
    @hrow (r * sin (z 1) * sin (z 0)) (-(ε * sin (z 1)) - r * cos (z 1) * cos (z 0)),
    mul_le_mul_of_nonneg_right ha hu, mul_le_mul_of_nonneg_right hb hu,
    mul_le_mul_of_nonneg_right hc hu]

private theorem pos_add_mul_cos (hr : |r| < R) (x : ℝ) : 0 < R + r * cos x := by
  have : |r * cos x| ≤ |r| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one x)
  linarith [neg_abs_le (r * cos x)]

/-- A diagonal quadratic form on the plane with positive weights is positive definite. -/
private theorem pos_mul_sq_add_mul_sq {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {u : 𝔼} (hu : u ≠ 0) :
    0 < a * u 0 ^ 2 + c * u 1 ^ 2 := by
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hu (by ext i; fin_cases i <;> simp [h.1, h.2])
  rcases hne with h | h
  · nlinarith [pow_pos (abs_pos.2 h) 2, sq_abs (u 0), sq_nonneg (u 1)]
  · nlinarith [pow_pos (abs_pos.2 h) 2, sq_abs (u 1), sq_nonneg (u 0)]

/-- **The critical points.** For `|r| < R`, the critical points of the perturbed torus height are
the points with `sin θ = 0` and `ε cos φ = r sin φ cos θ`. -/
theorem fderiv_torusHeight_eq_zero_iff (hr : |r| < R) {z : EuclideanSpace ℝ (Fin 2)} :
    fderiv ℝ (torusHeight R r ε) z = 0 ↔
      sin (z 0) = 0 ∧ ε * cos (z 1) = r * sin (z 1) * cos (z 0) := by
  have h : fderiv ℝ (torusHeight R r ε) z = 0 ↔ ∇ (torusHeight R r ε) z = 0 := by
    simp [gradient]
  rw [h]
  constructor
  · intro h0
    have h₀ := congrArg (fun v : 𝔼 ↦ v 0) h0
    have h₁ := congrArg (fun v : 𝔼 ↦ v 1) h0
    simp only [gradient_torusHeight_apply_zero, gradient_torusHeight_apply_one,
      PiLp.zero_apply, neg_eq_zero] at h₀ h₁
    exact ⟨(mul_eq_zero.1 h₀).resolve_left (pos_add_mul_cos hr _).ne', by linarith⟩
  · rintro ⟨h₀, h₁⟩
    ext i
    fin_cases i <;> simp [h₀, h₁]

/-- At a point with `sin θ = 0` the Hessian is diagonal. -/
private theorem hessianQuadraticForm_torusHeight_of_sin_eq_zero {z : 𝔼} (h : sin (z 0) = 0)
    (u : 𝔼) :
    hessianQuadraticForm (torusHeight R r ε) z u =
      -((R + r * cos (z 1)) * cos (z 0)) * u 0 ^ 2 +
        (-(ε * sin (z 1)) - r * cos (z 1) * cos (z 0)) * u 1 ^ 2 := by
  rw [hessianQuadraticForm_torusHeight, h]
  ring

/-- **Nondegeneracy of a diagonal critical point.** A critical point with `sin θ = 0` at which
both diagonal entries of the Hessian are nonzero is nondegenerate. -/
private theorem isNondegenerateCriticalPoint_of_sin_eq_zero {z : 𝔼}
    (hz : fderiv ℝ (torusHeight R r ε) z = 0) (h : sin (z 0) = 0)
    (ha : (R + r * cos (z 1)) * cos (z 0) ≠ 0)
    (hc : -(ε * sin (z 1)) - r * cos (z 1) * cos (z 0) ≠ 0) :
    IsNondegenerateCriticalPoint (torusHeight R r ε) z := by
  refine isNondegenerateCriticalPoint_iff_gradient.2
    ⟨contDiff_torusHeight.contDiffAt, by simp [gradient, hz], ?_⟩
  rw [hessianOperator_torusHeight]
  refine ContinuousLinearMap.isInvertible_of_injective_of_finrank_eq _ rfl
    ((injective_iff_map_eq_zero _).2 fun u hu ↦ ?_)
  have h₀ := congrArg (fun v : 𝔼 ↦ v 0) hu
  have h₁ := congrArg (fun v : 𝔼 ↦ v 1) hu
  simp only [hessField_apply, h, mul_zero, zero_mul, add_zero, zero_add] at h₀ h₁
  ext i
  fin_cases i
  · simpa [neg_mul, ha] using h₀
  · simpa [hc] using h₁

/-- For `|r| < R`, the Morse index at a point with `cos θ = 1` and `r cos φ + ε sin φ > 0`, a
maximum when it is critical, is `2`. -/
theorem morseIndex_torusHeight_eq_two (hr : |r| < R) {z : EuclideanSpace ℝ (Fin 2)}
    (h₀ : cos (z 0) = 1) (h₁ : 0 < r * cos (z 1) + ε * sin (z 1)) :
    morseIndex (torusHeight R r ε) z = 2 := by
  have hs : sin (z 0) = 0 := by nlinarith [sin_sq_add_cos_sq (z 0)]
  have ha := pos_add_mul_cos hr (z 1)
  refine (?_ : morseIndex _ _ = Module.finrank ℝ 𝔼).trans finrank_euclideanSpace_fin
  refine neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank.1 fun u hu ↦ ?_
  rw [neg_apply, hessianQuadraticForm_torusHeight_of_sin_eq_zero hs, h₀]
  linarith [pos_mul_sq_add_mul_sq ha h₁ hu]

/-- For `|r| < R`, the Morse index at a point with `cos θ = -1` and `r cos φ - ε sin φ > 0`, a
minimum when it is critical, is `0`. -/
theorem morseIndex_torusHeight_eq_zero (hr : |r| < R) {z : EuclideanSpace ℝ (Fin 2)}
    (h₀ : cos (z 0) = -1) (h₁ : 0 < r * cos (z 1) - ε * sin (z 1)) :
    morseIndex (torusHeight R r ε) z = 0 := by
  have hs : sin (z 0) = 0 := by nlinarith [sin_sq_add_cos_sq (z 0)]
  have ha := pos_add_mul_cos hr (z 1)
  refine morseIndex_eq_zero_of_posDef fun u hu ↦ ?_
  rw [hessianQuadraticForm_torusHeight_of_sin_eq_zero hs, h₀]
  linarith [pos_mul_sq_add_mul_sq ha h₁ hu]

/-- At a point at which the diagonal entries `-(R + r cos φ) cos θ` and
`-(ε sin φ + r cos φ cos θ)` of the Hessian have opposite signs, for instance a saddle, the Morse
index is `1`. -/
theorem morseIndex_torusHeight_eq_one {z : EuclideanSpace ℝ (Fin 2)}
    (h : (R + r * cos (z 1)) * cos (z 0) * (ε * sin (z 1) + r * cos (z 1) * cos (z 0)) < 0) :
    morseIndex (torusHeight R r ε) z = 1 := by
  have h₀ : hessianQuadraticForm (torusHeight R r ε) z e₀ =
      -((R + r * cos (z 1)) * cos (z 0)) := by
    rw [hessianQuadraticForm_torusHeight]
    simp
  have h₁ : hessianQuadraticForm (torusHeight R r ε) z e₁ =
      -(ε * sin (z 1) + r * cos (z 1) * cos (z 0)) := by
    rw [hessianQuadraticForm_torusHeight]
    simp
    ring
  set Q := hessianQuadraticForm (torusHeight R r ε) z
  -- The Hessian takes both signs at `e₀` and `e₁`, so both of its indices are positive, and they
  -- add up to at most `2`.
  have hQ : Q e₀ < 0 ∧ 0 < Q e₁ ∨ 0 < Q e₀ ∧ Q e₁ < 0 := by
    rw [h₀, h₁]
    rcases mul_neg_iff.1 h with h | h
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hneg : sigNeg Q ≠ 0 := by
    rw [Ne, ← QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero]
    intro hQ'
    rcases hQ with hQ | hQ
    · exact (hQ' e₀).not_gt hQ.1
    · exact (hQ' e₁).not_gt hQ.2
  have hpos : sigPos Q ≠ 0 := by
    rw [Ne, ← QuadraticForm.forall_nonpos_iff_sigPos_eq_zero]
    intro hQ'
    rcases hQ with hQ | hQ
    · exact (hQ' e₁).not_gt hQ.2
    · exact (hQ' e₀).not_gt hQ.1
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [finrank_euclideanSpace_fin] at hsum
  have hind : morseIndex (torusHeight R r ε) z = sigNeg Q := morseIndex_def
  omega

/-- If `(ρ c, ρ s) = (a, b)` with `ρ = ‖(a, b)‖ > 0`, then `a c + b s = ρ`. -/
private theorem mul_add_mul_eq {ρ a b c s : ℝ} (hρ : 0 < ρ) (h2 : ρ ^ 2 = a ^ 2 + b ^ 2)
    (hc : ρ * c = a) (hs : ρ * s = b) : a * c + b * s = ρ :=
  mul_left_cancel₀ hρ.ne' (by linear_combination a * hc + b * hs - h2)

/-- **The four kinds of critical points.** For `|r| < R`, with `ρ = √(r² + ε²)`, a point is
critical exactly when `cos θ = 1` and `(ρ cos φ, ρ sin φ) = ±(r, ε)`, or `cos θ = -1` and
`(ρ cos φ, ρ sin φ) = ±(r, -ε)`. -/
theorem fderiv_torusHeight_eq_zero_iff_cos_eq (hr : |r| < R) {z : EuclideanSpace ℝ (Fin 2)} :
    fderiv ℝ (torusHeight R r ε) z = 0 ↔
      (cos (z 0) = 1 ∧ √(r ^ 2 + ε ^ 2) * cos (z 1) = r ∧ √(r ^ 2 + ε ^ 2) * sin (z 1) = ε) ∨
      (cos (z 0) = 1 ∧ √(r ^ 2 + ε ^ 2) * cos (z 1) = -r ∧ √(r ^ 2 + ε ^ 2) * sin (z 1) = -ε) ∨
      (cos (z 0) = -1 ∧ √(r ^ 2 + ε ^ 2) * cos (z 1) = -r ∧ √(r ^ 2 + ε ^ 2) * sin (z 1) = ε) ∨
      (cos (z 0) = -1 ∧ √(r ^ 2 + ε ^ 2) * cos (z 1) = r ∧ √(r ^ 2 + ε ^ 2) * sin (z 1) = -ε) := by
  rw [fderiv_torusHeight_eq_zero_iff hr]
  rcases (add_nonneg (sq_nonneg r) (sq_nonneg ε)).eq_or_lt with h0 | hrε'
  · -- For `r = ε = 0` both sides say that `cos θ = ±1`.
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ ε = 0 := by constructor <;> nlinarith [sq_nonneg r, sq_nonneg ε]
    simp [sin_eq_zero_iff_cos_eq]
  set ρ := √(r ^ 2 + ε ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 hrε'
  have hρ2 : ρ ^ 2 = r ^ 2 + ε ^ 2 := Real.sq_sqrt hrε'.le
  refine ⟨fun ⟨hs, hc⟩ ↦ ?_, ?_⟩
  · have hcs := sin_sq_add_cos_sq (z 1)
    -- With `σ = cos θ = ±1` and `e = σ ε`, the critical point equation `e cos φ = r sin φ` puts
    -- `(cos φ, sin φ)` on the line through `(r, e)`, so it is `±(r, e) / ρ`.
    have key {e : ℝ} (he : ρ ^ 2 = r ^ 2 + e ^ 2) (hc : e * cos (z 1) = r * sin (z 1)) :
        ρ * cos (z 1) = r ∧ ρ * sin (z 1) = e ∨ ρ * cos (z 1) = -r ∧ ρ * sin (z 1) = -e := by
      set w := r * cos (z 1) + e * sin (z 1)
      have hcw : ρ ^ 2 * cos (z 1) = r * w := by linear_combination cos (z 1) * he + e * hc
      have hsw : ρ ^ 2 * sin (z 1) = e * w := by linear_combination sin (z 1) * he - r * hc
      have hw : w ^ 2 = ρ ^ 2 := by
        have : ρ ^ 2 * (w ^ 2 - ρ ^ 2) = 0 := by
          linear_combination w ^ 2 * he - (ρ ^ 2 * cos (z 1) + r * w) * hcw -
            (ρ ^ 2 * sin (z 1) + e * w) * hsw + ρ ^ 4 * hcs
        have := (mul_eq_zero.1 this).resolve_left (by positivity)
        linarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hw with hw | hw
      · refine Or.inl ⟨mul_left_cancel₀ hρ.ne' ?_, mul_left_cancel₀ hρ.ne' ?_⟩
        · linear_combination hcw + r * hw
        · linear_combination hsw + e * hw
      · refine Or.inr ⟨mul_left_cancel₀ hρ.ne' ?_, mul_left_cancel₀ hρ.ne' ?_⟩
        · linear_combination hcw + r * hw
        · linear_combination hsw + e * hw
    rcases sin_eq_zero_iff_cos_eq.1 hs with h₀ | h₀
    · rw [h₀, mul_one] at hc
      rcases key hρ2 hc with h | h
      · exact Or.inl ⟨h₀, h⟩
      · exact Or.inr (Or.inl ⟨h₀, h⟩)
    · rw [h₀] at hc
      rcases key (e := -ε) (by rw [hρ2, neg_sq]) (by linear_combination -hc) with h | h
      · exact Or.inr (Or.inr (Or.inr ⟨h₀, h⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h₀, h.1, by linear_combination h.2⟩))
  · -- Conversely `cos θ = ±1` gives `sin θ = 0`, and `ε cos φ = r sin φ cos θ` after scaling
    -- by `ρ`.
    rintro (⟨h₀, hc, hs⟩ | ⟨h₀, hc, hs⟩ | ⟨h₀, hc, hs⟩ | ⟨h₀, hc, hs⟩) <;>
      refine ⟨sin_eq_zero_iff_cos_eq.2 (by simp [h₀]), mul_left_cancel₀ hρ.ne' ?_⟩ <;>
      rw [h₀]
    · linear_combination ε * hc - r * hs
    · linear_combination ε * hc - r * hs
    · linear_combination ε * hc + r * hs
    · linear_combination ε * hc + r * hs

/-- **The perturbed torus height is a Morse function.** For `|r| < R` and `(r, ε) ≠ (0, 0)`,
every critical point is nondegenerate. -/
theorem isNondegenerateCriticalPoint_torusHeight (hr : |r| < R) (hrε : r ≠ 0 ∨ ε ≠ 0)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : fderiv ℝ (torusHeight R r ε) z = 0) :
    IsNondegenerateCriticalPoint (torusHeight R r ε) z := by
  have hpos : 0 < r ^ 2 + ε ^ 2 := by rcases hrε with h | h <;> positivity
  have hρ : 0 < √(r ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have hρ2 : √(r ^ 2 + ε ^ 2) ^ 2 = r ^ 2 + ε ^ 2 := Real.sq_sqrt hpos.le
  have ha := pos_add_mul_cos hr (z 1)
  have hs : sin (z 0) = 0 := ((fderiv_torusHeight_eq_zero_iff hr).1 hz).1
  rcases (fderiv_torusHeight_eq_zero_iff_cos_eq hr).1 hz with
    ⟨h₀, hc, hs'⟩ | ⟨h₀, hc, hs'⟩ | ⟨h₀, hc, hs'⟩ | ⟨h₀, hc, hs'⟩
  · have := mul_add_mul_eq hρ hρ2 hc hs'
    exact isNondegenerateCriticalPoint_of_sin_eq_zero hz hs (by rw [h₀, mul_one]; exact ha.ne')
      (show _ < (0 : ℝ) by rw [h₀]; linarith).ne
  · have := mul_add_mul_eq hρ (by rw [hρ2]; ring) hc hs'
    exact isNondegenerateCriticalPoint_of_sin_eq_zero hz hs (by rw [h₀, mul_one]; exact ha.ne')
      (show (0 : ℝ) < _ by rw [h₀]; linarith).ne'
  · have := mul_add_mul_eq hρ (by rw [hρ2]; ring) hc hs'
    exact isNondegenerateCriticalPoint_of_sin_eq_zero hz hs (by rw [h₀]; linarith)
      (show _ < (0 : ℝ) by rw [h₀]; linarith).ne
  · have := mul_add_mul_eq hρ (by rw [hρ2]; ring) hc hs'
    exact isNondegenerateCriticalPoint_of_sin_eq_zero hz hs (by rw [h₀]; linarith)
      (show (0 : ℝ) < _ by rw [h₀]; linarith).ne'

/-- **The critical values and indices.** For `|r| < R` and `(r, ε) ≠ (0, 0)`, with
`ρ = √(r² + ε²)`, a critical point of the perturbed torus height is a maximum of index `2` and
value `R + ρ`, a saddle of index `1` with `ρ sin φ = -ε` and value `R - ρ`, a saddle of index `1`
with `ρ sin φ = ε` and value `ρ - R`, or a minimum of index `0` and value `-R - ρ`. -/
theorem morseIndex_torusHeight_of_fderiv_eq_zero (hr : |r| < R) (hrε : r ≠ 0 ∨ ε ≠ 0)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : fderiv ℝ (torusHeight R r ε) z = 0) :
    (morseIndex (torusHeight R r ε) z = 2 ∧ torusHeight R r ε z = R + √(r ^ 2 + ε ^ 2)) ∨
    (morseIndex (torusHeight R r ε) z = 1 ∧ √(r ^ 2 + ε ^ 2) * sin (z 1) = -ε ∧
      torusHeight R r ε z = R - √(r ^ 2 + ε ^ 2)) ∨
    (morseIndex (torusHeight R r ε) z = 1 ∧ √(r ^ 2 + ε ^ 2) * sin (z 1) = ε ∧
      torusHeight R r ε z = √(r ^ 2 + ε ^ 2) - R) ∨
    (morseIndex (torusHeight R r ε) z = 0 ∧ torusHeight R r ε z = -R - √(r ^ 2 + ε ^ 2)) := by
  have hpos : 0 < r ^ 2 + ε ^ 2 := by rcases hrε with h | h <;> positivity
  have hρ : 0 < √(r ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have hρ2 : √(r ^ 2 + ε ^ 2) ^ 2 = r ^ 2 + ε ^ 2 := Real.sq_sqrt hpos.le
  have ha := pos_add_mul_cos hr (z 1)
  rcases (fderiv_torusHeight_eq_zero_iff_cos_eq hr).1 hz with
    ⟨h₀, hc, hs⟩ | ⟨h₀, hc, hs⟩ | ⟨h₀, hc, hs⟩ | ⟨h₀, hc, hs⟩
  · have := mul_add_mul_eq hρ hρ2 hc hs
    exact Or.inl ⟨morseIndex_torusHeight_eq_two hr h₀ (by linarith),
      by rw [torusHeight_apply, h₀]; linarith⟩
  · have := mul_add_mul_eq hρ (by rw [hρ2]; ring) hc hs
    have hw : ε * sin (z 1) + r * cos (z 1) * 1 = -√(r ^ 2 + ε ^ 2) := by linarith
    exact Or.inr (Or.inl ⟨morseIndex_torusHeight_eq_one
      (by rw [h₀, hw]; nlinarith [mul_pos ha hρ]), hs, by rw [torusHeight_apply, h₀]; linarith⟩)
  · have := mul_add_mul_eq hρ (by rw [hρ2]; ring) hc hs
    have hw : ε * sin (z 1) + r * cos (z 1) * -1 = √(r ^ 2 + ε ^ 2) := by linarith
    exact Or.inr (Or.inr (Or.inl ⟨morseIndex_torusHeight_eq_one
      (by rw [h₀, hw]; nlinarith [mul_pos ha hρ]), hs, by rw [torusHeight_apply, h₀]; linarith⟩))
  · have := mul_add_mul_eq hρ (by rw [hρ2]; ring) hc hs
    exact Or.inr (Or.inr (Or.inr ⟨morseIndex_torusHeight_eq_zero hr h₀ (by linarith),
      by rw [torusHeight_apply, h₀]; linarith⟩))

/-- The negative-gradient flow of the perturbed torus height. -/
local notation "Φ" =>
  negativeGradientFlow (torusHeight R r ε) (lipschitzWith_gradient_torusHeight R r ε)

/-- Along an orbit, the angle `φ` moves with velocity `r sin φ cos θ - ε cos φ`. -/
private theorem hasDerivAt_flow_apply_one (y : 𝔼) (t : ℝ) :
    HasDerivAt (fun t ↦ Φ t y 1)
      (r * sin (Φ t y 1) * cos (Φ t y 0) - ε * cos (Φ t y 1)) t := by
  have h := (isNegativeGradient_negativeGradientFlow (torusHeight R r ε)
    (lipschitzWith_gradient_torusHeight R r ε)).isIntegralCurve y t
  have h₁ : HasDerivAt (fun t ↦ Φ t y 1) (-∇ (torusHeight R r ε) (Φ t y) 1) t :=
    (ContinuousLinearMap.hasFDerivAt pr₁).comp_hasDerivAt t h
  convert h₁ using 1
  rw [gradient_torusHeight_apply_one]
  ring

/-- **The barrier.** For `ε ≠ 0`, along an orbit the quantity `ε sin φ` stays nonpositive once it
is: where it vanishes, `sin φ = 0` and its derivative is `-ε² < 0`. -/
private theorem flow_barrier (hε : ε ≠ 0) (y : 𝔼) {a t : ℝ} (ha : ε * sin (Φ a y 1) ≤ 0)
    (hat : a ≤ t) : ε * sin (Φ t y 1) ≤ 0 := by
  have hd (x : ℝ) : HasDerivAt (fun t ↦ ε * sin (Φ t y 1))
      (ε * (cos (Φ x y 1) * (r * sin (Φ x y 1) * cos (Φ x y 0) - ε * cos (Φ x y 1)))) x :=
    ((hasDerivAt_flow_apply_one y x).sin).const_mul ε
  refine image_le_of_deriv_right_lt_deriv_boundary (B := fun _ ↦ 0) (B' := fun _ ↦ 0)
    (fun x _ ↦ (hd x).continuousAt.continuousWithinAt) (fun x _ ↦ (hd x).hasDerivWithinAt) ha
    (fun _ ↦ hasDerivAt_const _ _) (fun x _ hx ↦ ?_) ⟨hat, le_rfl⟩
  -- Where `ε sin φ = 0`, `sin φ = 0`, so `cos² φ = 1` and the derivative is `-ε²`.
  have hs : sin (Φ x y 1) = 0 := (mul_eq_zero.1 hx).resolve_left hε
  have hc := sin_sq_add_cos_sq (Φ x y 1)
  rw [hs] at hc ⊢
  nlinarith [sq_pos_of_ne_zero hε]

/-- No orbit runs from a point with `ε sin φ < 0` to a point with `ε sin φ > 0`. -/
private theorem notMem_unstableSet_inter_stableSet (hε : ε ≠ 0) {p q y : 𝔼}
    (hp : ε * sin (p 1) < 0) (hq : 0 < ε * sin (q 1)) :
    y ∉ Flow.unstableSet Φ p ∩ Flow.stableSet Φ q := by
  rintro ⟨hu, hs⟩
  have hG : Continuous fun z : 𝔼 ↦ ε * sin (z 1) :=
    continuous_const.mul (continuous_sin.comp (ContinuousLinearMap.continuous pr₁))
  obtain ⟨a, ha⟩ := (((hG.tendsto p).comp (Flow.mem_unstableSet.1 hu)).eventually
    (gt_mem_nhds hp)).exists
  obtain ⟨T, hT⟩ := eventually_atTop.1 (((hG.tendsto q).comp (Flow.mem_stableSet.1 hs)).eventually
    (lt_mem_nhds hq))
  exact (flow_barrier hε y ha.le (le_max_left a T)).not_gt (hT _ (le_max_right a T))

/-- **The perturbation is Morse–Smale.** For `ε ≠ 0` and `√(r² + ε²) < R`, the negative-gradient
flow of `(R + r cos φ) cos θ + ε sin φ` is Morse–Smale. -/
theorem isMorseSmale_torusHeight (hε : ε ≠ 0) (hR : √(r ^ 2 + ε ^ 2) < R) :
    IsMorseSmale (torusHeight R r ε) (lipschitzWith_gradient_torusHeight R r ε) := by
  have hρ : 0 < √(r ^ 2 + ε ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hr : |r| < R := (Real.abs_le_sqrt (by nlinarith)).trans_lt hR
  have hfs : ContDiff ℝ 2 (torusHeight R r ε) := contDiff_torusHeight
  have hf := lipschitzWith_gradient_torusHeight R r ε
  refine .of_forall_ne_of_morseIndex_ne hfs fun p q y hp hq hpq hp0 hp2 hq0 _ hy ↦ ?_
  rw [finrank_euclideanSpace_fin] at hp2
  have hlt :=
    (isNegativeGradient_negativeGradientFlow _ hf).value_lt_of_mem_unstableSet_inter_stableSet
      (fun _ ↦ hfs.differentiable (by norm_num) _) hfs.continuous.continuousAt
      hfs.continuous.continuousAt hpq hy
  rcases morseIndex_torusHeight_of_fderiv_eq_zero hr (.inr hε) hp.fderiv_eq_zero with
    ⟨hip, -⟩ | ⟨-, hsp, hvp⟩ | ⟨-, -, hvp⟩ | ⟨hip, -⟩ <;>
  rcases morseIndex_torusHeight_of_fderiv_eq_zero hr (.inr hε) hq.fderiv_eq_zero with
    ⟨-, hvq⟩ | ⟨-, -, hvq⟩ | ⟨-, hsq, hvq⟩ | ⟨hiq, -⟩
  all_goals first
    | -- `p` is neither a maximum nor a minimum, and `q` is not a minimum.
      exact absurd hip hp2
    | exact absurd hip hp0
    | exact absurd hiq hq0
    | -- A connection that would not lower the value.
      exact absurd hlt (by linarith)
    | -- A connection between the two kinds of saddles crosses the barrier.
      have hp' : ε * sin (p 1) < 0 := neg_of_mul_neg_right
        (show √(r ^ 2 + ε ^ 2) * (ε * sin (p 1)) < 0 by
          rw [mul_left_comm, hsp]; nlinarith [sq_pos_of_ne_zero hε]) hρ.le
      have hq' : 0 < ε * sin (q 1) := pos_of_mul_pos_right
        (show 0 < √(r ^ 2 + ε ^ 2) * (ε * sin (q 1)) by
          rw [mul_left_comm, hsq]; nlinarith [sq_pos_of_ne_zero hε]) hρ.le
      exact absurd hy (notMem_unstableSet_inter_stableSet hε hp' hq')

/-- The trajectory `t ↦ (2 arctan (e^{c t}), φ)`, which for `c = R + r cos φ > 0` and
`sin φ = 0` joins `(0, φ)` to `(π, φ)` along the circle `φ` of the unperturbed torus height. -/
private noncomputable def connection (c φ t : ℝ) : 𝔼 :=
  (2 * arctan (exp (c * t))) • e₀ + φ • e₁

private theorem isIntegralCurve_connection {φ : ℝ} (hφ : sin φ = 0) :
    IsIntegralCurve (connection (R + r * cos φ) φ) fun _ z ↦ -∇ (torusHeight R r 0) z := by
  intro t
  set c := R + r * cos φ
  set x := exp (c * t)
  have hx : HasDerivAt (fun t ↦ exp (c * t)) (x * c) t := by
    simpa using ((hasDerivAt_id t).const_mul c).exp
  have hθ := (((hasDerivAt_arctan x).comp t hx).const_mul 2).smul_const e₀ |>.add_const (φ • e₁)
  refine hθ.congr_deriv ?_
  -- `sin (2 arctan x) = 2 x / (1 + x²)`, so the angle `θ` solves `θ' = c sin θ`.
  have hsq : √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  ext i
  fin_cases i
  · simp [connection, c, sin_two_mul, sin_arctan, cos_arctan]
    field_simp
    rw [hsq]
    ring
  · simp [connection, hφ]

private theorem connection_zero (c φ : ℝ) : connection c φ 0 = !₂[π / 2, φ] := by
  ext i
  fin_cases i <;> simp [connection, arctan_one]
  ring

private theorem tendsto_connection_atBot {c : ℝ} (hc : 0 < c) (φ : ℝ) :
    Tendsto (connection c φ) atBot (𝓝 !₂[0, φ]) := by
  have h : Tendsto (fun t ↦ exp (c * t)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hc)
  have := ((((continuous_arctan.tendsto 0).comp h).const_mul 2).smul_const e₀).add_const (φ • e₁)
  have e : (!₂[0, φ] : 𝔼) = (2 * arctan 0) • e₀ + φ • e₁ := by
    ext i
    fin_cases i <;> simp
  rw [e]
  exact this

private theorem tendsto_connection_atTop {c : ℝ} (hc : 0 < c) (φ : ℝ) :
    Tendsto (connection c φ) atTop (𝓝 !₂[π, φ]) := by
  have h : Tendsto (fun t ↦ arctan (exp (c * t))) atTop (𝓝 (π / 2)) :=
    (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc))
  have := ((h.const_mul 2).smul_const e₀).add_const (φ • e₁)
  have e : (!₂[π, φ] : 𝔼) = (2 * (π / 2)) • e₀ + φ • e₁ := by
    ext i
    fin_cases i
    · simp
      ring
    · simp
  rw [e]
  exact this

/-- **A saddle connection.** For `ε = 0`, on a circle `φ = φ₀` with `sin φ₀ = 0` and
`R + r cos φ₀ > 0`, the point `(π / 2, φ₀)` lies on a trajectory of the negative-gradient flow of
`(R + r cos φ) cos θ` from `(0, φ₀)` to `(π, φ₀)`. Both endpoints are saddles when moreover
`|r| < R` and `r cos φ₀ < 0`. -/
theorem mem_unstableSet_inter_stableSet_torusHeight_zero {φ : ℝ} (hφ : sin φ = 0)
    (hrφ : 0 < R + r * cos φ) :
    !₂[π / 2, φ] ∈
      Flow.unstableSet (negativeGradientFlow (torusHeight R r 0)
          (lipschitzWith_gradient_torusHeight R r 0)) !₂[0, φ] ∩
        Flow.stableSet (negativeGradientFlow (torusHeight R r 0)
          (lipschitzWith_gradient_torusHeight R r 0)) !₂[π, φ] := by
  have h (t : ℝ) := eq_negativeGradientFlow _ (lipschitzWith_gradient_torusHeight R r 0)
    (isIntegralCurve_connection hφ) t
  simp only [connection_zero] at h
  refine ⟨Flow.mem_unstableSet.2 ?_, Flow.mem_stableSet.2 ?_⟩
  · simpa only [← h] using tendsto_connection_atBot hrφ φ
  · simpa only [← h] using tendsto_connection_atTop hrφ φ

/-- **The unperturbed torus height is not Morse–Smale.** For `|r| < R` and `r ≠ 0`, the
negative-gradient flow of `(R + r cos φ) cos θ` is not Morse–Smale. Compare
`TauCeti.isMorseSmale_torusHeight`: for `ε ≠ 0` with `√(r² + ε²) < R`, the flow of the
perturbation by `ε sin φ` is Morse–Smale. -/
theorem not_isMorseSmale_torusHeight_zero (hr : |r| < R) (hr0 : r ≠ 0) :
    ¬IsMorseSmale (torusHeight R r 0) (lipschitzWith_gradient_torusHeight R r 0) := fun h ↦ by
  -- The circle `φ = π` for `r > 0`, or `φ = 0` for `r < 0`, carries a trajectory joining two
  -- saddles.
  obtain ⟨φ, hφ, hrφ⟩ : ∃ φ, sin φ = 0 ∧ r * cos φ < 0 := by
    rcases hr0.lt_or_gt with h | h
    · exact ⟨0, by simp, by simpa⟩
    · exact ⟨π, by simp, by simpa⟩
  have ha := pos_add_mul_cos hr φ
  have hp : fderiv ℝ (torusHeight R r 0) !₂[0, φ] = 0 :=
    (fderiv_torusHeight_eq_zero_iff hr).2 (by simp [hφ])
  have hq : fderiv ℝ (torusHeight R r 0) !₂[π, φ] = 0 :=
    (fderiv_torusHeight_eq_zero_iff hr).2 (by simp [hφ])
  have hip : morseIndex (torusHeight R r 0) !₂[0, φ] = 1 :=
    morseIndex_torusHeight_eq_one (by simp; nlinarith [mul_pos ha (neg_pos.2 hrφ)])
  have hiq : morseIndex (torusHeight R r 0) !₂[π, φ] = 1 :=
    morseIndex_torusHeight_eq_one (by simp; nlinarith [mul_pos ha (neg_pos.2 hrφ)])
  have hpq : (!₂[0, φ] : 𝔼) ≠ !₂[π, φ] := fun h ↦ by
    simpa [pi_ne_zero.symm] using congrArg (fun v : 𝔼 ↦ v 0) h
  have hy := mem_unstableSet_inter_stableSet_torusHeight_zero hφ ha
  exact (h.morseIndex_lt (isNondegenerateCriticalPoint_torusHeight hr (.inl hr0) hp)
    (isNondegenerateCriticalPoint_torusHeight hr (.inl hr0) hq) contDiff_torusHeight hpq
    hy.1 hy.2).ne (by rw [hip, hiq])

end TauCeti
