/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Diagonal
public import TauCeti.Probability.Distributions.Gaussian.LowDimension

/-!
# A singular diagonal Gaussian conditioning example

The explicit three-coordinate example has retained variance `a`, cross-covariance `(b, 0)`,
and observed covariance `diag(1, 0)`. It is a valid covariance exactly when `b² ≤ a`. Its
regression kernel at observation `(u, v)` has mean `m₁ + b * (u - m₂₁)` and variance
`(a - b ^ 2).toNNReal`, independently of `v`, even outside the affine support of the observed
law. This kernel agrees almost everywhere with the regular conditional law, including when
the totalized joint law is Dirac for `a < b²`. At `a = b²` the kernel is Dirac; at `b² < a`
it has positive variance.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 2.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- A three-coordinate covariance with retained variance `a`, cross-covariance `(b, 0)`, and
singular observed covariance `diag(1, 0)`. Its positive-semidefinite range is `b² ≤ a`. -/
def gaussianSingularDiagonalCovariance (a b : ℝ) :
    Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℝ :=
  fromBlocks (Matrix.of fun _ _ ↦ a) (Matrix.of fun _ ↦ ![b, 0])
    (Matrix.of fun i _ ↦ ![b, 0] i) (diagonal ![1, 0])

/-- The retained variance is `a`. -/
@[simp]
theorem gaussianSingularDiagonalCovariance_inl_inl (a b : ℝ) (i j : Unit) :
    gaussianSingularDiagonalCovariance a b (Sum.inl i) (Sum.inl j) = a := by
  rfl

/-- The covariance from the retained coordinate to the observed coordinates is `(b, 0)`. -/
@[simp]
theorem gaussianSingularDiagonalCovariance_inl_inr (a b : ℝ) (i : Unit) (j : Fin 2) :
    gaussianSingularDiagonalCovariance a b (Sum.inl i) (Sum.inr j) = ![b, 0] j := by
  rfl

/-- The covariance from the observed coordinates to the retained coordinate is `(b, 0)`. -/
@[simp]
theorem gaussianSingularDiagonalCovariance_inr_inl (a b : ℝ) (i : Fin 2) (j : Unit) :
    gaussianSingularDiagonalCovariance a b (Sum.inr i) (Sum.inl j) = ![b, 0] i := by
  rfl

/-- The observed covariance entries are those of the singular diagonal matrix `diag(1, 0)`. -/
@[simp]
theorem gaussianSingularDiagonalCovariance_inr_inr (a b : ℝ) (i j : Fin 2) :
    gaussianSingularDiagonalCovariance a b (Sum.inr i) (Sum.inr j) =
      diagonal ![1, 0] i j := by
  rfl

/-- The observed covariance block is the singular diagonal matrix `diag(1, 0)`. -/
@[simp]
theorem gaussianSingularDiagonalCovariance_submatrix_inr (a b : ℝ) :
    (gaussianSingularDiagonalCovariance a b).submatrix Sum.inr Sum.inr = diagonal ![1, 0] := by
  rfl

/-- The conditional covariance in the singular diagonal example is the scalar `a - b²`. -/
@[simp]
theorem gaussianCondCov_gaussianSingularDiagonalCovariance (a b : ℝ) :
    (gaussianSingularDiagonalCovariance a b).gaussianCondCov =
      diagonal (fun _ : Unit ↦ a - b ^ 2) := by
  ext i j
  rw [Matrix.gaussianCondCov_apply_of_diagonal
    (gaussianSingularDiagonalCovariance_submatrix_inr a b) (by intro k; fin_cases k <;> norm_num)]
  simp [Fin.sum_univ_two, pow_two]

/-- The singular diagonal example is a valid covariance precisely when the residual variance
is nonnegative. This includes the rank-one boundary `a = b²`. -/
@[simp]
theorem posSemidef_gaussianSingularDiagonalCovariance_iff (a b : ℝ) :
    (gaussianSingularDiagonalCovariance a b).PosSemidef ↔ b ^ 2 ≤ a := by
  constructor
  · intro h
    have hres := h.gaussianCondCov.diag_nonneg (i := ())
    simpa using hres
  · intro h
    let v : Unit ⊕ Fin 2 → ℝ := Sum.elim (fun _ ↦ b) ![1, 0]
    let e : Unit ⊕ Fin 2 → ℝ := Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)
    have heq : gaussianSingularDiagonalCovariance a b =
        vecMulVec v v + (a - b ^ 2) • vecMulVec e e := by
      ext (i | i) (j | j)
      · simp [v, e, vecMulVec_apply, pow_two]
      · fin_cases j <;> simp [v, e, vecMulVec_apply]
      · fin_cases i <;> simp [v, e, vecMulVec_apply]
      · fin_cases i <;> fin_cases j <;> simp [v, e, vecMulVec_apply]
    rw [heq]
    exact (posSemidef_vecMulVec_self_star v).add
      ((posSemidef_vecMulVec_self_star e).smul (sub_nonneg.mpr h))

/-- The conditional covariance is positive definite exactly in the positive-residual-variance
case, although the joint covariance is always singular. -/
theorem posDef_gaussianCondCov_gaussianSingularDiagonalCovariance_iff (a b : ℝ) :
    (gaussianSingularDiagonalCovariance a b).gaussianCondCov.PosDef ↔ b ^ 2 < a := by
  simp [Matrix.posDef_diagonal_iff, sub_pos]

end TauCeti.Probability

namespace EuclideanSpace

open TauCeti.Probability

/-- The regression mean ignores the zero-variance observed coordinate, even outside the
affine support of the observed law. -/
@[simp]
theorem gaussianCondMean_gaussianSingularDiagonalCovariance
    (m : EuclideanSpace ℝ (Unit ⊕ Fin 2)) (a b : ℝ) (x₂ : EuclideanSpace ℝ (Fin 2)) :
    m.gaussianCondMean (gaussianSingularDiagonalCovariance a b) x₂ =
      EuclideanSpace.single () (m (Sum.inl ()) + b * (x₂ 0 - m (Sum.inr 0))) := by
  ext i
  rw [gaussianCondMean_apply_of_diagonal m
    (gaussianSingularDiagonalCovariance_submatrix_inr a b)
    (by intro k; fin_cases k <;> norm_num)]
  simp [Fin.sum_univ_two]

/-- In the singular diagonal example the conditional kernel is a scalar Gaussian with mean
`m₁ + b * (u - m₂₁)` and variance `(a - b ^ 2).toNNReal`: this is `a - b²` when `b² ≤ a`,
and zero otherwise. It ignores the zero-variance observed coordinate even outside the affine
support. It agrees with the regular conditional law almost everywhere under the observed law. -/
theorem gaussianCondKernel_gaussianSingularDiagonalCovariance
    (m : EuclideanSpace ℝ (Unit ⊕ Fin 2)) (a b : ℝ) (x₂ : EuclideanSpace ℝ (Fin 2)) :
    m.gaussianCondKernel (gaussianSingularDiagonalCovariance a b) x₂ =
      (gaussianReal (m (Sum.inl ()) + b * (x₂ 0 - m (Sum.inr 0)))
        (a - b ^ 2).toNNReal).map (EuclideanSpace.single ()) := by
  rw [gaussianCondKernel_apply, multivariateGaussian_eq_map_single]
  simp

/-- At zero residual variance the singular diagonal conditional kernel is Dirac at its
regression mean, including observations outside the affine support. -/
theorem gaussianCondKernel_gaussianSingularDiagonalCovariance_sq
    (m : EuclideanSpace ℝ (Unit ⊕ Fin 2)) (b : ℝ) (x₂ : EuclideanSpace ℝ (Fin 2)) :
    m.gaussianCondKernel (gaussianSingularDiagonalCovariance (b ^ 2) b) x₂ =
      Measure.dirac (EuclideanSpace.single ()
        (m (Sum.inl ()) + b * (x₂ 0 - m (Sum.inr 0)))) := by
  simp

end EuclideanSpace

namespace TauCeti.Probability

/-- For a joint Gaussian with the singular diagonal covariance, its regular conditional law
is the explicit regression Gaussian almost everywhere under the observed law. -/
theorem condDistrib_gaussianSingularDiagonalCovariance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (X : Ω → EuclideanSpace ℝ (Unit ⊕ Fin 2))
    (m : EuclideanSpace ℝ (Unit ⊕ Fin 2)) {a b : ℝ}
    (hX : HasLaw X (multivariateGaussian m (gaussianSingularDiagonalCovariance a b)) P) :
    ∀ᵐ x₂ ∂P.map fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2,
      condDistrib (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).1)
          (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2) P x₂ =
        (gaussianReal (m (Sum.inl ()) + b * (x₂ 0 - m (Sum.inr 0)))
          (a - b ^ 2).toNNReal).map (EuclideanSpace.single ()) := by
  by_cases hab : b ^ 2 ≤ a
  · filter_upwards [condDistrib_multivariateGaussian X m hX
      ((posSemidef_gaussianSingularDiagonalCovariance_iff a b).mpr hab)] with x₂ hx₂
    rw [hx₂, EuclideanSpace.gaussianCondKernel_gaussianSingularDiagonalCovariance]
  · rw [multivariateGaussian_of_not_posSemidef m (by simpa using hab)] at hX
    have hfst : (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).1) =ᵐ[P]
        fun _ ↦ (EuclideanSpace.sumEquivProd m).1 :=
      hX.ae_eq_of_dirac.fun_comp (fun x ↦ (EuclideanSpace.sumEquivProd x).1)
    have hsnd : (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2) =ᵐ[P]
        fun _ ↦ (EuclideanSpace.sumEquivProd m).2 :=
      hX.ae_eq_of_dirac.fun_comp (fun x ↦ (EuclideanSpace.sumEquivProd x).2)
    rw [condDistrib_congr_left hfst]
    have hobs : ∀ᵐ x₂ ∂P.map (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2),
        x₂ = (EuclideanSpace.sumEquivProd m).2 :=
      (ae_map_iff (by fun_prop) (by measurability)).mpr hsnd
    filter_upwards [condDistrib_const (by fun_prop) (EuclideanSpace.sumEquivProd m).1,
      hobs] with x₂ hx₂ hm
    rw [hx₂, hm]
    have hmean : (EuclideanSpace.sumEquivProd m).1 =
        EuclideanSpace.single () (m (Sum.inl ())) := by
      ext i
      simp [EuclideanSpace.sumEquivProd]
    rw [Kernel.deterministic_apply, hmean]
    simp [Real.toNNReal_of_nonpos (by linarith : a - b ^ 2 ≤ 0),
      EuclideanSpace.sumEquivProd]

end TauCeti.Probability
