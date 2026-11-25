/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.Propagator.Holomorphic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Checks for Carathéodory systems: the Dirac coefficient

For `z ∈ ℂ` and `q = f + i g ∈ ℂ` let
`D(z, q) = [[f, -z - g], [z - g, -f]]`, the coefficient `-Ω(z - Q_q)` of the Dirac system, acting
on `EuclideanSpace ℂ (Fin 2)`. It is `z J + Q_q` with `J = [[0, -1], [1, 0]]` an isometry and
`Q_q = [[f, -g], [-g, -f]]` satisfying `‖Q_q v‖ = |q| ‖v‖`, so in the Euclidean operator norm
`‖D(z, q)‖ ≤ |z| + |q|` (`TauCeti.Examples.DiracCoefficient.norm_toEuclideanCLM_diracMatrix_le`).
Hence for `q` integrable on `[a, b]` the propagator of `r ↦ D(z, q(r))` is entire in `z`
(`TauCeti.Examples.DiracCoefficient.differentiable_propagator_dirac`). In the maximum-row-sum norm
of `Fin 2 → ℂ` the bound fails: at `z = 0` and `q = 1 + i` the coefficient has norm `2 > √2 = |q|`
(`TauCeti.Examples.DiracCoefficient.linftyOpNorm_diracMatrix_zero_one_add_I`).

These are Checks of §1.6 of the DiracScatteringAndNonlinearFourierTransform roadmap.
-/

public section

open MeasureTheory Set Matrix

namespace TauCeti.Examples.DiracCoefficient

/-- The Dirac coefficient `D(z, q) = [[f, -z - g], [z - g, -f]]` for `q = f + i g`. -/
def diracMatrix (z q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ), -z - q.im; z - q.im, -(q.re : ℂ)]

/-- The rotation `J = [[0, -1], [1, 0]]`. -/
def rotMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

/-- The potential part `Q_q = [[f, -g], [-g, -f]]` of the Dirac coefficient, `q = f + i g`. -/
def potMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ), -q.im; -q.im, -(q.re : ℂ)]

/-- The Dirac coefficient is `z J + Q_q`. -/
theorem diracMatrix_eq (z q : ℂ) : diracMatrix z q = z • rotMatrix + potMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracMatrix, rotMatrix, potMatrix] <;> ring

/-- The squared Euclidean norm on `ℂ²`. -/
private theorem norm_sq_euclidean (v : EuclideanSpace ℂ (Fin 2)) :
    ‖v‖ ^ 2 = Complex.normSq (v 0) + Complex.normSq (v 1) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm]

/-- The rotation `J` is an isometry of `ℂ²`. -/
theorem norm_toEuclideanCLM_rotMatrix_apply (v : EuclideanSpace ℂ (Fin 2)) :
    ‖toEuclideanCLM (𝕜 := ℂ) rotMatrix v‖ = ‖v‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_euclidean, norm_sq_euclidean]
  simp only [rotMatrix, ofLp_toEuclideanCLM, mulVec, dotProduct, Fin.sum_univ_two]
  simp [Complex.normSq_neg, add_comm]

/-- `‖Q_q v‖ = |q| ‖v‖` on `ℂ²`. -/
theorem norm_toEuclideanCLM_potMatrix_apply (q : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (potMatrix q) v‖ = ‖q‖ * ‖v‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow, norm_sq_euclidean, norm_sq_euclidean, Complex.sq_norm]
  simp only [potMatrix, ofLp_toEuclideanCLM, mulVec, dotProduct, Fin.sum_univ_two]
  simp [Complex.normSq_apply]
  ring

/-- **The Dirac coefficient in the Euclidean operator norm.** `‖D(z, q)‖ ≤ |z| + |q|`. -/
theorem norm_toEuclideanCLM_diracMatrix_le (z q : ℂ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (diracMatrix z q)‖ ≤ ‖z‖ + ‖q‖ := by
  rw [diracMatrix_eq, map_add, map_smul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hJ : ‖toEuclideanCLM (𝕜 := ℂ) rotMatrix‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        rw [norm_toEuclideanCLM_rotMatrix_apply, one_mul]
    calc ‖z • toEuclideanCLM (𝕜 := ℂ) rotMatrix‖
        ≤ ‖z‖ * ‖toEuclideanCLM (𝕜 := ℂ) rotMatrix‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖z‖ * 1 := by gcongr
      _ = ‖z‖ := mul_one _
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v =>
      (norm_toEuclideanCLM_potMatrix_apply q v).le

/-- The potential part is real-linear in `q`. -/
private theorem toEuclideanCLM_potMatrix (q : ℂ) :
    toEuclideanCLM (𝕜 := ℂ) (potMatrix q) =
      (q.re : ℂ) • toEuclideanCLM (𝕜 := ℂ) !![1, 0; 0, -1] +
        (q.im : ℂ) • toEuclideanCLM (𝕜 := ℂ) !![0, -1; -1, 0] := by
  have h : potMatrix q = (q.re : ℂ) • !![1, 0; 0, -1] + (q.im : ℂ) • !![0, -1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [potMatrix]
  rw [h, map_add, map_smul, map_smul]

/-- **The Dirac propagator is entire.** For `q` integrable on `[a, b]` and `s, t ∈ [a, b]`, the
propagator of `r ↦ D(z, q(r))` on `ℂ²` is an entire function of `z`. -/
theorem differentiable_propagator_dirac {q : ℝ → ℂ} {a b s t : ℝ}
    (hq : IntegrableOn q (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Differentiable ℂ fun z : ℂ ↦
      propagator (fun r ↦ toEuclideanCLM (𝕜 := ℂ) (diracMatrix z (q r))) t s := by
  have hB : IntegrableOn (fun r ↦ toEuclideanCLM (𝕜 := ℂ) (potMatrix (q r))) (Icc a b) := by
    simp_rw [toEuclideanCLM_potMatrix]
    exact (hq.re.ofReal.smul_const _).add (hq.im.ofReal.smul_const _)
  simpa [diracMatrix_eq, map_add, map_smul] using
    differentiable_propagator_smul_add (toEuclideanCLM (𝕜 := ℂ) rotMatrix) hB hs ht

open scoped Matrix.Norms.Operator in
/-- **The maximum-row-sum norm is too large.** At `z = 0` and `q = 1 + i` the Dirac coefficient has
maximum-row-sum norm `2`, which exceeds `|q| = √2`. -/
theorem linftyOpNorm_diracMatrix_zero_one_add_I :
    ‖diracMatrix 0 (1 + Complex.I)‖ = 2 ∧ ‖(1 + Complex.I : ℂ)‖ < 2 := by
  constructor
  · have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [linfty_opNorm_def, huniv]
    simp [diracMatrix]
    norm_num
  · have h : (1 + Complex.I : ℂ) = ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I := by simp
    rw [h, Complex.norm_add_mul_I, Real.sqrt_lt' two_pos]
    norm_num

end TauCeti.Examples.DiracCoefficient
