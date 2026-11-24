/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.FubiniStudy

/-!
# Normalization checks for the Fubini–Study Hermitian form

Concrete values of `TauCeti.fubiniStudyHermitian` that pin its normalization and the order of its
coefficients:

* **Standard line (`fubiniStudyHermitian_affineVector_zero`):** at the point `[1 : 0]` of `CP¹`,
  the lift of the coordinate vector of the chart `X_0 ≠ 0` has `H = 1 / π`.
* **Coefficient order (`fubiniStudyHermitian_affineVector_mixed`):** at the point with affine
  coordinates `w = (1, i) / √2` of `CP²`, where `r = 2`, the mixed coefficient `h(e_0, e_1)` is
  `w_0 conj (w_1) / (-r² π) = i / (8π)`; the transposed coefficient `conj (w_0) w_1` would give
  `-i / (8π)`.
* **Projective linear maps (`fubiniStudyHermitian_single_smul`):** the projective map induced by
  `diag (1, 2)` fixes `[e_0]` and doubles the tangent representative `e_1`, and
  `H_{e_0}(2 e_1, 2 e_1) = 4 / π ≠ 1 / π = H_{e_0}(e_1, e_1)`. So the Fubini–Study form is not
  invariant under all projective linear automorphisms, only under the unitary ones
  (`LinearIsometry.fubiniStudyHermitian_map_map_map`).
-/

public section

open RCLike Real
open scoped InnerProductSpace ComplexConjugate

namespace TauCeti.FubiniStudyExample

open ComplexProjectiveSpace

/-- At the standard line `[1 : 0]` of `CP¹`, the lift of the chart's coordinate vector has
Fubini–Study value `1 / π`. -/
theorem fubiniStudyHermitian_affineVector_zero :
    fubiniStudyHermitian ℂ (affineVector (0 : Fin 2) 0)
        (fderiv ℂ (affineVector 0) 0 (Pi.single 0 1))
        (fderiv ℂ (affineVector 0) 0 (Pi.single 0 1)) = 1 / π := by
  rw [fderiv_affineVector, fubiniStudyHermitian_affineVector_insertZeroL_single]
  simp

/-- At `w = (1, i) / √2` in the chart `X_0 ≠ 0` of `CP²`, the mixed Fubini–Study coefficient
`h(e_0, e_1)` is `i / (8π)`. -/
theorem fubiniStudyHermitian_affineVector_mixed :
    fubiniStudyHermitian ℂ (affineVector (0 : Fin 3) ![1 / √2, Complex.I / √2])
        (fderiv ℂ (affineVector 0) ![1 / √2, Complex.I / √2] (Pi.single 0 1))
        (fderiv ℂ (affineVector 0) ![1 / √2, Complex.I / √2] (Pi.single 1 1)) =
      Complex.I / (8 * π) := by
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt zero_le_two, Complex.ofReal_ofNat]
  have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hsum : (1 + ∑ l, ‖(![1 / √2, Complex.I / √2] : Fin 2 → ℂ) l‖ ^ 2 : ℝ) = 2 := by
    simp [Fin.sum_univ_two, hs]
    norm_num
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  have hs0 : ((√2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  rw [fderiv_affineVector, fubiniStudyHermitian_affineVector_insertZeroL_single, hsum]
  simp only [Fin.isValue, zero_ne_one, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_div₀, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  field_simp
  linear_combination (-4 * Complex.I) * h2

/-- The projective map induced by `diag (1, 2)` fixes `[e_0]` and doubles the tangent
representative `e_1`, which multiplies the Fubini–Study value `1 / π` there by `4`. -/
theorem fubiniStudyHermitian_single_smul :
    fubiniStudyHermitian ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
        (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) = 1 / π ∧
      fubiniStudyHermitian ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
        ((2 : ℂ) • EuclideanSpace.single 1 1) ((2 : ℂ) • EuclideanSpace.single 1 1) = 4 / π := by
  have h : fubiniStudyHermitian ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
      (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) = 1 / π := by
    simp [fubiniStudyHermitian_apply, EuclideanSpace.inner_single_left]
  refine ⟨h, ?_⟩
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, h]
  simp only [smul_eq_mul, Complex.conj_ofNat]
  ring

end TauCeti.FubiniStudyExample
