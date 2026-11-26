/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar

/-!
# Checks for the outer and inner distortion of a linear map

Worked examples for `Orientation.outerDistortion` (`q_O`) and `Orientation.innerDistortion`
(`q_I`) on a real inner product plane `E` with an orthonormal basis `e`, oriented by `e` on both
sides, writing `toLin e e M` for the operator with matrix `M` in that basis:

* `diag(2, 1)` has `‖A‖ = 2`, `J(A) = 2` and `ℓ(A) = 1`, so `q_O(A) = 4 / 2 = 2` and
  `q_I(A) = 2 / 1 = 2`;
* the reflection `R = diag(-1, 1)` has `q_O(R) = ∞` and `q_I(R) = 0`, while the naive quotient
  `‖R‖² / J(R)` is `-1`; the distortion inequality `‖R‖² ≤ K J(R)` holds for `K = -1`, which is
  why its comparison with `q_O ≤ K` needs `K ≥ 0`;
* the zero map has `q_O(0) = q_I(0) = 0`;
* `R ∘ R = id` has `q_I(id) = 1`, larger than `q_I(R) q_I(R) = 0`: submultiplicativity of `q_I`
  needs `J ≥ 0`;
* `-id` has `q_O(-id) = 1` on the plane, and `q_O(-id) = ∞` on an oriented space of dimension `3`;
* the projection `diag(1, 0)` has `J = 0`, so `q_O = ∞` and `q_I = 0`.
-/

public section

open Module Matrix LinearMap
open scoped ENNReal

namespace TauCeti.LinearDistortionChecks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (finrank ℝ E = 2)] (e : OrthonormalBasis (Fin 2) ℝ E)

/-- `diag(2, 1)` has outer distortion `‖A‖² / J(A) = 4 / 2 = 2` and inner distortion
`J(A) / ℓ(A)² = 2 / 1 = 2`. -/
example :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 := by
  have hJ : e.toBasis.orientation.orientedJacobian e.toBasis.orientation
      (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 := by simp
  constructor
  · rw [Orientation.outerDistortion_of_pos _ _ (by rw [hJ]; norm_num), hJ,
      norm_toContinuousLinearMap_eq_singularValues_zero,
      singularValues_toLin_diagonal_fin_two e (by norm_num)]
    norm_num
  · rw [Orientation.innerDistortion_of_pos _ _ (by rw [hJ]; norm_num), hJ, minimalStretch_def,
      finrank_eq_card_basis e.toBasis, singularValues_toLin_diagonal_fin_two e (by norm_num)]
    norm_num

/-- The reflection `R = diag(-1, 1)` has `q_O(R) = ∞` and `q_I(R) = 0`, while the naive quotient
`‖R‖² / J(R)` is `-1`. -/
example :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = ⊤ ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = 0 ∧
      ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]))‖ ^ 2 /
        e.toBasis.orientation.orientedJacobian e.toBasis.orientation
          (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = -1 := by
  refine ⟨Orientation.outerDistortion_of_nonpos _ _ (by simp) (by simp),
    Orientation.innerDistortion_of_nonpos _ _ (by simp), ?_⟩
  rw [norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- For `K = -1` the reflection satisfies the distortion inequality `‖R‖² ≤ K J(R)`, although
`q_O(R) = ∞`: the comparison of `‖A‖ⁿ ≤ K J(A)` with `q_O(A) ≤ K` needs `K ≥ 0`. -/
example :
    ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]))‖ ^ 2 ≤
      -1 * e.toBasis.orientation.orientedJacobian e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) := by
  rw [norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- The zero map has `q_O(0) = q_I(0) = 0`; with the convention `0 / 0 = ∞` every constant map
would fail to be quasiregular. -/
example : e.toBasis.orientation.outerDistortion e.toBasis.orientation (0 : E →ₗ[ℝ] E) = 0 ∧
    e.toBasis.orientation.innerDistortion e.toBasis.orientation (0 : E →ₗ[ℝ] E) = 0 :=
  ⟨Orientation.outerDistortion_zero _ _ two_pos, Orientation.innerDistortion_zero _ _ two_pos⟩

/-- `R ∘ R = id`, and `q_I(id) = 1 > 0 = q_I(R) q_I(R)`: submultiplicativity of the inner
distortion needs `J ≥ 0`. -/
example :
    toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]) ∘ₗ
        toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]) = LinearMap.id ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation (LinearMap.id : E →ₗ[ℝ] E) = 1 ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
          (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) *
        e.toBasis.orientation.innerDistortion e.toBasis.orientation
          (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← toLin_mul, diagonal_mul_diagonal, ← toLin_one e.toBasis]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]
  · have hid : (LinearIsometryEquiv.refl ℝ E : E →ₗ[ℝ] E) = LinearMap.id :=
      LinearMap.ext fun _ ↦ by simp
    rw [← hid]
    exact e.toBasis.orientation.innerDistortion_linearIsometryEquiv e.toBasis.orientation _
      (by rw [hid, Orientation.orientedJacobian_id])
  · rw [Orientation.innerDistortion_of_nonpos _ _ (by simp), zero_mul]

/-- `-id` on the plane has outer distortion `1`: `J(-id) = (-1)² = 1`. -/
example : e.toBasis.orientation.outerDistortion e.toBasis.orientation
    (-(LinearMap.id : E →ₗ[ℝ] E)) = 1 := by
  rw [← neg_one_smul ℝ (LinearMap.id : E →ₗ[ℝ] E),
    Orientation.outerDistortion_smul _ _ (by norm_num)]
  have hid : (LinearIsometryEquiv.refl ℝ E : E →ₗ[ℝ] E) = LinearMap.id :=
    LinearMap.ext fun _ ↦ by simp
  rw [← hid]
  exact e.toBasis.orientation.outerDistortion_linearIsometryEquiv e.toBasis.orientation _
    (by rw [hid, Orientation.orientedJacobian_id])

/-- `-id` on an oriented space of dimension `3` has outer distortion `∞`: `J(-id) = (-1)³ = -1`. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fact (finrank ℝ F = 3)] (o : Orientation ℝ F (Fin 3)) :
    o.outerDistortion o (-(LinearMap.id : F →ₗ[ℝ] F)) = ⊤ := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ F = 3)
  rw [← neg_one_smul ℝ (LinearMap.id : F →ₗ[ℝ] F)]
  refine o.outerDistortion_smul_of_pow_neg o (by norm_num) (by simp) fun h ↦ ?_
  obtain ⟨x, hx⟩ := exists_ne (0 : F)
  exact hx (by simpa using LinearMap.congr_fun h x)

/-- The projection `diag(1, 0)` has `J = 0`, so `q_O = ∞` and `q_I = 0`. -/
example :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ), 0])) = ⊤ ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ), 0])) = 0 := by
  exact ⟨Orientation.outerDistortion_of_nonpos _ _ (by simp) (by simp),
    Orientation.innerDistortion_of_nonpos _ _ (by simp)⟩

end TauCeti.LinearDistortionChecks
