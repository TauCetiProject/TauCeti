/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The covariance recursion of the discrete-time Kalman filter

For an observation matrix `C : Matrix κ ι ℝ`, an observation-noise covariance `R` and a prior
covariance `P` of a state in `ι → ℝ`, the Kalman filter forms the innovation covariance
`S = C P Cᵀ + R`, the Kalman gain `K = P Cᵀ S⁻¹` and the updated covariance
`P - P Cᵀ S⁻¹ C P`. A transition matrix `A` and a process-noise covariance `Q` then propagate the
covariance by `P ↦ A P Aᵀ + Q`, and the composite of the two updates is the discrete Riccati map

  `riccatiMap A C Q R P = A (P - P Cᵀ (C P Cᵀ + R)⁻¹ C P) Aᵀ + Q`.

These are the covariance equations of the filter, stated here as maps of matrices with no
probability, so that they can serve both the filter and linear systems theory. The inverse is
Mathlib's `Matrix.inv`, which is `0` on a singular matrix; with a positive definite `R` and a
positive semidefinite `P` the innovation covariance is positive definite, hence invertible.

The completion of the square (the Joseph form of the update) says that for every gain `K`,
`(1 - K C) P (1 - K C)ᵀ + K R Kᵀ` is the updated covariance plus `(K - K*) S (K - K*)ᵀ`, where
`K*` is the Kalman gain. So the Kalman gain minimizes the error covariance in the Loewner order,
and positive semidefiniteness and monotonicity of the updates follow. The information form
`(P⁺)⁻¹ = P⁻¹ + Cᵀ R⁻¹ C` of the measurement update comes instead from the Woodbury identity
`Matrix.add_mul_mul_inv_eq_sub`.

## Main definitions

* `Matrix.innovationCov C R P = C P Cᵀ + R`;
* `Matrix.kalmanGain C R P = P Cᵀ (C P Cᵀ + R)⁻¹`;
* `Matrix.measurementUpdate C R P = P - P Cᵀ (C P Cᵀ + R)⁻¹ C P`;
* `Matrix.timeUpdate A Q P = A P Aᵀ + Q`;
* `Matrix.riccatiMap A C Q R P`, the time update of the measurement update.

## Main results

* `Matrix.joseph_eq_measurementUpdate_add`: the completion of the square, and
  `Matrix.joseph_kalmanGain`: the Joseph form of the Kalman gain is the measurement update.
* `Matrix.joseph_sub_measurementUpdate_posSemidef` and `Matrix.joseph_eq_measurementUpdate_iff`:
  the Kalman gain minimizes the error covariance, and is the only minimizer.
* `Matrix.PosSemidef.measurementUpdate` and `Matrix.PosSemidef.riccatiMap`: the updates preserve
  positive semidefiniteness; `Matrix.PosSemidef.posDef_riccatiMap`: a positive definite process
  noise makes the Riccati map positive definite.
* `Matrix.measurementUpdate_sub_posSemidef` and `Matrix.riccatiMap_sub_posSemidef`: the updates
  are monotone in the Loewner order.
* `Matrix.inv_measurementUpdate`, `Matrix.kalmanGain_eq_measurementUpdate_mul` and
  `Matrix.inv_measurementUpdate_mulVec_add_kalmanGain`: the information form of the update.

## References

* Brian D. O. Anderson and John B. Moore, *Optimal Filtering*, Prentice-Hall, 1979: §3.1,
  equations (1.9) and (1.12) for the recursion; §5.2, Theorem 2.1, for the completion of the
  square; §3.1, Problem 1.2, for positivity; §4.4 for monotonicity; §6.3, equations (3.1) to
  (3.3) and (3.10), for the information form.
* Simo Särkkä, *Bayesian Filtering and Smoothing*, Cambridge University Press, 2013,
  Theorem 4.2.
* Peter D. Joseph introduced the symmetric form of the covariance update named after him.
-/

public section

noncomputable section

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The innovation covariance `C P Cᵀ + R` of a prior covariance `P`, an observation matrix `C`
and an observation-noise covariance `R`. -/
def innovationCov (C : Matrix κ ι ℝ) (R : Matrix κ κ ℝ) (P : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  C * P * Cᵀ + R

/-- The Kalman gain `P Cᵀ (C P Cᵀ + R)⁻¹`. -/
def kalmanGain (C : Matrix κ ι ℝ) (R : Matrix κ κ ℝ) (P : Matrix ι ι ℝ) : Matrix ι κ ℝ :=
  P * Cᵀ * (innovationCov C R P)⁻¹

/-- The measurement update `P - P Cᵀ (C P Cᵀ + R)⁻¹ C P` of a covariance `P`. -/
def measurementUpdate (C : Matrix κ ι ℝ) (R : Matrix κ κ ℝ) (P : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  P - kalmanGain C R P * C * P

omit [DecidableEq κ] in
/-- The time update `A P Aᵀ + Q` of a covariance `P`. -/
def timeUpdate (A Q P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A * P * Aᵀ + Q

/-- The discrete Riccati map `P ↦ A (P - P Cᵀ (C P Cᵀ + R)⁻¹ C P) Aᵀ + Q`: the measurement
update followed by the time update. -/
def riccatiMap (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) (Q : Matrix ι ι ℝ) (R : Matrix κ κ ℝ)
    (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  timeUpdate A Q (measurementUpdate C R P)

section Defs

variable {A Q P : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

omit [Fintype κ] [DecidableEq κ] in
theorem innovationCov_def : innovationCov C R P = C * P * Cᵀ + R := (rfl)

theorem kalmanGain_def : kalmanGain C R P = P * Cᵀ * (innovationCov C R P)⁻¹ := (rfl)

theorem measurementUpdate_def :
    measurementUpdate C R P = P - kalmanGain C R P * C * P := (rfl)

omit [DecidableEq κ] in
theorem timeUpdate_def : timeUpdate A Q P = A * P * Aᵀ + Q := (rfl)

theorem riccatiMap_def :
    riccatiMap A C Q R P = timeUpdate A Q (measurementUpdate C R P) := (rfl)

/-- The measurement update is the Schur complement `P - (P Cᵀ) S⁻¹ (C P)` of the innovation
covariance `S` in the block matrix with blocks `P`, `P Cᵀ`, `C P` and `S`. -/
theorem measurementUpdate_eq_sub :
    measurementUpdate C R P = P - P * Cᵀ * (innovationCov C R P)⁻¹ * (C * P) := by
  rw [measurementUpdate_def, kalmanGain_def, Matrix.mul_assoc _ C P]

/-- When the innovation covariance is invertible, the gain solves `K S = P Cᵀ`. -/
theorem kalmanGain_mul_innovationCov (hS : IsUnit (innovationCov C R P)) :
    kalmanGain C R P * innovationCov C R P = P * Cᵀ := by
  rw [kalmanGain_def, nonsing_inv_mul_cancel_right _ _ ((isUnit_iff_isUnit_det _).mp hS)]

/-- With a singular innovation covariance, Mathlib's junk inverse makes the gain vanish. -/
theorem kalmanGain_of_not_isUnit (hS : ¬IsUnit (innovationCov C R P)) :
    kalmanGain C R P = 0 := by
  rw [kalmanGain_def, nonsing_inv_apply_not_isUnit _ ((isUnit_iff_isUnit_det _).not.mp hS),
    Matrix.mul_zero]

/-- With a singular innovation covariance, the measurement update returns the prior covariance. -/
theorem measurementUpdate_of_not_isUnit (hS : ¬IsUnit (innovationCov C R P)) :
    measurementUpdate C R P = P := by
  rw [measurementUpdate_def, kalmanGain_of_not_isUnit hS, Matrix.zero_mul, Matrix.zero_mul,
    sub_zero]

omit [Fintype κ] [DecidableEq κ] in
@[simp]
theorem innovationCov_zero_left : innovationCov (0 : Matrix κ ι ℝ) R P = R := by
  simp [innovationCov_def]

/-- An observation matrix `0` carries no information: the gain vanishes. -/
@[simp]
theorem kalmanGain_zero_left : kalmanGain (0 : Matrix κ ι ℝ) R P = 0 := by
  simp [kalmanGain_def]

/-- An observation matrix `0` carries no information: the update returns the prior. -/
@[simp]
theorem measurementUpdate_zero_left : measurementUpdate (0 : Matrix κ ι ℝ) R P = P := by
  simp [measurementUpdate_def]

omit [Fintype κ] [DecidableEq κ] in
@[simp]
theorem innovationCov_zero_right : innovationCov C R (0 : Matrix ι ι ℝ) = R := by
  simp [innovationCov_def]

@[simp]
theorem kalmanGain_zero_right : kalmanGain C R (0 : Matrix ι ι ℝ) = 0 := by
  simp [kalmanGain_def]

@[simp]
theorem measurementUpdate_zero_right : measurementUpdate C R (0 : Matrix ι ι ℝ) = 0 := by
  simp [measurementUpdate_def]

end Defs

/-! ### Completion of the square -/

section Joseph

variable [DecidableEq ι] {P : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-- **Completion of the square.** If `P` and `R` are symmetric and the innovation covariance
`S = C P Cᵀ + R` is invertible, then for every gain `K` the Joseph form
`(1 - K C) P (1 - K C)ᵀ + K R Kᵀ` of the covariance of the error of `x̂ + K (y - C x̂)` is the
measurement update plus `(K - K*) S (K - K*)ᵀ`, where `K*` is the Kalman gain. -/
theorem joseph_eq_measurementUpdate_add (hP : P.IsSymm) (hR : R.IsSymm)
    (hS : IsUnit (innovationCov C R P)) (K : Matrix ι κ ℝ) :
    (1 - K * C) * P * (1 - K * C)ᵀ + K * R * Kᵀ =
      measurementUpdate C R P +
        (K - kalmanGain C R P) * innovationCov C R P * (K - kalmanGain C R P)ᵀ := by
  rw [measurementUpdate_def]
  set G := kalmanGain C R P
  set S := innovationCov C R P with hSdef
  have hG : G * S = P * Cᵀ := kalmanGain_mul_innovationCov hS
  have hSsymm : Sᵀ = S := by
    rw [hSdef, innovationCov_def]
    exact ((hP.mul_mul_transpose C).add hR).eq
  -- The transpose of `G S = P Cᵀ`, by the symmetry of `S` and `P`.
  have hGt : S * Gᵀ = C * P := by
    rw [← hSsymm, ← transpose_mul, hG, transpose_mul, transpose_transpose, hP.eq]
  have hcross : (K - G) * S * (K - G)ᵀ = (K * S - P * Cᵀ) * Kᵀ - (K - G) * (C * P) := by
    rw [transpose_sub, Matrix.mul_sub, Matrix.mul_assoc (K - G) S Gᵀ, hGt, Matrix.sub_mul K G S,
      hG]
  rw [hcross, hSdef, innovationCov_def, transpose_sub, transpose_mul,
    transpose_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
    Matrix.one_mul, Matrix.mul_one]
  abel

/-- At the Kalman gain the correction term of the completion of the square vanishes: the Joseph
form of the Kalman gain is the measurement update. -/
theorem joseph_kalmanGain (hP : P.IsSymm) (hR : R.IsSymm) (hS : IsUnit (innovationCov C R P)) :
    (1 - kalmanGain C R P * C) * P * (1 - kalmanGain C R P * C)ᵀ +
        kalmanGain C R P * R * (kalmanGain C R P)ᵀ = measurementUpdate C R P := by
  rw [joseph_eq_measurementUpdate_add hP hR hS, sub_self, Matrix.zero_mul, Matrix.zero_mul,
    add_zero]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- The innovation covariance of a positive semidefinite prior and observation noise is positive
semidefinite. -/
theorem PosSemidef.innovationCov (hP : P.PosSemidef) (hR : R.PosSemidef) (C : Matrix κ ι ℝ) :
    (Matrix.innovationCov C R P).PosSemidef := by
  rw [innovationCov_def]
  exact (hP.mul_mul_transpose_same C).add hR

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- The innovation covariance of a positive semidefinite prior and a positive definite
observation noise is positive definite. -/
theorem PosSemidef.posDef_innovationCov (hP : P.PosSemidef) (hR : R.PosDef) (C : Matrix κ ι ℝ) :
    (Matrix.innovationCov C R P).PosDef := by
  rw [innovationCov_def]
  exact PosDef.posSemidef_add (hP.mul_mul_transpose_same C) hR

/-- **The Kalman gain minimizes the error covariance.** For a positive semidefinite `P` and a
positive definite `R`, the Joseph form of every gain `K` exceeds the measurement update in the
Loewner order. -/
theorem joseph_sub_measurementUpdate_posSemidef (hP : P.PosSemidef) (hR : R.PosDef)
    (K : Matrix ι κ ℝ) :
    ((1 - K * C) * P * (1 - K * C)ᵀ + K * R * Kᵀ - measurementUpdate C R P).PosSemidef := by
  have hS := hP.posDef_innovationCov hR C
  rw [joseph_eq_measurementUpdate_add hP.isHermitian.isSymm hR.isHermitian.isSymm hS.isUnit,
    add_sub_cancel_left]
  exact hS.posSemidef.mul_mul_transpose_same (K - kalmanGain C R P)

/-- **The Kalman gain is the only minimizer.** For a positive semidefinite `P` and a positive
definite `R`, the Joseph form of a gain `K` equals the measurement update exactly when `K` is the
Kalman gain. -/
theorem joseph_eq_measurementUpdate_iff (hP : P.PosSemidef) (hR : R.PosDef)
    (K : Matrix ι κ ℝ) :
    (1 - K * C) * P * (1 - K * C)ᵀ + K * R * Kᵀ = measurementUpdate C R P ↔
      K = kalmanGain C R P := by
  have hS := hP.posDef_innovationCov hR C
  rw [joseph_eq_measurementUpdate_add hP.isHermitian.isSymm hR.isHermitian.isSymm hS.isUnit,
    add_eq_left, ← conjTranspose_eq_transpose_of_trivial,
    hS.mul_mul_conjTranspose_same_eq_zero_iff, sub_eq_zero]

end Joseph

/-! ### Positivity -/

section Positivity

variable {A Q P : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-- The measurement update of a positive semidefinite covariance with a positive semidefinite
observation noise is positive semidefinite. When the innovation covariance is invertible, the
update is the Joseph form of the Kalman gain; otherwise it is the prior itself. -/
theorem PosSemidef.measurementUpdate (hP : P.PosSemidef) (hR : R.PosSemidef)
    (C : Matrix κ ι ℝ) : (Matrix.measurementUpdate C R P).PosSemidef := by
  classical
  by_cases hS : IsUnit (Matrix.innovationCov C R P)
  · rw [← joseph_kalmanGain hP.isHermitian.isSymm hR.isHermitian.isSymm hS]
    exact (hP.mul_mul_transpose_same _).add (hR.mul_mul_transpose_same (kalmanGain C R P))
  · rwa [measurementUpdate_of_not_isUnit hS]

omit [DecidableEq κ] in
/-- The time update of a positive semidefinite covariance with a positive semidefinite process
noise is positive semidefinite. -/
theorem PosSemidef.timeUpdate (hP : P.PosSemidef) (hQ : Q.PosSemidef) (A : Matrix ι ι ℝ) :
    (Matrix.timeUpdate A Q P).PosSemidef := by
  rw [timeUpdate_def]
  exact (hP.mul_mul_transpose_same A).add hQ

omit [DecidableEq κ] in
/-- The time update of a positive semidefinite covariance with a positive definite process noise
is positive definite. -/
theorem PosSemidef.posDef_timeUpdate (hP : P.PosSemidef) (hQ : Q.PosDef) (A : Matrix ι ι ℝ) :
    (Matrix.timeUpdate A Q P).PosDef := by
  rw [timeUpdate_def]
  exact PosDef.posSemidef_add (hP.mul_mul_transpose_same A) hQ

/-- The Riccati map preserves positive semidefiniteness: if `P`, `Q` and `R` are positive
semidefinite, so is `riccatiMap A C Q R P`, for every `A` and `C`. -/
theorem PosSemidef.riccatiMap (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) : (Matrix.riccatiMap A C Q R P).PosSemidef := by
  rw [riccatiMap_def]
  exact (hP.measurementUpdate hR C).timeUpdate hQ A

/-- If `P` and `R` are positive semidefinite and `Q` is positive definite, the Riccati map
`riccatiMap A C Q R P` is positive definite, for every `A` and `C`. -/
theorem PosSemidef.posDef_riccatiMap (hP : P.PosSemidef) (hQ : Q.PosDef) (hR : R.PosSemidef)
    (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) : (Matrix.riccatiMap A C Q R P).PosDef := by
  rw [riccatiMap_def]
  exact (hP.measurementUpdate hR C).posDef_timeUpdate hQ A

end Positivity

/-! ### Monotonicity -/

section Monotonicity

variable {A Q P P' : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-- The measurement update is monotone in the Loewner order: if `R` is positive definite, `P` is
positive semidefinite and `P' - P` is positive semidefinite, then so is
`measurementUpdate C R P' - measurementUpdate C R P`. -/
theorem measurementUpdate_sub_posSemidef (hR : R.PosDef) (hP : P.PosSemidef)
    (hPP' : (P' - P).PosSemidef) :
    (measurementUpdate C R P' - measurementUpdate C R P).PosSemidef := by
  classical
  have hP' : P'.PosSemidef := by simpa using hP.add hPP'
  set K := kalmanGain C R P'
  -- The Joseph form of the gain `K` of `P'` is the update of `P'` at `P'`, and dominates the
  -- update of `P` at `P`; the two Joseph forms differ by a congruence of `P' - P`.
  have hK : (1 - K * C) * P' * (1 - K * C)ᵀ + K * R * Kᵀ = measurementUpdate C R P' :=
    joseph_kalmanGain hP'.isHermitian.isSymm hR.isHermitian.isSymm
      (hP'.posDef_innovationCov hR C).isUnit
  have hJ := joseph_sub_measurementUpdate_posSemidef (C := C) hP hR K
  set J := 1 - K * C
  have hdiff : measurementUpdate C R P' - measurementUpdate C R P =
      J * (P' - P) * Jᵀ + (J * P * Jᵀ + K * R * Kᵀ - measurementUpdate C R P) := by
    rw [← hK, Matrix.mul_sub J P' P, Matrix.sub_mul _ _ Jᵀ]
    abel
  rw [hdiff]
  refine PosSemidef.add ?_ hJ
  exact hPP'.mul_mul_transpose_same J

/-- **Monotonicity of the Riccati map.** If `R` is positive definite, `P` is positive
semidefinite and `P' - P` is positive semidefinite, then so is
`riccatiMap A C Q R P' - riccatiMap A C Q R P`, for every `A`, `C` and `Q`. -/
theorem riccatiMap_sub_posSemidef (hR : R.PosDef) (hP : P.PosSemidef)
    (hPP' : (P' - P).PosSemidef) :
    (riccatiMap A C Q R P' - riccatiMap A C Q R P).PosSemidef := by
  rw [riccatiMap_def, riccatiMap_def, timeUpdate_def, timeUpdate_def, add_sub_add_right_eq_sub,
    ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (measurementUpdate_sub_posSemidef (C := C) hR hP hPP').mul_mul_transpose_same A

end Monotonicity

/-! ### The information form -/

section Information

variable [DecidableEq ι] {P : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

omit [DecidableEq ι] in
/-- The Kalman gain in terms of the updated covariance: if the innovation covariance and `R` are
invertible, the gain is `P⁺ Cᵀ R⁻¹`, where `P⁺` is the measurement update of `P`. The prior `P`
may be singular. -/
theorem kalmanGain_eq_measurementUpdate_mul (hS : IsUnit (innovationCov C R P))
    (hR : IsUnit R) :
    kalmanGain C R P = measurementUpdate C R P * Cᵀ * R⁻¹ := by
  have hR' := (isUnit_iff_isUnit_det _).mp hR
  -- `P⁺ Cᵀ = P Cᵀ - K C P Cᵀ = K (S - C P Cᵀ) = K R`.
  have hPC : (P - kalmanGain C R P * C * P) * Cᵀ = kalmanGain C R P * R := by
    rw [Matrix.sub_mul, ← kalmanGain_mul_innovationCov hS, innovationCov_def]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [measurementUpdate_def, hPC, mul_nonsing_inv_cancel_right _ _ hR']

/-- **The measurement update as an inverse.** If `P` and `R` are positive definite, the updated
covariance is the inverse of the information matrix `P⁻¹ + Cᵀ R⁻¹ C`: this is the Woodbury
identity. -/
theorem measurementUpdate_eq_inv (hP : P.PosDef) (hR : R.PosDef) :
    measurementUpdate C R P = (P⁻¹ + Cᵀ * R⁻¹ * C)⁻¹ := by
  have hRR := nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hR.isUnit)
  have hPP := nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP.isUnit)
  have hinner : IsUnit (R⁻¹⁻¹ + C * P⁻¹⁻¹ * Cᵀ) := by
    rw [hRR, hPP, add_comm, ← innovationCov_def]
    exact (hP.posSemidef.posDef_innovationCov hR C).isUnit
  rw [add_mul_mul_inv_eq_sub _ _ _ _ hP.inv.isUnit hR.inv.isUnit hinner, hRR, hPP, add_comm R,
    ← innovationCov_def, measurementUpdate_eq_sub, Matrix.mul_assoc _ C P]

/-- **The information form of the measurement update.** If `P` and `R` are positive definite,
the inverse of the updated covariance is `P⁻¹ + Cᵀ R⁻¹ C`. -/
theorem inv_measurementUpdate (hP : P.PosDef) (hR : R.PosDef) :
    (measurementUpdate C R P)⁻¹ = P⁻¹ + Cᵀ * R⁻¹ * C := by
  have hI := hP.inv_add_conjTranspose_mul_inv_mul hR.posSemidef C
  rw [conjTranspose_eq_transpose_of_trivial] at hI
  rw [measurementUpdate_eq_inv hP hR, nonsing_inv_nonsing_inv _
    ((isUnit_iff_isUnit_det _).mp hI.isUnit)]

omit [DecidableEq ι] in
/-- The measurement update of a positive definite covariance with a positive definite
observation noise is positive definite, as the inverse of `P⁻¹ + Cᵀ R⁻¹ C`. -/
theorem PosDef.measurementUpdate (hP : P.PosDef) (hR : R.PosDef) (C : Matrix κ ι ℝ) :
    (Matrix.measurementUpdate C R P).PosDef := by
  classical
  rw [measurementUpdate_eq_inv hP hR, ← conjTranspose_eq_transpose_of_trivial C]
  exact (hP.inv_add_conjTranspose_mul_inv_mul hR.posSemidef C).inv

/-- **The information form of the filtered mean.** If `P` and `R` are positive definite, the
filtered mean `x̂⁺ = x̂ + K* (y - C x̂)` satisfies `(P⁺)⁻¹ x̂⁺ = P⁻¹ x̂ + Cᵀ R⁻¹ y`, where `K*` is
the Kalman gain and `P⁺` the measurement update of `P`. -/
theorem inv_measurementUpdate_mulVec_add_kalmanGain (hP : P.PosDef) (hR : R.PosDef)
    (x : ι → ℝ) (y : κ → ℝ) :
    (measurementUpdate C R P)⁻¹ *ᵥ (x + kalmanGain C R P *ᵥ (y - C *ᵥ x)) =
      P⁻¹ *ᵥ x + (Cᵀ * R⁻¹) *ᵥ y := by
  have hU := (isUnit_iff_isUnit_det _).mp (hP.measurementUpdate hR C).isUnit
  -- `(P⁺)⁻¹ K* = Cᵀ R⁻¹` by the expression of the gain through `P⁺`.
  have hK : (measurementUpdate C R P)⁻¹ * kalmanGain C R P = Cᵀ * R⁻¹ := by
    rw [kalmanGain_eq_measurementUpdate_mul (hP.posSemidef.posDef_innovationCov hR C).isUnit
      hR.isUnit, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hU]
  rw [mulVec_add, mulVec_mulVec, hK, mulVec_sub, mulVec_mulVec, inv_measurementUpdate hP hR,
    add_mulVec]
  abel

end Information

end Matrix
