/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.Matrix.Control.Riccati

/-!
# The recursion of the discrete-time Kalman filter

A linear state-space model `x(k+1) = A(k) x(k) + w(k)`, `y(k) = C(k) x(k) + v(k)` with states in
`EuclideanSpace ℝ ι` and observations in `EuclideanSpace ℝ κ` is described by its coefficient
matrices `A k` and `C k`, the covariances `Q k` and `R k` of the process and observation noises,
and the mean `m₀` and covariance `P₀` of the initial state. This file defines these data as
`TauCeti.StateSpaceModel` and the Kalman filter as two explicit recursions on them:

* the covariance recursion, which does not depend on the observations: the predicted covariance
  `P(k|k-1)` starts at `P₀` and follows the Riccati map, and the filtered covariance `P(k|k)` is
  its measurement update;
* the mean recursion along an observation sequence `ys`: the predicted mean `x̂(k|k-1)` starts at
  `m₀`, the filtered mean is `x̂(k|k) = x̂(k|k-1) + K(k) (ys k - C(k) x̂(k|k-1))` with the Kalman
  gain `K(k)` of `P(k|k-1)`, and `x̂(k+1|k) = A(k) x̂(k|k)`.

The predicted mean at time `k` is an affine function of the observations before time `k`, and the
filtered mean an affine function of the observations up to time `k`. The covariances are positive
semidefinite when `P₀`, the `Q k` and the `R k` are, and the predicted covariance after a positive
definite process noise is positive definite. No probability enters here: the probabilistic
models whose conditional laws these recursions compute are stated on top of this file.

## Main definitions

* `TauCeti.StateSpaceModel ι κ`: the data of a linear state-space model.
* `TauCeti.StateSpaceModel.predCov` and `TauCeti.StateSpaceModel.filtCov`: the predicted and
  filtered covariances.
* `TauCeti.StateSpaceModel.gain`: the Kalman gain at time `k`.
* `TauCeti.StateSpaceModel.predMean` and `TauCeti.StateSpaceModel.filtMean`: the predicted and
  filtered means along an observation sequence.

## Main results

* `TauCeti.StateSpaceModel.exists_affineMap_predMean` and
  `TauCeti.StateSpaceModel.exists_affineMap_filtMean`: the means are affine functions of the
  observations they read, and `TauCeti.StateSpaceModel.predMean_congr` and
  `TauCeti.StateSpaceModel.filtMean_congr` say they read no others.
* `TauCeti.StateSpaceModel.posSemidef_predCov`, `TauCeti.StateSpaceModel.posSemidef_filtCov` and
  `TauCeti.StateSpaceModel.posDef_predCov_succ`: positivity of the covariances.

## References

* Brian D. O. Anderson and John B. Moore, *Optimal Filtering*, Prentice-Hall, 1979: §3.1,
  equations (1.6) to (1.12).
* Simo Särkkä, *Bayesian Filtering and Smoothing*, Cambridge University Press, 2013,
  Theorem 4.2. Its observations start at time `1`; here the first observation is `ys 0`.
* Rudolf E. Kalman introduced the filter in 1960.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

/-- The data of a linear state-space model `x(k+1) = A(k) x(k) + w(k)`, `y(k) = C(k) x(k) + v(k)`
with states in `EuclideanSpace ℝ ι` and observations in `EuclideanSpace ℝ κ`: the transition
matrices `A k`, the observation matrices `C k`, the process-noise covariances `Q k`, the
observation-noise covariances `R k`, and the mean `m₀` and covariance `P₀` of the initial state.
No condition is built in; each statement carries the hypotheses it needs. -/
@[ext]
structure StateSpaceModel (ι κ : Type*) where
  /-- The transition matrix at time `k`. -/
  A : ℕ → Matrix ι ι ℝ
  /-- The observation matrix at time `k`. -/
  C : ℕ → Matrix κ ι ℝ
  /-- The process-noise covariance at time `k`. -/
  Q : ℕ → Matrix ι ι ℝ
  /-- The observation-noise covariance at time `k`. -/
  R : ℕ → Matrix κ κ ℝ
  /-- The mean of the initial state. -/
  m₀ : EuclideanSpace ℝ ι
  /-- The covariance of the initial state. -/
  P₀ : Matrix ι ι ℝ

namespace StateSpaceModel

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (M : StateSpaceModel ι κ)

/-! ### The covariance recursion -/

/-- The predicted covariance `P(k|k-1)`: `P₀` at time `0`, then the Riccati map of time `k`
applied to `P(k|k-1)` at time `k + 1`. -/
def predCov : ℕ → Matrix ι ι ℝ
  | 0 => M.P₀
  | k + 1 => riccatiMap (M.A k) (M.C k) (M.Q k) (M.R k) (predCov k)

/-- The filtered covariance `P(k|k)`: the measurement update of the predicted covariance. -/
def filtCov (k : ℕ) : Matrix ι ι ℝ :=
  measurementUpdate (M.C k) (M.R k) (M.predCov k)

/-- The Kalman gain at time `k`, the gain `P Cᵀ (C P Cᵀ + R)⁻¹` of the predicted covariance
`P = P(k|k-1)`. -/
def gain (k : ℕ) : Matrix ι κ ℝ :=
  kalmanGain (M.C k) (M.R k) (M.predCov k)

@[simp]
theorem predCov_zero : M.predCov 0 = M.P₀ := (rfl)

@[simp]
theorem predCov_succ (k : ℕ) :
    M.predCov (k + 1) = riccatiMap (M.A k) (M.C k) (M.Q k) (M.R k) (M.predCov k) := (rfl)

theorem filtCov_def (k : ℕ) : M.filtCov k = measurementUpdate (M.C k) (M.R k) (M.predCov k) :=
  (rfl)

theorem gain_def (k : ℕ) : M.gain k = kalmanGain (M.C k) (M.R k) (M.predCov k) := (rfl)

/-- The predicted covariance is the time update of the filtered covariance. -/
theorem predCov_succ_eq_timeUpdate (k : ℕ) :
    M.predCov (k + 1) = timeUpdate (M.A k) (M.Q k) (M.filtCov k) := by
  rw [predCov_succ, riccatiMap_def, filtCov_def]

/-- The filtered covariance is `P - K C P` with `P` the predicted covariance and `K` the gain. -/
theorem filtCov_eq_sub (k : ℕ) : M.filtCov k = M.predCov k - M.gain k * M.C k * M.predCov k := by
  rw [filtCov_def, measurementUpdate_def, gain_def]

/-! ### Positivity of the covariances -/

variable {M}

/-- If `P₀` and the `Q j` and `R j` for `j < k` are positive semidefinite, so is the predicted
covariance `P(k|k-1)`. -/
theorem posSemidef_predCov {k : ℕ} (hP₀ : M.P₀.PosSemidef)
    (hQ : ∀ j < k, (M.Q j).PosSemidef) (hR : ∀ j < k, (M.R j).PosSemidef) :
    (M.predCov k).PosSemidef := by
  induction k with
  | zero => exact hP₀
  | succ k ih =>
    exact (ih (fun j hj ↦ hQ j (by omega)) fun j hj ↦ hR j (by omega)).riccatiMap
      (hQ k (by omega)) (hR k (by omega)) _ _

/-- If `P₀` and the `Q j` for `j < k` and the `R j` for `j ≤ k` are positive semidefinite, so is
the filtered covariance `P(k|k)`. -/
theorem posSemidef_filtCov {k : ℕ} (hP₀ : M.P₀.PosSemidef)
    (hQ : ∀ j < k, (M.Q j).PosSemidef) (hR : ∀ j ≤ k, (M.R j).PosSemidef) :
    (M.filtCov k).PosSemidef :=
  (posSemidef_predCov hP₀ hQ fun j hj ↦ hR j hj.le).measurementUpdate (hR k le_rfl) _

/-- If the covariances up to time `k` are positive semidefinite and the process noise `Q k` is
positive definite, the predicted covariance `P(k+1|k)` is positive definite. -/
theorem posDef_predCov_succ {k : ℕ} (hP₀ : M.P₀.PosSemidef)
    (hQ : ∀ j < k, (M.Q j).PosSemidef) (hQk : (M.Q k).PosDef)
    (hR : ∀ j ≤ k, (M.R j).PosSemidef) :
    (M.predCov (k + 1)).PosDef :=
  (posSemidef_predCov hP₀ hQ fun j hj ↦ hR j hj.le).posDef_riccatiMap hQk (hR k le_rfl) _ _

variable (M)

/-! ### The mean recursion -/

variable [DecidableEq ι]

/-- The predicted mean `x̂(k|k-1)` along the observation sequence `ys`: `m₀` at time `0`, and
`A(k) (x̂ + K(k) (ys k - C(k) x̂))` at time `k + 1`, where `x̂ = x̂(k|k-1)` and `K(k)` is the Kalman
gain. It reads `ys j` for `j < k` only. -/
def predMean (ys : ℕ → EuclideanSpace ℝ κ) : ℕ → EuclideanSpace ℝ ι
  | 0 => M.m₀
  | k + 1 => (M.A k).toEuclideanLin (predMean ys k +
      (M.gain k).toEuclideanLin (ys k - (M.C k).toEuclideanLin (predMean ys k)))

/-- The filtered mean `x̂(k|k) = x̂ + K(k) (ys k - C(k) x̂)` along the observation sequence `ys`,
where `x̂ = x̂(k|k-1)` is the predicted mean and `K(k)` the Kalman gain. It reads `ys j` for
`j ≤ k` only. -/
def filtMean (ys : ℕ → EuclideanSpace ℝ κ) (k : ℕ) : EuclideanSpace ℝ ι :=
  M.predMean ys k + (M.gain k).toEuclideanLin (ys k - (M.C k).toEuclideanLin (M.predMean ys k))

variable (ys : ℕ → EuclideanSpace ℝ κ)

@[simp]
theorem predMean_zero : M.predMean ys 0 = M.m₀ := (rfl)

/-- The predicted mean is the transition of the filtered mean. -/
@[simp]
theorem predMean_succ (k : ℕ) :
    M.predMean ys (k + 1) = (M.A k).toEuclideanLin (M.filtMean ys k) := (rfl)

theorem filtMean_def (k : ℕ) :
    M.filtMean ys k = M.predMean ys k +
      (M.gain k).toEuclideanLin (ys k - (M.C k).toEuclideanLin (M.predMean ys k)) := (rfl)

/-- If the predicted mean at time `k` is an affine function of the observations before time `k`,
the filtered mean at time `k` is an affine function of the observations up to time `k`. -/
private theorem exists_affineMap_filtMean_of_predMean {k : ℕ}
    (h : ∃ g : (Fin k → EuclideanSpace ℝ κ) →ᵃ[ℝ] EuclideanSpace ℝ ι,
      ∀ ys, M.predMean ys k = g fun j ↦ ys j) :
    ∃ g : (Fin (k + 1) → EuclideanSpace ℝ κ) →ᵃ[ℝ] EuclideanSpace ℝ ι,
      ∀ ys, M.filtMean ys k = g fun j ↦ ys j := by
  obtain ⟨g, hg⟩ := h
  -- The prediction reads the first `k` coordinates of the window, the correction its last one.
  let p := g.comp (LinearMap.funLeft ℝ (EuclideanSpace ℝ κ) (Fin.castSucc (n := k))).toAffineMap
  refine ⟨p + (M.gain k).toEuclideanLin.toAffineMap.comp
    ((LinearMap.proj (Fin.last k)).toAffineMap - (M.C k).toEuclideanLin.toAffineMap.comp p),
    fun ys ↦ ?_⟩
  have hp : p (fun j ↦ ys j) = g fun j ↦ ys j :=
    congrArg g (funext fun j ↦ by simp [LinearMap.funLeft_apply])
  simp [hp, filtMean_def, hg]

/-- The predicted mean `x̂(k|k-1)` is an affine function of the observations `ys j`, `j < k`. -/
theorem exists_affineMap_predMean (k : ℕ) :
    ∃ g : (Fin k → EuclideanSpace ℝ κ) →ᵃ[ℝ] EuclideanSpace ℝ ι,
      ∀ ys, M.predMean ys k = g fun j ↦ ys j := by
  induction k with
  | zero => exact ⟨AffineMap.const ℝ _ M.m₀, fun ys ↦ rfl⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := M.exists_affineMap_filtMean_of_predMean ih
    exact ⟨(M.A k).toEuclideanLin.toAffineMap.comp g, fun ys ↦ by simp [hg]⟩

/-- The filtered mean `x̂(k|k)` is an affine function of the observations `ys j`, `j ≤ k`. -/
theorem exists_affineMap_filtMean (k : ℕ) :
    ∃ g : (Fin (k + 1) → EuclideanSpace ℝ κ) →ᵃ[ℝ] EuclideanSpace ℝ ι,
      ∀ ys, M.filtMean ys k = g fun j ↦ ys j :=
  M.exists_affineMap_filtMean_of_predMean (M.exists_affineMap_predMean k)

variable {M ys}

/-- The predicted mean `x̂(k|k-1)` depends only on the observations `ys j` with `j < k`. -/
theorem predMean_congr {ys' : ℕ → EuclideanSpace ℝ κ} {k : ℕ} (h : ∀ j < k, ys j = ys' j) :
    M.predMean ys k = M.predMean ys' k := by
  obtain ⟨g, hg⟩ := M.exists_affineMap_predMean k
  rw [hg, hg]
  exact congrArg g (funext fun j ↦ h j j.isLt)

/-- The filtered mean `x̂(k|k)` depends only on the observations `ys j` with `j ≤ k`. -/
theorem filtMean_congr {ys' : ℕ → EuclideanSpace ℝ κ} {k : ℕ} (h : ∀ j ≤ k, ys j = ys' j) :
    M.filtMean ys k = M.filtMean ys' k := by
  obtain ⟨g, hg⟩ := M.exists_affineMap_filtMean k
  rw [hg, hg]
  exact congrArg g (funext fun j ↦ h j (Nat.lt_succ_iff.mp j.isLt))

/-! ### Examples

The scalar model `A = C = Q = R = P₀ = 1` with `m₀ = 0`: its predicted covariances are
`1, 3/2, 8/5, …` and its filtered covariances `1/2, 3/5, …`, and the filtered mean after the
observations `y 0` and `y 1` is `(y 0 + 3 y 1) / 5`. -/

/-- The scalar model `A = C = Q = R = P₀ = 1`, `m₀ = 0`. -/
private def scalarModel : StateSpaceModel (Fin 1) (Fin 1) where
  A _ := 1
  C _ := 1
  Q _ := 1
  R _ := 1
  m₀ := 0
  P₀ := 1

/-- The first predicted covariance of the scalar model is `3/2`. -/
private theorem scalarModel_predCov_one : scalarModel.predCov 1 = diagonal fun _ ↦ 3 / 2 := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [scalarModel, riccatiMap_def, timeUpdate_def, measurementUpdate_def, kalmanGain_def,
    innovationCov_def, one_add_one_eq_two, ofNat_apply]

example : scalarModel.predCov 2 = diagonal fun _ ↦ 8 / 5 := by
  rw [predCov_succ, scalarModel_predCov_one]
  ext i j
  fin_cases i; fin_cases j
  norm_num [scalarModel, riccatiMap_def, timeUpdate_def, measurementUpdate_def, kalmanGain_def,
    innovationCov_def]

example : scalarModel.filtCov 0 = diagonal fun _ ↦ 1 / 2 := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [filtCov_def, scalarModel, measurementUpdate_def, kalmanGain_def,
    innovationCov_def, one_add_one_eq_two, ofNat_apply]

example : scalarModel.filtCov 1 = diagonal fun _ ↦ 3 / 5 := by
  rw [filtCov_def, scalarModel_predCov_one]
  ext i j
  fin_cases i; fin_cases j
  norm_num [scalarModel, measurementUpdate_def, kalmanGain_def, innovationCov_def]

example (ys : ℕ → EuclideanSpace ℝ (Fin 1)) :
    scalarModel.filtMean ys 0 = (2 : ℝ)⁻¹ • ys 0 := by
  ext i
  fin_cases i
  norm_num [filtMean_def, gain_def, scalarModel, kalmanGain_def,
    innovationCov_def, one_add_one_eq_two, ofNat_apply, mulVec_diagonal]

example (ys : ℕ → EuclideanSpace ℝ (Fin 1)) :
    scalarModel.predMean ys 1 = (2 : ℝ)⁻¹ • ys 0 := by
  ext i
  fin_cases i
  norm_num [filtMean_def, gain_def, scalarModel, kalmanGain_def,
    innovationCov_def, one_add_one_eq_two, ofNat_apply, mulVec_diagonal]

example (ys : ℕ → EuclideanSpace ℝ (Fin 1)) :
    scalarModel.filtMean ys 1 = (5 : ℝ)⁻¹ • (ys 0 + (3 : ℝ) • ys 1) := by
  rw [filtMean_def, gain_def, scalarModel_predCov_one]
  ext i
  fin_cases i
  norm_num [filtMean_def, gain_def, scalarModel, kalmanGain_def,
    innovationCov_def, one_add_one_eq_two, ofNat_apply, mulVec_diagonal]
  ring

end StateSpaceModel

end TauCeti
