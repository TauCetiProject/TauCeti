/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateT.Marginal
import TauCeti.Probability.Distributions.StudentT.Moments
public import TauCeti.Probability.Moments.Covariance
import Mathlib.Analysis.Matrix.PosDef

/-!
# Moments of multivariate t laws

A multivariate t law with nonzero positive semidefinite scale and positive degrees of freedom
`ν` has a finite natural norm moment of order `n` exactly when `n < ν`. Zero scale gives a
Dirac law and hence moments of every order, including in zero dimension. The mean is the
location for `ν > 1`, and the covariance is `ν / (ν - 2)` times the scale for `ν > 2`.

The existing `map_eval_multivariateTMeasure` and `map_inner_multivariateTMeasure` reduce the
calculation to scalar Student t moments. Mathlib's `memLp_piLp_iff` and covariance bilinear
form give the vector mean and covariance by coordinate integrability and polarization.
In particular, singular nonzero scales have the same moment threshold as
nonsingular scales.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {ν : ℝ}

/-- The natural `Lᵖ` moments of a multivariate t law are finite exactly below its degrees of
freedom, except that a zero scale gives finite moments of every order. -/
@[simp]
theorem memLp_id_natCast_multivariateTMeasure_iff (hν : 0 < ν) (hS : S.PosSemidef) (n : ℕ) :
    MemLp id n (multivariateTMeasure m S ν) ↔ S = 0 ∨ (n : ℝ) < ν := by
  let _ := isProbabilityMeasure_studentTMeasure hν
  have hcoord (i : ι) :
      MemLp (fun x : EuclideanSpace ℝ ι => x i) n (multivariateTMeasure m S ν) ↔
        S i i = 0 ∨ (n : ℝ) < ν := by
    have hmap : MemLp id n ((multivariateTMeasure m S ν).map
        (fun x : EuclideanSpace ℝ ι => x i)) ↔
        MemLp (fun x : EuclideanSpace ℝ ι => x i) n (multivariateTMeasure m S ν) := by
      simpa only [Function.id_comp] using
        (memLp_map_measure_iff (g := id) (f := fun x : EuclideanSpace ℝ ι => x i)
          aestronglyMeasurable_id (by fun_prop))
    rw [← hmap, map_eval_multivariateTMeasure m hS ν i]
    by_cases hi : S i i = 0
    · simp [hi, Measure.map_const]
    · rw [memLp_id_map_affine_iff (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne hS.diag_nonneg (Ne.symm hi))),
        memLp_id_natCast_studentTMeasure_iff hν]
      simp [hi]
  rw [memLp_piLp_iff]
  simp only [id_eq, hcoord]
  constructor
  · intro h
    by_cases hn : (n : ℝ) < ν
    · exact Or.inr hn
    · left
      apply hS.trace_eq_zero_iff.mp
      exact Finset.sum_eq_zero fun i _ => (h i).resolve_right hn
  · rintro (rfl | hn) i
    · simp
    · exact Or.inr hn

/-- The identity is square-integrable under a multivariate t law when `ν > 2`. -/
theorem memLp_two_id_multivariateTMeasure (hν : 2 < ν) (hS : S.PosSemidef) :
    MemLp id 2 (multivariateTMeasure m S ν) :=
  (memLp_id_natCast_multivariateTMeasure_iff (lt_trans zero_lt_two hν) hS 2).2
    (Or.inr (by simpa using hν))

/-- A natural norm moment of a multivariate t law exists exactly below its degrees of
freedom, with every order allowed at zero scale. -/
@[simp]
theorem integrable_norm_pow_multivariateTMeasure_iff (hν : 0 < ν) (hS : S.PosSemidef)
    (n : ℕ) :
    Integrable (fun x => ‖x‖ ^ n) (multivariateTMeasure m S ν) ↔ S = 0 ∨ (n : ℝ) < ν := by
  let _ := isProbabilityMeasure_multivariateTMeasure m hν hS
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [hν]
  · rw [← memLp_id_natCast_multivariateTMeasure_iff (m := m) hν hS n,
      ← integrable_norm_rpow_iff aestronglyMeasurable_id (by exact_mod_cast hn.ne')
        (by simp)]
    simp

/-- The vector identity is integrable exactly above one degree of freedom, or at zero scale. -/
@[simp]
theorem integrable_id_multivariateTMeasure_iff (hν : 0 < ν) (hS : S.PosSemidef) :
    Integrable id (multivariateTMeasure m S ν) ↔ S = 0 ∨ 1 < ν := by
  simpa only [memLp_one_iff_integrable, Nat.cast_one] using
    memLp_id_natCast_multivariateTMeasure_iff (m := m) hν hS 1

/-- The Bochner mean of a multivariate t law is its location when `ν > 1`. -/
@[simp]
theorem integral_id_multivariateTMeasure (hν : 1 < ν) (hS : S.PosSemidef) :
    ∫ x, x ∂multivariateTMeasure m S ν = m := by
  have hν0 : 0 < ν := lt_trans zero_lt_one hν
  let _ := isProbabilityMeasure_multivariateTMeasure m hν0 hS
  let _ := isProbabilityMeasure_studentTMeasure hν0
  have hμ : Integrable id (multivariateTMeasure m S ν) :=
    (integrable_id_multivariateTMeasure_iff hν0 hS).2 (Or.inr hν)
  have ht : Integrable id (studentTMeasure ν) :=
    (integrable_id_studentTMeasure_iff hν0).2 hν
  ext i
  have heval := eval_integral_piLp (fun j => hμ.eval_piLp j) i
  simp only [id_eq] at heval
  have hi : HasLaw (fun x : EuclideanSpace ℝ ι => x i)
      ((studentTMeasure ν).map fun t => m i + √(S i i) * t)
      (multivariateTMeasure m S ν) :=
    ⟨by fun_prop, map_eval_multivariateTMeasure m hS ν i⟩
  rw [heval, hi.integral_eq, integral_id_map_affine ht, integral_id_studentTMeasure]
  simp

/-- The variance of a real linear projection of a multivariate t vector is
`ν / (ν - 2)` times its directional scale, including zero directional scale. -/
@[simp]
theorem variance_inner_multivariateTMeasure (hν : 2 < ν) (hS : S.PosSemidef)
    (θ : EuclideanSpace ℝ ι) :
    Var[fun x => ⟪θ, x⟫; multivariateTMeasure m S ν] =
      ν / (ν - 2) * ⟪θ, S.toEuclideanLin θ⟫ := by
  have hν0 : 0 < ν := lt_trans zero_lt_two hν
  let _ := isProbabilityMeasure_multivariateTMeasure m hν0 hS
  let _ := isProbabilityMeasure_studentTMeasure hν0
  rw [← variance_id_map (by fun_prop), map_inner_multivariateTMeasure m θ hS ν,
    variance_id_map_affine, variance_id_studentTMeasure hν, Real.sq_sqrt]
  · ring
  · simpa only [RCLike.re_to_real, real_inner_comm] using
      (Matrix.isPositive_toEuclideanLin_iff.mpr hS).2 θ

/-- The covariance bilinear form of a multivariate t law is `ν / (ν - 2)` times the
bilinear form of its scale matrix. -/
@[simp]
theorem covarianceBilin_multivariateTMeasure (hν : 2 < ν) (hS : S.PosSemidef)
    (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (multivariateTMeasure m S ν) x y =
      ν / (ν - 2) * ⟪x, S.toEuclideanLin y⟫ := by
  let _ := isProbabilityMeasure_multivariateTMeasure m (lt_trans zero_lt_two hν) hS
  have hμ : MemLp id 2 (multivariateTMeasure m S ν) :=
    memLp_two_id_multivariateTMeasure hν hS
  have hself (z : EuclideanSpace ℝ ι) :
      covarianceBilin (multivariateTMeasure m S ν) z z =
        ν / (ν - 2) * ⟪z, S.toEuclideanLin z⟫ := by
    rw [covarianceBilin_self hμ, variance_inner_multivariateTMeasure hν hS]
  have hsym : ⟪y, S.toEuclideanLin x⟫ = ⟪x, S.toEuclideanLin y⟫ := by
    simpa only [real_inner_comm] using
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hS.isHermitian) x y
  have h := hself (x + y)
  simp only [map_add, add_apply, inner_add_left, inner_add_right] at h
  rw [covarianceBilin_comm y x, hself x, hself y, hsym] at h
  linarith

/-- The covariance matrix of a multivariate t law is `ν / (ν - 2)` times its scale matrix;
the scale itself is not the covariance. -/
@[simp]
theorem covMatrix_multivariateTMeasure (hν : 2 < ν) (hS : S.PosSemidef) :
    covMatrix (multivariateTMeasure m S ν) = (ν / (ν - 2)) • S := by
  let _ := isProbabilityMeasure_multivariateTMeasure m (lt_trans zero_lt_two hν) hS
  have hμ : MemLp id 2 (multivariateTMeasure m S ν) :=
    memLp_two_id_multivariateTMeasure hν hS
  ext i j
  have h := covarianceBilin_multivariateTMeasure (m := m) hν hS
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [covarianceBilin_eq_covMatrix _ hμ] at h
  simpa [EuclideanSpace.inner_single_left] using h

section HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}

/-- A vector with a multivariate t law has a finite natural norm moment exactly below the
degrees of freedom, unless its scale is zero. -/
theorem integrable_norm_pow_of_hasLaw_multivariateTMeasure_iff (hν : 0 < ν)
    (hS : S.PosSemidef) (hX : HasLaw X (multivariateTMeasure m S ν) P) (n : ℕ) :
    Integrable (fun ω => ‖X ω‖ ^ n) P ↔ S = 0 ∨ (n : ℝ) < ν := by
  have h := integrable_norm_pow_multivariateTMeasure_iff (m := m) hν hS n
  rw [← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable] at h
  exact h

/-- The expectation of a vector with a multivariate t law is its location for `ν > 1`. -/
theorem integral_of_hasLaw_multivariateTMeasure (hν : 1 < ν) (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateTMeasure m S ν) P) : ∫ ω, X ω ∂P = m := by
  rw [hX.integral_eq, integral_id_multivariateTMeasure hν hS]

/-- Covariance of linear observables of a multivariate t vector, for `ν > 2`. -/
theorem covariance_inner_of_hasLaw_multivariateTMeasure (hν : 2 < ν) (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateTMeasure m S ν) P) (x y : EuclideanSpace ℝ ι) :
    cov[fun ω => ⟪x, X ω⟫, fun ω => ⟪y, X ω⟫; P] =
      ν / (ν - 2) * ⟪x, S.toEuclideanLin y⟫ := by
  let _ := isProbabilityMeasure_multivariateTMeasure m (lt_trans zero_lt_two hν) hS
  have hμ : MemLp id 2 (multivariateTMeasure m S ν) :=
    memLp_two_id_multivariateTMeasure hν hS
  rw [hX.covariance_fun_comp (by fun_prop) (by fun_prop),
    ← covarianceBilin_apply_eq_cov hμ, covarianceBilin_multivariateTMeasure hν hS]

end HasLaw

end TauCeti.Probability
