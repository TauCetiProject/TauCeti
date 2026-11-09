/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
public import TauCeti.RingTheory.PowerSeries.BoundedHom
import TauCeti.RingTheory.PowerSeries.SubstInv

/-!
# Recovering the Tate parameter from the j-invariant

The reciprocal of the Tate j-invariant is an integral power series `q + ⋯`. Its integral
compositional inverse converges on the open unit ball over every complete non-archimedean
normed field. Evaluating this inverse at `j⁻¹` recovers the unique nonzero Tate parameter
of norm below one with prescribed invariant `j`, whenever `‖j‖ > 1`.

This supplies the parameter needed to compare a curve with nonintegral j-invariant with a Tate
curve. Equality of j-invariants alone does not assert that the curves are isomorphic over the
base field; the possible twist is not addressed here.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.5.
-/

public section

open PowerSeries

namespace TauCeti

/-- The integral expansion of `1 / j(q) = Δ(q) / c₄(q)³`. -/
noncomputable def tateReciprocalJ : ℤ⟦X⟧ :=
  tateCurve.Δ * (tateCurve.c₄ ^ 3).invOfUnit 1

/-- The reciprocal Tate j-series has zero constant coefficient. -/
@[simp] theorem constantCoeff_tateReciprocalJ : constantCoeff tateReciprocalJ = 0 := by
  simp [tateReciprocalJ]

/-- The reciprocal Tate j-series starts with `q`. -/
@[simp] theorem coeff_one_tateReciprocalJ : coeff 1 tateReciprocalJ = 1 := by
  simp [tateReciprocalJ, coeff_one_mul, constantCoeff_invOfUnit]

/-- Multiplying the reciprocal j-series by `c₄³` gives the Tate discriminant. -/
theorem tateReciprocalJ_mul_c₄_pow_three :
    tateReciprocalJ * tateCurve.c₄ ^ 3 = tateCurve.Δ := by
  rw [tateReciprocalJ, mul_assoc, invOfUnit_mul _ 1 (by simp), mul_one]

/-- The integral compositional inverse of `1 / j(q)`, evaluated later at `1 / j`. -/
noncomputable def tateParameterSeries : ℤ⟦X⟧ :=
  tateReciprocalJ.substInvOfIsUnit (by simp)

/-- The inverse series has zero constant coefficient. -/
@[simp] theorem constantCoeff_tateParameterSeries : constantCoeff tateParameterSeries = 0 := by
  simp [tateParameterSeries]

/-- Substituting the parameter series in the reciprocal j-series gives the variable. -/
@[simp] theorem tateReciprocalJ_subst_tateParameterSeries :
    tateReciprocalJ.subst tateParameterSeries = X :=
  subst_substInvOfIsUnit_right _ constantCoeff_tateReciprocalJ _

/-- Substituting the reciprocal j-series in the parameter series gives the variable. -/
@[simp] theorem tateParameterSeries_subst_tateReciprocalJ :
    tateParameterSeries.subst tateReciprocalJ = X :=
  subst_substInvOfIsUnit_left _ constantCoeff_tateReciprocalJ _

section Ring

variable {K : Type*} [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K]

/-- The inverse parameter series preserves norms in the open unit ball. -/
@[simp] theorem norm_evalIntSeries_tateParameterSeries (q : K) (hq : ‖q‖ < 1) :
    ‖evalIntSeries q hq tateParameterSeries‖ = ‖q‖ := by
  obtain ⟨u, hu⟩ := exists_unit_eq_X_mul_of_subst_eq_X
    constantCoeff_tateParameterSeries tateReciprocalJ_subst_tateParameterSeries
  rw [hu, map_mul, evalIntSeries_X]
  exact norm_mul_evalIntSeries_of_isUnit q q hq u.isUnit

end Ring

section Field

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Evaluation of the reciprocal j-series is the reciprocal of the analytic Tate invariant. -/
@[simp] theorem evalIntSeries_tateReciprocalJ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    evalIntSeries (q : K) hq tateReciprocalJ = (tateCurveAt q hq).j⁻¹ := by
  have h := congrArg (evalIntSeries (q : K) hq) tateReciprocalJ_mul_c₄_pow_three
  have hc : (tateCurveAt q hq).c₄ ≠ 0 := by
    have hn := norm_tateCurveAt_c₄ q hq
    exact fun hz ↦ by simp [hz] at hn
  rw [map_mul, map_pow, ← WeierstrassCurve.map_c₄ tateCurve,
    ← WeierstrassCurve.map_Δ tateCurve, ← tateCurveAt_def] at h
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp
  simpa only [mul_comm] using h

/-- The Tate parameter with prescribed invariant `j` of norm greater than one. -/
noncomputable def tateParameterOfJ (j : K) (hj : 1 < ‖j‖) : Kˣ :=
  Units.mk0 (evalIntSeries j⁻¹ (by simpa using inv_lt_one_of_one_lt₀ hj) tateParameterSeries)
    (by
      apply norm_pos_iff.mp
      rw [norm_evalIntSeries_tateParameterSeries]
      exact norm_pos_iff.mpr (inv_ne_zero (norm_pos_iff.mp (zero_lt_one.trans hj))))

/-- The recovered parameter has norm `‖j‖⁻¹`. -/
@[simp] theorem norm_tateParameterOfJ (j : K) (hj : 1 < ‖j‖) :
    ‖(tateParameterOfJ j hj : K)‖ = ‖j‖⁻¹ := by
  simp [tateParameterOfJ]

/-- The recovered parameter lies in the open unit ball. -/
theorem norm_tateParameterOfJ_lt_one (j : K) (hj : 1 < ‖j‖) :
    ‖(tateParameterOfJ j hj : K)‖ < 1 := by
  rw [norm_tateParameterOfJ]
  exact inv_lt_one_of_one_lt₀ hj

/-- The recovered Tate curve has the prescribed j-invariant. -/
@[simp] theorem j_tateCurveAt_tateParameterOfJ (j : K) (hj : 1 < ‖j‖) :
    (tateCurveAt (tateParameterOfJ j hj) (norm_tateParameterOfJ_lt_one j hj)).j = j := by
  have h := congrArg (evalIntSeries j⁻¹ (by simpa using inv_lt_one_of_one_lt₀ hj))
    tateReciprocalJ_subst_tateParameterSeries
  rw [evalIntSeries_subst _ _ _ _ constantCoeff_tateParameterSeries, evalIntSeries_X] at h
  have he : evalIntSeries (tateParameterOfJ j hj : K)
      (norm_tateParameterOfJ_lt_one j hj) tateReciprocalJ = j⁻¹ := h
  rw [evalIntSeries_tateReciprocalJ] at he
  exact inv_injective he

/-- A Tate parameter of norm below one is uniquely determined by its j-invariant. -/
@[simp] theorem tateParameterOfJ_j_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateParameterOfJ (tateCurveAt q hq).j
      (by
        rw [norm_tateCurveAt_j]
        exact (one_lt_inv₀ (norm_pos_iff.mpr q.ne_zero)).mpr hq) = q := by
  apply Units.ext
  have h := congrArg (evalIntSeries (q : K) hq) tateParameterSeries_subst_tateReciprocalJ
  rw [evalIntSeries_subst _ _ _ _ constantCoeff_tateReciprocalJ, evalIntSeries_X] at h
  simpa only [evalIntSeries_tateReciprocalJ, tateParameterOfJ, Units.val_mk0] using h

/-- The analytic Tate j-invariant is injective on nonzero parameters of norm below one. -/
@[simp] theorem j_tateCurveAt_inj {q r : Kˣ} (hq : ‖(q : K)‖ < 1) (hr : ‖(r : K)‖ < 1) :
    (tateCurveAt q hq).j = (tateCurveAt r hr).j ↔ q = r := by
  constructor
  · intro h
    rw [← tateParameterOfJ_j_tateCurveAt q hq, ← tateParameterOfJ_j_tateCurveAt r hr]
    congr 1
  · rintro rfl
    rfl

/-- Every invariant of norm greater than one comes from exactly one Tate parameter in the
punctured open unit ball. -/
theorem existsUnique_tateCurveAt_j (j : K) (hj : 1 < ‖j‖) :
    ∃! q : {q : Kˣ // ‖(q : K)‖ < 1}, (tateCurveAt q.val q.property).j = j := by
  refine ⟨⟨tateParameterOfJ j hj, norm_tateParameterOfJ_lt_one j hj⟩,
    j_tateCurveAt_tateParameterOfJ j hj, ?_⟩
  intro q hq
  apply Subtype.ext
  exact (j_tateCurveAt_inj q.property _).mp (hq.trans (j_tateCurveAt_tateParameterOfJ j hj).symm)

end Field

end TauCeti
