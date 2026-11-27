/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Haar
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Measure.Haar.Matrix.SkewAdjoint
import Mathlib.RingTheory.Complex
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Transport of the Cayley measure between unitary groups of congruent forms

Let `A` and `A'` be invertible Hermitian complex matrices of size `n`, and suppose that the forms
are congruent up to a real scalar: `bᴴ (t A) b = A'` for an invertible `b` and a real `t ≠ 0`.
Then `g ↦ b⁻¹ g b` is an isomorphism from `U(A) = Matrix.unitaryGroupOf A` onto `U(A')`
(`Matrix.unitaryGroupOf.conjHom`), and for every `a` with `a b ∈ U(A')` the map `g ↦ a g b` is a
bijection `U(A) → U(A')` (`Matrix.unitaryGroupOf.transport`). Every bijection `g ↦ a g b` between
the two groups is of this form when `A' = bᴴ (t A) b`; this covers left and right translations,
conjugation by permutation matrices, and `U(A) = U(-A)`.

The main result, `Matrix.unitaryGroupOf.map_transport_cayleyMeasure`, computes the image of the
Cayley measure `μ^c_A` (`Matrix.unitaryGroupOf.cayleyMeasure`) built from an additive Haar measure
`μ` on the skew-Hermitian matrices:

`(g ↦ a g b)_* μ^c_A = (|det A| / |det A'|) ^ n • μ^c_{A'}`.

In particular the map is measure preserving when `|det A| = |det A'|`, for instance between the
unitary groups of two Hermitian involutions (`Matrix.unitaryGroupOf.measurePreserving_transport`).

In Cayley coordinates the conjugation `g ↦ b⁻¹ g b` is the linear congruence
`S ↦ t bᴴ S b` of skew-Hermitian matrices (`Matrix.unitaryGroupOf.cayleyChart_congr`), because
`A'⁻¹ (t bᴴ S b) = b⁻¹ (A⁻¹ S) b`; it preserves the Cayley density, and its determinant is
`|t| ^ (n ^ 2) |det b| ^ (2 n) = (|det A'| / |det A|) ^ n`. The left translation by `a b ∈ U(A')`
is absorbed by the left invariance of `μ^c_{A'}`.

## Main definitions

* `Matrix.unitaryGroupOf.conjHom`: the isomorphism `g ↦ b⁻¹ g b` from `U(A)` to `U(A')`.
* `Matrix.unitaryGroupOf.transport`: the map `g ↦ a g b` from `U(A)` to `U(A')`.

## Main results

* `Matrix.unitaryGroupOf.map_transport_cayleyMeasure`: the image of the Cayley measure.
* `Matrix.unitaryGroupOf.measurePreserving_transport`,
  `Matrix.unitaryGroupOf.measurePreserving_transport_of_mul_self_eq_one`: the cases
  `|det A| = |det A'|` and that of two Hermitian involutions.

## Provenance

This is §1.2 (b) of the ShortGRH background roadmap HolomorphicDiscreteSeriesOfUnitaryGroups,
adapted from `New.measurePreserving_haarU` in `src/Lib/DiscreteSeries/Haar/CayleyChart.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There
the statement is for Hermitian involutions and the normalised Haar measure, and the Jacobian is
computed on tangent vectors at every point of the chart; here the forms are any invertible
Hermitian matrices, the measure is built from any additive Haar measure, and the map is reduced to
a linear congruence in Cayley coordinates followed by a left translation.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, §VIII.2.
-/

public section

open MeasureTheory Complex Set
open scoped ENNReal

namespace Matrix

namespace unitaryGroupOf

variable {n : Type*} [Fintype n] [DecidableEq n] {A A' : Matrix n n ℂ} {b : GL n ℂ} {t : ℝ}

section Algebra

/-- If `bᴴ (t A) b = A'`, conjugation `g ↦ b⁻¹ g b` maps the unitary group of `A` into that of
`A'`. -/
theorem inv_mul_mul_mem (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {g : GL n ℂ}
    (hg : g ∈ unitaryGroupOf A) : b⁻¹ * g * b ∈ unitaryGroupOf A' := by
  rw [mem_unitaryGroupOf_iff] at hg ⊢
  rw [← hb]
  have h1 : star ((b⁻¹ : GL n ℂ) : Matrix n n ℂ) * star (b : Matrix n n ℂ) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have h2 : (b : Matrix n n ℂ) * ((b⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 := Units.mul_inv b
  calc star (((b⁻¹ * g * b : GL n ℂ)) : Matrix n n ℂ) * (star (b : Matrix n n ℂ) * (t • A) * b) *
        ((b⁻¹ * g * b : GL n ℂ) : Matrix n n ℂ)
      = star (b : Matrix n n ℂ) * star (g : Matrix n n ℂ) *
          (star ((b⁻¹ : GL n ℂ) : Matrix n n ℂ) * star (b : Matrix n n ℂ)) * (t • A) *
          ((b : Matrix n n ℂ) * ((b⁻¹ : GL n ℂ) : Matrix n n ℂ)) * g * b := by
        simp only [Units.val_mul, star_mul, Matrix.mul_assoc]
    _ = star (b : Matrix n n ℂ) * (t • (star (g : Matrix n n ℂ) * A * g)) * b := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = star (b : Matrix n n ℂ) * (t • A) * b := by rw [hg]

/-- The **conjugation isomorphism** `g ↦ b⁻¹ g b` from the unitary group of `A` to that of
`A' = bᴴ (t A) b`. -/
noncomputable def conjHom (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') :
    unitaryGroupOf A →* unitaryGroupOf A' where
  toFun g := ⟨b⁻¹ * g * b, inv_mul_mul_mem hb g.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

@[simp]
theorem coe_conjHom_apply (hb : star (b : Matrix n n ℂ) * (t • A) * b = A')
    (g : unitaryGroupOf A) :
    (((conjHom hb g : unitaryGroupOf A') : GL n ℂ) : Matrix n n ℂ) =
      (b : Matrix n n ℂ)⁻¹ * ((g : GL n ℂ) : Matrix n n ℂ) * b := by
  simp [conjHom, coe_units_inv]

/-- The conjugation isomorphism is continuous. -/
theorem continuous_conjHom (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') :
    Continuous (conjHom hb) :=
  ((continuous_const.mul continuous_subtypeVal).mul continuous_const).subtype_mk _

/-- For `a b ∈ U(A')`, the map `g ↦ a g b` from the unitary group of `A` to that of
`A' = bᴴ (t A) b`: the left translation by `a b` of the conjugation isomorphism `g ↦ b⁻¹ g b`. -/
noncomputable def transport (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {a : GL n ℂ}
    (hab : a * b ∈ unitaryGroupOf A') (g : unitaryGroupOf A) : unitaryGroupOf A' :=
  ⟨a * b, hab⟩ * conjHom hb g

/-- `Matrix.unitaryGroupOf.transport` is `g ↦ a g b`. -/
@[simp]
theorem coe_transport_apply (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {a : GL n ℂ}
    (hab : a * b ∈ unitaryGroupOf A') (g : unitaryGroupOf A) :
    (((transport hb hab g : unitaryGroupOf A') : GL n ℂ) : Matrix n n ℂ) =
      (a : Matrix n n ℂ) * ((g : GL n ℂ) : Matrix n n ℂ) * b := by
  simp [transport, conjHom, Matrix.mul_assoc]

/-- `Matrix.unitaryGroupOf.transport` is continuous. -/
theorem continuous_transport (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {a : GL n ℂ}
    (hab : a * b ∈ unitaryGroupOf A') : Continuous (transport hb hab) :=
  continuous_const.mul (continuous_conjHom hb)

end Algebra

section Chart

variable (b t) in
/-- The **congruence** `S ↦ t bᴴ S b` of skew-Hermitian matrices, which represents the
conjugation `g ↦ b⁻¹ g b` in Cayley coordinates (`Matrix.unitaryGroupOf.cayleyChart_congr`). -/
noncomputable def congrSkew :
    skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix n n ℂ) :=
  t • skewAdjointConjugate ℝ (star (b : Matrix n n ℂ))

@[simp]
theorem coe_congrSkew_apply (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    (congrSkew b t S : Matrix n n ℂ) = t • (star (b : Matrix n n ℂ) * S * b) := by
  simp [congrSkew, star_eq_conjTranspose]

/-- In Cayley coordinates, `A'⁻¹ (t bᴴ S b) = b⁻¹ (A⁻¹ S) b`. -/
theorem inv_mul_congrSkew (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    A'⁻¹ * (congrSkew b t S : Matrix n n ℂ) =
      (b : Matrix n n ℂ)⁻¹ * (A⁻¹ * (S : Matrix n n ℂ)) * b := by
  have hB : IsUnit (b : Matrix n n ℂ) := b.isUnit
  have hBd : IsUnit (b : Matrix n n ℂ).det := (isUnit_iff_isUnit_det _).1 hB
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA
  have hA' : IsUnit A' := by
    rw [← hb]
    exact ((hB.star).mul (hA.smul (Units.mk0 (t : ℝ) ht))).mul hB
  have key : A' * ((b : Matrix n n ℂ)⁻¹ * (A⁻¹ * (S : Matrix n n ℂ)) * b) =
      congrSkew b t S := by
    rw [coe_congrSkew_apply, ← hb]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hBd, mul_nonsing_inv_cancel_left _ _ hAd]
  rw [← key, nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).1 hA')]

/-- The congruence conjugates `1 + c A⁻¹ S` by `b`. -/
theorem one_add_smul_inv_mul_congrSkew (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (c : ℂ)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    1 + c • (A'⁻¹ * (congrSkew b t S : Matrix n n ℂ)) =
      (b : Matrix n n ℂ)⁻¹ * (1 + c • (A⁻¹ * (S : Matrix n n ℂ))) * b := by
  rw [inv_mul_congrSkew hA ht hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 b.isUnit), Matrix.mul_smul, Matrix.smul_mul]

/-- The congruence conjugates `1 - A⁻¹ S / 2` by `b`. -/
theorem one_sub_smul_inv_mul_congrSkew (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    1 - (2 : ℂ)⁻¹ • (A'⁻¹ * (congrSkew b t S : Matrix n n ℂ)) =
      (b : Matrix n n ℂ)⁻¹ * (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))) * b := by
  simpa only [neg_smul, ← sub_eq_add_neg] using
    one_add_smul_inv_mul_congrSkew hA ht hb (-(2 : ℂ)⁻¹) S

/-- The congruence preserves the source of the Cayley chart. -/
theorem congrSkew_mem_cayleyChartSource_iff (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {S : skewAdjoint.submodule ℝ (Matrix n n ℂ)} :
    congrSkew b t S ∈ cayleyChartSource A' ↔ S ∈ cayleyChartSource A := by
  rw [mem_cayleyChartSource_iff_det_ne_zero, mem_cayleyChartSource_iff_det_ne_zero,
    one_sub_smul_inv_mul_congrSkew hA ht hb, det_conj' b.isUnit]

/-- **The Cayley chart intertwines the congruence with conjugation**:
`φ_{A'}(t bᴴ S b) = b⁻¹ φ_A(S) b`. -/
theorem cayleyChart_congr (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyChart A' (congrSkew b t S) =
      (b : Matrix n n ℂ)⁻¹ * cayleyChart A S * b := by
  have hBd : IsUnit (b : Matrix n n ℂ).det := (isUnit_iff_isUnit_det _).1 b.isUnit
  rw [cayleyChart_eq, cayleyChart_eq, one_sub_smul_inv_mul_congrSkew hA ht hb,
    one_add_smul_inv_mul_congrSkew hA ht hb, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    nonsing_inv_nonsing_inv _ hBd]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hBd]

/-- The congruence preserves the Cayley density. -/
theorem cayleyDensity_congrSkew (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyDensity A' (congrSkew b t S) = cayleyDensity A S := by
  rw [cayleyDensity_def, cayleyDensity_def, one_sub_smul_inv_mul_congrSkew hA ht hb,
    det_conj' b.isUnit]

/-- **The group-valued Cayley chart intertwines the congruence with conjugation.** -/
theorem cayleyChartUnitary_congr (hA : A.IsHermitian) (hA' : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyChartUnitary A' (congrSkew b t S) = conjHom hb (cayleyChartUnitary A S) := by
  have hA'' : A'.IsHermitian :=
    hb ▸ isHermitian_conjTranspose_mul_mul (b : Matrix n n ℂ) (hA.smul (IsSelfAdjoint.all t))
  by_cases hS : S ∈ cayleyChartSource A
  · apply unitaryGroupOf.ext
    rw [coe_conjHom_apply, coe_cayleyChartUnitary hA hS,
      coe_cayleyChartUnitary hA''
        ((congrSkew_mem_cayleyChartSource_iff hA' ht hb).2 hS), cayleyChart_congr hA' ht hb]
  · rw [cayleyChartUnitary_of_notMem hS, map_one, cayleyChartUnitary_of_notMem
      (mt (congrSkew_mem_cayleyChartSource_iff hA' ht hb).1 hS)]

/-- The determinant of the congruence is `t ^ (n ^ 2) |det b| ^ (2 n)`. -/
theorem det_congrSkew :
    LinearMap.det (congrSkew b t) =
      t ^ (Fintype.card n ^ 2) * normSq (b : Matrix n n ℂ).det ^ Fintype.card n := by
  rw [congrSkew, LinearMap.det_smul, finrank_skewAdjoint_submodule ℝ ℂ n
      Complex.mem_range_algebraMap_of_isSelfAdjoint Complex.val_mk0_I_mem_skewAdjoint,
    det_skewAdjointConjugate Complex.mem_range_algebraMap_of_isSelfAdjoint
      Complex.val_mk0_I_mem_skewAdjoint, Algebra.norm_complex_apply, star_eq_conjTranspose,
    det_conjTranspose, Complex.star_def, normSq_conj]

/-- The absolute value of the determinant of the congruence is `(|det A'| / |det A|) ^ n`. -/
theorem abs_det_congrSkew (hA : IsUnit A) (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') :
    |LinearMap.det (congrSkew b t)| = (‖A'.det‖ / ‖A.det‖) ^ Fintype.card n := by
  have hAd : ‖A.det‖ ≠ 0 := norm_ne_zero_iff.2 ((isUnit_iff_isUnit_det _).1 hA).ne_zero
  have hdet : ‖A'.det‖ = |t| ^ Fintype.card n * ‖(b : Matrix n n ℂ).det‖ ^ 2 * ‖A.det‖ := by
    rw [← hb, det_mul, det_mul, det_smul_of_tower, star_eq_conjTranspose, det_conjTranspose]
    simp only [norm_mul, norm_star, norm_smul, norm_pow, Real.norm_eq_abs]
    ring
  rw [det_congrSkew, hdet, mul_div_assoc, div_self hAd, mul_one, abs_mul, abs_pow, abs_pow,
    abs_of_nonneg (normSq_nonneg _), normSq_eq_norm_sq, mul_pow, ← pow_mul, sq, mul_comm]
  ring

end Chart

section Measure

variable (μ : Measure (skewAdjoint.submodule ℝ (Matrix n n ℂ))) [μ.IsAddHaarMeasure]
  [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)]
  [MeasurableSpace (unitaryGroupOf A')] [BorelSpace (unitaryGroupOf A')]

/-- **Transport of the Cayley measure.** Let `A`, `A'` be invertible Hermitian matrices with
`bᴴ (t A) b = A'` for an invertible `b` and a real `t ≠ 0`, and let `a b ∈ U(A')`. For an additive
Haar measure `μ` on the skew-Hermitian matrices, the bijection `g ↦ a g b` from `U(A)` to `U(A')`
carries the Cayley measure of `A` to `(|det A| / |det A'|) ^ n` times that of `A'`. -/
theorem map_transport_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {a : GL n ℂ}
    (hab : a * b ∈ unitaryGroupOf A') :
    (cayleyMeasure A μ).map (transport hb hab) =
      ENNReal.ofReal ((‖A.det‖ / ‖A'.det‖) ^ Fintype.card n) • cayleyMeasure A' μ := by
  have hA'' : A'.IsHermitian :=
    hb ▸ isHermitian_conjTranspose_mul_mul (b : Matrix n n ℂ) (hA.smul (IsSelfAdjoint.all t))
  have hAd : A.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hA').ne_zero
  have hA'd : A'.det ≠ 0 := by
    rw [← hb, det_mul, det_mul, det_smul_of_tower]
    have := ((isUnit_iff_isUnit_det _).1 b.isUnit).ne_zero
    simp [this, hAd, ht, star_eq_conjTranspose, det_conjTranspose]
  have hdet : LinearMap.det (congrSkew b t) ≠ 0 := by
    rw [det_congrSkew]
    have := ((isUnit_iff_isUnit_det _).1 b.isUnit).ne_zero
    simp [this, ht]
  have hunit : IsUnit A' := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA'd)
  have := isMulLeftInvariant_cayleyMeasure μ hA'' hunit
  have hmeas := (continuous_transport hb hab).measurable
  refine Measure.ext_of_lintegral _ fun F hF ↦ ?_
  let c : unitaryGroupOf A' := ⟨a * b, hab⟩
  -- The integrand of the right side in Cayley coordinates, composed with the congruence, is
  -- that of the left side.
  have hG : (fun S ↦ cayleyDensity A' (congrSkew b t S) *
      F (c * cayleyChartUnitary A' (congrSkew b t S))) =
        fun S ↦ cayleyDensity A S * F (transport hb hab (cayleyChartUnitary A S)) := by
    ext S
    rw [cayleyDensity_congrSkew hA' ht hb, cayleyChartUnitary_congr hA hA' ht hb]
    rfl
  have hL := μ.lintegral_comp_linearMap_skewAdjoint hdet
    fun S ↦ cayleyDensity A' S * F (c * cayleyChartUnitary A' S)
  rw [hG] at hL
  rw [lintegral_map hF hmeas, lintegral_smul_measure,
    lintegral_cayleyMeasure μ hA (F := fun g ↦ F (transport hb hab g)) (hF.comp hmeas),
    ← lintegral_mul_left_eq_self F c,
    lintegral_cayleyMeasure μ hA'' (F := fun g ↦ F (c * g)) (hF.comp (measurable_const_mul c))]
  rw [hL, smul_eq_mul, abs_inv, abs_det_congrSkew hA' hb, ← inv_pow, inv_div]

/-- **The transport of the Cayley measure is measure preserving** when `|det A| = |det A'|`. -/
theorem measurePreserving_transport (hA : A.IsHermitian) (hA' : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {a : GL n ℂ}
    (hab : a * b ∈ unitaryGroupOf A') (hdet : ‖A.det‖ = ‖A'.det‖) :
    MeasurePreserving (transport hb hab) (cayleyMeasure A μ) (cayleyMeasure A' μ) := by
  refine ⟨(continuous_transport hb hab).measurable, ?_⟩
  rw [map_transport_cayleyMeasure μ hA hA' ht hb hab, hdet, div_self, one_pow, ENNReal.ofReal_one,
    one_smul]
  rw [← hdet]
  exact norm_ne_zero_iff.2 ((isUnit_iff_isUnit_det _).1 hA').ne_zero

/-- A matrix `J` with `J * J = 1` has `|det J| = 1`. -/
theorem norm_det_eq_one_of_mul_self_eq_one {J : Matrix n n ℂ} (hJ : J * J = 1) :
    ‖J.det‖ = 1 := by
  have h : ‖J.det‖ ^ 2 = 1 := by rw [sq, ← norm_mul, ← det_mul, hJ, det_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- **The transport between unitary groups of Hermitian involutions is measure preserving**: for
Hermitian `J`, `J'` with `J * J = 1 = J' * J'`, `bᴴ (t J) b = J'` and `a b ∈ U(J')`, the map
`g ↦ a g b` carries the Cayley measure of `J` to that of `J'`. -/
theorem measurePreserving_transport_of_mul_self_eq_one (hA : A.IsHermitian) (hAA : A * A = 1)
    (hA'A' : A' * A' = 1) (ht : t ≠ 0) (hb : star (b : Matrix n n ℂ) * (t • A) * b = A')
    {a : GL n ℂ} (hab : a * b ∈ unitaryGroupOf A') :
    MeasurePreserving (transport hb hab) (cayleyMeasure A μ) (cayleyMeasure A' μ) :=
  measurePreserving_transport μ hA ⟨⟨A, A, hAA, hAA⟩, rfl⟩ ht hb hab
    (by rw [norm_det_eq_one_of_mul_self_eq_one hAA, norm_det_eq_one_of_mul_self_eq_one hA'A'])

end Measure

end unitaryGroupOf

end Matrix
