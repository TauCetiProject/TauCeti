/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Haar.Basic
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Measure.Haar.Matrix.SkewAdjoint
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Transport of the Cayley measure between unitary groups of congruent forms

Let `A` and `A'` be invertible Hermitian complex matrices of size `n`, and suppose that the forms
are congruent up to a real scalar: `bᴴ (t A) b = A'` for an invertible `b` and a real `t ≠ 0`.
Then `g ↦ b⁻¹ g b` is an isomorphism from `U(A) = Matrix.unitaryGroupOf A` onto `U(A')`
(`Matrix.unitaryGroupOf.conjEquiv`), and for every `a` with `a b ∈ U(A')` the map `g ↦ a g b` is a
bijection `U(A) → U(A')` (`Matrix.unitaryGroupOf.transport`). Every bijection `g ↦ a g b` between
the two groups is of this form when `A' = bᴴ (t A) b`; this covers left and right translations,
conjugation by permutation matrices, and `U(A) = U(-A)`.

The main result, `Matrix.unitaryGroupOf.map_transport_cayleyMeasure`, computes the image of the
Cayley measure `μ^c_A` (`Matrix.unitaryGroupOf.cayleyMeasure`) built from an additive Haar measure
`μ` on the skew-Hermitian matrices:

`(g ↦ a g b)_* μ^c_A = (|det A| / |det A'|) ^ n • μ^c_{A'}`.

In particular the map is measure preserving when `|det A| = |det A'|`
(`Matrix.unitaryGroupOf.measurePreserving_transport`), for instance between the unitary groups of
two Hermitian involutions (`Matrix.unitaryGroupOf.measurePreserving_transport_of_mul_self_eq_one`).

In Cayley coordinates the conjugation `g ↦ b⁻¹ g b` is the linear congruence
`S ↦ t bᴴ S b` of skew-Hermitian matrices (`Matrix.unitaryGroupOf.congrSkew` and
`Matrix.unitaryGroupOf.cayleyChart_congrSkew`, in the file of the Cayley chart), because
`A'⁻¹ (t bᴴ S b) = b⁻¹ (A⁻¹ S) b`; it preserves the Cayley density
(`Matrix.unitaryGroupOf.cayleyDensity_congrSkew`), and the absolute value of its determinant is
`|t| ^ (n ^ 2) |det b| ^ (2 n) = (|det A'| / |det A|) ^ n`. The left translation by `a b ∈ U(A')`
is absorbed by the left invariance of `μ^c_{A'}`.

## Main results

* `Matrix.unitaryGroupOf.cayleyDensity_congrSkew`: the congruence preserves the Cayley density.
* `Matrix.unitaryGroupOf.map_transport_cayleyMeasure`: the image of the Cayley measure.
* `Matrix.unitaryGroupOf.measurePreserving_transport`,
  `Matrix.unitaryGroupOf.measurePreserving_transport_of_mul_self_eq_one`: the cases
  `|det A| = |det A'|` and that of two Hermitian involutions.

## Provenance

Adapted from `New.measurePreserving_haarU` in `src/Lib/DiscreteSeries/Haar/CayleyChart.lean` of
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

/-- The congruence preserves the Cayley density. -/
theorem cayleyDensity_congrSkew (hA : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyDensity A' (congrSkew b t S) = cayleyDensity A S := by
  rw [cayleyDensity_def, cayleyDensity_def, one_sub_smul_inv_mul_congrSkew hA ht hb,
    det_conj' b.isUnit]

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
    (cayleyMeasure A μ).map (transport ht hb hab) =
      ENNReal.ofReal ((‖A.det‖ / ‖A'.det‖) ^ Fintype.card n) • cayleyMeasure A' μ := by
  have hA'' : A'.IsHermitian :=
    hb ▸ isHermitian_conjTranspose_mul_mul (b : Matrix n n ℂ) (hA.smul (IsSelfAdjoint.all t))
  have hdet : LinearMap.det (congrSkew b t) ≠ 0 := by
    rw [det_congrSkew]
    have := ((isUnit_iff_isUnit_det _).1 b.isUnit).ne_zero
    simp [this, ht]
  have := isMulLeftInvariant_cayleyMeasure μ hA'' (isUnit_of_star_mul_smul_mul_eq hA' ht hb)
  have hmeas := (continuous_transport ht hb hab).measurable
  refine Measure.ext_of_lintegral _ fun F hF ↦ ?_
  let c : unitaryGroupOf A' := ⟨a * b, hab⟩
  -- The integrand of the right side in Cayley coordinates, composed with the congruence, is
  -- that of the left side.
  have hG : (fun S ↦ cayleyDensity A' (congrSkew b t S) *
      F (c * cayleyChartUnitary A' (congrSkew b t S))) =
        fun S ↦ cayleyDensity A S * F (transport ht hb hab (cayleyChartUnitary A S)) := by
    ext S
    rw [cayleyDensity_congrSkew hA' ht hb, cayleyChartUnitary_congrSkew hA hA' ht hb,
      transport_apply]
  have hL := μ.lintegral_comp_linearMap_skewAdjoint hdet
    fun S ↦ cayleyDensity A' S * F (c * cayleyChartUnitary A' S)
  rw [hG] at hL
  rw [lintegral_map hF hmeas, lintegral_smul_measure,
    lintegral_cayleyMeasure μ hA (F := fun g ↦ F (transport ht hb hab g)) (hF.comp hmeas),
    ← lintegral_mul_left_eq_self F c,
    lintegral_cayleyMeasure μ hA'' (F := fun g ↦ F (c * g)) (hF.comp (measurable_const_mul c))]
  rw [hL, smul_eq_mul, abs_inv, abs_det_congrSkew hA' hb, ← inv_pow, inv_div]

/-- **The transport of the Cayley measure is measure preserving** when `|det A| = |det A'|`. -/
theorem measurePreserving_transport (hA : A.IsHermitian) (hA' : IsUnit A) (ht : t ≠ 0)
    (hb : star (b : Matrix n n ℂ) * (t • A) * b = A') {a : GL n ℂ}
    (hab : a * b ∈ unitaryGroupOf A') (hdet : ‖A.det‖ = ‖A'.det‖) :
    MeasurePreserving (transport ht hb hab) (cayleyMeasure A μ) (cayleyMeasure A' μ) := by
  refine ⟨(continuous_transport ht hb hab).measurable, ?_⟩
  rw [map_transport_cayleyMeasure μ hA hA' ht hb hab, hdet, div_self, one_pow, ENNReal.ofReal_one,
    one_smul]
  rw [← hdet]
  exact norm_ne_zero_iff.2 ((isUnit_iff_isUnit_det _).1 hA').ne_zero

/-- **The transport between unitary groups of Hermitian involutions is measure preserving**: for
Hermitian `J`, `J'` with `J * J = 1 = J' * J'`, `bᴴ (t J) b = J'` and `a b ∈ U(J')`, the map
`g ↦ a g b` carries the Cayley measure of `J` to that of `J'`. -/
theorem measurePreserving_transport_of_mul_self_eq_one (hA : A.IsHermitian) (hAA : A * A = 1)
    (hA'A' : A' * A' = 1) (ht : t ≠ 0) (hb : star (b : Matrix n n ℂ) * (t • A) * b = A')
    {a : GL n ℂ} (hab : a * b ∈ unitaryGroupOf A') :
    MeasurePreserving (transport ht hb hab) (cayleyMeasure A μ) (cayleyMeasure A' μ) := by
  have h {J : Matrix n n ℂ} (hJ : J * J = 1) : ‖J.det‖ = 1 :=
    (detMonoidHom.isOfFinOrder <|
      (isOfFinOrder_iff_pow_eq_one (x := J)).2 ⟨2, two_pos, by rw [sq, hJ]⟩).norm_eq_one
  exact measurePreserving_transport μ hA ⟨⟨A, A, hAA, hAA⟩, rfl⟩ ht hb hab
    (by rw [h hAA, h hA'A'])

end Measure

end unitaryGroupOf

end Matrix
