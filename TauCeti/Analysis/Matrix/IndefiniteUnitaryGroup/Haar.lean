/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Cayley
public import TauCeti.MeasureTheory.Measure.Haar.Matrix.SkewAdjoint
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Group.Units
import TauCeti.MeasureTheory.Measure.Haar.ZeroLocus
import TauCeti.LinearAlgebra.Matrix.Determinant.Pencil
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The Cayley measure is a Haar measure on the unitary group of a Hermitian form

Let `A` be an invertible Hermitian complex matrix of size `n`, for instance a Hermitian involution
`J = diag(±1)`, and `U(A) = Matrix.unitaryGroupOf A` the group of matrices `g` with `gᴴ A g = A`,
such as `U(p, q)`. The Cayley chart `φ(S) = (1 + A⁻¹ S / 2) (1 - A⁻¹ S / 2)⁻¹`
(`Matrix.unitaryGroupOf.cayleyChart`) parametrizes the elements `g` of `U(A)` with `1 + g`
invertible by the skew-Hermitian matrices `S` with `D(S) = 1 - A⁻¹ S / 2` invertible. Given a
measure `μ` on the skew-Hermitian matrices, the **Cayley measure** `μ^c` on `U(A)`
(`Matrix.unitaryGroupOf.cayleyMeasure`) is the image under `φ` of the measure of density
`|det D(S)|^(-2 n)` (`Matrix.unitaryGroupOf.cayleyDensity`) with respect to `μ`. When `μ` is an
additive Haar measure, `μ^c` is a left and right Haar measure on `U(A)`. Taking for `μ` the
Lebesgue measure in the coordinates `Im S_aa`, `Re S_ab`, `Im S_ab` (`a < b`) divided by the
volume `∏_{i ≤ n} 2 π^i / (i - 1)!` of `U(n)` gives the compact-dual normalization of Haar measure
on `U(p, q)`, whose density at the identity in Cayley coordinates does not depend on the
signature.

The density is the determinant of the logarithmic derivative `S ↦ φ(S)ᴴ A dφ_S` of the chart
(`Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart`). This pull-back of the
Maurer–Cartan form is invariant under left multiplication by `a ∈ U(A)`, so the transition map
`τ = φ⁻¹ ∘ (a ·) ∘ φ` has Jacobian `|det dτ_S| = |det D(S)|^(-2 n) / |det D(τ(S))|^(-2 n)`, and
the change of variables formula gives left invariance. The chart does not cover `U(A)`, and `τ`
is only defined where `1 + a φ(S)` is invertible; the remaining points are the zeros of the
polynomial `S ↦ det ((1 + a) + (a - 1) A⁻¹ S / 2)`, which does not vanish identically, so they
form a null set (`MeasureTheory.Measure.addHaar_setOf_det_add_eq_zero`). In Cayley coordinates
inversion is `S ↦ -S`, which preserves the density, so `μ^c` is invariant under inversion and
hence right invariant. A compact neighbourhood of the identity inside the image of the chart has
positive finite measure, so `μ^c` is a Haar measure.

Derivatives are taken for the Frobenius norm on matrices, whose topology is the topology of
entries; measures and statements use the topology of entries.

## Main definitions

* `Matrix.unitaryGroupOf.cayleyChartUnitary A S`: the Cayley chart as a map to `U(A)`, equal to
  `1` off the source of the chart.
* `Matrix.unitaryGroupOf.cayleyDensity A S`: the density `|det (1 - A⁻¹ S / 2)|^(-2 n)`.
* `Matrix.unitaryGroupOf.cayleyMeasure A μ`: the Cayley measure on `U(A)`.

## Main results

* `Matrix.unitaryGroupOf.lintegral_cayleyMeasure`: integrals for the Cayley measure in Cayley
  coordinates.
* `Matrix.unitaryGroupOf.isMulLeftInvariant_cayleyMeasure`,
  `Matrix.unitaryGroupOf.isInvInvariant_cayleyMeasure`,
  `Matrix.unitaryGroupOf.isMulRightInvariant_cayleyMeasure`: for an additive Haar measure `μ`, the
  Cayley measure is invariant under left multiplication, inversion and right multiplication.
* `Matrix.unitaryGroupOf.isHaarMeasure_cayleyMeasure`: it is a Haar measure.

## Provenance

The measure and its invariance correspond to `New.haarU`, `New.lintegral_eq_cayleyChart` and
`New.measurePreserving_haarU` (file `src/Lib/DiscreteSeries/Haar/CayleyChart.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), for a Hermitian
involution and the normalized Lebesgue measure; there the Jacobian of a translation is computed
through a congruence of skew-Hermitian matrices, and the points outside a chart are moved into it
by rotating with a generic scalar. Here the measure is built from any additive Haar measure on the
skew-Hermitian matrices and for every invertible Hermitian `A`, the Jacobian comes from the
invariance of the logarithmic derivative, the points outside the chart are a polynomial zero set,
and right invariance is deduced from invariance under inversion.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press, 1939, Chapter II, §10.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, §VIII.2.
-/

public section

open MeasureTheory Complex TauCeti Set Filter Topology
open scoped ENNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace unitaryGroupOf

variable {A : Matrix n n ℂ} {S : skewAdjoint.submodule ℝ (Matrix n n ℂ)}

/-- The Cayley chart with values in the unitary group is measurable. -/
theorem measurable_cayleyChartUnitary [MeasurableSpace (unitaryGroupOf A)]
    [BorelSpace (unitaryGroupOf A)] (hA : A.IsHermitian) (hA' : IsUnit A) :
    Measurable (cayleyChartUnitary A) := by
  classical
  have h : cayleyChartUnitary A = (cayleyChartSource A).piecewise (cayleyChartUnitary A) 1 := by
    ext1 S
    by_cases hS : S ∈ cayleyChartSource A
    · simp [hS]
    · simp [hS]
  rw [h]
  exact (continuousOn_cayleyChartUnitary hA hA').measurable_piecewise continuousOn_const
    isOpen_cayleyChartSource.measurableSet

/-- The **Cayley density** `|det (1 - A⁻¹ S / 2)|^(-2 n)` of the skew-Hermitian `S`, where
`n` is the size of the matrices. It is the determinant of the logarithmic derivative of the
Cayley chart (`Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart`), and it
vanishes off the source of the chart. -/
noncomputable def cayleyDensity (A : Matrix n n ℂ)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹

/-- The defining formula of the Cayley density. -/
theorem cayleyDensity_def (A : Matrix n n ℂ) (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyDensity A S = ENNReal.ofReal
      (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹ :=
  (rfl)

/-- The Cayley density vanishes off the source of the chart. -/
@[simp]
theorem cayleyDensity_of_notMem (hS : S ∉ cayleyChartSource A) : cayleyDensity A S = 0 := by
  have hn : Nonempty n := by
    by_contra h
    have : IsEmpty n := not_nonempty_iff.1 h
    exact hS (mem_cayleyChartSource.2 (isUnit_of_subsingleton _))
  have hdet : (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det = 0 := by
    simpa only [mem_cayleyChartSource_iff_det_ne_zero, not_not] using hS
  simp [cayleyDensity_def, hdet, Fintype.card_ne_zero]

/-- The Cayley density is positive on the source of the chart. -/
theorem cayleyDensity_pos (hS : S ∈ cayleyChartSource A) : 0 < cayleyDensity A S := by
  simpa [cayleyDensity_def] using normSq_det_pow_pos_of_mem_cayleyChartSource hS

/-- The Cayley density is continuous on the source of the chart. -/
theorem continuousOn_cayleyDensity :
    ContinuousOn (cayleyDensity A) (cayleyChartSource A) := by
  refine ENNReal.continuous_ofReal.comp_continuousOn
    (ContinuousOn.inv₀ ((Continuous.pow (by fun_prop) _).continuousOn) ?_)
  intro S hS
  exact (normSq_det_pow_pos_of_mem_cayleyChartSource hS).ne'

/-- The Cayley density is measurable. -/
theorem measurable_cayleyDensity : Measurable (cayleyDensity A) :=
  ((Continuous.measurable (Continuous.pow (by fun_prop) _)).inv).ennreal_ofReal

/-- The determinant `det (1 + A⁻¹ S / 2)` at `-S` is the conjugate of `det (1 - A⁻¹ S / 2)`. -/
private theorem det_one_sub_neg (hA : A.IsHermitian) (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    (1 - (2 : ℂ)⁻¹ • (A⁻¹ * ((-S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) : Matrix n n ℂ))).det =
      star (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det := by
  have hS : star (S : Matrix n n ℂ) = -S := skewAdjoint.mem_iff.1 S.property
  have hA' : star A⁻¹ = A⁻¹ := by
    rw [star_eq_conjTranspose, conjTranspose_nonsing_inv, hA.eq]
  rw [← det_conjTranspose, ← star_eq_conjTranspose]
  simp only [star_sub, star_one, star_smul, star_mul, hS, hA', star_inv₀, star_ofNat,
    NegMemClass.coe_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg, sub_neg_eq_add]
  rw [← Matrix.smul_mul, det_one_add_mul_comm, Matrix.mul_smul]

/-- The source of the Cayley chart is invariant under `S ↦ -S`. -/
@[simp]
theorem neg_mem_cayleyChartSource (hA : A.IsHermitian) :
    -S ∈ cayleyChartSource A ↔ S ∈ cayleyChartSource A := by
  simp only [mem_cayleyChartSource, isUnit_iff_isUnit_det, det_one_sub_neg hA, isUnit_star]

/-- The Cayley density is invariant under `S ↦ -S`. -/
@[simp]
theorem cayleyDensity_neg (hA : A.IsHermitian) (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyDensity A (-S) = cayleyDensity A S := by
  rw [cayleyDensity_def, cayleyDensity_def, det_one_sub_neg hA, Complex.star_def, normSq_conj]

/-- The Cayley chart sends `-S` to the inverse of its value at `S`. -/
@[simp]
theorem cayleyChartUnitary_neg (hA : A.IsHermitian) (hA' : IsUnit A)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyChartUnitary A (-S) = (cayleyChartUnitary A S)⁻¹ := by
  by_cases hS : S ∈ cayleyChartSource A
  · have hS' := (neg_mem_cayleyChartSource hA).2 hS
    refine eq_inv_of_mul_eq_one_left (unitaryGroupOf.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, coe_cayleyChartUnitary hA hA' hS,
      coe_cayleyChartUnitary hA hA' hS', cayleyChart_eq, cayleyChart_eq]
    have h1 := isUnit_iff_ne_zero.2 (mem_cayleyChartSource_iff_det_ne_zero.1 hS')
    have h2 := isUnit_iff_ne_zero.2 (mem_cayleyChartSource_iff_det_ne_zero.1 hS)
    simp only [NegMemClass.coe_neg, Matrix.mul_neg, smul_neg, sub_neg_eq_add] at h1 ⊢
    generalize (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)) = X at h1 h2 ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + X)⁻¹, nonsing_inv_mul _ h1, Matrix.one_mul,
      ← sub_eq_add_neg, mul_nonsing_inv _ h2]
    simp
  · rw [cayleyChartUnitary_of_notMem hS,
      cayleyChartUnitary_of_notMem (mt (neg_mem_cayleyChartSource hA).1 hS), inv_one]

section Transition

variable (hA : A.IsHermitian) (hA' : IsUnit A) (a : unitaryGroupOf A)
include hA hA'

/-- The points of the source of the Cayley chart whose image stays in the image of the chart after
left multiplication by `a`. -/
private def transitionSource (a : unitaryGroupOf A) :
    Set (skewAdjoint.submodule ℝ (Matrix n n ℂ)) :=
  {S | S ∈ cayleyChartSource A ∧ IsUnit (1 + ((a : GL n ℂ) : Matrix n n ℂ) * cayleyChart A S)}

omit hA hA' in
private theorem isOpen_transitionSource : IsOpen (transitionSource a) := by
  exact ContinuousOn.isOpen_inter_preimage
    (continuousOn_const.add (continuousOn_const.mul continuousOn_cayleyChart))
    isOpen_cayleyChartSource IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range

/-- On `transitionSource a`, the product `a φ(S)` lies in the image of the chart. -/
private theorem isUnit_one_add_mul_cayleyChartUnitary {S} (hS : S ∈ transitionSource a) :
    IsUnit (1 + (((a * cayleyChartUnitary A S : unitaryGroupOf A) : GL n ℂ) : Matrix n n ℂ)) := by
  simpa [coe_cayleyChartUnitary hA hA' hS.1] using hS.2

omit hA hA' in
/-- The **transition map** `S ↦ φ⁻¹(a φ(S))` of the Cayley chart `φ` under left multiplication
by `a`. -/
private noncomputable def cayleyTransition (a : unitaryGroupOf A)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) : skewAdjoint.submodule ℝ (Matrix n n ℂ) :=
  cayleyChartInv A (((a : GL n ℂ) : Matrix n n ℂ) * cayleyChart A S)

/-- On `transitionSource a`, the transition map is the inverse of the chart at `a φ(S)`. -/
private theorem cayleyTransition_eq {S} (hS : S ∈ transitionSource a) :
    cayleyTransition a S = ((cayleyChartEquiv hA hA').symm
      ⟨a * cayleyChartUnitary A S, isUnit_one_add_mul_cayleyChartUnitary hA hA' a hS⟩).val := by
  rw [← cayleyChartInv_eq_cayleyChartEquiv_symm hA hA', cayleyTransition,
    Subgroup.coe_mul, Units.val_mul,
    coe_cayleyChartUnitary hA hA' hS.1]

private theorem cayleyTransition_mem {S} (hS : S ∈ transitionSource a) :
    cayleyTransition a S ∈ cayleyChartSource A := by
  rw [cayleyTransition_eq hA hA' a hS]
  exact ((cayleyChartEquiv hA hA').symm _).property

private theorem cayleyChartUnitary_cayleyTransition {S} (hS : S ∈ transitionSource a) :
    cayleyChartUnitary A (cayleyTransition a S) = a * cayleyChartUnitary A S := by
  rw [cayleyChartUnitary_eq_cayleyChartEquiv hA hA' (cayleyTransition_mem hA hA' a hS)]
  simp_rw [cayleyTransition_eq hA hA' a hS]
  simp

private theorem cayleyChart_cayleyTransition {S} (hS : S ∈ transitionSource a) :
    cayleyChart A (cayleyTransition a S) = ((a : GL n ℂ) : Matrix n n ℂ) * cayleyChart A S := by
  have := congrArg (fun g : unitaryGroupOf A ↦ ((g : GL n ℂ) : Matrix n n ℂ))
    (cayleyChartUnitary_cayleyTransition hA hA' a hS)
  simpa [coe_cayleyChartUnitary hA hA' hS.1,
    coe_cayleyChartUnitary hA hA' (cayleyTransition_mem hA hA' a hS)] using this

/-- The transition map is injective on `transitionSource a`. -/
private theorem injOn_cayleyTransition : InjOn (cayleyTransition a) (transitionSource a) :=
  fun S hS S' hS' h ↦ by
    have := congrArg (cayleyChartUnitary A) h
    rw [cayleyChartUnitary_cayleyTransition hA hA' a hS,
      cayleyChartUnitary_cayleyTransition hA hA' a hS', mul_right_inj] at this
    apply injOn_cayleyChart hA hA' hS.1 hS'.1
    rw [← coe_cayleyChartUnitary hA hA' hS.1, ← coe_cayleyChartUnitary hA hA' hS'.1, this]

/-- The image of `transitionSource a` under the transition map contains `transitionSource a⁻¹`:
`τ_a (τ_{a⁻¹} S) = S` there. -/
private theorem transitionSource_inv_subset_image :
    transitionSource a⁻¹ ⊆ cayleyTransition a '' transitionSource a := by
  intro S' hS'
  have hT := cayleyTransition_mem hA hA' a⁻¹ hS'
  have hfT := cayleyChartUnitary_cayleyTransition hA hA' a⁻¹ hS'
  have hT' : cayleyTransition a⁻¹ S' ∈ transitionSource a := by
    refine ⟨hT, ?_⟩
    have h := isUnit_one_add_cayleyChart hA hA' hS'.1
    rwa [← coe_cayleyChartUnitary hA hA' hS'.1, ← mul_inv_cancel_left a (cayleyChartUnitary A S'),
      ← hfT, Subgroup.coe_mul, Units.val_mul, coe_cayleyChartUnitary hA hA' hT] at h
  refine ⟨_, hT', ?_⟩
  apply injOn_cayleyChart hA hA' (cayleyTransition_mem hA hA' a hT') hS'.1
  rw [← coe_cayleyChartUnitary hA hA' (cayleyTransition_mem hA hA' a hT'),
    ← coe_cayleyChartUnitary hA hA' hS'.1, cayleyChartUnitary_cayleyTransition hA hA' a hT', hfT,
    mul_inv_cancel_left]

omit hA hA' in
open scoped Matrix.Norms.Frobenius in
private theorem differentiableAt_cayleyTransition {S} (hS : S ∈ transitionSource a) :
    DifferentiableAt ℝ (cayleyTransition a) S :=
  (differentiableAt_cayleyChartInv hS.2).comp S
    ((differentiableAt_cayleyChart (mem_cayleyChartSource.1 hS.1)).const_mul _)

open scoped Matrix.Norms.Frobenius in
/-- Differentiating `φ(τ(S)) = a φ(S)`: `dφ_{τ(S)} (dτ_S T) = a dφ_S T`. -/
private theorem fderiv_cayleyChart_cayleyTransition_apply {S} (hS : S ∈ transitionSource a)
    (T : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    fderiv ℝ (cayleyChart A) (cayleyTransition a S) (fderiv ℝ (cayleyTransition a) S T) =
      ((a : GL n ℂ) : Matrix n n ℂ) * fderiv ℝ (cayleyChart A) S T := by
  have h1 := (differentiableAt_cayleyChart (mem_cayleyChartSource.1
    (cayleyTransition_mem hA hA' a hS))).hasFDerivAt.comp S
      (differentiableAt_cayleyTransition a hS).hasFDerivAt
  have h2 := (differentiableAt_cayleyChart (mem_cayleyChartSource.1 hS.1)).hasFDerivAt.const_mul
    ((a : GL n ℂ) : Matrix n n ℂ)
  have heq : (fun S ↦ ((a : GL n ℂ) : Matrix n n ℂ) * cayleyChart A S) =ᶠ[𝓝 S]
      cayleyChart A ∘ cayleyTransition a :=
    Filter.eventually_of_mem ((isOpen_transitionSource a).mem_nhds hS) fun S' hS' ↦
      (cayleyChart_cayleyTransition hA hA' a hS').symm
  have := DFunLike.congr_fun (h1.unique (h2.congr_of_eventuallyEq heq.symm)) T
  -- The composite and the scalar multiple mix Frobenius and default matrix instances, so their
  -- `_apply` lemmas do not fire; both sides agree with the goal after unfolding.
  exact this

open scoped Matrix.Norms.Frobenius in
/-- **The Jacobian of the transition map.** Since the logarithmic derivative of the chart is
invariant under left multiplication by `a`, the determinant of `dτ_S` is the ratio of the Cayley
densities at `S` and at `τ(S)`. -/
private theorem det_fderiv_cayleyTransition_mul {S} (hS : S ∈ transitionSource a) :
    (fderiv ℝ (cayleyTransition a) S).det * (normSq (1 - (2 : ℂ)⁻¹ •
      (A⁻¹ * (cayleyTransition a S : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹ =
      (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹ := by
  rw [← det_codRestrict_mulLeft_comp_fderiv_cayleyChart hA hA' (mem_cayleyChartSource.1 hS.1),
    ← det_codRestrict_mulLeft_comp_fderiv_cayleyChart hA hA'
      (mem_cayleyChartSource.1 (cayleyTransition_mem hA hA' a hS)),
    mul_comm, ContinuousLinearMap.det, ← LinearMap.det_comp]
  refine congrArg LinearMap.det (LinearMap.ext fun T ↦ Subtype.ext ?_)
  -- The composite mixes Frobenius and default matrix instances, so the `_apply` lemmas of the
  -- linear maps do not fire; the goal is restated by unfolding.
  change star (cayleyChart A (cayleyTransition a S)) * A *
      fderiv ℝ (cayleyChart A) (cayleyTransition a S) (fderiv ℝ (cayleyTransition a) S T) =
    star (cayleyChart A S) * A * fderiv ℝ (cayleyChart A) S T
  rw [fderiv_cayleyChart_cayleyTransition_apply hA hA' a hS,
    cayleyChart_cayleyTransition hA hA' a hS, star_mul]
  have ha : star ((a : GL n ℂ) : Matrix n n ℂ) * A * ((a : GL n ℂ) : Matrix n n ℂ) = A :=
    mem_unitaryGroupOf_iff.1 a.property
  calc star (cayleyChart A S) * star ((a : GL n ℂ) : Matrix n n ℂ) * A *
        (((a : GL n ℂ) : Matrix n n ℂ) * fderiv ℝ (cayleyChart A) S T)
      = star (cayleyChart A S) * (star ((a : GL n ℂ) : Matrix n n ℂ) * A *
          ((a : GL n ℂ) : Matrix n n ℂ)) * fderiv ℝ (cayleyChart A) S T := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha]

open scoped Matrix.Norms.Frobenius in
/-- The Cayley density transforms under the transition map by its Jacobian. -/
private theorem ofReal_abs_det_mul_cayleyDensity {S} (hS : S ∈ transitionSource a) :
    ENNReal.ofReal |(fderiv ℝ (cayleyTransition a) S).det| *
      cayleyDensity A (cayleyTransition a S) = cayleyDensity A S := by
  have hpos (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) (hS : S ∈ cayleyChartSource A) :
      0 < (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹ :=
    inv_pos.2 (normSq_det_pow_pos_of_mem_cayleyChartSource hS)
  rw [cayleyDensity_def, cayleyDensity_def, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← abs_of_pos (hpos _ (cayleyTransition_mem hA hA' a hS)), ← abs_mul,
    det_fderiv_cayleyTransition_mul hA hA' a hS, abs_of_pos (hpos _ hS.1)]

end Transition

/-- The **Cayley measure** on the unitary group of `A` attached to a measure `μ` on the
skew-Hermitian matrices: the image under the Cayley chart of the measure of density
`|det (1 - A⁻¹ S / 2)|^(-2 n)` with respect to `μ`. For an invertible Hermitian `A` and an additive
Haar measure `μ` it is a left and right Haar measure on the unitary group of `A`
(`Matrix.unitaryGroupOf.isHaarMeasure_cayleyMeasure`). -/
noncomputable def cayleyMeasure (A : Matrix n n ℂ) [MeasurableSpace (unitaryGroupOf A)]
    (μ : Measure (skewAdjoint.submodule ℝ (Matrix n n ℂ))) : Measure (unitaryGroupOf A) :=
  (μ.withDensity (cayleyDensity A)).map (cayleyChartUnitary A)

variable {A : Matrix n n ℂ} (μ : Measure (skewAdjoint.submodule ℝ (Matrix n n ℂ)))
  [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)]

omit [BorelSpace (unitaryGroupOf A)] in
/-- The defining formula of the Cayley measure. -/
theorem cayleyMeasure_def :
    cayleyMeasure A μ = (μ.withDensity (cayleyDensity A)).map (cayleyChartUnitary A) :=
  (rfl)

/-- **Integrals for the Cayley measure** in Cayley coordinates:
`∫ F dμ^c = ∫ |det (1 - A⁻¹ S / 2)|^(-2 n) F (φ(S)) dμ(S)`. -/
theorem lintegral_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A)
    {F : unitaryGroupOf A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g ∂cayleyMeasure A μ = ∫⁻ S, cayleyDensity A S * F (cayleyChartUnitary A S) ∂μ := by
  rw [cayleyMeasure_def, lintegral_map hF (measurable_cayleyChartUnitary hA hA')]
  exact lintegral_withDensity_eq_lintegral_mul _ measurable_cayleyDensity
    (hF.comp (measurable_cayleyChartUnitary hA hA'))

section Invariance

variable [μ.IsAddHaarMeasure]

omit [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)] in
/-- For an invertible matrix `a`, the set of points `S` of the source of the chart at which
`1 + a φ(S)` is singular is null. It is contained in the zero set of
`S ↦ det ((1 + a) + (a - 1) A⁻¹ S / 2)`, which does not vanish at `S = i s A` for all but finitely
many real `s`. -/
private theorem measure_setOf_not_isUnit_one_add_mul_cayleyChart (hA : A.IsHermitian)
    (hA' : IsUnit A) (a : GL n ℂ) :
    μ {S | S ∈ cayleyChartSource A ∧ ¬IsUnit (1 + (a : Matrix n n ℂ) * cayleyChart A S)} = 0 := by
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA'
  let L : skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ :=
    LinearMap.mulLeft ℝ ((2 : ℂ)⁻¹ • (((a : Matrix n n ℂ) - 1) * A⁻¹)) ∘ₗ
      (skewAdjoint.submodule ℝ (Matrix n n ℂ)).subtype
  have hL (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      L S = ((a : Matrix n n ℂ) - 1) * ((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))) := by
    simp [L, Matrix.mul_assoc]
  refine measure_mono_null (fun S hS ↦ ?_)
    (Measure.addHaar_setOf_det_add_eq_zero μ (1 + (a : Matrix n n ℂ)) L ?_)
  · -- `(1 + a φ(S)) (1 - X) = (1 + a) + (a - 1) X` with `X = A⁻¹ S / 2`.
    obtain ⟨hS, hS'⟩ := hS
    have hD := isUnit_iff_ne_zero.2 (mem_cayleyChartSource_iff_det_ne_zero.1 hS)
    have key : (1 + (a : Matrix n n ℂ) * cayleyChart A S) *
        (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))) = 1 + (a : Matrix n n ℂ) + L S := by
      rw [cayleyChart_eq, hL, add_mul, one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
        nonsing_inv_mul _ hD, Matrix.mul_one]
      generalize (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)) = X
      noncomm_ring
    have h0 : (1 + (a : Matrix n n ℂ) * cayleyChart A S).det = 0 := by
      rwa [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hS'
    simp only [mem_ofPred_eq, ← key, det_mul, h0, zero_mul]
  · -- `S = i s A` gives `(1 + a) + (a - 1) X = (1 - i s / 2) + (1 + i s / 2) a`.
    have hfinite := finite_setOf_det_smul_add_eq_zero
      ((a : Matrix n n ℂ) - 1) (1 + (a : Matrix n n ℂ)) ⟨-1, by
        have h : (-1 : ℂ) • ((a : Matrix n n ℂ) - 1) + (1 + (a : Matrix n n ℂ)) =
            (2 : ℂ) • (1 : Matrix n n ℂ) := by module
        rw [h, det_smul, det_one, mul_one]
        exact pow_ne_zero _ (by norm_num)⟩
    obtain ⟨s, -, hs⟩ := Set.infinite_univ.exists_notMem_finite
      (hfinite.preimage
        (f := fun s : ℝ ↦ I * s / 2) (fun x _ y _ h ↦ by simpa using h))
    simp only [mem_preimage, mem_ofPred_eq] at hs
    have hmem : (I * s) • A ∈ skewAdjoint.submodule ℝ (Matrix n n ℂ) := by
      -- Membership in the submodule of skew-Hermitian matrices is membership in `skewAdjoint`.
      change (I * s) • A ∈ skewAdjoint (Matrix n n ℂ)
      rw [skewAdjoint.mem_iff, star_smul, star_eq_conjTranspose A, hA.eq]
      simp
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [hL]
    convert hs using 2
    simp only [Matrix.mul_smul, nonsing_inv_mul _ hd, Matrix.mul_one,
      smul_smul]
    module

open scoped Matrix.Norms.Frobenius in
/-- Left invariance of integrals for the Cayley measure. For an invertible Hermitian `A`, an
additive Haar measure `μ` and `a` in the unitary group of `A`,
`∫ F(a g) dμ^c(g) = ∫ F dμ^c`. -/
private theorem lintegral_mul_left_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A)
    (a : unitaryGroupOf A) {F : unitaryGroupOf A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (a * g) ∂cayleyMeasure A μ = ∫⁻ g, F g ∂cayleyMeasure A μ := by
  rw [lintegral_cayleyMeasure μ hA hA' (F := fun g ↦ F (a * g)) (hF.comp (measurable_const_mul a)),
    lintegral_cayleyMeasure μ hA hA' hF]
  -- The transition map `τ = φ⁻¹ ∘ (a ·) ∘ φ` is a diffeomorphism from `transitionSource a`
  -- onto a set containing `transitionSource a⁻¹`, and both sets have null complements in the
  -- source of the chart, off which the density vanishes.
  have hsupp {G : unitaryGroupOf A → ℝ≥0∞} {T : Set (skewAdjoint.submodule ℝ (Matrix n n ℂ))}
      (b : unitaryGroupOf A) (hT : transitionSource b ⊆ T) :
      ∫⁻ S, cayleyDensity A S * G (cayleyChartUnitary A S) ∂μ =
        ∫⁻ S in T, cayleyDensity A S * G (cayleyChartUnitary A S) ∂μ := by
    rw [← Measure.restrict_congr_set (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2
      (measure_setOf_not_isUnit_one_add_mul_cayleyChart μ hA hA' (b : GL n ℂ))))]
    refine (setLIntegral_eq_of_support_subset fun S hS ↦ ?_).symm
    have hS' : S ∈ cayleyChartSource A := by
      by_contra h
      simp [Function.mem_support, cayleyDensity_of_notMem h] at hS
    by_cases hb : IsUnit (1 + ((b : GL n ℂ) : Matrix n n ℂ) * cayleyChart A S)
    · exact Or.inl (hT ⟨hS', hb⟩)
    · exact Or.inr ⟨hS', hb⟩
  rw [hsupp a⁻¹ (transitionSource_inv_subset_image hA hA' a),
    μ.lintegral_image_eq_lintegral_abs_det_fderiv_mul_skewAdjoint
    (isOpen_transitionSource a).measurableSet
    (fun S hS ↦ (differentiableAt_cayleyTransition a hS).hasFDerivAt.hasFDerivWithinAt)
    (injOn_cayleyTransition hA hA' a),
    hsupp (G := fun g ↦ F (a * g)) a subset_rfl]
  refine setLIntegral_congr_fun (isOpen_transitionSource a).measurableSet fun S hS ↦ ?_
  rw [← mul_assoc, ofReal_abs_det_mul_cayleyDensity hA hA' a hS,
    cayleyChartUnitary_cayleyTransition hA hA' a hS]

/-- **The Cayley measure is left invariant.** For an invertible Hermitian `A` and an additive
Haar measure `μ`, the Cayley measure on the unitary group of `A` is invariant under left
multiplication. -/
theorem isMulLeftInvariant_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A) :
    (cayleyMeasure A μ).IsMulLeftInvariant :=
  ⟨fun a ↦ Measure.ext_of_lintegral _ fun F hF ↦ by
    rw [lintegral_map hF (measurable_const_mul a), lintegral_mul_left_cayleyMeasure μ hA hA' a hF]⟩

/-- Inversion invariance of integrals for the Cayley measure: `∫ F(g⁻¹) dμ^c = ∫ F dμ^c`.
In Cayley coordinates inversion is `S ↦ -S`, which preserves the density and `μ`. -/
private theorem lintegral_inv_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A)
    {F : unitaryGroupOf A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g⁻¹ ∂cayleyMeasure A μ = ∫⁻ g, F g ∂cayleyMeasure A μ := by
  rw [lintegral_cayleyMeasure μ hA hA' (F := fun g ↦ F g⁻¹) (hF.comp measurable_inv),
    lintegral_cayleyMeasure μ hA hA' hF,
    ← lintegral_neg_eq_self (μ := μ) (fun S ↦ cayleyDensity A S * F (cayleyChartUnitary A S))]
  simp only [cayleyDensity_neg hA, cayleyChartUnitary_neg hA hA']

/-- **The Cayley measure is invariant under inversion.** -/
theorem isInvInvariant_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A) :
    (cayleyMeasure A μ).IsInvInvariant :=
  ⟨Measure.ext_of_lintegral _ fun F hF ↦ by
    rw [Measure.inv, lintegral_map hF measurable_inv, lintegral_inv_cayleyMeasure μ hA hA' hF]⟩

/-- **The Cayley measure is right invariant.** -/
theorem isMulRightInvariant_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A) :
    (cayleyMeasure A μ).IsMulRightInvariant := by
  have := isMulLeftInvariant_cayleyMeasure μ hA hA'
  have := isInvInvariant_cayleyMeasure μ hA hA'
  rw [← Measure.inv_eq_self (cayleyMeasure A μ)]
  infer_instance

/-- **The Cayley measure is a Haar measure.** For an invertible Hermitian `A` and an additive Haar
measure `μ` on the skew-Hermitian matrices, the Cayley measure is a left Haar measure on the
unitary group of `A`; it is also right invariant
(`Matrix.unitaryGroupOf.isMulRightInvariant_cayleyMeasure`). -/
theorem isHaarMeasure_cayleyMeasure (hA : A.IsHermitian) (hA' : IsUnit A) :
    (cayleyMeasure A μ).IsHaarMeasure := by
  have := isMulLeftInvariant_cayleyMeasure μ hA hA'
  obtain ⟨K₀, hK₀, h0, hK₀s⟩ :=
    exists_compact_subset isOpen_cayleyChartSource (zero_mem_cayleyChartSource (A := A))
  have hf := continuousOn_cayleyChartUnitary hA hA'
  have hfm := measurable_cayleyChartUnitary hA hA'
  set K := cayleyChartUnitary A '' K₀
  have hK : IsCompact K := hK₀.image_of_continuousOn (hf.mono hK₀s)
  have hopen := isOpen_image_cayleyChartUnitary hA hA' isOpen_interior (interior_subset.trans hK₀s)
  have h1 : (1 : unitaryGroupOf A) ∈ interior K := by
    refine interior_maximal (image_mono interior_subset) hopen ⟨0, h0, ?_⟩
    exact cayleyChartUnitary_zero A
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hmeas : cayleyMeasure A μ K = ∫⁻ S in cayleyChartUnitary A ⁻¹' K, cayleyDensity A S ∂μ := by
    rw [cayleyMeasure_def, Measure.map_apply hfm hKm, withDensity_apply _ (hfm hKm)]
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK ⟨1, h1⟩ ?_ ?_
  · -- `K` has positive measure: the density is positive on `K₀`, which has positive measure.
    rw [hmeas]
    refine ((setLIntegral_pos_iff measurable_cayleyDensity).2 ?_).ne'
    refine (Measure.measure_pos_of_nonempty_interior μ ⟨0, h0⟩).trans_le
      (measure_mono fun S hS ↦ ?_)
    exact ⟨(cayleyDensity_pos (hK₀s hS)).ne', mem_image_of_mem _ hS⟩
  · -- `K` has finite measure: the points of `φ⁻¹(K)` at which the density is nonzero lie in `K₀`,
    -- on which the density is bounded.
    rw [hmeas]
    refine (lt_of_le_of_lt (b := ∫⁻ S in K₀, cayleyDensity A S ∂μ) ?_ ?_).ne
    · rw [← lintegral_indicator (hfm hKm), ← lintegral_indicator hK₀.isClosed.measurableSet]
      refine lintegral_mono fun S ↦ ?_
      by_cases hS : S ∈ cayleyChartUnitary A ⁻¹' K
      · by_cases hS' : S ∈ cayleyChartSource A
        · rw [indicator_of_mem hS]
          obtain ⟨S₀, hS₀, hS₀'⟩ : cayleyChartUnitary A S ∈ cayleyChartUnitary A '' K₀ := hS
          have : S₀ = S := injOn_cayleyChart hA hA' (hK₀s hS₀) hS' <| by
            rw [← coe_cayleyChartUnitary hA hA' (hK₀s hS₀), hS₀', coe_cayleyChartUnitary hA hA' hS']
          rw [indicator_of_mem (this ▸ hS₀)]
        · rw [indicator_of_mem hS, cayleyDensity_of_notMem hS']
          exact bot_le
      · simp [indicator_of_notMem hS]
    · obtain ⟨S₁, -, hmax⟩ := hK₀.exists_isMaxOn ⟨0, interior_subset h0⟩
        (continuousOn_cayleyDensity.mono hK₀s)
      calc ∫⁻ S in K₀, cayleyDensity A S ∂μ ≤ ∫⁻ _ in K₀, cayleyDensity A S₁ ∂μ :=
            setLIntegral_mono measurable_const fun S hS ↦ hmax hS
        _ = cayleyDensity A S₁ * μ K₀ := setLIntegral_const _ _
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK₀.measure_lt_top

end Invariance

end unitaryGroupOf
end Matrix
