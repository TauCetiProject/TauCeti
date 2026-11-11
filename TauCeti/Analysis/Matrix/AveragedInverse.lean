/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
import TauCeti.Analysis.Holder.Integral
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Matrix.Holder
import TauCeti.Analysis.Matrix.InverseSegment
import TauCeti.Analysis.Matrix.PosDef

/-!
# Segment-averaged inverse matrices

`Matrix.segmentAveragedInverse A B` integrates `((1-t) A + t B)⁻¹` entrywise over `[0, 1]`.
Its API gives the self and endpoint-swap identities, symmetry for symmetric endpoints,
positive definiteness for positive-definite endpoints, and the quadratic-form integral formula.

The coefficients of a log-determinant difference equation are the integral of the inverse of
the segment joining two Hessians. Continuous positive definite fields on compact sets give uniform
ellipticity bounds. If the field also has Hölder entries, the averaged coefficients of every
admissible translation have a common entrywise Hölder bound.

The arguments follow the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

noncomputable section

open Set MeasureTheory Matrix
open scoped NNReal

namespace Matrix

/-- The entrywise integral `∫₀¹ ((1 - t) • A + t • B)⁻¹ dt`.
The matrix inverse is zero at singular matrices, and an entry integral is zero if it is not
integrable. Positive-definite endpoints ensure an invertible segment and integrable entries,
so in that case this is the usual averaged inverse. -/
def segmentAveragedInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ t in (0 : ℝ)..1, ((1 - t) • A + t • B)⁻¹ i j

/-- An entry of the segment-averaged inverse is the integral of the corresponding inverse entry. -/
@[simp] theorem segmentAveragedInverse_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (i j : ι) :
    segmentAveragedInverse A B i j = ∫ t in (0 : ℝ)..1, ((1 - t) • A + t • B)⁻¹ i j := by
  rw [segmentAveragedInverse, Matrix.of_apply]

/-- Averaging the constant inverse segment returns the inverse. -/
@[simp] theorem segmentAveragedInverse_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : segmentAveragedInverse A A = A⁻¹ := by
  ext i j
  rw [segmentAveragedInverse_apply]
  simp_rw [← add_smul, sub_add_cancel, one_smul]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]

/-- Reversing the two endpoints does not change the segment-averaged inverse. -/
theorem segmentAveragedInverse_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) : segmentAveragedInverse A B = segmentAveragedInverse B A := by
  ext i j
  rw [segmentAveragedInverse_apply, segmentAveragedInverse_apply]
  have h := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => ((1 - t) • A + t • B)⁻¹ i j) 1 (a := 0) (b := 1)
  simpa only [sub_sub_cancel, sub_zero, sub_self, add_comm] using h.symm

/-- Symmetric endpoints give a symmetric segment-averaged inverse, even when singular. -/
theorem isSymm_segmentAveragedInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsSymm) (hB : B.IsSymm) :
    (segmentAveragedInverse A B).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, segmentAveragedInverse_apply]
  apply intervalIntegral.integral_congr
  intro t _
  exact ((hA.smul (1 - t)).add (hB.smul t)).inv.apply i j

end Matrix

namespace TauCeti

section SegmentInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {X : Type*} [PseudoMetricSpace X]

/-- Uniform entry bounds on the inverse segments transfer the Hölder modulus of the endpoints
to the entries of the averaged inverse. -/
theorem holderWith_segmentAveragedInverse_apply (P Q : X → Matrix ι ι ℝ) (C r L : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j))
    (hp : ∀ x, (P x).PosDef) (hq : ∀ x, (Q x).PosDef)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x i j, |((1 - t) • P x + t • Q x)⁻¹ i j| ≤ L) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
      (fun x => segmentAveragedInverse (P x) (Q x) i j) := by
  simp only [segmentAveragedInverse_apply]
  have hh : ∀ t ∈ uIoc (0 : ℝ) 1,
      HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
        (fun x => ((1 - t) • P x + t • Q x)⁻¹ i j) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht
    exact holderWith_matrix_inv_apply (fun x => (1 - t) • P x + t • Q x) C r L
      (fun x => ((hp x).one_sub_smul_add_smul (hq x) ht').isUnit) (hb t ht')
      (holderWith_one_sub_smul_add_smul_apply P Q C r hP hQ ht') i j
  simpa only [sub_zero, nnnorm_one, one_mul] using
    holderWith_intervalIntegral (fun t x => ((1 - t) • P x + t • Q x)⁻¹ i j)
      ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
      (fun x => (hp x).intervalIntegrable_inv_segment_apply (hq x) i j) hh

end SegmentInverse

section HolderTranslations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [SeminormedAddCommGroup E]

/-- One entry bound works for all endpoint pairs in `s`. For every displacement preserving both
endpoints in `s`, the translated averaged field has entrywise Hölder constant `(card ι)^2 L^2 C`. -/
theorem exists_uniform_segmentAveragedInverse_holderOnWith (H : E → Matrix ι ι ℝ) {s : Set E}
    (hs : IsCompact s) (C r : ℝ≥0) (hr : 0 < r)
    (hH : ∀ i j, HolderOnWith C r (fun x => H x i j) s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ L : ℝ≥0,
      0 < L ∧
        (∀ x ∈ s, ∀ y ∈ s, ∀ i j, |segmentAveragedInverse (H x) (H y) i j| ≤ L) ∧
          ∀ (d : E) (a : Set E),
            a ⊆ s →
              (∀ x ∈ a, x + d ∈ s) →
                ∀ i j,
                  HolderOnWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
                    (fun x => segmentAveragedInverse (H x) (H (x + d)) i j) a := by
  have hc : ContinuousOn H s :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (hH i j).continuousOn hr
  obtain ⟨L, hL, hcap⟩ := exists_uniform_inv_segment_apply_bound H hs hc hpos
  have hmean (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) (i j : ι) :
      |segmentAveragedInverse (H x) (H y) i j| ≤ (L : ℝ) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := (L : ℝ))
      (f := fun t => ((1 - t) • H x + t • H y)⁻¹ i j)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht
        exact hcap x hx y hy t ht' i j)
    simpa only [segmentAveragedInverse_apply, Real.norm_eq_abs, sub_zero, abs_one,
      mul_one, one_mul] using h
  refine ⟨L, hL, hmean, ?_⟩
  intro d a ha hshift i j
  let P : a → Matrix ι ι ℝ := fun x => H x
  let Q : a → Matrix ι ι ℝ := fun x => H (x + d)
  have hP (k l : ι) : HolderWith C r (fun x : a => P x k l) := by
    intro x y
    exact hH k l x (ha x.property) y (ha y.property)
  have hQ (k l : ι) : HolderWith C r (fun x : a => Q x k l) := by
    intro x y
    have hh := hH k l (x + d) (hshift x x.property) (y + d) (hshift y y.property)
    simpa only [edist_add_right, Subtype.edist_eq] using hh
  have hB (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : a) (k l : ι) :
    |((1 - θ) • P x + θ • Q x)⁻¹ k l| ≤ L :=
    hcap x (ha x.property) (x + d) (hshift x x.property) θ hθ k l
  exact
    HolderWith.restrict_iff.mp (holderWith_segmentAveragedInverse_apply P Q C r L hP hQ
      (fun x => hpos x (ha x.property)) (fun x => hpos (x + d) (hshift x x.property)) hB i j)

end HolderTranslations

section Ellipticity

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form of the averaged inverse is the integral of the inverse quadratic forms. -/
theorem _root_.Matrix.segmentAveragedInverse_toQuadraticForm' (A B : Matrix ι ι ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (ξ : ι → ℝ) :
    (segmentAveragedInverse A B).toQuadraticForm' ξ =
      ∫ t in (0 : ℝ)..1, (((1 - t) • A + t • B)⁻¹).toQuadraticForm' ξ := by
  symm
  simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hi := hA.intervalIntegrable_inv_segment_apply hB
  have hm (i j : ι) := ((hi i j).mul_const (ξ j)).const_mul (ξ i)
  have hr (i : ι) :
      IntervalIntegrable (fun t : ℝ => ∑ j, ξ i * (((1 - t) • A + t • B)⁻¹ i j * ξ j))
        volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hm i j) using 1
    funext t
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun i t => ∑ j, ξ i * (((1 - t) • A + t • B)⁻¹ i j * ξ j)) (fun i _ => hr i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun j t => ξ i * (((1 - t) • A + t • B)⁻¹ i j * ξ j)) (fun j _ => hm i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    segmentAveragedInverse_apply]

/-- Positive-definite endpoints give a positive-definite segment-averaged inverse. -/
theorem _root_.Matrix.posDef_segmentAveragedInverse (A B : Matrix ι ι ℝ)
    (hA : A.PosDef) (hB : B.PosDef) : (segmentAveragedInverse A B).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr
    (Matrix.isSymm_segmentAveragedInverse
      (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian)
      (Matrix.isHermitian_iff_isSymm.mp hB.isHermitian)), ?_⟩
  intro ξ hξ
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hA.intervalIntegrable_inv_segment_toQuadraticForm' hB ξ)
    (fun t ht => by
      rw [Matrix.toQuadraticForm'_apply]
      exact (hA.one_sub_smul_add_smul hB ⟨ht.1.le, ht.2.le⟩).inv.dotProduct_mulVec_pos hξ)
    zero_lt_one
  rwa [← Matrix.segmentAveragedInverse_toQuadraticForm' A B hA hB,
    Matrix.toQuadraticForm'_apply] at h

/-- A continuous positive definite matrix field on a compact set gives uniform quadratic lower
and upper bounds for the segment-averaged inverse of all endpoint pairs. -/
theorem exists_uniform_segmentAveragedInverse_ellipticity [TopologicalSpace X]
    (H : X → Matrix ι ι ℝ)
    {s : Set X} (hs : IsCompact s) (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ ξ : EuclideanSpace ℝ ι,
      a * ‖ξ‖ ^ 2 ≤ (segmentAveragedInverse (H x) (H y)).toQuadraticForm' ξ ∧
        (segmentAveragedInverse (H x) (H y)).toQuadraticForm' ξ ≤ b * ‖ξ‖ ^ 2 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hposSegment (z : (s × s) × Icc (0 : ℝ) 1) :
      (((1 - (z.2 : ℝ)) • H z.1.1 + (z.2 : ℝ) • H z.1.2)⁻¹).PosDef :=
    ((hpos z.1.1 z.1.1.property).one_sub_smul_add_smul (hpos z.1.2 z.1.2.property) z.2.property).inv
  obtain ⟨a, b, ha, hb, hbound⟩ := exists_uniform_quadratic_bounds _
    (continuous_inv_segment_pairs H hH hpos) hposSegment
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx y hy ξ
  have hi := (hpos x hx).intervalIntegrable_inv_segment_toQuadraticForm' (hpos y hy) ξ
  have heq := (Matrix.segmentAveragedInverse_toQuadraticForm' (H x) (H y)
    (hpos x hx) (hpos y hy) ξ).symm
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hbound ((⟨x, hx⟩, ⟨y, hy⟩), ⟨t, ht⟩) ξ
  have hlo := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hi
    (fun t ht => (he t ht).1)
  have hup := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const
    (fun t ht => (he t ht).2)
  rw [heq] at hlo hup
  exact ⟨by simpa using hlo, by simpa using hup⟩

end Ellipticity

end TauCeti
