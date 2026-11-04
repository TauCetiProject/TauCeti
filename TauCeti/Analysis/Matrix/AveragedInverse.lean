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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.Matrix.PosDef

/-!
# Hölder bounds and ellipticity for segment-averaged inverses

The coefficients of a log-determinant difference equation are the integral of the inverse of
the segment joining two Hessians. A compact family of positive definite matrices gives uniform
ellipticity and a uniform Hölder modulus for the coefficients obtained by translating the field.
The constants are chosen before the translation.

The arguments follow the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

noncomputable section

namespace TauCeti

open Set Metric MeasureTheory Matrix
open scoped NNReal ENNReal Matrix.Norms.Elementwise

/-- The integral of the inverse of the segment from `A` to `B`, taken entry by entry. -/
def segmentAveragedInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ t in (0 : ℝ)..1, ((1 - t) • A + t • B)⁻¹ i j

/-- An entry of the segment-averaged inverse is the integral of the corresponding inverse entry. -/
theorem segmentAveragedInverse_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (i j : ι) :
    segmentAveragedInverse A B i j = ∫ t in (0 : ℝ)..1, ((1 - t) • A + t • B)⁻¹ i j := by
  rw [segmentAveragedInverse]

section InverseEntries

open scoped BigOperators NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
**Entrywise modulus of the inverse.** For invertible `A`, `B` whose inverse entries are bounded by
`L ≥ 0` and whose
entrywise difference is bounded by `d ≥ 0`, `|A⁻¹ᵢⱼ − B⁻¹ᵢⱼ| ≤ n² L² d` with `n = card ι`, from
`A⁻¹ − B⁻¹ = A⁻¹ (B − A) B⁻¹`. -/
private theorem abs_inv_sub_inv_entry_le {A B : Matrix ι ι ℝ} {L d : ℝ}
    (hA : IsUnit A) (hB : IsUnit B)
    (hL : 0 ≤ L) (hd : 0 ≤ d) (ha : ∀ i j, |A⁻¹ i j| ≤ L) (hb : ∀ i j, |B⁻¹ i j| ≤ L)
    (hab : ∀ i j, |A i j - B i j| ≤ d) (i j : ι) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (Fintype.card ι : ℝ) ^ 2 * L ^ 2 * d := by
  classical
  have hi : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv ⟨fun _ => hB, fun _ => hA⟩
  calc
    |A⁻¹ i j - B⁻¹ i j| = |∑ k : ι, ∑ l : ι, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      change |(A⁻¹ - B⁻¹) i j| = _
      rw [hi]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    _ ≤ ∑ k : ι, ∑ l : ι, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      exact
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, L * d * L := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_mul, abs_sub_comm (B l k) (A l k)]
      exact
        mul_le_mul (mul_le_mul (ha i l) (hab l k) (abs_nonneg _) hL) (hb k j) (abs_nonneg _)
          (mul_nonneg hL hd)
    _ = _ := by simp; ring

/-- A map with `dist (f x) (f y) ≤ C · dist x y ^ r` is `(C, r)`-Hölder. -/
private theorem holderWith_of_dist_bound {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (C r : ℝ≥0)
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg]
  calc
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x y)
    _ = _ := by rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/--
If a field `P` of invertible matrices has `(C, r)`-Hölder entries and inverse entries bounded by
`L`, every entry of
`P⁻¹` is `(n² L² C, r)`-Hölder; the constant is fixed before the entries and the points. -/
private theorem holderWith_inverse_entries {X : Type*} [PseudoMetricSpace X] (P : X → Matrix ι ι ℝ)
    (C r L : ℝ≥0) (hP : ∀ x, IsUnit (P x)) (hb : ∀ x i j, |(P x)⁻¹ i j| ≤ L)
    (hc : ∀ i j, HolderWith C r (fun x => P x i j)) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r (fun x => (P x)⁻¹ i j) := by
  apply holderWith_of_dist_bound
  intro x y
  have h :=
    abs_inv_sub_inv_entry_le (hP x) (hP y) L.coe_nonneg
      (mul_nonneg C.coe_nonneg (Real.rpow_nonneg dist_nonneg _)) (hb x) (hb y)
      (fun a b => by simpa only [Real.dist_eq] using (hc a b).dist_le x y) i j
  simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using
    h

end InverseEntries

/--
If `q t` is `(C, r)`-Hölder for every `t ∈ (0, 1]` and every `t ↦ q t x` is interval integrable on
`[0, 1]`, then
`x ↦ ∫₀¹ q t x dt` is `(C, r)`-Hölder with the same constants. -/
private theorem holderWith_unit_interval_mean {X : Type*} [PseudoMetricSpace X] (q : ℝ → X → ℝ)
    (C r : ℝ≥0) (hq : ∀ x, IntervalIntegrable (fun t => q t x) volume 0 1)
    (hh : ∀ t ∈ uIoc (0 : ℝ) 1, HolderWith C r (q t)) :
    HolderWith C r (fun x => ∫ t in (0 : ℝ)..1, q t x) := by
  apply holderWith_of_dist_bound
  intro x y
  rw [Real.dist_eq, ← intervalIntegral.integral_sub (hq x) (hq y)]
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1, ‖q t x - q t y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ) :=
    fun t ht => by simpa only [Real.norm_eq_abs, Real.dist_eq] using (hh t ht).dist_le x y
  simpa only [sub_zero, abs_one, one_mul, mul_one, Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

section AveragedInverse

open Set MeasureTheory
open scoped NNReal ENNReal

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [Fintype ι] [DecidableEq ι] in
/--
For `t ∈ [0, 1]`, the entries of `(1 − t) P + t Q` are `(C, r)`-Hölder when those of `P` and `Q`
are. -/
private theorem holderWith_convex_matrix_entries (P Q : X → Matrix ι ι ℝ) (C r : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j)) {t : ℝ} (ht : t ∈ Icc 0 1) (i j : ι) :
    HolderWith C r (fun x => ((1 - t) • P x + t • Q x) i j) := by
  have h := ((hP i j).smul (1 - t)).add ((hQ i j).smul t)
  have heq : C * ‖1 - t‖₊ + C * ‖t‖₊ = C := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    ring
  rw [heq] at h
  convert h using 1
  rfl

/--
**Hölder averaged inverse.** If `P` and `Q` have `(C, r)`-Hölder entries and every `(1 − t) P x + t
Q x`, `t ∈ [0, 1]`,
is invertible with inverse entries bounded by `L`, then `x ↦ ∫₀¹ ((1 − t) P x + t Q x)⁻¹ᵢⱼ dt` is
`(n² L² C, r)`-Hölder.
Interval integrability is derived from continuity of the inverse. -/
private theorem holderWith_averaged_inverse_entries (P Q : X → Matrix ι ι ℝ) (C r L : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j))
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, IsUnit ((1 - t) • P x + t • Q x))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x i j, |((1 - t) • P x + t • Q x)⁻¹ i j| ≤ L) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
      (fun x => ∫ t in (0 : ℝ)..1, ((1 - t) • P x + t • Q x)⁻¹ i j) := by
  have hint (x : X) :
    IntervalIntegrable (fun t : ℝ => ((1 - t) • P x + t • Q x)⁻¹ i j) volume 0 1 := by
    have hc : ContinuousOn (fun t : ℝ => ((1 - t) • P x + t • Q x)⁻¹ i j) (Icc 0 1) := by
      intro t ht
      have hn : (((1 - t) • P x + t • Q x).det) ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det ((1 - t) • P x + t • Q x)).mp (hu t ht x)).ne_zero
      have hm : ContinuousAt (fun s : ℝ => ((1 - s) • P x + s • Q x)⁻¹) t :=
        (continuousAt_matrix_inv ((1 - t) • P x + t • Q x)
              (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hn)).comp
          (f := fun s : ℝ => (1 - s) • P x + s • Q x) (by fun_prop)
      exact
        (((continuous_apply j).comp (continuous_apply i)).continuousAt.comp (f := fun s : ℝ =>
            ((1 - s) • P x + s • Q x)⁻¹) hm).continuousWithinAt
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  apply holderWith_unit_interval_mean _ _ _ hint
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simp only [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  exact
    holderWith_inverse_entries (fun x => (1 - t) • P x + t • Q x) C r L (hu t ht') (hb t ht')
      (holderWith_convex_matrix_entries P Q C r hP hQ ht') i j

end AveragedInverse

section CompactPositiveFields

open Set MeasureTheory
open scoped NNReal Matrix.Norms.Elementwise ComplexOrder

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X] [CompactSpace X]

omit [Fintype ι] [DecidableEq ι] in
/--
Convex combinations `(1 − t) A + t B`, `t ∈ [0, 1]`, of positive definite matrices are positive
definite. -/
private theorem posDef_convex_segment {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ((1 - t) • A + t • B).PosDef :=
  convex_setOfPred_posDef hA hB (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

/--
On a compact space, continuous positive definite fields `P` and `Q` admit one bound `L > 0` on every
entry of
`((1 − t) P x + t Q x)⁻¹`, `t ∈ [0, 1]`; it is derived from continuity of the inverse on the compact
`X × [0, 1]`. -/
private theorem exists_uniform_inverse_entry_bound_on_compact (P Q : X → Matrix ι ι ℝ)
    (hP : Continuous P) (hQ : Continuous Q) (hPP : ∀ x, (P x).PosDef)
    (hQP : ∀ x, (Q x).PosDef) :
    ∃ L : ℝ≥0, 0 < L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x i j, |((1 - t) • P x + t • Q x)⁻¹ i j| ≤ L := by
  let F : X × Icc (0 : ℝ) 1 → Matrix ι ι ℝ := fun z =>
    (1 - (z.2 : ℝ)) • P z.1 + (z.2 : ℝ) • Q z.1
  have hc : Continuous F := by fun_prop
  have hi : Continuous (fun z => (F z)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply
      (continuousAt_matrix_inv (F z)
            (by
              simpa only [Ring.inverse_eq_inv'] using
                continuousAt_inv₀
                  (posDef_convex_segment (hPP z.1) (hQP z.1) z.2.property).det_pos.ne')).comp
        (f := F) hc.continuousAt
  obtain ⟨R, hR⟩ := (isCompact_range hi).isBounded.exists_norm_le
  let L : ℝ≥0 := ⟨max R 0 + 1, by positivity⟩
  refine ⟨L, by change (0 : ℝ) < max R 0 + 1; positivity, ?_⟩
  intro t ht x i j
  have hh := hR ((F (x, ⟨t, ht⟩))⁻¹) ⟨(x, ⟨t, ht⟩), rfl⟩
  have he := Matrix.norm_apply_le_norm ((F (x, ⟨t, ht⟩))⁻¹) (i := i) (j := j)
  change |((F (x, ⟨t, ht⟩))⁻¹) i j| ≤ (L : ℝ)
  rw [← Real.norm_eq_abs]
  exact he.trans (hh.trans (by change R ≤ max R 0 + 1; linarith [le_max_left R 0]))

end CompactPositiveFields

/-- Positive definite endpoints give a symmetric segment-averaged inverse. -/
theorem segmentAveragedInverse_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (segmentAveragedInverse A B).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, segmentAveragedInverse]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hsymm := Matrix.isHermitian_iff_isSymm.mp (posDef_convex_segment hA hB ht').inv.isHermitian
  exact hsymm.apply i j

section HolderTranslations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]

/-- One inverse cap for all endpoint pairs in a compact set. It is chosen
before either endpoint, interpolation parameter or displacement. -/
private theorem exists_pair_inverse_cap (H : E → Matrix ι ι ℝ) {s : Set E} (hs : IsCompact s)
    (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ L : ℝ≥0,
      0 < L ∧
        ∀ x ∈ s, ∀ y ∈ s, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ i j, |((1 - θ) • H x + θ • H y)⁻¹ i j| ≤ L := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let P : s × s → Matrix ι ι ℝ := fun z => H z.1
  let Q : s × s → Matrix ι ι ℝ := fun z => H z.2
  have hc : Continuous (fun x : s => H x) := hH.domRestrict
  obtain ⟨L, hL, hb⟩ :=
    exists_uniform_inverse_entry_bound_on_compact P Q (hc.comp continuous_fst)
      (hc.comp continuous_snd) (fun z => hpos z.1 z.1.property) (fun z => hpos z.2 z.2.property)
  exact ⟨L, hL, fun x hx y hy θ hθ i j => hb θ hθ (⟨x, hx⟩, ⟨y, hy⟩) i j⟩

/-- Uniform Hölder control of the *same* finite-difference coefficients.
The cap and Hölder constant are chosen before the displacement and the
inner set, and therefore do not deteriorate as a scalar step tends to zero.
Only containment of both endpoint sets in the fixed compact set is needed. -/
theorem exists_uniform_averagedInverse_holder (H : E → Matrix ι ι ℝ) {s : Set E}
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
  obtain ⟨L, hL, hcap⟩ := exists_pair_inverse_cap H hs hc hpos
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
    simpa [segmentAveragedInverse, Real.norm_eq_abs] using h
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
  have hU (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : a) : IsUnit ((1 - θ) • P x + θ • Q x) :=
    (posDef_convex_segment (hpos x (ha x.property))
      (hpos (x + d) (hshift x x.property)) hθ).isUnit
  have hB (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : a) (k l : ι) :
    |((1 - θ) • P x + θ • Q x)⁻¹ k l| ≤ L :=
    hcap x (ha x.property) (x + d) (hshift x x.property) θ hθ k l
  exact
    HolderWith.restrict_iff.mp (holderWith_averaged_inverse_entries P Q C r L hP hQ hU hB i j)

end HolderTranslations

section Ellipticity

variable {ι X : Type*} [Fintype ι]

/-- The real matrix quadratic form in the Euclidean standard coordinates. -/
private def quadratic (M : Matrix ι ι ℝ) (ξ : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ j, M i j * ξ i * ξ j

/-- Quadratic scaling, including scalar zero. -/
private theorem quadratic_smul (M : Matrix ι ι ℝ) (a : ℝ) (ξ : EuclideanSpace ℝ ι) :
    quadratic M (a • ξ) = a ^ 2 * quadratic M ξ := by
  unfold quadratic
  simp only [PiLp.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive definiteness is strict positivity of this quadratic form. -/
private theorem quadratic_pos {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {ξ : EuclideanSpace ℝ ι} (hξ : ξ ≠ 0) : 0 < quadratic M ξ := by
  have hfun : (fun i => ξ i) ≠ 0 := by
    intro h
    apply hξ
    ext i
    exact congrFun h i
  have hp := hM.dotProduct_mulVec_pos hfun
  simpa only [quadratic, dotProduct, Matrix.mulVec, star_trivial,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hp

/-- Uniform lower and upper quadratic bounds for a compact continuous positive definite family.
The constants precede both the family parameter and the vector. -/
private theorem exists_uniform_quadratic_bounds [TopologicalSpace X] [CompactSpace X]
    (A : X → Matrix ι ι ℝ) (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) :
    ∃ a b : ℝ,
      0 < a ∧
        0 < b ∧
          ∀ x (ξ : EuclideanSpace ℝ ι),
            a * ‖ξ‖ ^ 2 ≤ (∑ i, ∑ j, A x i j * ξ i * ξ j) ∧
              (∑ i, ∑ j, A x i j * ξ i * ξ j) ≤ b * ‖ξ‖ ^ 2 := by
  let S : Set (X × EuclideanSpace ℝ ι) := univ ×ˢ sphere 0 1
  let F : X × EuclideanSpace ℝ ι → ℝ := fun z => quadratic (A z.1) z.2
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere 0 1)
  have hc : Continuous F := by
    unfold F quadratic
    fun_prop
  have hp (z : X × EuclideanSpace ℝ ι) (hz : z ∈ S) : 0 < F z := by
    apply quadratic_pos (hpos z.1)
    have hn : ‖z.2‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz.2
    intro hzero
    simp only [hzero, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨a, ha, hlo⟩ := hS.exists_forall_le' hc.continuousOn hp
  obtain ⟨U, hU⟩ := (hS.image hc).isBounded.exists_norm_le
  let b : ℝ := |U| + 1
  have hb : 0 < b := add_pos_of_nonneg_of_pos (abs_nonneg U) zero_lt_one
  refine ⟨a, b, ha, hb, ?_⟩
  intro x ξ
  by_cases hz : ξ = 0
  · simp only [hz, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl, and_self]
  have hw : ‖NormedSpace.normalize ξ‖ = 1 := NormedSpace.norm_normalize hz
  have hm : (x, NormedSpace.normalize ξ) ∈ S := by
    exact ⟨mem_univ _, by simpa only [mem_sphere_iff_norm, sub_zero] using hw⟩
  have hlo' := hlo (x, NormedSpace.normalize ξ) hm
  have hup' : F (x, NormedSpace.normalize ξ) ≤ b := by
    have hu := hU (F (x, NormedSpace.normalize ξ)) ⟨(x, NormedSpace.normalize ξ), hm, rfl⟩
    have hu' : |F (x, NormedSpace.normalize ξ)| ≤ U := by simpa only [Real.norm_eq_abs] using hu
    exact
      (le_abs_self _).trans
        (hu'.trans ((le_abs_self U).trans (le_add_of_nonneg_right zero_le_one)))
  have hscale := quadratic_smul (A x) ‖ξ‖ (NormedSpace.normalize ξ)
  rw [NormedSpace.norm_smul_normalize] at hscale
  constructor
  · calc
      a * ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * a := mul_comm _ _
      _ ≤ ‖ξ‖ ^ 2 * F (x, NormedSpace.normalize ξ) :=
        mul_le_mul_of_nonneg_left hlo' (sq_nonneg _)
      _ = quadratic (A x) ξ := hscale.symm
  · calc
      quadratic (A x) ξ = ‖ξ‖ ^ 2 * F (x, NormedSpace.normalize ξ) := hscale
      _ ≤ ‖ξ‖ ^ 2 * b := mul_le_mul_of_nonneg_left hup' (sq_nonneg _)
      _ = b * ‖ξ‖ ^ 2 := mul_comm _ _

variable {E : Type*} [DecidableEq ι]

private def matrixSegment (A B : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  (1 - θ) • A + θ • B

private def inverseMatrixSegment (A B : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  (matrixSegment A B θ)⁻¹

private theorem continuousOn_inverseMatrixSegment {A B : Matrix ι ι ℝ} (hA : A.PosDef)
    (hB : B.PosDef) : ContinuousOn (inverseMatrixSegment A B) (Icc (0 : ℝ) 1) := by
  have hc : Continuous (matrixSegment A B) := by unfold matrixSegment; fun_prop
  intro θ hθ
  exact
    ((continuousAt_matrix_inv (matrixSegment A B θ)
            (by
              simpa only [matrixSegment, Ring.inverse_eq_inv'] using
                continuousAt_inv₀ (posDef_convex_segment hA hB hθ).det_pos.ne')).comp
        (f := matrixSegment A B) hc.continuousAt).continuousWithinAt

private theorem integral_quadratic {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (ξ : EuclideanSpace ℝ ι) :
    IntervalIntegrable (fun θ : ℝ => ∑ i, ∑ j, inverseMatrixSegment A B θ i j * ξ i * ξ j)
        volume 0 1 ∧
      (∫ θ in (0 : ℝ)..1, ∑ i, ∑ j, inverseMatrixSegment A B θ i j * ξ i * ξ j) =
        ∑ i, ∑ j, (∫ θ in (0 : ℝ)..1, inverseMatrixSegment A B θ i j) * ξ i * ξ j := by
  have hi (i j : ι) :
    IntervalIntegrable (fun θ : ℝ => inverseMatrixSegment A B θ i j) volume 0 1 := by
    have he : Continuous (fun D : Matrix ι ι ℝ => D i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact
      (he.comp_continuousOn (continuousOn_inverseMatrixSegment hA hB)).intervalIntegrable_of_Icc
        zero_le_one
  have hm (i j : ι) := ((hi i j).mul_const (ξ i)).mul_const (ξ j)
  have hr (i : ι) :
    IntervalIntegrable (fun θ : ℝ => ∑ j, inverseMatrixSegment A B θ i j * ξ i * ξ j) volume 0
      1 := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hm i j) using 1
    funext θ
    simp only [Finset.sum_apply]
  have hq :
    IntervalIntegrable (fun θ : ℝ => ∑ i, ∑ j, inverseMatrixSegment A B θ i j * ξ i * ξ j)
      volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hr i) using 1
    funext θ
    simp only [Finset.sum_apply]
  refine ⟨hq, ?_⟩
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (f := fun i θ =>
      ∑ j, inverseMatrixSegment A B θ i j * ξ i * ξ j) (fun i _ => hr i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (f := fun j θ =>
      inverseMatrixSegment A B θ i j * ξ i * ξ j) (fun j _ => hm i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]

/--
Uniform positive quadratic lower and upper bounds for the averaged-inverse coefficients of the
log-determinant finite-difference equation. The constants precede all endpoint, displacement and
vector choices; norms are Euclidean and the zero vector is included. -/
theorem exists_uniform_averagedInverse_ellipticity [NormedAddCommGroup E] (H : E → Matrix ι ι ℝ)
    {s : Set E} (hs : IsCompact s) (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ a b : ℝ,
      0 < a ∧
        0 < b ∧
          ∀ (d x : E),
            x ∈ s →
              x + d ∈ s →
                ∀ ξ : EuclideanSpace ℝ ι,
                  let A := segmentAveragedInverse (H x) (H (x + d))
                  a * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ ∧ A.toQuadraticForm' ξ ≤ b * ‖ξ‖ ^ 2 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let P : s → Matrix ι ι ℝ := fun x => H x
  have hP : Continuous P := hH.domRestrict
  let M : (s × s) × Icc (0 : ℝ) 1 → Matrix ι ι ℝ := fun z =>
    matrixSegment (P z.1.1) (P z.1.2) z.2
  have hM : Continuous M := by unfold M matrixSegment; fun_prop
  have hp (z : (s × s) × Icc (0 : ℝ) 1) : (M z).PosDef :=
    posDef_convex_segment (hpos z.1.1 z.1.1.property) (hpos z.1.2 z.1.2.property) z.2.property
  have hI : Continuous (fun z => (M z)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact
      (continuousAt_matrix_inv (M z)
            (by
              simpa only [Ring.inverse_eq_inv'] using
                continuousAt_inv₀ (hp z).det_pos.ne')).comp
        (f := M) hM.continuousAt
  obtain ⟨a, b, ha, hb, hbound⟩ :=
    exists_uniform_quadratic_bounds (fun z => (M z)⁻¹) hI (fun z => (hp z).inv)
  refine ⟨a, b, ha, hb, ?_⟩
  intro d x hx hxd ξ
  have hq := integral_quadratic (hpos x hx) (hpos (x + d) hxd) ξ
  have heq :
    (∫ θ in (0 : ℝ)..1, ∑ i, ∑ j, inverseMatrixSegment (H x) (H (x + d)) θ i j * ξ i * ξ j) =
      ∑ i, ∑ j, segmentAveragedInverse (H x) (H (x + d)) i j * ξ i * ξ j := by
    simpa only [inverseMatrixSegment, matrixSegment, segmentAveragedInverse] using hq.2
  have he (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) := hbound ((⟨x, hx⟩, ⟨x + d, hxd⟩), ⟨θ, hθ⟩) ξ
  have hlo :=
    intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => a * ‖ξ‖ ^ 2) volume 0 1) hq.1
      (fun θ hθ => (he θ hθ).1)
  have hup :=
    intervalIntegral.integral_mono_on zero_le_one hq.1
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => b * ‖ξ‖ ^ 2) volume 0 1)
      (fun θ hθ => (he θ hθ).2)
  rw [heq] at hlo hup
  have hqf (A : Matrix ι ι ℝ) :
      A.toQuadraticForm' ξ = ∑ i, ∑ j, A i j * ξ i * ξ j := by
    simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_left_comm, mul_assoc]
  dsimp only
  rw [hqf]
  exact ⟨by simpa using hlo, by simpa using hup⟩

end Ellipticity

end TauCeti
