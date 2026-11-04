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
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Matrix.PosDef

/-!
# Hölder bounds and ellipticity for segment-averaged inverses

The coefficients of a log-determinant difference equation are the integral of the inverse of
the segment joining two Hessians. Continuous positive definite fields on compact sets give uniform
ellipticity bounds. If the field also has Hölder entries, the averaged coefficients of every
admissible translation have a common entrywise Hölder bound.

The arguments follow the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

noncomputable section

namespace TauCeti

open Set Metric MeasureTheory Matrix
open scoped NNReal ENNReal Matrix.Norms.Elementwise ComplexOrder

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
      rw [← Matrix.sub_apply, hi]
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

/--
If a field `P` of invertible matrices has `(C, r)`-Hölder entries and inverse entries bounded by
`L`, every entry of
`P⁻¹` is `(n² L² C, r)`-Hölder; the constant is fixed before the entries and the points. -/
private theorem holderWith_inverse_entries {X : Type*} [PseudoMetricSpace X] (P : X → Matrix ι ι ℝ)
    (C r L : ℝ≥0) (hP : ∀ x, IsUnit (P x)) (hb : ∀ x i j, |(P x)⁻¹ i j| ≤ L)
    (hc : ∀ i j, HolderWith C r (fun x => P x i j)) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r (fun x => (P x)⁻¹ i j) := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le ?_)
  intro x _ y _
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
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le ?_)
  intro x _ y _
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
  funext x
  simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]

end AveragedInverse

section SegmentInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A point of the segment between positive definite matrices is positive definite. -/
private theorem posDef_convex_segment {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ((1 - t) • A + t • B).PosDef :=
  convex_setOfPred_posDef hA hB (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

private theorem continuousAt_segment_inverse {X : Type*} [TopologicalSpace X]
    {P Q : X → Matrix ι ι ℝ} {t : X → ℝ} {x : X}
    (hP : ContinuousAt P x) (hQ : ContinuousAt Q x) (ht : ContinuousAt t x)
    (hp : (P x).PosDef) (hq : (Q x).PosDef) (hx : t x ∈ Icc 0 1) :
    ContinuousAt (fun y => ((1 - t y) • P y + t y • Q y)⁻¹) x := by
  have hc : ContinuousAt (fun y => (1 - t y) • P y + t y • Q y) x := by fun_prop
  exact hc.matrix_inv (posDef_convex_segment hp hq hx).det_pos.ne'

private theorem intervalIntegrable_segment_inverse_apply {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (i j : ι) :
    IntervalIntegrable (fun t : ℝ => ((1 - t) • A + t • B)⁻¹ i j) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one (fun t ht => ?_)
  have hc := continuousAt_segment_inverse (P := fun _ : ℝ => A) (Q := fun _ : ℝ => B)
    (t := id) continuousAt_const continuousAt_const continuousAt_id hA hB ht
  exact ((continuous_apply_apply i j).continuousAt.comp hc).continuousWithinAt

variable {X : Type*} [PseudoMetricSpace X]

/-- Uniform entry bounds on the inverse segments transfer the Hölder modulus of the endpoints
to the entries of the averaged inverse. -/
private theorem holderWith_averaged_inverse_entries (P Q : X → Matrix ι ι ℝ) (C r L : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j))
    (hp : ∀ x, (P x).PosDef) (hq : ∀ x, (Q x).PosDef)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x i j, |((1 - t) • P x + t • Q x)⁻¹ i j| ≤ L) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
      (fun x => ∫ t in (0 : ℝ)..1, ((1 - t) • P x + t • Q x)⁻¹ i j) := by
  apply holderWith_unit_interval_mean _ _ _
    (fun x => intervalIntegrable_segment_inverse_apply (hp x) (hq x) i j)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht
  exact holderWith_inverse_entries (fun x => (1 - t) • P x + t • Q x) C r L
    (fun x => (posDef_convex_segment (hp x) (hq x) ht').isUnit) (hb t ht')
    (holderWith_convex_matrix_entries P Q C r hP hQ ht') i j

end SegmentInverse

section CompactPositiveFields

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]

private theorem continuous_pair_segment_inverse {s : Set X} (H : X → Matrix ι ι ℝ)
    (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    Continuous (fun z : (s × s) × Icc (0 : ℝ) 1 =>
      ((1 - (z.2 : ℝ)) • H z.1.1 + (z.2 : ℝ) • H z.1.2)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact continuousAt_segment_inverse
    (hH.domRestrict.comp (continuous_fst.comp continuous_fst)).continuousAt
    (hH.domRestrict.comp (continuous_snd.comp continuous_fst)).continuousAt
    (continuous_subtype_val.comp continuous_snd).continuousAt
    (hpos z.1.1 z.1.1.property) (hpos z.1.2 z.1.2.property) z.2.property

private theorem exists_pair_inverse_cap (H : X → Matrix ι ι ℝ) {s : Set X} (hs : IsCompact s)
    (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ L : ℝ≥0,
      0 < L ∧
        ∀ x ∈ s, ∀ y ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, |((1 - t) • H x + t • H y)⁻¹ i j| ≤ L := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hcompact := isCompact_range (continuous_pair_segment_inverse H hH hpos)
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  let L : ℝ≥0 := (max R 0 + 1).toNNReal
  have hL : (L : ℝ) = max R 0 + 1 := Real.coe_toNNReal _ (by positivity)
  refine ⟨L, by exact_mod_cast (show (0 : ℝ) < (L : ℝ) by rw [hL]; positivity), ?_⟩
  intro x hx y hy t ht i j
  have hcap := hR _ ⟨((⟨x, hx⟩, ⟨y, hy⟩), ⟨t, ht⟩), rfl⟩
  rw [← Real.norm_eq_abs, hL]
  exact Matrix.norm_apply_le_norm _ |>.trans (hcap.trans (by linarith [le_max_left R 0]))

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

/-- One entry bound works for all endpoint pairs in `s`. For every displacement preserving both
endpoints in `s`, the translated averaged field has entrywise Hölder constant `(card ι)^2 L^2 C`. -/
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
  have hB (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : a) (k l : ι) :
    |((1 - θ) • P x + θ • Q x)⁻¹ k l| ≤ L :=
    hcap x (ha x.property) (x + d) (hshift x x.property) θ hθ k l
  exact
    HolderWith.restrict_iff.mp (holderWith_averaged_inverse_entries P Q C r L hP hQ
      (fun x => hpos x (ha x.property)) (fun x => hpos (x + d) (hshift x x.property)) hB i j)

end HolderTranslations

section Ellipticity

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- Uniform lower and upper quadratic bounds for a compact continuous positive definite family.
The constants precede both the family parameter and the vector. -/
private theorem exists_uniform_quadratic_bounds [TopologicalSpace X] [CompactSpace X]
    (A : X → Matrix ι ι ℝ) (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) :
    ∃ a b : ℝ,
      0 < a ∧
        0 < b ∧
          ∀ x (ξ : EuclideanSpace ℝ ι),
            a * ‖ξ‖ ^ 2 ≤ (A x).toQuadraticForm' ξ ∧ (A x).toQuadraticForm' ξ ≤ b * ‖ξ‖ ^ 2 := by
  let S : Set (X × EuclideanSpace ℝ ι) := univ ×ˢ sphere 0 1
  let F : X × EuclideanSpace ℝ ι → ℝ := fun z => (A z.1).toQuadraticForm' z.2
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere 0 1)
  have hc : Continuous F := by
    simp only [F, Matrix.toQuadraticForm'_apply]
    fun_prop
  have hp (z : X × EuclideanSpace ℝ ι) (hz : z ∈ S) : 0 < F z := by
    simp only [F, Matrix.toQuadraticForm'_apply]
    apply (hpos z.1).dotProduct_mulVec_pos
    have hn : ‖z.2‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz.2
    intro hzero
    have hz : z.2 = 0 := by
      ext i
      exact congrFun hzero i
    simp only [hz, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨a, ha, hlo⟩ := hS.exists_forall_le' hc.continuousOn hp
  obtain ⟨U, hU⟩ := (hS.image hc).isBounded.exists_norm_le
  let b : ℝ := |U| + 1
  have hb : 0 < b := add_pos_of_nonneg_of_pos (abs_nonneg U) zero_lt_one
  refine ⟨a, b, ha, hb, ?_⟩
  intro x ξ
  by_cases hz : ξ = 0
  · simp [hz]
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
  have hscale := (A x).toQuadraticForm'.map_smul ‖ξ‖ (NormedSpace.normalize ξ).ofLp
  rw [← WithLp.ofLp_smul, NormedSpace.norm_smul_normalize, smul_eq_mul, ← pow_two] at hscale
  constructor
  · calc
      a * ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * a := mul_comm _ _
      _ ≤ ‖ξ‖ ^ 2 * F (x, NormedSpace.normalize ξ) :=
        mul_le_mul_of_nonneg_left hlo' (sq_nonneg _)
      _ = (A x).toQuadraticForm' ξ := hscale.symm
  · calc
      (A x).toQuadraticForm' ξ = ‖ξ‖ ^ 2 * F (x, NormedSpace.normalize ξ) := hscale
      _ ≤ ‖ξ‖ ^ 2 * b := mul_le_mul_of_nonneg_left hup' (sq_nonneg _)
      _ = b * ‖ξ‖ ^ 2 := mul_comm _ _

private theorem integral_quadratic {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (ξ : EuclideanSpace ℝ ι) :
    IntervalIntegrable (fun t : ℝ => (((1 - t) • A + t • B)⁻¹).toQuadraticForm' ξ)
        volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, (((1 - t) • A + t • B)⁻¹).toQuadraticForm' ξ) =
        (segmentAveragedInverse A B).toQuadraticForm' ξ := by
  simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hi := intervalIntegrable_segment_inverse_apply hA hB
  have hm (i j : ι) := ((hi i j).mul_const (ξ j)).const_mul (ξ i)
  have hr (i : ι) :
      IntervalIntegrable (fun t : ℝ => ∑ j, ξ i * (((1 - t) • A + t • B)⁻¹ i j * ξ j))
        volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hm i j) using 1
    funext t
    simp only [Finset.sum_apply]
  refine ⟨?_, ?_⟩
  · convert IntervalIntegrable.sum Finset.univ (fun i _ => hr i) using 1
    funext t
    simp only [Finset.sum_apply]
  · rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun i t => ∑ j, ξ i * (((1 - t) • A + t • B)⁻¹ i j * ξ j)) (fun i _ => hr i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun j t => ξ i * (((1 - t) • A + t • B)⁻¹ i j * ξ j)) (fun j _ => hm i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
      segmentAveragedInverse_apply]

/-- A continuous positive definite matrix field on a compact set gives uniform quadratic lower
and upper bounds for the segment-averaged inverse of all endpoint pairs. -/
theorem exists_uniform_averagedInverse_ellipticity [TopologicalSpace X] (H : X → Matrix ι ι ℝ)
    {s : Set X} (hs : IsCompact s) (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ ξ : EuclideanSpace ℝ ι,
      a * ‖ξ‖ ^ 2 ≤ (segmentAveragedInverse (H x) (H y)).toQuadraticForm' ξ ∧
        (segmentAveragedInverse (H x) (H y)).toQuadraticForm' ξ ≤ b * ‖ξ‖ ^ 2 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hposSegment (z : (s × s) × Icc (0 : ℝ) 1) :
      (((1 - (z.2 : ℝ)) • H z.1.1 + (z.2 : ℝ) • H z.1.2)⁻¹).PosDef :=
    (posDef_convex_segment
      (hpos z.1.1 z.1.1.property) (hpos z.1.2 z.1.2.property) z.2.property).inv
  obtain ⟨a, b, ha, hb, hbound⟩ := exists_uniform_quadratic_bounds _
    (continuous_pair_segment_inverse H hH hpos) hposSegment
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx y hy ξ
  obtain ⟨hi, heq⟩ := integral_quadratic (hpos x hx) (hpos y hy) ξ
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hbound ((⟨x, hx⟩, ⟨y, hy⟩), ⟨t, ht⟩) ξ
  have hlo := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hi
    (fun t ht => (he t ht).1)
  have hup := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const
    (fun t ht => (he t ht).2)
  rw [heq] at hlo hup
  exact ⟨by simpa using hlo, by simpa using hup⟩

end Ellipticity

end TauCeti
