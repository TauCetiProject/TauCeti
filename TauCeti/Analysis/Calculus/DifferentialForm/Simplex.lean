/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.FullSimplex
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.LinearAlgebra.Alternating.AddConst
import TauCeti.MeasureTheory.Function.Jacobian.Affine

/-!
# Stokes' theorem for the standard simplex

Let `Δⁿ⁺¹ = {x ∈ ℝⁿ⁺¹ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}` be the full-dimensional standard simplex
(`TauCeti.fullSimplex`), with faces `δᵢ : Δⁿ → Δⁿ⁺¹` for `i = 0, …, n + 1`, the restrictions of
the affine maps `TauCeti.simplexMapAmbient i.succAbove`. For an `n`-form `ω` on `ℝⁿ⁺¹` that is
`C¹` within `Δⁿ⁺¹`,

`∫_{Δⁿ⁺¹} dω(e₀, …, eₙ) = ∑ᵢ (-1)ⁱ ∫_{Δⁿ} ω(δᵢ y)(Dδᵢ e₀, …, Dδᵢ eₙ₋₁) dy`

(`TauCeti.setIntegral_fullSimplex_extDerivWithin`), where `dω` is the exterior derivative within
`Δⁿ⁺¹` and both sides are Bochner integrals for the Lebesgue measure. Pulled back along a smooth
singular simplex, this is the computation behind Stokes' theorem for smooth singular chains,
`∫_c dω = ∫_{∂c} ω`. No regularity outside `Δⁿ⁺¹` is required.

## Main result

* `TauCeti.setIntegral_fullSimplex_extDerivWithin`: Stokes' theorem for the standard simplex.

## Implementation notes

Lee deduces Stokes' theorem for chains [Lee, Thm. 18.12]
from Stokes' theorem on manifolds with corners [Lee, Thm. 16.25]; here the simplex is treated
directly by iterated integrals. Writing `dω(e) = ∑ᵢ (-1)ⁱ ∂ᵢgᵢ` with
`gᵢ = ω(e₀, …, êᵢ, …, eₙ)`, Fubini along the `i`-th coordinate and the fundamental theorem of
calculus turn `∫ ∂ᵢgᵢ` into the integral of `gᵢ` over the slanted face `∑ xⱼ = 1` minus its
integral over the face `xᵢ = 0`, which is the face `δᵢ₊₁`. The slanted face is `δ₀`,
parametrized by dropping the `i`-th coordinate instead of the zeroth one; the two
parametrizations differ by a permutation of the vertices of `Δⁿ`, which preserves integrals over
`Δⁿ` (`MeasureTheory.setIntegral_comp_continuousAffineMap_of_image_eq`). Finally the edges
`eₖ₊₁ - e₀` of `δ₀` expand `ω` into `∑ᵢ (-1)ⁱ gᵢ` (`AlternatingMap.map_sub_const`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 16.25 and Theorem 18.12.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- The point of `ℝⁿ⁺¹` whose `i`-th coordinate is `t` and whose other coordinates are those of
`y`. -/
private def insertCoord (i : Fin (n + 1)) (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (i.insertNth t y.ofLp)

@[simp]
private theorem insertCoord_apply_self (i : Fin (n + 1)) (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    insertCoord i t y i = t := by
  simp [insertCoord]

@[simp]
private theorem insertCoord_apply_succAbove (i : Fin (n + 1)) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) : insertCoord i t y (i.succAbove j) = y j := by
  simp [insertCoord]

@[simp]
private theorem insertCoord_zero_apply_succ (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    insertCoord 0 t y j.succ = y j := by
  simp [insertCoord]

private theorem sum_insertCoord (i : Fin (n + 1)) (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ∑ j, insertCoord i t y j = t + ∑ j, y j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

private theorem insertCoord_mem_fullSimplex_iff {i : Fin (n + 1)} {t : ℝ}
    {y : EuclideanSpace ℝ (Fin n)} :
    insertCoord i t y ∈ fullSimplex (n + 1) ↔ y ∈ fullSimplex n ∧ t ∈ Icc 0 (1 - ∑ j, y j) := by
  simp only [mem_fullSimplex_iff, i.forall_iff_succAbove, insertCoord_apply_self,
    insertCoord_apply_succAbove, sum_insertCoord, mem_Icc]
  constructor
  · rintro ⟨⟨ht, hy⟩, hs⟩
    exact ⟨⟨hy, by linarith⟩, ht, by linarith⟩
  · rintro ⟨⟨hy, -⟩, ht, hs⟩
    exact ⟨⟨ht, hy⟩, by linarith⟩

/-- `insertCoord i` as a measurable equivalence `ℝ × ℝⁿ ≃ ℝⁿ⁺¹`. -/
private def insertCoordEquiv (i : Fin (n + 1)) :
    ℝ × EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i).symm.trans (MeasurableEquiv.toLp 2 _))

private theorem insertCoordEquiv_apply (i : Fin (n + 1)) (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    insertCoordEquiv i z = insertCoord i z.1 z.2 :=
  rfl

/-- Isolating one coordinate turns the Lebesgue measure of `ℝⁿ⁺¹` into a product measure. -/
private theorem measurePreserving_insertCoordEquiv (i : Fin (n + 1)) :
    MeasurePreserving (insertCoordEquiv i) (volume.prod volume) volume := by
  have h1 : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm) (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n + 1) → ℝ)) := by
    simpa [volume_pi] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ (volume : Measure ℝ)) i).symm
  exact ((PiLp.volume_preserving_toLp (Fin (n + 1))).comp h2).comp h1

/-- **Fubini along the `i`-th coordinate of the simplex.** -/
private theorem setIntegral_fullSimplex_eq_integral_insertCoord
    (i : Fin (n + 1)) {h : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hh : IntegrableOn h (fullSimplex (n + 1))) :
    ∫ x in fullSimplex (n + 1), h x =
      ∫ y in fullSimplex n, ∫ t in (0 : ℝ)..1 - ∑ j, y j, h (insertCoord i t y) := by
  have hmp := measurePreserving_insertCoordEquiv (n := n) i
  have hm := (isClosed_fullSimplex (n + 1)).measurableSet
  have hint : Integrable (fun z ↦ (fullSimplex (n + 1)).indicator h (insertCoordEquiv i z))
      (volume.prod volume) :=
    (hmp.integrable_comp_emb (insertCoordEquiv i).measurableEmbedding).2
      ((integrable_indicator_iff hm).2 hh)
  rw [← integral_indicator hm, ← hmp.integral_comp' ((fullSimplex (n + 1)).indicator h),
    integral_prod_symm _ hint,
    ← integral_indicator (isClosed_fullSimplex n).measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ fullSimplex n
  · have hb : (0 : ℝ) ≤ 1 - ∑ j, y j := sub_nonneg.2 (mem_fullSimplex_iff.1 hy).2
    rw [indicator_of_mem hy, intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    congr 1
    ext t
    simp only [insertCoordEquiv_apply, indicator, insertCoord_mem_fullSimplex_iff, hy, true_and]
  · have hy' : ∀ t, insertCoord i t y ∉ fullSimplex (n + 1) := fun t hmem ↦
      hy (insertCoord_mem_fullSimplex_iff.1 hmem).1
    simp [indicator_of_notMem hy, insertCoordEquiv_apply, hy']

/-- The fundamental theorem of calculus along the segment of the simplex in the direction of the
`i`-th coordinate, for a function that is `C¹` within the simplex. -/
private theorem integral_fderivWithin_insertCoord [CompleteSpace F]
    {g : EuclideanSpace ℝ (Fin (n + 1)) → F} (hg : ContDiffOn ℝ 1 g (fullSimplex (n + 1)))
    (i : Fin (n + 1)) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ fullSimplex n) :
    ∫ t in (0 : ℝ)..1 - ∑ j, y j,
        fderivWithin ℝ g (fullSimplex (n + 1)) (insertCoord i t y) (EuclideanSpace.single i 1) =
      g (insertCoord i (1 - ∑ j, y j) y) - g (insertCoord i 0 y) := by
  have hb : (0 : ℝ) ≤ 1 - ∑ j, y j := sub_nonneg.2 (mem_fullSimplex_iff.1 hy).2
  have hmaps :
      MapsTo (fun t ↦ insertCoord i t y) (Icc 0 (1 - ∑ j, y j)) (fullSimplex (n + 1)) :=
    fun t ht ↦ insertCoord_mem_fullSimplex_iff.2 ⟨hy, ht⟩
  -- The segment is the line through `insertCoord i 0 y` in the direction `eᵢ`.
  have hline : ∀ t, HasDerivAt (fun s ↦ insertCoord i s y) (EuclideanSpace.single i 1) t := by
    have heq : (fun s ↦ insertCoord i s y) =
        fun s ↦ insertCoord i 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      ext s j
      cases j using i.succAboveCases <;> simp
    intro t
    rw [heq]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
      (insertCoord i 0 y)
  have hderiv : ∀ t ∈ Icc 0 (1 - ∑ j, y j), HasDerivWithinAt (fun s ↦ g (insertCoord i s y))
      (fderivWithin ℝ g (fullSimplex (n + 1)) (insertCoord i t y) (EuclideanSpace.single i 1))
      (Icc 0 (1 - ∑ j, y j)) t := fun t ht ↦
    ((hg.differentiableOn one_ne_zero _ (hmaps ht)).hasFDerivWithinAt).comp_hasDerivWithinAt t
      (hline t).hasDerivWithinAt hmaps
  have hcont : ContinuousOn (fun t ↦ fderivWithin ℝ g (fullSimplex (n + 1)) (insertCoord i t y)
      (EuclideanSpace.single i 1)) (Icc 0 (1 - ∑ j, y j)) :=
    ((hg.continuousOn_fderivWithin (uniqueDiffOn_fullSimplex _) le_rfl).comp
      (continuous_iff_continuousAt.2 fun t ↦ (hline t).continuousAt).continuousOn
        hmaps).clm_apply continuousOn_const
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
    (fun t ht ↦ (hderiv t ht).continuousWithinAt)
    (fun t ht ↦ (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) ?_
  exact (hcont.mono (uIcc_of_le hb).subset).intervalIntegrable

/-- The face `δᵢ₊₁` is the bottom face `xᵢ = 0` of the segments in the `i`-th direction. -/
private theorem simplexMapAmbient_succ_succAbove_eq_insertCoord (i : Fin (n + 1))
    (y : EuclideanSpace ℝ (Fin n)) :
    simplexMapAmbient i.succ.succAbove y = insertCoord i 0 y :=
  simplexMapAmbient_succ_succAbove_eq i y

/-- The slanted face `∑ xⱼ = 1` of the segments in the `i`-th direction is the face `δ₀`, up to
the permutation `i.cycleRange.symm` of the vertices of `Δⁿ`: the two parametrizations drop the
`i`-th coordinate and the zeroth one, respectively. -/
private theorem simplexMapAmbient_succ_cycleRange_symm (i : Fin (n + 1))
    (y : EuclideanSpace ℝ (Fin n)) :
    simplexMapAmbient Fin.succ
        (simplexMapAmbient (i.cycleRange.symm : Fin (n + 1) → Fin (n + 1)) y) =
      insertCoord i (1 - ∑ j, y j) y := by
  -- The permuted point consists of the coordinates of `insertCoord i (1 - ∑ j, y j) y` but the
  -- zeroth one.
  have hT : ∀ j, simplexMapAmbient (i.cycleRange.symm : Fin (n + 1) → Fin (n + 1)) y j =
      insertCoord i (1 - ∑ j, y j) y j.succ := fun j ↦ by
    rw [simplexMapAmbient_apply_of_injective i.cycleRange.symm.injective _
      (k := i.cycleRange j.succ) (by simp)]
    exact Fin.cons_apply_cycleRange _ _ _ _
  rw [simplexMapAmbient_succ_eq]
  ext j
  cases j using Fin.cases with
  | zero =>
    have hs := sum_insertCoord i (1 - ∑ j, y j) y
    rw [Fin.sum_univ_succ] at hs
    simp only [Fin.cons_zero, hT]
    linarith
  | succ j => simp [hT]

/-- The full-dimensional simplex has positive volume. -/
private theorem volume_fullSimplex_ne_zero (n : ℕ) : volume (fullSimplex n) ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior _ (nonempty_interior_fullSimplex n)).ne'

/-- The derivative of a `C¹` function along `eᵢ` integrates over `Δⁿ⁺¹` to its integral over
the slanted face `δ₀`, minus its integral over the face `δᵢ₊₁`. -/
private theorem setIntegral_fullSimplex_fderivWithin [CompleteSpace F]
    {g : EuclideanSpace ℝ (Fin (n + 1)) → F} (hg : ContDiffOn ℝ 1 g (fullSimplex (n + 1)))
    (i : Fin (n + 1)) :
    ∫ x in fullSimplex (n + 1), fderivWithin ℝ g (fullSimplex (n + 1)) x
        (EuclideanSpace.single i 1) =
      (∫ y in fullSimplex n, g (simplexMapAmbient Fin.succ y)) -
        ∫ y in fullSimplex n, g (simplexMapAmbient i.succ.succAbove y) := by
  have hm := (isClosed_fullSimplex n).measurableSet
  have hgc : ∀ f : Fin (n + 1) → Fin (n + 2),
      IntegrableOn (fun y ↦ g (simplexMapAmbient f y)) (fullSimplex n) := fun f ↦
    (hg.continuousOn.comp (simplexMapAmbient f).continuous.continuousOn
      (mapsTo_simplexMapAmbient f)).integrableOn_compact (isCompact_fullSimplex n)
  have hc : ContinuousOn (fun x ↦ fderivWithin ℝ g (fullSimplex (n + 1)) x
      (EuclideanSpace.single i 1)) (fullSimplex (n + 1)) :=
    (hg.continuousOn_fderivWithin (uniqueDiffOn_fullSimplex _) le_rfl).clm_apply
      continuousOn_const
  -- The slanted face, parametrized by dropping the `i`-th coordinate, is `δ₀` up to a vertex
  -- permutation of `Δⁿ`.
  have htop : ∫ y in fullSimplex n, g (insertCoord i (1 - ∑ j, y j) y) =
      ∫ y in fullSimplex n, g (simplexMapAmbient Fin.succ y) := by
    simp_rw [← simplexMapAmbient_succ_cycleRange_symm]
    exact setIntegral_comp_continuousAffineMap_of_image_eq volume hm
      (volume_fullSimplex_ne_zero n) (isCompact_fullSimplex n).measure_lt_top.ne _
      (simplexMapAmbient_image_fullSimplex i.cycleRange.symm)
      fun y ↦ g (simplexMapAmbient Fin.succ y)
  rw [← htop, setIntegral_fullSimplex_eq_integral_insertCoord i
    (hc.integrableOn_compact (isCompact_fullSimplex _))]
  simp_rw [simplexMapAmbient_succ_succAbove_eq_insertCoord]
  rw [← integral_sub ?_ ?_]
  · exact setIntegral_congr_fun hm fun y hy ↦ integral_fderivWithin_insertCoord hg i hy
  · simp_rw [← simplexMapAmbient_succ_cycleRange_symm]
    exact (hg.continuousOn.comp ((simplexMapAmbient _).continuous.comp
      (simplexMapAmbient _).continuous).continuousOn
      ((mapsTo_simplexMapAmbient _).comp (mapsTo_simplexMapAmbient _))).integrableOn_compact
        (isCompact_fullSimplex n)
  · simp_rw [← simplexMapAmbient_succ_succAbove_eq_insertCoord]
    exact hgc _

/-- Along the edges `eₖ₊₁ - e₀` of the face `δ₀`, an `n`-form on `ℝⁿ⁺¹` is the alternating sum of
its coordinate coefficients. -/
private theorem apply_simplexMapAmbient_succ_contLinear
    (ω₀ : EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] F) :
    ω₀ (fun k ↦ (simplexMapAmbient Fin.succ).contLinear (EuclideanSpace.single k 1)) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
        ω₀ (i.removeNth fun j ↦ EuclideanSpace.single j 1) := by
  simp_rw [simplexMapAmbient_succ_contLinear_single]
  set e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun j ↦ EuclideanSpace.single j 1
  have h := ω₀.toAlternatingMap.map_sub_const (Fin.tail e) (e 0)
  rw [Fin.cons_self_tail] at h
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp

/-- Along the face `δᵢ₊₁`, an `n`-form on `ℝⁿ⁺¹` is its coordinate coefficient omitting `eᵢ`. -/
private theorem apply_simplexMapAmbient_succ_succAbove_contLinear (i : Fin (n + 1))
    (ω₀ : EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] F) :
    ω₀ (fun k ↦ (simplexMapAmbient i.succ.succAbove).contLinear (EuclideanSpace.single k 1)) =
      ω₀ (i.removeNth fun j ↦ EuclideanSpace.single j 1) := by
  simp_rw [simplexMapAmbient_succ_succAbove_contLinear_single]
  -- `i.removeNth v` is by definition `fun k ↦ v (i.succAbove k)`.
  rfl

/-- **Stokes' theorem for the standard simplex.** For an `n`-form `ω` on `ℝⁿ⁺¹` that is `C¹`
within the full-dimensional simplex `Δⁿ⁺¹`, the integral over `Δⁿ⁺¹` of its exterior derivative
within `Δⁿ⁺¹`, evaluated on the standard basis, is the alternating sum over the faces
`δᵢ = simplexMapAmbient i.succAbove` of the integrals over `Δⁿ` of the pullback of `ω` along
`δᵢ`, evaluated on the standard basis. -/
theorem setIntegral_fullSimplex_extDerivWithin [CompleteSpace F]
    {ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (fullSimplex (n + 1))) :
    ∫ x in fullSimplex (n + 1),
        extDerivWithin ω (fullSimplex (n + 1)) x (fun j ↦ EuclideanSpace.single j 1) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • ∫ y in fullSimplex n,
        ω (simplexMapAmbient i.succAbove y)
          (fun k ↦ (simplexMapAmbient i.succAbove).contLinear (EuclideanSpace.single k 1)) := by
  -- The coordinate coefficients `gᵢ = ω(e₀, …, êᵢ, …, eₙ)` of `ω`.
  set g : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → F :=
    fun i x ↦ ω x (i.removeNth fun j ↦ EuclideanSpace.single j 1)
  have hg : ∀ i, ContDiffOn ℝ 1 (g i) (fullSimplex (n + 1)) := fun i ↦
    (ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) F
      (i.removeNth fun j ↦ EuclideanSpace.single j 1)).contDiff.comp_contDiffOn hω
  have hU := uniqueDiffOn_fullSimplex (n + 1)
  -- `dω(e) = ∑ᵢ (-1)ⁱ ∂ᵢ gᵢ` on the simplex.
  have hd : ∀ x ∈ fullSimplex (n + 1),
      extDerivWithin ω (fullSimplex (n + 1)) x (fun j ↦ EuclideanSpace.single j 1) =
        ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
          fderivWithin ℝ (g i) (fullSimplex (n + 1)) x (EuclideanSpace.single i 1) :=
    fun x hx ↦ by
    rw [extDerivWithin_apply (hω.differentiableOn one_ne_zero x hx) (hU x hx)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    simp [g]
  have hdi : ∀ i, IntegrableOn (fun x ↦ fderivWithin ℝ (g i) (fullSimplex (n + 1)) x
      (EuclideanSpace.single i 1)) (fullSimplex (n + 1)) := fun i ↦
    ((hg i).continuousOn_fderivWithin hU le_rfl).clm_apply continuousOn_const
      |>.integrableOn_compact (isCompact_fullSimplex _)
  have hgi : ∀ i, IntegrableOn (fun y ↦ g i (simplexMapAmbient Fin.succ y)) (fullSimplex n) :=
    fun i ↦ ((hg i).continuousOn.comp (simplexMapAmbient _).continuous.continuousOn
      (mapsTo_simplexMapAmbient _)).integrableOn_compact (isCompact_fullSimplex n)
  -- Integrate `∑ᵢ (-1)ⁱ ∂ᵢ gᵢ` term by term, and split off the face `δ₀` on the right.
  rw [setIntegral_congr_fun (isClosed_fullSimplex _).measurableSet hd, integral_finsetSum _
    (f := fun (i : Fin (n + 1)) x ↦ (-1 : ℝ) ^ (i : ℕ) •
      fderivWithin ℝ (g i) (fullSimplex (n + 1)) x (EuclideanSpace.single i 1))
    fun i _ ↦ (hdi i).smul ((-1 : ℝ) ^ (i : ℕ)), Fin.sum_univ_succ (n := n + 1)]
  simp only [Fin.succAbove_zero, apply_simplexMapAmbient_succ_contLinear,
    apply_simplexMapAmbient_succ_succAbove_contLinear]
  simp_rw [integral_smul, setIntegral_fullSimplex_fderivWithin (hg _)]
  rw [integral_finsetSum _
      (f := fun (i : Fin (n + 1)) y ↦ (-1 : ℝ) ^ (i : ℕ) • g i (simplexMapAmbient Fin.succ y))
      fun i _ ↦ (hgi i).smul ((-1 : ℝ) ^ (i : ℕ))]
  simp only [integral_smul, smul_sub, Finset.sum_sub_distrib, Fin.val_zero, pow_zero, one_smul,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg, g]

end TauCeti
