/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Geometry.Convex.FullSimplex
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Integrals over the standard simplex

Let `Δᵖ⁺¹ = {x ∈ ℝᵖ⁺¹ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}` be the full-dimensional standard simplex. Slicing it
along its `j`-th coordinate writes an integral over `Δᵖ⁺¹` as an iterated integral over
`0 ≤ x_j ≤ 1 - ∑_{i ≠ j} xᵢ` and then over the remaining coordinates in `Δᵖ`. Combined with the
fundamental theorem of calculus on each slice, this computes the integral over `Δᵖ⁺¹` of a partial
derivative of a `C¹` function as the difference of its integrals over the face `∑ xᵢ = 1` and the
face `x_j = 0`. The face `∑ xᵢ = 1` read through the coordinates other than the `j`-th one, and
read through the face map `simplexMapAmbient (Fin.succAbove 0)`, differ by an affine symmetry of
`Δᵖ` permuting its vertices, so integrals over the two readings agree.

These are the scalar computations behind Stokes' theorem on the standard simplex.

## Main results

* `TauCeti.volume_real_fullSimplex_zero`: `Δ⁰` has real volume `1`.
* `TauCeti.setIntegral_fullSimplex_eq_iterated`: the integral over `Δᵖ⁺¹` of a function integrable
  on it, as an iterated integral along the `j`-th coordinate and then over `Δᵖ`.
* `ContDiffOn.integral_fderivWithin_fullSimplex`: the integral over `Δᵖ⁺¹` of the `j`-th partial
  derivative of a `C¹` function is the difference of its integrals over the face `∑ xᵢ = 1` and
  the face `xⱼ = 0`, both read through the coordinates other than the `j`-th one.
* `TauCeti.setIntegral_toLp_insertNth_eq`: the two readings of the face `∑ xᵢ = 1` give the same
  integral.
-/

public section

open MeasureTheory Set WithLp

namespace TauCeti

/-- The `0`-dimensional standard simplex is a single point of real volume `1`. -/
@[simp]
theorem volume_real_fullSimplex_zero : volume.real (fullSimplex 0) = 1 := by
  rw [fullSimplex_zero_eq_univ, volume_euclideanSpace_eq_dirac]
  simp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **Slicing the standard simplex along a coordinate.** The integral over `Δᵖ⁺¹` of a function
integrable on it is the iterated integral that first integrates along the `j`-th coordinate, over
`0 ≤ t ≤ 1 - ∑ k, y k`, and then over the remaining coordinates `y` in the coordinate simplex. -/
theorem setIntegral_fullSimplex_eq_iterated {p : ℕ}
    {D : EuclideanSpace ℝ (Fin (p + 1)) → F} (hD : IntegrableOn D (fullSimplex (p + 1)))
    (j : Fin (p + 1)) :
    ∫ x in fullSimplex (p + 1), D x = ∫ y in coordinateSimplex (Fin p),
      ∫ t in Icc 0 (1 - ∑ k, y k), D (toLp 2 (j.insertNth t y)) := by
  -- Transport the integral over `Δ` to the coordinate simplex of `Fin (p + 1) → ℝ`, then split off
  -- the `j`-th coordinate.
  set Δ := fullSimplex (p + 1)
  have hΔc : IsCompact Δ := isCompact_fullSimplex _
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) ↦ ℝ) j
  set Γ := e.symm.trans (MeasurableEquiv.toLp 2 (Fin (p + 1) → ℝ))
  have hΓ : MeasurePreserving Γ :=
    (PiLp.volume_preserving_toLp _).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (p + 1) ↦ ℝ) j).symm
  have hΓγ (q : ℝ × (Fin p → ℝ)) : Γ q = toLp 2 (j.insertNth q.1 q.2) := by
    simp [Γ, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  set S : Set (ℝ × (Fin p → ℝ)) := Γ ⁻¹' Δ
  have hmem (y : Fin p → ℝ) (t : ℝ) :
      (t, y) ∈ S ↔ y ∈ coordinateSimplex (Fin p) ∧ t ∈ Icc 0 (1 - ∑ k, y k) := by
    rw [mem_preimage, hΓγ]
    exact toLp_insertNth_mem_fullSimplex_iff j t y
  have hSm : MeasurableSet S := hΔc.isClosed.measurableSet.preimage Γ.measurable
  have hint : IntegrableOn (fun q ↦ D (Γ q)) S :=
    (hΓ.integrableOn_comp_preimage Γ.measurableEmbedding).2 hD
  have hslice (y : Fin p → ℝ) : ∫ t, S.indicator (fun q ↦ D (Γ q)) (t, y) =
      (coordinateSimplex (Fin p)).indicator
        (fun y ↦ ∫ t in Icc 0 (1 - ∑ k, y k), D (toLp 2 (j.insertNth t y))) y := by
    by_cases hy : y ∈ coordinateSimplex (Fin p)
    · rw [indicator_of_mem hy, ← integral_indicator measurableSet_Icc]
      congr 1 with t
      by_cases ht : t ∈ Icc 0 (1 - ∑ k, y k)
      · rw [indicator_of_mem ((hmem y t).2 ⟨hy, ht⟩), indicator_of_mem ht, hΓγ]
      · rw [indicator_of_notMem (fun h ↦ ht ((hmem y t).1 h).2), indicator_of_notMem ht]
    · rw [indicator_of_notMem hy]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t ↦
        indicator_of_notMem (fun h ↦ hy ((hmem y t).1 h).1) _)
  calc ∫ x in Δ, D x = ∫ q in S, D (Γ q) :=
        (hΓ.setIntegral_preimage_emb Γ.measurableEmbedding D Δ).symm
    _ = ∫ q, S.indicator (fun q ↦ D (Γ q)) q := (integral_indicator hSm).symm
    _ = ∫ y, ∫ t, S.indicator (fun q ↦ D (Γ q)) (t, y) :=
        integral_prod_symm _ ((integrable_indicator_iff hSm).2 hint)
    _ = _ := by
        simp_rw [hslice]
        exact integral_indicator (isClosed_coordinateSimplex _).measurableSet

/-- **The fundamental theorem of calculus along a coordinate of the standard simplex.** For a
function `g` that is `C¹` on `Δᵖ⁺¹`, the integral over `Δᵖ⁺¹` of its partial derivative in the
direction `e_j` is the integral over `Δᵖ` of the difference of its values at the points of the faces
`∑ xᵢ = 1` and `x_j = 0` whose other coordinates are given by `y ∈ Δᵖ`. -/
theorem _root_.ContDiffOn.integral_fderivWithin_fullSimplex {p : ℕ}
    {g : EuclideanSpace ℝ (Fin (p + 1)) → F} (hg : ContDiffOn ℝ 1 g (fullSimplex (p + 1)))
    (j : Fin (p + 1)) :
    ∫ x in fullSimplex (p + 1), fderivWithin ℝ g (fullSimplex (p + 1)) x
        (EuclideanSpace.single j 1) =
      ∫ y in fullSimplex p, (g (toLp 2 (j.insertNth (1 - ∑ k, y k) y.ofLp)) -
        g (toLp 2 (j.insertNth 0 y.ofLp))) := by
  -- Along the segment `t ↦ γ y t` through `Δᵖ⁺¹` in the direction `e_j`, the fundamental theorem
  -- of calculus computes the integral of the partial derivative (`hftc`); slicing `Δᵖ⁺¹` along the
  -- `j`-th coordinate assembles these segment integrals.
  set Δ := fullSimplex (p + 1)
  set D : EuclideanSpace ℝ (Fin (p + 1)) → F :=
    fun x ↦ fderivWithin ℝ g Δ x (EuclideanSpace.single j 1)
  set γ : (Fin p → ℝ) → ℝ → EuclideanSpace ℝ (Fin (p + 1)) := fun y t ↦ toLp 2 (j.insertNth t y)
  have hγ (y : Fin p → ℝ) (t : ℝ) : γ y t = γ y 0 + t • EuclideanSpace.single j 1 := by
    ext i
    cases i using j.succAboveCases <;> simp [γ, Fin.insertNth_apply_succAbove]
  have hDc : ContinuousOn D Δ :=
    (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single j 1)).continuous.comp_continuousOn
      (hg.continuousOn_fderivWithin (uniqueDiffOn_fullSimplex _) le_rfl)
  have hftc (y : Fin p → ℝ) (hy : y ∈ coordinateSimplex (Fin p)) :
      ∫ t in Icc 0 (1 - ∑ k, y k), D (γ y t) = g (γ y (1 - ∑ k, y k)) - g (γ y 0) := by
    have hL : 0 ≤ 1 - ∑ k, y k := sub_nonneg.2 ((mem_coordinateSimplex _ _).1 hy).2
    have hmaps : MapsTo (γ y) (Icc 0 (1 - ∑ k, y k)) Δ := fun t ht ↦
      (toLp_insertNth_mem_fullSimplex_iff j t y).2 ⟨hy, ht⟩
    have hγd (t : ℝ) : HasDerivAt (γ y) (EuclideanSpace.single j 1) t := by
      rw [show γ y = fun t ↦ γ y 0 + t • EuclideanSpace.single j 1 from funext (hγ y)]
      simpa using ((hasDerivAt_id t).smul_const
        (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin (p + 1)))).const_add (γ y 0)
    have hγc : Continuous (γ y) := continuous_iff_continuousAt.2 fun t ↦ (hγd t).continuousAt
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
      (hg.continuousOn.comp hγc.continuousOn hmaps) (fun t ht ↦ ?_) ?_
    · have ht' : t ∈ Icc 0 (1 - ∑ k, y k) := Ioo_subset_Icc_self ht
      have hgd := ((hg.differentiableOn one_ne_zero) _ (hmaps ht')).hasFDerivWithinAt
      exact (hgd.comp_hasDerivWithinAt t (hγd t).hasDerivWithinAt hmaps).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · exact (hDc.comp hγc.continuousOn hmaps).intervalIntegrable_of_Icc hL
  have hΔp : ofLp ⁻¹' coordinateSimplex (Fin p) = fullSimplex p := by
    ext y
    simp
  rw [setIntegral_fullSimplex_eq_iterated
      (hDc.integrableOn_compact (isCompact_fullSimplex _)) j,
    setIntegral_congr_fun (isClosed_coordinateSimplex _).measurableSet hftc,
    ← (PiLp.volume_preserving_ofLp (Fin p)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm.measurableEmbedding, hΔp]

omit [CompleteSpace F] in
/-- Reading the face of `Δᵖ⁺¹` opposite the origin through the coordinates other than the `j`-th
one, or through the last `p` coordinates, gives the same integral. -/
theorem setIntegral_toLp_insertNth_eq {p : ℕ} (j : Fin (p + 1))
    (G : EuclideanSpace ℝ (Fin (p + 1)) → F) :
    ∫ y in fullSimplex p, G (toLp 2 (j.insertNth (1 - ∑ k, y k) y.ofLp)) =
      ∫ y in fullSimplex p, G (simplexMapAmbient (Fin.succAbove 0) y) := by
  simp_rw [toLp_insertNth_eq_simplexMapAmbient]
  exact (simplexMapAmbient j.cycleRange.symm).setIntegral_comp_of_image_eq volume
    (isCompact_fullSimplex p).isClosed.measurableSet
    (isCompact_fullSimplex p).measure_lt_top.ne (image_simplexMapAmbient_perm _)
    fun z ↦ G (simplexMapAmbient (Fin.succAbove 0) z)


end TauCeti
