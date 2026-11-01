/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Geometry.Convex.FullSimplex
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.LinearAlgebra.Alternating.Translate
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Stokes' theorem on the standard simplex

Let `Δᵖ⁺¹ = {x ∈ ℝᵖ⁺¹ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}` be the full-dimensional standard simplex and
`Fᵢ = simplexMapAmbient i.succAbove : ℝᵖ → ℝᵖ⁺¹` its `i`-th face map, the affine map sending the
vertices of `Δᵖ` to the vertices of `Δᵖ⁺¹` other than the `i`-th one. For a `p`-form `ω` with values
in a complete space that is `C¹` on `Δᵖ⁺¹`, with forms evaluated on the standard basis,

`∫_{Δᵖ⁺¹} dω = ∑ᵢ (-1)ⁱ ∫_{Δᵖ} Fᵢ^* ω`

(`ContDiffOn.integral_extDerivWithin_fullSimplex`). The exterior derivative is taken within
`Δᵖ⁺¹`, so no regularity outside the closed simplex is needed. This is Stokes' theorem for the
standard simplex with its boundary chain `∑ᵢ (-1)ⁱ Fᵢ`; pulling forms back along a smooth singular
simplex turns it into Stokes' theorem for smooth singular chains.

The proof is direct and does not view the simplex as a manifold with corners. The exterior
derivative is the alternating sum of the coordinate derivatives of the coefficients
`ω(e₀, …, êⱼ, …, eₚ)`. Integrating the `j`-th coordinate derivative first along the `j`-th
coordinate (`ContDiffOn.integral_fderivWithin_fullSimplex`) leaves the difference of the integrals
over the face `xⱼ = 0`, which is the face `F_{j+1}`, and over the face `∑ xᵢ = 1`, each read through
the remaining coordinates. Reading the face `∑ xᵢ = 1` through the coordinates other than the `j`-th
one or through the last `p` ones, as `F₀` does, differs by an affine symmetry of `Δᵖ` that permutes
its vertices, so the integrals agree (`ContinuousAffineMap.setIntegral_comp_of_image_eq`). Finally
`F₀` carries the standard basis to the edge vectors `e_{k+1} - e₀`, on which `ω` is the alternating
sum of its coefficients (`AlternatingMap.map_succ_sub_zero`).

## Main results

* `ContDiffOn.integral_fderivWithin_fullSimplex`: the integral over `Δᵖ⁺¹` of the `j`-th partial
  derivative of a `C¹` function is the difference of its integrals over the face `∑ xᵢ = 1` and
  the face `xⱼ = 0`, both read through the coordinates other than the `j`-th one.
* `ContDiffOn.integral_extDerivWithin_fullSimplex`: Stokes' theorem on `Δᵖ⁺¹`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.12 (Stokes's
  theorem for chains), with its convention for the standard simplex and its faces.
-/

public section

open MeasureTheory Set WithLp

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **Slicing the standard simplex along a coordinate.** The integral over `Δᵖ⁺¹` of a function
continuous on it is the iterated integral that first integrates along the `j`-th coordinate, over
`0 ≤ t ≤ 1 - ∑ k, y k`, and then over the remaining coordinates `y` in the coordinate simplex. -/
private theorem setIntegral_fullSimplex_eq_iterated {p : ℕ}
    {D : EuclideanSpace ℝ (Fin (p + 1)) → F} (hD : ContinuousOn D (fullSimplex (p + 1)))
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
    (hΓ.integrableOn_comp_preimage Γ.measurableEmbedding).2 (hD.integrableOn_compact hΔc)
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
  rw [setIntegral_fullSimplex_eq_iterated hDc j,
    setIntegral_congr_fun (isClosed_coordinateSimplex _).measurableSet hftc,
    ← (PiLp.volume_preserving_ofLp (Fin p)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm.measurableEmbedding, hΔp]

omit [CompleteSpace F] in
/-- Reading the face of `Δᵖ⁺¹` opposite the origin through the coordinates other than the `j`-th
one, or through the last `p` coordinates, gives the same integral. -/
private theorem setIntegral_toLp_insertNth_eq {p : ℕ} (j : Fin (p + 1))
    (G : EuclideanSpace ℝ (Fin (p + 1)) → F) :
    ∫ y in fullSimplex p, G (toLp 2 (j.insertNth (1 - ∑ k, y k) y.ofLp)) =
      ∫ y in fullSimplex p, G (simplexMapAmbient (Fin.succAbove 0) y) := by
  simp_rw [toLp_insertNth_eq_simplexMapAmbient]
  exact (simplexMapAmbient j.cycleRange.symm).setIntegral_comp_of_image_eq volume
    (isCompact_fullSimplex p).isClosed.measurableSet
    (isCompact_fullSimplex p).measure_lt_top.ne (image_simplexMapAmbient_perm _)
    fun z ↦ G (simplexMapAmbient (Fin.succAbove 0) z)

/-- **Stokes' theorem on the standard simplex.** For a `p`-form `ω` that is `C¹` on the standard
simplex `Δᵖ⁺¹`, the integral of its exterior derivative over `Δᵖ⁺¹` is the alternating sum over
`i` of the integrals over `Δᵖ` of its pullbacks along the face maps `simplexMapAmbient i.succAbove`,
all forms being evaluated on the standard basis. -/
theorem _root_.ContDiffOn.integral_extDerivWithin_fullSimplex {p : ℕ}
    {ω : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (fullSimplex (p + 1))) :
    ∫ x in fullSimplex (p + 1), extDerivWithin ω (fullSimplex (p + 1)) x
        (fun i ↦ EuclideanSpace.single i 1) =
      ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) • ∫ y in fullSimplex p,
        ω (simplexMapAmbient i.succAbove y)
          (fun k ↦ (simplexMapAmbient i.succAbove).contLinear (EuclideanSpace.single k 1)) := by
  set Δ := fullSimplex (p + 1)
  set e : Fin (p + 1) → EuclideanSpace ℝ (Fin (p + 1)) := fun i ↦ EuclideanSpace.single i 1
  set g : Fin (p + 1) → EuclideanSpace ℝ (Fin (p + 1)) → F := fun j x ↦ ω x (j.removeNth e)
  have hg (j : Fin (p + 1)) : ContDiffOn ℝ 1 (g j) Δ :=
    (ContinuousAlternatingMap.apply ℝ _ F (j.removeNth e)).contDiff.comp_contDiffOn hω
  have hΔu : UniqueDiffOn ℝ Δ := uniqueDiffOn_fullSimplex _
  -- Integrability of the integrands below: all are continuous on compact simplices.
  have hint (j : Fin (p + 1)) {A : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin (p + 1))}
      (hA : Continuous A) (hAm : MapsTo A (fullSimplex p) Δ) :
      IntegrableOn (fun y ↦ g j (A y)) (fullSimplex p) :=
    ((hg j).continuousOn.comp hA.continuousOn hAm).integrableOn_compact (isCompact_fullSimplex p)
  have htop (j : Fin (p + 1)) :
      IntegrableOn (fun y ↦ g j (toLp 2 (j.insertNth (1 - ∑ k, y k) y.ofLp)))
        (fullSimplex p) := by
    simp_rw [toLp_insertNth_eq_simplexMapAmbient]
    exact hint j ((simplexMapAmbient _).continuous.comp (simplexMapAmbient _).continuous)
      ((mapsTo_simplexMapAmbient _).comp (mapsTo_simplexMapAmbient _))
  have hbot (j : Fin (p + 1)) :
      IntegrableOn (fun y ↦ g j (toLp 2 (j.insertNth 0 y.ofLp))) (fullSimplex p) := by
    simp_rw [← simplexMapAmbient_succAbove_succ]
    exact hint j (simplexMapAmbient _).continuous (mapsTo_simplexMapAmbient _)
  have hzero (j : Fin (p + 1)) :
      IntegrableOn (fun y ↦ g j (simplexMapAmbient (Fin.succAbove 0) y)) (fullSimplex p) :=
    hint j (simplexMapAmbient _).continuous (mapsTo_simplexMapAmbient _)
  have hD (j : Fin (p + 1)) : IntegrableOn (fun x ↦ fderivWithin ℝ (g j) Δ x (e j)) Δ :=
    ((ContinuousLinearMap.apply ℝ F (e j)).continuous.comp_continuousOn
      ((hg j).continuousOn_fderivWithin hΔu le_rfl)).integrableOn_compact
        (isCompact_fullSimplex _)
  -- The left-hand side: the exterior derivative is the alternating sum of the coordinate
  -- derivatives of the coefficients `g j`, each of which is computed by
  -- `ContDiffOn.integral_fderivWithin_fullSimplex`.
  have hext : ∀ x ∈ Δ, extDerivWithin ω Δ x e =
      ∑ j : Fin (p + 1), (-1 : ℝ) ^ (j : ℕ) • fderivWithin ℝ (g j) Δ x (e j) := by
    intro x hx
    rw [extDerivWithin_apply ((hω.differentiableOn one_ne_zero) x hx) (hΔu x hx)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    rfl
  have hLHS : ∫ x in Δ, extDerivWithin ω Δ x e =
      ∑ j : Fin (p + 1), (-1 : ℝ) ^ (j : ℕ) •
        ((∫ y in fullSimplex p, g j (simplexMapAmbient (Fin.succAbove 0) y)) -
          ∫ y in fullSimplex p, g j (toLp 2 (j.insertNth 0 y.ofLp))) := by
    rw [setIntegral_congr_fun (isCompact_fullSimplex _).isClosed.measurableSet hext,
      integral_finsetSum _ fun j _ ↦ ?_]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_smul, ← setIntegral_toLp_insertNth_eq j (g j),
        ← integral_sub (htop j) (hbot j)]
      exact congrArg _ ((hg j).integral_fderivWithin_fullSimplex j)
    · exact (hD j).smul _
  -- The right-hand side: on the face opposite the origin the form evaluates on edge vectors, and
  -- splits into the coefficients `g j` (`AlternatingMap.map_succ_sub_zero`); on the face opposite
  -- `e_j` it is the coefficient `g j`.
  have hface₀ (y : EuclideanSpace ℝ (Fin p)) :
      ω (simplexMapAmbient (Fin.succAbove 0) y)
          (fun k ↦ (simplexMapAmbient (Fin.succAbove 0)).contLinear (EuclideanSpace.single k 1)) =
        ∑ j : Fin (p + 1), (-1 : ℝ) ^ (j : ℕ) • g j (simplexMapAmbient (Fin.succAbove 0) y) := by
    simp_rw [contLinear_simplexMapAmbient_succAbove_zero]
    exact AlternatingMap.map_succ_sub_zero (R := ℝ)
      (ω (simplexMapAmbient (Fin.succAbove 0) y)).toAlternatingMap e
  have hface (j : Fin (p + 1)) (y : EuclideanSpace ℝ (Fin p)) :
      ω (simplexMapAmbient j.succ.succAbove y)
          (fun k ↦ (simplexMapAmbient j.succ.succAbove).contLinear (EuclideanSpace.single k 1)) =
        g j (toLp 2 (j.insertNth 0 y.ofLp)) := by
    have h : (fun k ↦ (simplexMapAmbient j.succ.succAbove).contLinear
        (EuclideanSpace.single k (1 : ℝ))) = j.removeNth e :=
      funext fun k ↦ contLinear_simplexMapAmbient_succAbove_succ j k
    rw [h, simplexMapAmbient_succAbove_succ]
  rw [hLHS, Fin.sum_univ_succ (n := p + 1)]
  simp_rw [hface₀, hface]
  rw [integral_finsetSum _ fun j _ ↦ ?_]
  · simp only [integral_smul, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_add_neg _ _
  · exact (hzero j).smul _

end TauCeti
