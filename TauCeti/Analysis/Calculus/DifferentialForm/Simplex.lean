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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.LinearAlgebra.Alternating.Translate
import TauCeti.MeasureTheory.Integral.FullSimplex

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
its vertices, so the integrals agree (`TauCeti.setIntegral_toLp_insertNth_eq`). Finally
`F₀` carries the standard basis to the edge vectors `e_{k+1} - e₀`, on which `ω` is the alternating
sum of its coefficients (`AlternatingMap.map_succ_sub_zero`).

The scalar computations, the coordinate fundamental theorem of calculus and the comparison of the
two readings of the face `∑ xᵢ = 1`, are in `TauCeti.MeasureTheory.Integral.FullSimplex`.

## Main results

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
/-- The exterior derivative of a `C¹` form on the standard basis is the alternating sum of the
coordinate derivatives of the coefficients `x ↦ ω x (j.removeNth e)`. -/
private lemma extDerivWithin_fullSimplex_eq_sum {p : ℕ}
    {ω : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (fullSimplex (p + 1))) {x : EuclideanSpace ℝ (Fin (p + 1))}
    (hx : x ∈ fullSimplex (p + 1)) :
    extDerivWithin ω (fullSimplex (p + 1)) x (fun i ↦ EuclideanSpace.single i 1) =
      ∑ j : Fin (p + 1), (-1 : ℝ) ^ (j : ℕ) •
        fderivWithin ℝ (fun x ↦ ω x (j.removeNth fun i ↦ EuclideanSpace.single i 1))
          (fullSimplex (p + 1)) x (EuclideanSpace.single j 1) := by
  rw [extDerivWithin_apply ((hω.differentiableOn one_ne_zero) x hx)
    (uniqueDiffOn_fullSimplex _ x hx)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The integral of the exterior derivative over `Δᵖ⁺¹` as an alternating sum of differences of
integrals of the coefficients `x ↦ ω x (j.removeNth e)` over two faces of `Δᵖ`. -/
private lemma integral_extDerivWithin_fullSimplex_eq_sum {p : ℕ}
    {ω : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (fullSimplex (p + 1))) :
    ∫ x in fullSimplex (p + 1), extDerivWithin ω (fullSimplex (p + 1)) x
        (fun i ↦ EuclideanSpace.single i 1) =
      ∑ j : Fin (p + 1), (-1 : ℝ) ^ (j : ℕ) •
        ((∫ y in fullSimplex p, ω (simplexMapAmbient (Fin.succAbove 0) y)
            (j.removeNth fun i ↦ EuclideanSpace.single i 1)) -
          ∫ y in fullSimplex p, ω (toLp 2 (j.insertNth 0 y.ofLp))
            (j.removeNth fun i ↦ EuclideanSpace.single i 1)) := by
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
  have hD (j : Fin (p + 1)) : IntegrableOn (fun x ↦ fderivWithin ℝ (g j) Δ x (e j)) Δ :=
    ((ContinuousLinearMap.apply ℝ F (e j)).continuous.comp_continuousOn
      ((hg j).continuousOn_fderivWithin hΔu le_rfl)).integrableOn_compact
        (isCompact_fullSimplex _)
  -- The exterior derivative is the alternating sum of the coordinate derivatives of the
  -- coefficients `g j`, each of which is computed by
  -- `ContDiffOn.integral_fderivWithin_fullSimplex`.
  rw [setIntegral_congr_fun (isCompact_fullSimplex _).isClosed.measurableSet
      fun x hx ↦ extDerivWithin_fullSimplex_eq_sum hω hx,
    integral_finsetSum _ fun j _ ↦ ?_]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_smul, ← setIntegral_toLp_insertNth_eq j (g j),
      ← integral_sub (htop j) (hbot j)]
    exact congrArg _ ((hg j).integral_fderivWithin_fullSimplex j)
  · exact (hD j).smul _

omit [CompleteSpace F] in
/-- On the face of `Δᵖ⁺¹` opposite the origin, the form evaluates on the edge vectors and splits
into the coefficients `x ↦ ω x (j.removeNth e)` (`AlternatingMap.map_succ_sub_zero`). -/
private lemma eval_face_zero {p : ℕ}
    (ω : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F)
    (y : EuclideanSpace ℝ (Fin p)) :
    ω (simplexMapAmbient (Fin.succAbove 0) y)
        (fun k ↦ (simplexMapAmbient (Fin.succAbove 0)).contLinear (EuclideanSpace.single k 1)) =
      ∑ j : Fin (p + 1), (-1 : ℝ) ^ (j : ℕ) • ω (simplexMapAmbient (Fin.succAbove 0) y)
        (j.removeNth fun i ↦ EuclideanSpace.single i 1) := by
  simp_rw [contLinear_simplexMapAmbient_succAbove_zero]
  exact AlternatingMap.map_succ_sub_zero (R := ℝ)
    (ω (simplexMapAmbient (Fin.succAbove 0) y)).toAlternatingMap
    fun i ↦ EuclideanSpace.single i 1

omit [CompleteSpace F] in
/-- On the face of `Δᵖ⁺¹` opposite `e_j`, the form evaluates to the coefficient
`x ↦ ω x (j.removeNth e)` at the corresponding point of the face. -/
private lemma eval_face_succ {p : ℕ}
    (ω : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F)
    (j : Fin (p + 1)) (y : EuclideanSpace ℝ (Fin p)) :
    ω (simplexMapAmbient j.succ.succAbove y)
        (fun k ↦ (simplexMapAmbient j.succ.succAbove).contLinear (EuclideanSpace.single k 1)) =
      ω (toLp 2 (j.insertNth 0 y.ofLp)) (j.removeNth fun i ↦ EuclideanSpace.single i 1) := by
  have h : (fun k ↦ (simplexMapAmbient j.succ.succAbove).contLinear
      (EuclideanSpace.single k (1 : ℝ))) = j.removeNth fun i ↦ EuclideanSpace.single i 1 :=
    funext fun k ↦ contLinear_simplexMapAmbient_succAbove_succ j k
  rw [h, simplexMapAmbient_succAbove_succ]

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
  have hzero (j : Fin (p + 1)) : IntegrableOn (fun y ↦ ω (simplexMapAmbient (Fin.succAbove 0) y)
      (j.removeNth fun i ↦ EuclideanSpace.single i 1)) (fullSimplex p) :=
    (((ContinuousAlternatingMap.apply ℝ _ F _).continuous.comp_continuousOn
      (hω.continuousOn.comp (simplexMapAmbient _).continuous.continuousOn
        (mapsTo_simplexMapAmbient _)))).integrableOn_compact (isCompact_fullSimplex p)
  rw [integral_extDerivWithin_fullSimplex_eq_sum hω, Fin.sum_univ_succ (n := p + 1)]
  simp_rw [eval_face_zero, eval_face_succ]
  rw [integral_finsetSum _ fun j _ ↦ ?_]
  · simp only [integral_smul, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_add_neg _ _
  · exact (hzero j).smul _

end TauCeti
