/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.InvariantForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.RepresentationTheory.Continuous.LinHom
import TauCeti.RepresentationTheory.Compact.Invariants

/-!
# Haar averaging of real bilinear forms

A continuous representation of a compact group averages each given continuous real bilinear
form by pulling both arguments back through the inverse action and integrating against normalized
Haar measure. The average is a continuous bilinear form, and the operation is continuous and linear
in the starting form. It preserves symmetry and strict positive definiteness on arbitrary real
normed spaces, without requiring the representation space to be complete or finite-dimensional.

## Main definitions

* `ContRepresentation.averageBilinearForm`: Haar averaging as an operator on continuous forms.

## Main results

* `ContRepresentation.averageBilinearForm_apply`: the inverse-action integral formula.
* `ContRepresentation.isInvariantForm_averageBilinearForm`: the averaged form is invariant.
* `ContRepresentation.isSymm_averageBilinearForm` and
  `ContRepresentation.posDef_averageBilinearForm`: symmetry and positivity are preserved.
* `ContRepresentation.averageBilinearForm_eq_self` and `averageBilinearForm_eq_self_iff`:
  averaging fixes exactly invariant forms.
* `ContRepresentation.averageBilinearForm_idempotent`: averaging is a projection.
* `ContRepresentation.averageBilinearForm_bilinearComp`: pulling back the input by an action
  operator does not change its average.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), Lemma 10.4.14, for the invariant-inner-product construction.
-/

public noncomputable section

open MeasureTheory TauCeti

namespace ContRepresentation

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

-- Cache the canonical instances for the nested operator space; without these, elaborating
-- the continuity statement exceeds the default instance-search depth.
private local instance normedBilinear : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance normedSpaceBilinear : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable (π : ContRepresentation ℝ G V)

/-- The existing iterated Hom representation acts on continuous bilinear forms. -/
private def bilinearRepresentation : ContRepresentation ℝ G (V →L[ℝ] V →L[ℝ] ℝ) :=
  linHom π (linHom π (trivial ℝ G ℝ))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem bilinearRepresentation_apply (g : G) (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    bilinearRepresentation π g B v w = B (π g⁻¹ v) (π g⁻¹ w) := by
  simp only [bilinearRepresentation, linHom_apply_apply, trivial_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem mem_bilinearRepresentation_invariants_iff (B : V →L[ℝ] V →L[ℝ] ℝ) :
    B ∈ (bilinearRepresentation π).invariants ↔
      Representation.IsInvariantForm π.toRepresentation B.toBilinForm := by
  have hi (g : G) (x : V) : π g⁻¹ (π g x) = x := by
    simpa only [toRepresentation_apply] using Representation.inv_self_apply π.toRepresentation g x
  constructor
  · intro hB
    apply Representation.isInvariantForm_iff.mpr
    intro g v w
    have h := congrArg (fun C : V →L[ℝ] V →L[ℝ] ℝ ↦ C (π g v) (π g w)) (hB g)
    simpa only [bilinearRepresentation_apply,
      hi, toRepresentation_apply, ContinuousLinearMap.toBilinForm_apply] using h.symm
  · intro hB g
    ext v w
    rw [bilinearRepresentation_apply]
    exact hB.apply g⁻¹ v w

variable (hπ : Continuous π)

include hπ

private theorem continuous_bilinearRepresentation : Continuous (bilinearRepresentation π) :=
  continuous_linHom π _ hπ (continuous_linHom π _ hπ continuous_const)

variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Average a given real continuous bilinear form against normalized Haar measure, using
inverse-action pullback. This is a continuous linear operator on the space of forms. -/
def averageBilinearForm : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  haarAverageMap (bilinearRepresentation π) (continuous_bilinearRepresentation π hπ)

/-- The averaged form is the integral of the inverse-action pullbacks of the starting form. -/
theorem averageBilinearForm_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    averageBilinearForm π hπ B v w =
      ∫ g, B (π g⁻¹ v) (π g⁻¹ w) ∂haarProb G := by
  have hi : Integrable (fun g ↦ bilinearRepresentation π g B) (haarProb G) := by
    apply TauCeti.integrable_continuousMap G
      (⟨fun g ↦ bilinearRepresentation π g B,
        (ContinuousLinearMap.apply ℝ _ B).continuous.comp
          (continuous_bilinearRepresentation π hπ)⟩ : C(G, V →L[ℝ] V →L[ℝ] ℝ))
  have h := ((ContinuousLinearMap.apply ℝ ℝ w).comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) v)).integral_comp_comm hi
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    bilinearRepresentation_apply, averageBilinearForm, haarAverageMap_apply] using h.symm

/-- The Haar-averaged form is invariant under the original representation. -/
theorem isInvariantForm_averageBilinearForm (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Representation.IsInvariantForm π.toRepresentation
      (averageBilinearForm π hπ B).toBilinForm :=
  (mem_bilinearRepresentation_invariants_iff π _).mp
    (haarAverageMap_invariant (bilinearRepresentation π)
      (continuous_bilinearRepresentation π hπ) B)

/-- Averaging preserves symmetry of a continuous real bilinear form. -/
theorem isSymm_averageBilinearForm (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm) :
    (averageBilinearForm π hπ B).toBilinForm.IsSymm := by
  constructor
  intro v w
  simp only [ContinuousLinearMap.toBilinForm_apply]
  rw [averageBilinearForm_apply, averageBilinearForm_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦ hB.eq _ _)

/-- Averaging preserves positive definiteness, without requiring symmetry of the input. -/
theorem posDef_averageBilinearForm (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : B.toBilinForm.toQuadraticMap.PosDef) :
    (averageBilinearForm π hπ B).toBilinForm.toQuadraticMap.PosDef := by
  intro v hv
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
    averageBilinearForm_apply]
  have hp (g : G) : 0 < B (π g⁻¹ v) (π g⁻¹ v) := by
    have hn : π g⁻¹ v ≠ 0 := by
      intro hzero
      have hc : π g (π g⁻¹ v) = v := Representation.self_inv_apply π.toRepresentation g v
      rw [hzero, map_zero] at hc
      exact hv hc.symm
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
      ContinuousLinearMap.toBilinForm_apply] using hB (π g⁻¹ v) hn
  have hi : Integrable (fun g ↦ B (π g⁻¹ v) (π g⁻¹ v)) (haarProb G) := by
    apply TauCeti.integrable_continuousMap G
      (⟨fun g ↦ B (π g⁻¹ v) (π g⁻¹ v), ?_⟩ : C(G, ℝ))
    have hInv := hπ.comp continuous_inv
    exact (B.continuous.comp (hInv.clm_apply continuous_const)).clm_apply
      (hInv.clm_apply continuous_const)
  apply (integral_pos_iff_support_of_nonneg (fun g ↦ (hp g).le) hi).mpr
  have hs : Function.support (fun g : G ↦ B (π g⁻¹ v) (π g⁻¹ v)) = Set.univ := by
    ext g
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hp g)
  rw [hs, measure_univ]
  exact zero_lt_one

/-- Averaging fixes every invariant continuous bilinear form. -/
@[simp]
theorem averageBilinearForm_eq_self (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : Representation.IsInvariantForm π.toRepresentation B.toBilinForm) :
    averageBilinearForm π hπ B = B := by
  exact haarAverageMap_id (bilinearRepresentation π) (continuous_bilinearRepresentation π hπ)
    ((mem_bilinearRepresentation_invariants_iff π B).mpr hB)

/-- A continuous bilinear form is fixed by averaging exactly when it is invariant. -/
theorem averageBilinearForm_eq_self_iff (B : V →L[ℝ] V →L[ℝ] ℝ) :
    averageBilinearForm π hπ B = B ↔
      Representation.IsInvariantForm π.toRepresentation B.toBilinForm := by
  refine ⟨fun h ↦ ?_, averageBilinearForm_eq_self π hπ B⟩
  rw [← h]
  exact isInvariantForm_averageBilinearForm π hπ B

/-- Haar averaging is idempotent on continuous real bilinear forms. -/
@[simp]
theorem averageBilinearForm_idempotent (B : V →L[ℝ] V →L[ℝ] ℝ) :
    averageBilinearForm π hπ (averageBilinearForm π hπ B) = averageBilinearForm π hπ B :=
  DFunLike.congr_fun (haarAverageMap_comp_self (bilinearRepresentation π)
    (continuous_bilinearRepresentation π hπ)) B

/-- Averaging is unchanged if the starting form is pulled back by an action operator. -/
@[simp]
theorem averageBilinearForm_bilinearComp (B : V →L[ℝ] V →L[ℝ] ℝ) (h : G) :
    averageBilinearForm π hπ (B.bilinearComp (π h) (π h)) = averageBilinearForm π hπ B := by
  have he : B.bilinearComp (π h) (π h) = bilinearRepresentation π h⁻¹ B := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply, bilinearRepresentation_apply, inv_inv]
  rw [he]
  exact haarAverageMap_comp_apply (bilinearRepresentation π)
    (continuous_bilinearRepresentation π hπ) h⁻¹ B

end ContRepresentation
