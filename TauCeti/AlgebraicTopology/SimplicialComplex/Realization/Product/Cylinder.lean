/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Product.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Realizing finite simplicial cylinders

The ordered simplicial cylinder of a finite complex is homeomorphic to the product of its
weak realization with the unit interval. The time coordinate is the total barycentric
weight at the terminal interval vertex. The two simplicial endpoint inclusions correspond
to the inclusions at times zero and one, so the identification respects the ends of the
cylinder, as needed for relative homotopies and simplicial collapse.

The construction composes the staircase-product homeomorphism with
`realizationOneSimplexHomeomorphUnitInterval`, which uses Mathlib's
`Convexity.StdSimplex.homeomorphI`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (triangulating products of polyhedra).
-/

public section

noncomputable section

namespace AbstractSimplicialComplex

open PreAbstractSimplicialComplex.SimplicialMap

variable {α : Type*} [LinearOrder α] (K : AbstractSimplicialComplex α)
  (hK : K.faces.Finite)

/-- The ordered simplicial cylinder of a finite complex realizes to its topological cylinder,
with the original coordinate first and time second. -/
def orderedCylinderRealizationHomeomorph :
    Realization K.orderedCylinder ≃ₜ Realization K × unitInterval :=
  -- Transport both the realization carrier and its topology along the characteristic equality.
  Eq.rec (motive := fun C _ => Realization C ≃ₜ Realization K × unitInterval)
    ((K.orderedProdRealizationHomeomorph (⊤ : AbstractSimplicialComplex (Fin 2))
      (finite_faces_orderedProd hK (Set.toFinite _))).trans
        ((Homeomorph.refl _).prodCongr realizationOneSimplexHomeomorphUnitInterval))
    (K.orderedCylinder_def).symm

/-- The spatial coordinate is the first marginal of the barycentric coordinates. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_fst_val (z : Realization K.orderedCylinder) :
    (K.orderedCylinderRealizationHomeomorph hK z).1.1 = Finsupp.mapDomain Prod.fst z.1 := by
  -- Eliminate the carrier equality before applying the product computation rule.
  unfold orderedCylinderRealizationHomeomorph
  generalize_proofs hfin hEq
  generalize K.orderedCylinder = C at hEq z ⊢
  cases hEq
  let z' : Realization (K.orderedProd (⊤ : AbstractSimplicialComplex (Fin 2))) := z
  have h := K.orderedProdRealizationMap_fst_val (⊤ : AbstractSimplicialComplex (Fin 2)) z'
  rw [← orderedProdRealizationHomeomorph_apply K _
    (finite_faces_orderedProd hK (Set.toFinite _))] at h
  exact h

/-- Time is the total barycentric weight over the terminal interval vertex. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_snd_coe (z : Realization K.orderedCylinder) :
    ((K.orderedCylinderRealizationHomeomorph hK z).2 : ℝ) =
      Finsupp.mapDomain Prod.snd z.1 1 := by
  -- Eliminate the carrier equality before applying the product computation rule.
  unfold orderedCylinderRealizationHomeomorph
  generalize_proofs hfin hEq
  generalize K.orderedCylinder = C at hEq z ⊢
  cases hEq
  let z' : Realization (K.orderedProd (⊤ : AbstractSimplicialComplex (Fin 2))) := z
  have h := K.orderedProdRealizationMap_snd_val (⊤ : AbstractSimplicialComplex (Fin 2)) z'
  rw [← orderedProdRealizationHomeomorph_apply K _
    (finite_faces_orderedProd hK (Set.toFinite _))] at h
  have ht := congrArg (fun w : Fin 2 →₀ ℝ => w 1) h
  rw [← realizationOneSimplexHomeomorphUnitInterval_coe] at ht
  exact ht

/-- The inverse cylinder identification has the prescribed spatial marginal. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_symm_fst_val (p : Realization K × unitInterval) :
    Finsupp.mapDomain Prod.fst
      ((K.orderedCylinderRealizationHomeomorph hK).symm p).1 = p.1.1 := by
  have h := congrArg (fun q => q.1.1)
    ((K.orderedCylinderRealizationHomeomorph hK).apply_symm_apply p)
  simpa only [orderedCylinderRealizationHomeomorph_fst_val] using h

/-- The inverse cylinder identification puts total weight equal to time on the terminal end. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_symm_snd_val_one
    (p : Realization K × unitInterval) :
    Finsupp.mapDomain Prod.snd
      ((K.orderedCylinderRealizationHomeomorph hK).symm p).1 1 = (p.2 : ℝ) := by
  have h := congrArg (fun q => (q.2 : ℝ))
    ((K.orderedCylinderRealizationHomeomorph hK).apply_symm_apply p)
  simpa only [orderedCylinderRealizationHomeomorph_snd_coe] using h

/-- The inverse cylinder identification puts the complementary total weight on the initial end. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_symm_snd_val_zero
    (p : Realization K × unitInterval) :
    Finsupp.mapDomain Prod.snd
      ((K.orderedCylinderRealizationHomeomorph hK).symm p).1 0 = 1 - (p.2 : ℝ) := by
  -- Reduce the inverse of the composite to the product inverse and interval inverse.
  unfold orderedCylinderRealizationHomeomorph
  generalize_proofs hfin hEq
  generalize K.orderedCylinder = C at hEq ⊢
  cases hEq
  simp only [Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.coe_prodCongr, Homeomorph.refl_symm, Homeomorph.refl_apply]
  have h := K.orderedProdRealizationHomeomorph_symm_snd_val
    (⊤ : AbstractSimplicialComplex (Fin 2))
    (finite_faces_orderedProd hK (Set.toFinite _))
    (p.1, realizationOneSimplexHomeomorphUnitInterval.symm p.2)
  have ht := congrArg (fun w : Fin 2 →₀ ℝ => w 0) h
  rw [realizationOneSimplexHomeomorphUnitInterval_symm_apply_val_zero] at ht
  exact ht

/-- The simplicial zero-end inclusion becomes the time-zero inclusion. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_zero (x : Realization K) :
    K.orderedCylinderRealizationHomeomorph hK ((orderedCylinderZero K).realizationMap x) =
      (x, 0) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [orderedCylinderRealizationHomeomorph_fst_val,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_orderedCylinderZero, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  · apply Subtype.ext
    simp only [orderedCylinderRealizationHomeomorph_snd_coe,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_orderedCylinderZero, ← Finsupp.mapDomain_comp]
    simp [Finsupp.mapDomain_apply]

/-- The simplicial one-end inclusion becomes the time-one inclusion. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_one (x : Realization K) :
    K.orderedCylinderRealizationHomeomorph hK ((orderedCylinderOne K).realizationMap x) =
      (x, 1) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [orderedCylinderRealizationHomeomorph_fst_val,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_orderedCylinderOne, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  · apply Subtype.ext
    simp only [orderedCylinderRealizationHomeomorph_snd_coe,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_orderedCylinderOne, ← Finsupp.mapDomain_comp]
    simp [Finsupp.mapDomain_apply]

/-- At time zero the inverse is the simplicial zero-end inclusion. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_symm_zero (x : Realization K) :
    (K.orderedCylinderRealizationHomeomorph hK).symm (x, 0) =
      (orderedCylinderZero K).realizationMap x := by
  apply (K.orderedCylinderRealizationHomeomorph hK).injective
  simp

/-- At time one the inverse is the simplicial one-end inclusion. -/
@[simp]
theorem orderedCylinderRealizationHomeomorph_symm_one (x : Realization K) :
    (K.orderedCylinderRealizationHomeomorph hK).symm (x, 1) =
      (orderedCylinderOne K).realizationMap x := by
  apply (K.orderedCylinderRealizationHomeomorph hK).injective
  simp

end AbstractSimplicialComplex
