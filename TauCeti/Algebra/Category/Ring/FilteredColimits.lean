/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite relation matrices over filtered ring colimits

A finite matrix of relations lifts to a common stage of a filtered system of rings.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti.CommRingCat

/-- A finite relation matrix over a filtered ring colimit descends to one stage. -/
theorem exists_stage_finite_relation_matrix
    {ι : Type u} [Category.{u} ι] [IsFiltered ι]
    (D : ι ⥤ CommRingCat.{u}) (n m : ℕ)
    (r : (Fin m → (colimit D : CommRingCat.{u})) →ₗ[(colimit D : CommRingCat.{u})]
      (Fin n → (colimit D : CommRingCat.{u}))) :
    ∃ (j : ι) (rᵢ : (Fin m → D.obj j) →ₗ[D.obj j] (Fin n → D.obj j)),
      ∀ (row : Fin n) (col : Fin m),
        (colimit.ι D j).hom (rᵢ (Pi.single col 1) row) = r (Pi.single col 1) row := by
  classical
  have reps (a : Fin n × Fin m) :=
    Concrete.colimit_exists_rep D (r (Pi.single a.2 1) a.1)
  choose j x ha using reps
  obtain ⟨row, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (a : Fin n × Fin m) : j a ⟶ row :=
    (hj (Finset.mem_image_of_mem j (Finset.mem_univ a))).some
  let entry (a : Fin n × Fin m) : D.obj row := D.map (f a) (x a)
  have hb (a : Fin n × Fin m) :
      (colimit.ι D row).hom (entry a) = r (Pi.single a.2 1) a.1 := by
    exact (ConcreteCategory.congr_hom (colimit.w D (f a)) (x a)).trans (ha a)
  refine ⟨row, Matrix.toLin' (Matrix.of
    (fun rowIndex columnIndex ↦ entry (rowIndex, columnIndex))), ?_⟩
  intro rowIndex columnIndex
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact hb (rowIndex, columnIndex)

end TauCeti.CommRingCat
