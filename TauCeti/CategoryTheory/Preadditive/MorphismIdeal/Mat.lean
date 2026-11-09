/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor
public import TauCeti.CategoryTheory.Preadditive.Mat
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Morphism ideals in the additive envelope

An ideal of a preadditive category extends to its matrix category by requiring every entry to
belong to the ideal. Restriction along the one-term-family embedding recovers the original
ideal, and every ideal in the matrix category is obtained this way. Thus passing to the additive
envelope introduces no new morphism ideals.

The entrywise characterization for an arbitrary ideal uses the inclusions and projections of
Mathlib's `CategoryTheory.Mat_.isoBiproductEmbedding`. Each entry is obtained by composing
with an inclusion and a projection, and a matrix is the sum of these entrywise contributions.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.MorphismIdeal

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Extend a morphism ideal to finite matrices, entry by entry. -/
def mat (I : MorphismIdeal C) : MorphismIdeal (Mat_ C) where
  hom M N :=
    { carrier := {f | ∀ i j, f i j ∈ I.hom (M.X i) (N.X j)}
      zero_mem' := fun _ _ => zero_mem _
      add_mem' := fun hf hg i j => add_mem (hf i j) (hg i j)
      neg_mem' := fun hf i j => neg_mem (hf i j) }
  comp_mem_left f _ hg i k := by
    rw [Mat_.comp_apply]
    exact sum_mem fun j _ => I.comp_mem_left (f i j) (hg j k)
  comp_mem_right g hf i k := by
    rw [Mat_.comp_apply]
    exact sum_mem fun j _ => I.comp_mem_right (g j k) (hf i j)

/-- Membership in the extended ideal is entrywise membership. -/
@[simp]
theorem mem_mat_hom (I : MorphismIdeal C) {M N : Mat_ C} {f : M ⟶ N} :
    f ∈ I.mat.hom M N ↔ ∀ i j, f i j ∈ I.hom (M.X i) (N.X j) := Iff.rfl

/-- Restricting the matrix extension to one-term families recovers the original ideal. -/
@[simp]
theorem mat_comap_embedding (I : MorphismIdeal C) : I.mat.comap (Mat_.embedding C) = I := by
  ext X Y f
  simp only [mem_comap_hom, mem_mat_hom]
  exact ⟨fun h => h PUnit.unit PUnit.unit, fun h _ _ => h⟩

/-- Any ideal in a matrix category contains a matrix exactly when it contains all the entries,
viewed as morphisms between one-term families. -/
theorem mem_hom_iff_entries (J : MorphismIdeal (Mat_ C)) {M N : Mat_ C} (f : M ⟶ N) :
    f ∈ J.hom M N ↔ ∀ i j, (Mat_.embedding C).map (f i j) ∈
      J.hom ((Mat_.embedding C).obj (M.X i)) ((Mat_.embedding C).obj (N.X j)) := by
  classical
  let ι (A : Mat_ C) (i : A.ι) : (Mat_.embedding C).obj (A.X i) ⟶ A :=
    biproduct.ι (fun i => (Mat_.embedding C).obj (A.X i)) i ≫ A.isoBiproductEmbedding.inv
  let π (A : Mat_ C) (i : A.ι) : A ⟶ (Mat_.embedding C).obj (A.X i) :=
    A.isoBiproductEmbedding.hom ≫ biproduct.π (fun i => (Mat_.embedding C).obj (A.X i)) i
  have hentry (i : M.ι) (j : N.ι) : ι M i ≫ f ≫ π N j =
      (Mat_.embedding C).map (f i j) := by
    dsimp only [ι, π]
    rw [Mat_.isoBiproductEmbedding_inv, Mat_.isoBiproductEmbedding_hom]
    dsimp only [Mat_.embedding]
    simp only [Category.assoc]
    erw [biproduct.ι_desc_assoc, biproduct.lift_π]
    funext ⟨⟩ ⟨⟩
    -- The singleton embedding hides its dependent index family from `comp_apply` rewriting.
    -- Expand the two matrix products with the ambient families made explicit.
    change (∑ k, (if h : i = k then eqToHom (congrArg M.X h) else 0) ≫
      ∑ l, f k l ≫ (if h : l = j then eqToHom (congrArg N.X h) else 0)) = f i j
    simp [dite_comp, comp_dite]
  have htotal (A : Mat_ C) : ∑ i, π A i ≫ ι A i = 𝟙 A := by
    dsimp only [ι, π]
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
    exact A.isoBiproductEmbedding.hom_inv_id
  constructor
  · intro hf i j
    rw [← hentry]
    exact J.comp_mem_left _ (J.comp_mem_right _ hf)
  · intro hf
    have hsum : f = ∑ i, ∑ j, π M i ≫ (Mat_.embedding C).map (f i j) ≫ ι N j := by
      calc
        f = (∑ i, π M i ≫ ι M i) ≫ f ≫ (∑ j, π N j ≫ ι N j) := by simp [htotal]
        _ = ∑ i, ∑ j, π M i ≫ (ι M i ≫ f ≫ π N j) ≫ ι N j := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
          rw [Finset.sum_comm]
        _ = _ := by simp_rw [hentry]
    rw [hsum]
    exact sum_mem fun i _ => sum_mem fun j _ =>
      J.comp_mem_left (π M i) (J.comp_mem_right (ι N j) (hf i j))

/-- Every ideal of the additive envelope is the extension of its restriction. -/
@[simp]
theorem comap_embedding_mat (J : MorphismIdeal (Mat_ C)) :
    (J.comap (Mat_.embedding C)).mat = J := by
  ext M N f
  simp only [mem_mat_hom, mem_comap_hom]
  exact (J.mem_hom_iff_entries f).symm

/-- Matrix extension preserves and reflects inclusion of ideals. -/
@[simp]
theorem mat_le_mat_iff {I J : MorphismIdeal C} : I.mat ≤ J.mat ↔ I ≤ J := by
  constructor
  · intro h
    simpa using comap_mono (Mat_.embedding C) h
  · intro h
    exact le_def.mpr fun _ _ _ hf i j => (le_def.mp h) _ (hf i j)

end TauCeti.MorphismIdeal
