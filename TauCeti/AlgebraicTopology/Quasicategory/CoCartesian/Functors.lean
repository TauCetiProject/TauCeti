/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Sections
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom.Composition

/-!
# Relative functors preserving coCartesian edges

For maps `p : X ⟶ B` and `q : Y ⟶ B`, `SSet.coCartesianFunctors p q` is the full
subcomplex of `Fun_B(X, Y)` spanned by functors preserving coCartesian edges. When `q` is
an inner fibration it is a quasicategory. Its higher simplices are relative families whose
functors at parameter vertices preserve coCartesian edges; no preservation condition is
imposed on transformation edges.

Composition and units restrict from relative internal homs. Evaluation over a base vertex
gives a map to the functor quasicategory between the fibres. The case with source `𝟙 B`
recovers `SSet.coCartesianSections q`.

## References

* J. Lurie, *Higher Topos Theory*, §3.1.3 (marked mapping objects) and
  Corollary 3.3.3.2 (the coCartesian dual for sections).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
  Opposite Simplicial

universe u

namespace SSet

variable {B X Y Z W : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) (s : W ⟶ B)

/-- The relative functors which preserve coCartesian edges, as a full subcomplex. -/
def coCartesianFunctors : (ihomOver q p : SSet).Subcomplex :=
  (ihomOver q p : SSet).fullEnhancedSubcategory fun f ↦
    ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
      (e.map (ihomOver.obj₀Equiv f).val).IsCoCartesian q

/-- The full-subcategory presentation of relative coCartesian functors. -/
lemma coCartesianFunctors_eq_fullEnhancedSubcategory :
    coCartesianFunctors p q = (ihomOver q p : SSet).fullEnhancedSubcategory
      (fun f ↦ ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv f).val).IsCoCartesian q) :=
  (rfl)

variable {p q r s}

/-- Membership of a vertex means preservation of coCartesian edges. -/
@[simp]
lemma mem_coCartesianFunctors_obj_zero_iff (f : (ihomOver q p : SSet) _⦋0⦌) :
    f ∈ (coCartesianFunctors p q).obj (op ⦋0⦌) ↔
      ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv f).val).IsCoCartesian q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory,
    mem_fullEnhancedSubcategory_obj_zero_iff]

/-- Preservation for a family is tested only at parameter vertices. -/
@[simp low]
lemma mem_coCartesianFunctors_obj_iff {n : ℕ} (f : (ihomOver q p : SSet) _⦋n⦌) :
    f ∈ (coCartesianFunctors p q).obj (op ⦋n⦌) ↔
      ∀ (i : Fin (n + 1)) ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv ((ihomOver q p : SSet).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op f)).val).IsCoCartesian q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory,
    mem_fullEnhancedSubcategory_obj_iff_forall_fin]

/-- A family of relative functors factors through the preserving functors exactly when
it preserves coCartesian edges at each parameter vertex. -/
@[simp]
lemma range_le_coCartesianFunctors_iff {P : SSet.{u}} (f : P ⟶ ihomOver q p) :
    Subcomplex.range f ≤ coCartesianFunctors p q ↔
      ∀ a : P _⦋0⦌, ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv (f.app _ a)).val).IsCoCartesian q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory, range_le_fullEnhancedSubcategory_iff]

namespace coCartesianFunctors

/-- The inclusion of the preserving functors is fully faithful. -/
instance isFullyFaithful_ι : IsFullyFaithful (coCartesianFunctors p q).ι :=
  inferInstanceAs (IsFullyFaithful ((ihomOver q p : SSet).fullEnhancedSubcategory _).ι)

/-- The inclusion of the preserving functors is an inner fibration. -/
instance innerFibration_ι : InnerFibration (coCartesianFunctors p q).ι :=
  inferInstanceAs (InnerFibration ((ihomOver q p : SSet).fullEnhancedSubcategory _).ι)

/-- The relative coCartesian functors into an inner fibration form a quasicategory. -/
instance quasicategory [InnerFibration q] : Quasicategory (coCartesianFunctors p q : SSet) :=
  inferInstanceAs (Quasicategory ((ihomOver q p : SSet).fullEnhancedSubcategory _ : SSet))

/-- Vertices are maps over the base which preserve coCartesian edges. -/
def obj₀Equiv :
    (coCartesianFunctors p q : SSet) _⦋0⦌ ≃
      {f : {f : X ⟶ Y // f ≫ q = p} //
        ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
          (e.map f.val).IsCoCartesian q} :=
  (fullEnhancedSubcategory.verticesEquiv _).trans
    ((ihomOver.obj₀Equiv (p := q) (f := p)).subtypeEquiv (fun _ ↦ Iff.rfl))

/-- The underlying relative map of a preserving functor. -/
@[simp]
lemma obj₀Equiv_apply_val (f : (coCartesianFunctors p q : SSet) _⦋0⦌) :
    dsimp% (obj₀Equiv f).val = ihomOver.obj₀Equiv f.val :=
  congrArg (ihomOver.obj₀Equiv (p := q) (f := p))
    (fullEnhancedSubcategory.verticesEquiv_apply_coe _ _)

/-- A map over the base preserving coCartesian edges gives its corresponding vertex. -/
@[simp]
lemma obj₀Equiv_symm_apply_val
    (f : {f : {f : X ⟶ Y // f ≫ q = p} //
      ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map f.val).IsCoCartesian q}) :
    dsimp% (obj₀Equiv.symm f).val = ihomOver.obj₀Equiv.symm f.val :=
  fullEnhancedSubcategory.verticesEquiv_symm_apply_coe _ _

/-- The underlying relative functor of a vertex preserves coCartesian edges. -/
lemma isCoCartesian_map (f : (coCartesianFunctors p q : SSet) _⦋0⦌)
    {x y : X _⦋0⦌} (e : Edge x y) (he : e.IsCoCartesian p) :
    (e.map (ihomOver.obj₀Equiv f.val).val).IsCoCartesian q :=
  (mem_coCartesianFunctors_obj_zero_iff f.val).1 f.property e he

/-- The identity functor preserves coCartesian edges. -/
def id (p : X ⟶ B) : 𝟙_ SSet.{u} ⟶ coCartesianFunctors p p :=
  Subcomplex.lift (ihomOver.id p) ((range_le_coCartesianFunctors_iff _).2 fun a _ _ e he ↦ by
    rw [ihomOver.obj₀Equiv_id_app_coe]
    exact he.of_edge_eq (by simp))

/-- Forgetting preservation sends the unit to the relative identity. -/
@[reassoc (attr := simp)]
lemma id_ι (p : X ⟶ B) : id p ≫ (coCartesianFunctors p p).ι = ihomOver.id p :=
  Subcomplex.lift_ι _ _

/-- Composition of relative coCartesian functors, including parameter families. -/
def comp (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) :
    (coCartesianFunctors p q : SSet) ⊗ (coCartesianFunctors q r : SSet) ⟶
      coCartesianFunctors p r :=
  Subcomplex.lift
    (ihomOver.compHom (fst _ _ ≫ (coCartesianFunctors p q).ι)
      (snd _ _ ≫ (coCartesianFunctors q r).ι))
    ((range_le_coCartesianFunctors_iff _).2 fun a _ _ e he ↦ by
      rw [ihomOver.obj₀Equiv_compHom_app_coe]
      exact (isCoCartesian_map
        ((snd (coCartesianFunctors p q : SSet) (coCartesianFunctors q r : SSet)).app _ a) _
        (isCoCartesian_map
          ((fst (coCartesianFunctors p q : SSet) (coCartesianFunctors q r : SSet)).app _ a)
          e he)).of_edge_eq (by
            simp only [Edge.map_edge, NatTrans.comp_app_apply, Subfunctor.ι_app,
              TypeCat.hom_ofHom, TypeCat.Fun.mk_apply]))

/-- The preserving composition is induced by relative simplicial composition. -/
@[reassoc (attr := simp)]
lemma comp_ι (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) :
    comp p q r ≫ (coCartesianFunctors p r).ι =
      ((coCartesianFunctors p q).ι ⊗ₘ (coCartesianFunctors q r).ι) ≫
        ihomOver.comp p q r := by
  rw [comp, Subcomplex.lift_ι, ← lift_fst_comp_snd_comp, ihomOver.lift_comp]

/-- Left unit law for relative coCartesian functors. -/
@[reassoc (attr := simp)]
lemma id_comp (p : X ⟶ B) (q : Y ⟶ B) :
    (λ_ (coCartesianFunctors p q : SSet)).inv ≫ id p ▷ _ ≫ comp p p q = 𝟙 _ := by
  rw [← cancel_mono (coCartesianFunctors p q).ι]
  simp only [Category.assoc, comp_ι, tensorHom_def_assoc, ← comp_whiskerRight_assoc, id_ι]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
    ihomOver.id_comp, Category.comp_id, Category.id_comp]

/-- Right unit law for relative coCartesian functors. -/
@[reassoc (attr := simp)]
lemma comp_id (p : X ⟶ B) (q : Y ⟶ B) :
    (ρ_ (coCartesianFunctors p q : SSet)).inv ≫ _ ◁ id q ≫ comp p q q = 𝟙 _ := by
  rw [← cancel_mono (coCartesianFunctors p q).ι]
  simp only [Category.assoc, comp_ι, tensorHom_def_assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, id_ι,
    ← rightUnitor_inv_naturality_assoc, ihomOver.comp_id,
    Category.comp_id, Category.id_comp]

/-- Associativity of composition of relative coCartesian functors. -/
@[reassoc]
lemma assoc (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) (s : W ⟶ B) :
    (α_ (coCartesianFunctors p q : SSet) (coCartesianFunctors q r : SSet)
      (coCartesianFunctors r s : SSet)).inv ≫ comp p q r ▷ _ ≫ comp p r s =
        _ ◁ comp q r s ≫ comp p q s := by
  rw [← cancel_mono (coCartesianFunctors p s).ι]
  simp [comp, ihomOver.comp_compHom, ihomOver.compHom_assoc]

end coCartesianFunctors

/-- Functors from the base itself preserving coCartesian edges are exactly coCartesian
sections: every edge is coCartesian over the identity. -/
@[simp]
lemma coCartesianFunctors_id_left (q : Y ⟶ B) :
    coCartesianFunctors (𝟙 B) q = coCartesianSections q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory,
    coCartesianSections_eq_fullEnhancedSubcategory]
  congr 1
  funext f
  exact propext ⟨fun h _ _ e ↦ h e (Edge.isCoCartesian_of_isIso _ _),
    fun h _ _ e _ ↦ h e⟩

end SSet
