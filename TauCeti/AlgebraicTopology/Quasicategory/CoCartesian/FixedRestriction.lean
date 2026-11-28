/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Functors

/-!
# Relative functors with a fixed restriction

For maps `p : X ⟶ B`, `q : Y ⟶ B`, a map `i : A ⟶ X`, and a map
`a : A ⟶ Y` over `B`, `SSet.ihomOver.fixedRestriction i a` is the fibre of relative
restriction at `a`. A family parametrized by `Z` is a map `X ⊗ Z ⟶ Y` over `B` whose
restriction to `A ⊗ Z` is the constant family at `a`.

When `i` is a monomorphism and `q` is an inner fibration this fibre is a quasicategory.
Pulling back `SSet.coCartesianFunctors p q` gives its full subquasicategory of functors
preserving coCartesian edges. Evaluation on a fibre of the base is the existing
`SSet.ihomOver.evalFiber` after the inclusions. These constructions allow a common part of
the source and target to be held fixed while retaining all relative natural transformations.

Restriction along the identity leaves exactly the prescribed functor: the fibre is terminal,
and so is its preserving subcategory when that functor preserves coCartesian edges.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.7 and §3.1.3.

The restriction fibration uses Mathlib's `SSet.innerFibration_pullbackObjObjπ`, by Jack McKoen
and Joël Riou, through `SSet.ihomOver.innerFibration_pre`.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed
  Opposite Simplicial

namespace SSet.ihomOver

variable {A X Y B Z : SSet.{u}} {p : X ⟶ B} {q : Y ⟶ B}
  (i : A ⟶ X) (a : {a : A ⟶ Y // a ≫ q = i ≫ p})

/-- Relative functors whose restriction along `i` is the prescribed relative functor `a`.
Higher simplices restrict to constant families at `a`. -/
noncomputable def fixedRestriction : (ihomOver q p : SSet).Subcomplex :=
  fiber (pre i) (obj₀Equiv.symm a)

/-- A relative family has fixed restriction exactly when its uncurried map agrees with the
constant family at `a` on `A ⊗ Z`. -/
lemma range_le_fixedRestriction_iff (φ : Z ⟶ ihomOver q p) :
    Subcomplex.range φ ≤ fixedRestriction i a ↔
      i ▷ Z ≫ (homEquiv φ).val = fst A Z ≫ a.val := by
  rw [fixedRestriction, range_le_fiber_iff, ← (homEquiv (p := q) (f := i ≫ p)).injective.eq_iff,
    Subtype.ext_iff, homEquiv_comp_pre_coe, homEquiv_const_coe]

/-- Vertices with fixed restriction are precisely relative maps extending `a`. -/
@[simp]
lemma mem_fixedRestriction_obj_zero_iff (v : (ihomOver q p : SSet) _⦋0⦌) :
    v ∈ (fixedRestriction i a).obj (op ⦋0⦌) ↔
      i ≫ (obj₀Equiv v).val = a.val := by
  rw [fixedRestriction, mem_fiber_iff, SimplexCategory.const_eq_id, op_id,
    CategoryTheory.Functor.map_id, types_id_apply,
    ← (obj₀Equiv (p := q) (f := i ≫ p)).injective.eq_iff,
    Subtype.ext_iff, obj₀Equiv_pre_app_coe, Equiv.apply_symm_apply]

namespace fixedRestriction

/-- Fixed-restriction relative functors form a quasicategory when `i` is a monomorphism and
`q` is an inner fibration. No fibrancy of the base or source is required. -/
instance quasicategory [Mono i] [InnerFibration q] :
    Quasicategory (fixedRestriction i a : SSet) :=
  fiber.quasicategory _ _

/-- Maps into the fixed-restriction fibre are relative families extending the constant
family at `a`. -/
noncomputable def homEquiv :
    (Z ⟶ fixedRestriction i a) ≃
      {g : X ⊗ Z ⟶ Y // g ≫ q = fst X Z ≫ p ∧ i ▷ Z ≫ g = fst A Z ≫ a.val} where
  toFun φ := ⟨(ihomOver.homEquiv (φ ≫ (fixedRestriction i a).ι)).val,
    (ihomOver.homEquiv (φ ≫ (fixedRestriction i a).ι)).property,
    (range_le_fixedRestriction_iff i a _).1 (by
      rintro n _ ⟨z, rfl⟩
      exact (φ.app n z).property)⟩
  invFun g := Subcomplex.lift (ihomOver.homEquiv.symm ⟨g.val, g.property.1⟩)
    ((range_le_fixedRestriction_iff i a _).2 (by
      rw [Equiv.apply_symm_apply]
      exact g.property.2))
  left_inv φ := by
    rw [← cancel_mono (fixedRestriction i a).ι]
    simp only [Subcomplex.lift_ι]
    exact ihomOver.homEquiv.symm_apply_apply _
  right_inv g := Subtype.ext (by simp only [Subcomplex.lift_ι, Equiv.apply_symm_apply])

/-- The family classified by a map is its underlying relative family. -/
lemma homEquiv_apply_coe (φ : Z ⟶ fixedRestriction i a) :
    (homEquiv i a φ).val =
      (ihomOver.homEquiv (φ ≫ (fixedRestriction i a).ι)).val :=
  (rfl)

/-- Forgetting fixed restriction in a classified family recovers the relative family. -/
@[reassoc (attr := simp)]
lemma homEquiv_symm_apply_ι
    (g : {g : X ⊗ Z ⟶ Y // g ≫ q = fst X Z ≫ p ∧ i ▷ Z ≫ g = fst A Z ≫ a.val}) :
    (homEquiv i a).symm g ≫ (fixedRestriction i a).ι =
      ihomOver.homEquiv.symm ⟨g.val, g.property.1⟩ :=
  (rfl)

/-- The family description is natural in the parameter. -/
@[simp]
lemma homEquiv_comp_coe {Z' : SSet.{u}} (h : Z' ⟶ Z) (φ : Z ⟶ fixedRestriction i a) :
    (homEquiv i a (h ≫ φ)).val = X ◁ h ≫ (homEquiv i a φ).val := by
  simp only [homEquiv_apply_coe, Category.assoc, ihomOver.homEquiv_comp_coe]

/-- Vertices are maps over the base whose restriction is exactly `a`. -/
noncomputable def obj₀Equiv :
    (fixedRestriction i a : SSet) _⦋0⦌ ≃
      {f : {f : X ⟶ Y // f ≫ q = p} // i ≫ f.val = a.val} :=
  (ihomOver.obj₀Equiv (p := q) (f := p)).subtypeEquiv
    (mem_fixedRestriction_obj_zero_iff i a)

/-- Forgetting the restriction equation in the vertex description gives the relative map. -/
@[simp]
lemma obj₀Equiv_apply_val (v : (fixedRestriction i a : SSet) _⦋0⦌) :
    dsimp% (obj₀Equiv i a v).val = ihomOver.obj₀Equiv v.val :=
  (rfl)

/-- The vertex representing an extension has the corresponding underlying relative vertex. -/
@[simp]
lemma obj₀Equiv_symm_apply_val
    (f : {f : {f : X ⟶ Y // f ≫ q = p} // i ≫ f.val = a.val}) :
    dsimp% ((obj₀Equiv i a).symm f).val = ihomOver.obj₀Equiv.symm f.val :=
  (rfl)

/-- Restricting along the identity leaves a terminal simplicial set, with unique functor `a`.
This does not require fibrancy. -/
noncomputable def isTerminalId (a : {a : X ⟶ Y // a ≫ q = (𝟙 X) ≫ p}) :
    IsTerminal (fixedRestriction (𝟙 X) a : SSet) :=
  IsTerminal.ofUniqueHom
    (fun Z ↦ (homEquiv (𝟙 X) a).symm ⟨fst X Z ≫ a.val, by
      constructor
      · simp [a.property]
      · simp⟩)
    (fun _ φ ↦ (homEquiv (𝟙 X) a).injective (Subtype.ext (by
      simpa using (homEquiv (𝟙 X) a φ).property.2)))

/-- The unique extension along the identity is the constant family at `a`. -/
@[reassoc (attr := simp)]
lemma isTerminalId_from_ι (a : {a : X ⟶ Y // a ≫ q = (𝟙 X) ≫ p}) (Z : SSet.{u}) :
    (isTerminalId a).from Z ≫ (fixedRestriction (𝟙 X) a).ι =
      const (ihomOver.obj₀Equiv.symm ⟨a.val, by simpa using a.property⟩) := by
  apply ihomOver.homEquiv.injective
  apply Subtype.ext
  rw [ihomOver.homEquiv_const_coe, ← homEquiv_apply_coe]
  simpa using (homEquiv (𝟙 X) a ((isTerminalId a).from Z)).property.2

/-- Fibre evaluation of the unique identity-restriction extension is the constant family at
the induced map of fibres. Use this as an explicit rewrite after forgetting the restriction. -/
@[reassoc]
lemma isTerminalId_from_evalFiber (a : {a : X ⟶ Y // a ≫ q = (𝟙 X) ≫ p})
    (Z : SSet.{u}) (b : B _⦋0⦌) :
    (isTerminalId a).from Z ≫ (fixedRestriction (𝟙 X) a).ι ≫ ihomOver.evalFiber p q b =
      const ((ihomObj₀Equiv _ _).symm
        (fiber.map a.val (by simpa using a.property) b)) := by
  rw [isTerminalId_from_ι_assoc, const_comp]
  congr 1
  apply (ihomObj₀Equiv _ _).injective
  exact (ihomOver.ihomObj₀Equiv_evalFiber_app b
    (ihomOver.obj₀Equiv.symm ⟨a.val, by simpa using a.property⟩)).trans
      (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- The full subcomplex of fixed-restriction relative functors preserving coCartesian edges,
obtained by pulling back the preserving functors along the fibre inclusion. -/
noncomputable def coCartesianFunctors : (fixedRestriction i a : SSet).Subcomplex :=
  (SSet.coCartesianFunctors p q).preimage (fixedRestriction i a).ι

/-- The pulled-back preserving functors are a full subcategory of the fixed-restriction fibre. -/
lemma coCartesianFunctors_eq_fullEnhancedSubcategory :
    coCartesianFunctors i a = (fixedRestriction i a : SSet).fullEnhancedSubcategory
      (fun v ↦ ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv v.val).val).IsCoCartesian q) := by
  ext n v
  simp only [coCartesianFunctors, Subcomplex.preimage_obj, Set.mem_preimage,
    SSet.coCartesianFunctors_eq_fullEnhancedSubcategory, mem_fullEnhancedSubcategory_obj_iff]
  -- The fibre inclusion sends each simplex to its underlying relative simplex.
  rfl

/-- Membership at a vertex means preservation by its underlying relative functor. -/
@[simp]
lemma mem_coCartesianFunctors_obj_zero_iff (v : (fixedRestriction i a : SSet) _⦋0⦌) :
    v ∈ (coCartesianFunctors i a).obj (op ⦋0⦌) ↔
      ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv v.val).val).IsCoCartesian q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory,
    mem_fullEnhancedSubcategory_obj_zero_iff]

/-- A simplex preserves coCartesian edges exactly when its parameter vertices do. -/
@[simp low]
lemma mem_coCartesianFunctors_obj_iff {n : ℕ} (v : (fixedRestriction i a : SSet) _⦋n⦌) :
    v ∈ (coCartesianFunctors i a).obj (op ⦋n⦌) ↔
      ∀ j : Fin (n + 1), ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv (((fixedRestriction i a : SSet).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op v).val)).val).IsCoCartesian q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory,
    mem_fullEnhancedSubcategory_obj_iff_forall_fin]

/-- A family in the fixed fibre preserves coCartesian edges exactly when it does so at each
parameter vertex. Transformation edges carry no additional preservation requirement. -/
@[simp]
lemma range_le_coCartesianFunctors_iff (φ : Z ⟶ fixedRestriction i a) :
    Subcomplex.range φ ≤ coCartesianFunctors i a ↔
      ∀ z : Z _⦋0⦌, ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map (ihomOver.obj₀Equiv (φ.app _ z).val).val).IsCoCartesian q := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory, range_le_fullEnhancedSubcategory_iff]

/-- When the whole source is prescribed, every extension preserves coCartesian edges if
`a` does. -/
lemma coCartesianFunctors_id_eq_top
    (a : {a : X ⟶ Y // a ≫ q = (𝟙 X) ≫ p})
    (ha : ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
      (e.map a.val).IsCoCartesian q) :
    coCartesianFunctors (𝟙 X) a = ⊤ := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory, ← top_le_iff,
    le_fullEnhancedSubcategory_iff]
  intro v _
  have hv : (ihomOver.obj₀Equiv v.val).val = a.val := by
    simpa using (obj₀Equiv (𝟙 X) a v).property
  intro x y e he
  exact (ha e he).of_edge_eq (congrArg (fun f : X ⟶ Y ↦ f.app _ e.edge) hv.symm)

namespace coCartesianFunctors

/-- Forgetting preservation is an inner fibration. -/
instance innerFibration_ι : InnerFibration (coCartesianFunctors i a).ι := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory]
  infer_instance

/-- Forgetting preservation is fully faithful. -/
instance isFullyFaithful_ι : IsFullyFaithful (coCartesianFunctors i a).ι := by
  rw [coCartesianFunctors_eq_fullEnhancedSubcategory]
  infer_instance

/-- CoCartesian-preserving extensions of a fixed restriction form a quasicategory. -/
instance quasicategory [Mono i] [InnerFibration q] :
    Quasicategory (coCartesianFunctors i a : SSet) :=
  quasicategory_of_innerFibration (coCartesianFunctors i a).ι

/-- Vertices are relative extensions of `a` preserving coCartesian edges. -/
noncomputable def obj₀Equiv :
    (coCartesianFunctors i a : SSet) _⦋0⦌ ≃
      {f : {f : {f : X ⟶ Y // f ≫ q = p} // i ≫ f.val = a.val} //
        ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
          (e.map f.val.val).IsCoCartesian q} :=
  (fixedRestriction.obj₀Equiv i a).subtypeEquiv (fun v ↦ by
    rw [mem_coCartesianFunctors_obj_zero_iff, fixedRestriction.obj₀Equiv_apply_val])

/-- Forgetting preservation in the vertex description gives the fixed-restriction extension. -/
@[simp]
lemma obj₀Equiv_apply_val (v : (coCartesianFunctors i a : SSet) _⦋0⦌) :
    dsimp% (obj₀Equiv i a v).val = fixedRestriction.obj₀Equiv i a v.val :=
  (rfl)

/-- An extension preserving coCartesian edges gives the corresponding preserving vertex. -/
@[simp]
lemma obj₀Equiv_symm_apply_val
    (f : {f : {f : {f : X ⟶ Y // f ≫ q = p} // i ≫ f.val = a.val} //
      ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
        (e.map f.val.val).IsCoCartesian q}) :
    dsimp% ((obj₀Equiv i a).symm f).val = (fixedRestriction.obj₀Equiv i a).symm f.val :=
  (rfl)

/-- Preserving extensions along the identity form a terminal simplicial set when `a` preserves
coCartesian edges. This does not require fibrancy. -/
noncomputable def isTerminalId
    (a : {a : X ⟶ Y // a ≫ q = (𝟙 X) ≫ p})
    (ha : ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
      (e.map a.val).IsCoCartesian q) :
    IsTerminal (coCartesianFunctors (𝟙 X) a : SSet) :=
  (fixedRestriction.isTerminalId a).ofIso
    ((Subcomplex.topIso (fixedRestriction (𝟙 X) a : SSet)).symm ≪≫
      (Subcomplex.eqToIso (coCartesianFunctors_id_eq_top a ha)).symm)

/-- The unique preserving extension forgets to the unique relative extension. -/
@[reassoc (attr := simp)]
lemma isTerminalId_from_ι
    (a : {a : X ⟶ Y // a ≫ q = (𝟙 X) ≫ p})
    (ha : ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), e.IsCoCartesian p →
      (e.map a.val).IsCoCartesian q) (Z : SSet.{u}) :
    (isTerminalId a ha).from Z ≫ (coCartesianFunctors (𝟙 X) a).ι =
      (fixedRestriction.isTerminalId a).from Z :=
  (fixedRestriction.isTerminalId a).hom_ext _ _

end coCartesianFunctors

end fixedRestriction

end SSet.ihomOver
