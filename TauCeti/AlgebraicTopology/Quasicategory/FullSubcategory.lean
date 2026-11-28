/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Full subcategories of quasicategories

Given a predicate `P` on the vertices of a simplicial set `X`, the full enhanced subcategory
`X.fullEnhancedSubcategory P` is the subcomplex of `X` consisting of the simplices all of whose
vertices satisfy `P`. When `X` is a quasicategory, this is the full subcategory of the
`∞`-category `X` spanned by the objects satisfying `P`.

## Main declarations

* `SSet.fullEnhancedSubcategory`: the full enhanced subcategory of `X` on `P`.
* `SSet.mem_fullEnhancedSubcategory_obj_iff_forall_fin`: an `n`-simplex lies in it exactly
  when each of its `n + 1` vertices satisfies `P`.
* `SSet.le_fullEnhancedSubcategory_iff`: it is the largest subcomplex whose vertices satisfy `P`;
  `SSet.range_le_fullEnhancedSubcategory_iff` is the corresponding factorization criterion for
  maps into `X`.
* `SSet.exists_lift_of_forall_boundary`: a map whose lifting problems against boundary inclusions,
  with bottom map in a full enhanced subcategory of the target, all have solutions, restricts over
  that full subcategory to a trivial fibration.
* `SSet.fullEnhancedSubcategory.verticesEquiv`: its vertices are the vertices of `X` satisfying
  `P`.
* `SSet.hasLiftingProperty_fullEnhancedSubcategory_ι`: the inclusion has the right lifting
  property against every map that is surjective on vertices. In particular it is an inner
  fibration, so the full enhanced subcategory of a quasicategory is a quasicategory.
* `CategoryTheory.ObjectProperty.nerveFullSubcategoryIso`: for the nerve of an ordinary
  category, the full enhanced subcategory is the nerve of the full subcategory.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.11.
-/

public section

open CategoryTheory Opposite Simplicial

universe u v

namespace SSet

variable {X : SSet.{u}}

variable (X) in
/-- The full enhanced subcategory of a simplicial set `X` on a predicate `P` on its vertices: the
subcomplex of the simplices all of whose vertices satisfy `P`. -/
def fullEnhancedSubcategory (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj n := {x | ∀ v : ⦋0⦌ ⟶ n.unop, P (X.map v.op x)}
  map f x hx v := by
    simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] using hx (v ≫ f.unop)

variable (P : X _⦋0⦌ → Prop)

/-- A simplex lies in the full enhanced subcategory on `P` exactly when each of its vertices
satisfies `P`. -/
lemma mem_fullEnhancedSubcategory_obj_iff {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    x ∈ (X.fullEnhancedSubcategory P).obj n ↔ ∀ v : ⦋0⦌ ⟶ n.unop, P (X.map v.op x) :=
  Iff.rfl

/-- An `n`-simplex lies in the full enhanced subcategory on `P` exactly when each of its `n + 1`
vertices satisfies `P`. -/
lemma mem_fullEnhancedSubcategory_obj_iff_forall_fin {n : ℕ} (x : X _⦋n⦌) :
    x ∈ (X.fullEnhancedSubcategory P).obj _ ↔
      ∀ i : Fin (n + 1), P (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) := by
  rw [mem_fullEnhancedSubcategory_obj_iff]
  exact ⟨fun h _ ↦ h _, fun h v ↦ SimplexCategory.eq_const_of_zero v ▸ h _⟩

/-- A vertex lies in the full enhanced subcategory on `P` exactly when it satisfies `P`. -/
@[simp]
lemma mem_fullEnhancedSubcategory_obj_zero_iff (x : X _⦋0⦌) :
    x ∈ (X.fullEnhancedSubcategory P).obj (op ⦋0⦌) ↔ P x := by
  simp [mem_fullEnhancedSubcategory_obj_iff_forall_fin]

/-- The full enhanced subcategory on `P` is the largest subcomplex all of whose vertices
satisfy `P`. -/
lemma le_fullEnhancedSubcategory_iff (A : X.Subcomplex) :
    A ≤ X.fullEnhancedSubcategory P ↔ ∀ x ∈ A.obj (op ⦋0⦌), P x := by
  refine ⟨fun h x hx ↦ ?_, fun h n x hx v ↦ h _ (A.map v.op hx)⟩
  simpa using h _ hx

/-- A map of simplicial sets factors through the full enhanced subcategory on `P` exactly when it
sends every vertex to a vertex satisfying `P`. -/
lemma range_le_fullEnhancedSubcategory_iff {Y : SSet.{u}} (f : Y ⟶ X) :
    Subcomplex.range f ≤ X.fullEnhancedSubcategory P ↔ ∀ y : Y _⦋0⦌, P (f.app _ y) := by
  simp [le_fullEnhancedSubcategory_iff]

/-- **Lifting along monomorphisms from lifting along boundaries, over a full subcategory.** Let
`ρ : A ⟶ B` be a map of simplicial sets and `P` a predicate on the vertices of `B`. Suppose that
every lifting problem of `∂Δ[n] ⟶ Δ[n]` against `ρ` whose bottom map `Δ[n] ⟶ B` sends all vertices
into `P` has a solution. Then so does every lifting problem of a monomorphism `i : Y ⟶ Z` against
`ρ` whose bottom map sends all vertices into `P`: the restriction of `ρ` over the full enhanced
subcategory `B.fullEnhancedSubcategory P` is a trivial fibration. -/
theorem exists_lift_of_forall_boundary {A B : SSet.{u}} (ρ : A ⟶ B) (P : B _⦋0⦌ → Prop)
    (hρ : ∀ (n : ℕ) (t : (∂Δ[n] : SSet.{u}) ⟶ A) (b : Δ[n] ⟶ B), t ≫ ρ = ∂Δ[n].ι ≫ b →
      (∀ z : Δ[n] _⦋0⦌, P (b.app _ z)) → ∃ l : Δ[n] ⟶ A, ∂Δ[n].ι ≫ l = t ∧ l ≫ ρ = b)
    {Y Z : SSet.{u}} (i : Y ⟶ Z) [Mono i] (t : Y ⟶ A) (b : Z ⟶ B) (w : t ≫ ρ = i ≫ b)
    (hb : ∀ z : Z _⦋0⦌, P (b.app _ z)) :
    ∃ l : Z ⟶ A, i ≫ l = t ∧ l ≫ ρ = b := by
  let H := B.fullEnhancedSubcategory P
  -- A map lands in the preimage of `H` when its composite with `ρ` lands in `H`.
  have hpre {W : SSet.{u}} (f : W ⟶ A) (hf : Subcomplex.range (f ≫ ρ) ≤ H) :
      Subcomplex.range f ≤ H.preimage ρ := by
    rwa [← Subcomplex.image_le_iff, ← Subcomplex.range_comp]
  -- Restriction of `ρ` over `H` is a trivial fibration: it suffices to lift against boundary
  -- inclusions.
  have hρ' : (MorphismProperty.monomorphisms SSet.{u}).rlp (H.fromPreimage ρ) := by
    rw [rlp_monomorphisms]
    rintro _ _ _ ⟨n⟩
    refine ⟨fun {t b} sq ↦ ?_⟩
    obtain ⟨l, hl₁, hl₂⟩ := hρ n (t ≫ (H.preimage ρ).ι) (b ≫ H.ι)
      (by rw [Category.assoc, ← Subcomplex.fromPreimage_ι, ← Category.assoc, sq.w,
        Category.assoc])
      (fun z ↦ (mem_fullEnhancedSubcategory_obj_zero_iff _ _).1 (b.app _ z).property)
    have hl : Subcomplex.range l ≤ H.preimage ρ := hpre l (by
      rw [hl₂, Subcomplex.range_comp]
      exact (Subcomplex.image_le_range _ _).trans (by simp))
    exact ⟨⟨{ l := Subcomplex.lift l hl
              fac_left := by rw [← cancel_mono (H.preimage ρ).ι, Category.assoc,
                Subcomplex.lift_ι, hl₁]
              fac_right := by rw [← cancel_mono H.ι, Category.assoc,
                Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.lift_ι, hl₂] }⟩⟩
  have hb' : Subcomplex.range b ≤ H := (range_le_fullEnhancedSubcategory_iff _ _).2 hb
  have ht : Subcomplex.range t ≤ H.preimage ρ := hpre t (by
    rw [w, Subcomplex.range_comp]
    exact (Subcomplex.image_le_range _ _).trans hb')
  have sq : CommSq (Subcomplex.lift t ht) i (H.fromPreimage ρ) (Subcomplex.lift b hb') :=
    ⟨by rw [← cancel_mono H.ι, Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc,
      Subcomplex.lift_ι, Category.assoc, Subcomplex.lift_ι, w]⟩
  have := hρ' i (MorphismProperty.monomorphisms.infer_property i)
  refine ⟨sq.lift ≫ (H.preimage ρ).ι, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left, Subcomplex.lift_ι]
  · rw [Category.assoc, ← Subcomplex.fromPreimage_ι, ← Category.assoc, sq.fac_right,
      Subcomplex.lift_ι]

@[gcongr]
lemma fullEnhancedSubcategory_mono {P Q : X _⦋0⦌ → Prop} (h : P ≤ Q) :
    X.fullEnhancedSubcategory P ≤ X.fullEnhancedSubcategory Q :=
  fun _ _ hx v ↦ h _ (hx v)

variable (X) in
/-- The full enhanced subcategory on the predicate that always holds is everything. -/
@[simp]
lemma fullEnhancedSubcategory_top : X.fullEnhancedSubcategory ⊤ = ⊤ :=
  top_le_iff.mp fun _ _ _ _ ↦ trivial

variable (X) in
/-- The full enhanced subcategory on the predicate that never holds is empty. -/
@[simp]
lemma fullEnhancedSubcategory_bot : X.fullEnhancedSubcategory ⊥ = ⊥ :=
  le_bot_iff.mp fun _ _ hx ↦ (hx (SimplexCategory.const _ _ 0)).elim

/-- The vertices of the full enhanced subcategory on `P` are the vertices satisfying `P`. -/
def fullEnhancedSubcategory.verticesEquiv :
    (X.fullEnhancedSubcategory P).obj (op ⦋0⦌) ≃ {x : X _⦋0⦌ // P x} :=
  Equiv.subtypeEquivRight (mem_fullEnhancedSubcategory_obj_zero_iff P)

@[simp]
lemma fullEnhancedSubcategory.verticesEquiv_apply_coe
    (x : (X.fullEnhancedSubcategory P).obj (op ⦋0⦌)) :
    (verticesEquiv P x : X _⦋0⦌) = x.val := by
  simp [verticesEquiv]

@[simp]
lemma fullEnhancedSubcategory.verticesEquiv_symm_apply_coe (x : {x : X _⦋0⦌ // P x}) :
    ((verticesEquiv P).symm x).val = x.val := by
  simp [verticesEquiv]

/-- The inclusion of a full enhanced subcategory has the right lifting property against every
map of simplicial sets that is surjective on vertices. -/
lemma hasLiftingProperty_fullEnhancedSubcategory_ι {A B : SSet.{u}} (i : A ⟶ B)
    (hi : Function.Surjective (i.app (op ⦋0⦌))) :
    HasLiftingProperty i (X.fullEnhancedSubcategory P).ι where
  sq_hasLift {a b} sq := by
    have hb : Subcomplex.range b ≤ X.fullEnhancedSubcategory P := by
      refine (range_le_fullEnhancedSubcategory_iff P b).2 fun y ↦ ?_
      obtain ⟨z, rfl⟩ := hi y
      have hz : b.app _ (i.app _ z) = (a.app _ z).val := congr($(sq.w).app _ z).symm
      exact hz ▸ (mem_fullEnhancedSubcategory_obj_zero_iff P _).mp (a.app _ z).property
    exact ⟨⟨{ l := Subcomplex.lift b hb
              fac_left := by rw [← cancel_mono (Subcomplex.ι _)]; simp [sq.w] }⟩⟩

/-- The inclusion of a full enhanced subcategory is an inner fibration: inner horn inclusions are
surjective on vertices. -/
instance : InnerFibration (X.fullEnhancedSubcategory P).ι where
  mem := by
    rintro _ _ _ ⟨i, -, -⟩
    exact hasLiftingProperty_fullEnhancedSubcategory_ι P _ fun y ↦ ⟨⟨y, by simp⟩, rfl⟩

/-- The full enhanced subcategory of a quasicategory is a quasicategory. -/
instance [Quasicategory X] : Quasicategory (X.fullEnhancedSubcategory P : SSet) :=
  quasicategory_of_innerFibration (X.fullEnhancedSubcategory P).ι

end SSet

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- The nerve of the full subcategory of `C` on `P` is isomorphic to the full enhanced
subcategory of the nerve of `C` on the vertices whose object satisfies `P`. -/
def nerveFullSubcategoryIso :
    nerve P.FullSubcategory ≅
      ((nerve C).fullEnhancedSubcategory fun x ↦ P (nerveEquiv x) : SSet) where
  hom := SSet.Subcomplex.lift (nerveMap P.ι) <|
    (SSet.range_le_fullEnhancedSubcategory_iff _ _).2 fun y ↦ (nerveEquiv y).property
  -- The `k`-th vertex of a simplex `x` of `nerve C` is `x.obj k` definitionally, and lifting a
  -- functor through `P.FullSubcategory` and composing with `P.ι` are mutually inverse on the nose.
  inv :=
    { app _ := ↾fun x ↦ P.lift x.val fun k ↦ x.property (SimplexCategory.const _ _ k)
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Under `nerveFullSubcategoryIso`, the inclusion of the full enhanced subcategory corresponds to
the nerve of the inclusion of the full subcategory. -/
@[reassoc (attr := simp)]
lemma nerveFullSubcategoryIso_hom_ι :
    P.nerveFullSubcategoryIso.hom ≫ SSet.Subcomplex.ι _ = nerveMap P.ι :=
  (rfl)

end CategoryTheory.ObjectProperty
