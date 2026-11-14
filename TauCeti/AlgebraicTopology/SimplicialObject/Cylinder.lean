/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# The cylinder functor on simplicial objects

In any category `C` with finite coproducts, the simplicial cylinder `X × Δ[1]` of a simplicial
object `X : SimplicialObject C` is formed by taking in each simplicial degree `m` the finite
coproduct indexed by all monotone maps `m.unop ⟶ ⦋1⦌` of copies of `X.obj m`. Precomposition on
the indexing morphisms together with `X.map` makes this a functor
`CategoryTheory.SimplicialObject.cylinder C : SimplicialObject C ⥤ SimplicialObject C`, equipped
with two endpoint inclusions `cylinderι₀ C` and `cylinderι₁ C` (corresponding to the constant maps
with values `0` and `1`) and the folding retraction `cylinderπ C`.

Using Joël Riou's enumeration `SimplexCategory.toMk₁` of morphisms `⦋n⦌ ⟶ ⦋1⦌`, any morphism
`Φ : (cylinder C).obj X ⟶ Y` restricting to `f` at `cylinderι₀` and to `g` at `cylinderι₁` yields
a combinatorial simplicial homotopy `Homotopy.ofCylinderHom Φ h₀ h₁ : Homotopy f g`, generalizing
`SSet.Homotopy.toSimplicialObjectHomotopy` from simplicial sets to arbitrary categories with finite
coproducts.

## Main definitions and results

* `CategoryTheory.SimplicialObject.cylinder`: the cylinder endofunctor on `SimplicialObject C`,
  characterized by the universal property of its summand inclusions `cylinderι` and `cylinderDesc`.
* `CategoryTheory.SimplicialObject.cylinderι₀`, `CategoryTheory.SimplicialObject.cylinderι₁`,
  `CategoryTheory.SimplicialObject.cylinderπ`: the two endpoint inclusions into the cylinder and
  their common retraction.
* `CategoryTheory.SimplicialObject.Homotopy.ofCylinderHom`: extracts a combinatorial simplicial
  homotopy `Homotopy f g` from a morphism out of `(cylinder C).obj X` with endpoints `f` and `g`.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, Satz 1.15.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter I, §1 and Chapter III, §2.
-/

public noncomputable section

universe v u

open CategoryTheory Limits Opposite SimplexCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

section Cylinder

variable (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]

/-- The cylinder endofunctor `X ↦ X × Δ[1]` on simplicial objects in a category with finite
coproducts: in degree `m`, it is the finite coproduct of copies of `X.obj m` indexed by morphisms
`m.unop ⟶ ⦋1⦌` in `SimplexCategory`. -/
def cylinder : SimplicialObject C ⥤ SimplicialObject C where
  obj X :=
    { obj m := ∐ fun _ : (m.unop ⟶ ⦋1⦌) ↦ X.obj m
      map θ := Sigma.desc fun α ↦
        X.map θ ≫ Sigma.ι (fun _ : (_ ⟶ ⦋1⦌) ↦ _) (θ.unop ≫ α)
      map_id m := Sigma.hom_ext _ _ fun α ↦ by
        simp
      map_comp θ η := Sigma.hom_ext _ _ fun α ↦ by
        simp [Category.assoc] }
  map f :=
    { app m := Sigma.desc fun α ↦
        f.app m ≫ Sigma.ι (fun _ : (m.unop ⟶ ⦋1⦌) ↦ _) α
      naturality m n θ := Sigma.hom_ext _ _ fun α ↦ by
        dsimp
        simp [NatTrans.naturality_assoc] }
  map_id X := by
    ext m α
    dsimp
    simp
  map_comp f g := by
    ext m α
    dsimp
    simp

variable {C}

/-- The coproduct summand inclusion `X.obj m ⟶ ((cylinder C).obj X).obj m` indexed by a monotone
map `α : m.unop ⟶ ⦋1⦌`. -/
def cylinderι (X : SimplicialObject C) {m : SimplexCategoryᵒᵖ} (α : m.unop ⟶ ⦋1⦌) :
    X.obj m ⟶ ((cylinder C).obj X).obj m :=
  Sigma.ι (fun _ : (m.unop ⟶ ⦋1⦌) ↦ X.obj m) α

/-- Universal morphism out of `((cylinder C).obj X).obj m` determined by its components on each
summand `α : m.unop ⟶ ⦋1⦌`. -/
def cylinderDesc {X : SimplicialObject C} {m : SimplexCategoryᵒᵖ} {Z : C}
    (φ : (m.unop ⟶ ⦋1⦌) → (X.obj m ⟶ Z)) :
    ((cylinder C).obj X).obj m ⟶ Z :=
  Sigma.desc φ

@[reassoc (attr := simp)]
lemma cylinderι_desc {X : SimplicialObject C} {m : SimplexCategoryᵒᵖ} {Z : C}
    (φ : (m.unop ⟶ ⦋1⦌) → (X.obj m ⟶ Z)) (α : m.unop ⟶ ⦋1⦌) :
    cylinderι X α ≫ cylinderDesc φ = φ α :=
  Sigma.ι_comp_desc φ α

/-- Two morphisms out of `((cylinder C).obj X).obj m` are equal when they agree on every summand
inclusion `cylinderι X α`. -/
lemma cylinder_hom_ext {X : SimplicialObject C} {m : SimplexCategoryᵒᵖ} {Z : C}
    {u v : ((cylinder C).obj X).obj m ⟶ Z}
    (h : ∀ α : m.unop ⟶ ⦋1⦌, cylinderι X α ≫ u = cylinderι X α ≫ v) :
    u = v :=
  Sigma.hom_ext _ _ h

@[reassoc (attr := simp)]
lemma cylinderι_map (X : SimplicialObject C) {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n)
    (α : m.unop ⟶ ⦋1⦌) :
    cylinderι X α ≫ ((cylinder C).obj X).map θ = X.map θ ≫ cylinderι X (θ.unop ≫ α) :=
  Sigma.ι_comp_desc _ α

@[reassoc (attr := simp)]
lemma cylinderι_δ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) (α : ⦋n + 1⦌ ⟶ ⦋1⦌) :
    cylinderι X α ≫ ((cylinder C).obj X).δ i = X.δ i ≫ cylinderι X (SimplexCategory.δ i ≫ α) :=
  cylinderι_map X (SimplexCategory.δ i).op α

@[reassoc (attr := simp)]
lemma cylinderι_σ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) (α : ⦋n⦌ ⟶ ⦋1⦌) :
    cylinderι X α ≫ ((cylinder C).obj X).σ i = X.σ i ≫ cylinderι X (SimplexCategory.σ i ≫ α) :=
  cylinderι_map X (SimplexCategory.σ i).op α

@[reassoc (attr := simp)]
lemma cylinderι_cylinder_map {X Y : SimplicialObject C} (f : X ⟶ Y) {m : SimplexCategoryᵒᵖ}
    (α : m.unop ⟶ ⦋1⦌) :
    cylinderι X α ≫ ((cylinder C).map f).app m = f.app m ≫ cylinderι Y α :=
  Sigma.ι_comp_desc _ α

variable (C) in
/-- Inclusion of the `0`-end `X ⟶ (cylinder C).obj X` of the simplicial cylinder, indexed by the
constant map with value `0 : Fin 2`. -/
def cylinderι₀ : 𝟭 (SimplicialObject C) ⟶ cylinder C where
  app X :=
    { app m := cylinderι X (SimplexCategory.const m.unop ⦋1⦌ 0)
      naturality m n θ := by
        simp only [Functor.id_obj, cylinderι_map]
        rfl }
  naturality X Y f := by
    ext m
    simp

@[simp]
lemma cylinderι₀_app_app (X : SimplicialObject C) (m : SimplexCategoryᵒᵖ) :
    ((cylinderι₀ C).app X).app m = cylinderι X (SimplexCategory.const m.unop ⦋1⦌ 0) :=
  (rfl)

variable (C) in
/-- Inclusion of the `1`-end `X ⟶ (cylinder C).obj X` of the simplicial cylinder, indexed by the
constant map with value `1 : Fin 2`. -/
def cylinderι₁ : 𝟭 (SimplicialObject C) ⟶ cylinder C where
  app X :=
    { app m := cylinderι X (SimplexCategory.const m.unop ⦋1⦌ 1)
      naturality m n θ := by
        simp only [Functor.id_obj, cylinderι_map]
        rfl }
  naturality X Y f := by
    ext m
    simp

@[simp]
lemma cylinderι₁_app_app (X : SimplicialObject C) (m : SimplexCategoryᵒᵖ) :
    ((cylinderι₁ C).app X).app m = cylinderι X (SimplexCategory.const m.unop ⦋1⦌ 1) :=
  (rfl)

variable (C) in
/-- The folding projection `(cylinder C).obj X ⟶ X` acting as the identity on each summand. -/
def cylinderπ : cylinder C ⟶ 𝟭 (SimplicialObject C) where
  app X :=
    { app m := cylinderDesc fun _ ↦ 𝟙 (X.obj m)
      naturality m n θ := cylinder_hom_ext fun α ↦ by
        simp }
  naturality X Y f := by
    ext m
    exact cylinder_hom_ext fun α ↦ by simp

@[reassoc (attr := simp)]
lemma cylinderι_cylinderπ_app_app (X : SimplicialObject C) {m : SimplexCategoryᵒᵖ}
    (α : m.unop ⟶ ⦋1⦌) :
    cylinderι X α ≫ ((cylinderπ C).app X).app m = 𝟙 (X.obj m) :=
  cylinderι_desc _ α

@[reassoc (attr := simp)]
lemma cylinderι₀_comp_cylinderπ : cylinderι₀ C ≫ cylinderπ C = 𝟙 (𝟭 (SimplicialObject C)) := by
  ext X m
  simp

@[reassoc (attr := simp)]
lemma cylinderι₁_comp_cylinderπ : cylinderι₁ C ≫ cylinderπ C = 𝟙 (𝟭 (SimplicialObject C)) := by
  ext X m
  simp

namespace Homotopy

/-- A morphism out of the simplicial cylinder `Φ : (cylinder C).obj X ⟶ Y` restricting to `f` at
`cylinderι₀` and to `g` at `cylinderι₁` induces a combinatorial simplicial homotopy
`Homotopy f g`. -/
def ofCylinderHom {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (Φ : (cylinder C).obj X ⟶ Y)
    (h₀ : (cylinderι₀ C).app X ≫ Φ = f) (h₁ : (cylinderι₁ C).app X ≫ Φ = g) :
    Homotopy f g where
  h {n} i := X.σ i ≫ cylinderι X (SimplexCategory.toMk₁ i.succ.castSucc) ≫ Φ.app (op ⦋n + 1⦌)
  h_zero_comp_δ_zero n := by
    rw [Category.assoc, Category.assoc, ← SimplicialObject.δ_naturality Φ, cylinderι_δ_assoc,
      X.δ_comp_σ_self'_assoc (by simp)]
    have hα : SimplexCategory.δ 0 ≫ SimplexCategory.toMk₁ (0 : Fin (n + 1)).succ.castSucc =
        SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
      rw [SimplexCategory.δ_comp_toMk₁_of_lt _ _ (by simp)]
      refine ConcreteCategory.hom_ext _ _ fun k ↦ ?_
      simp [SimplexCategory.toMk₁_apply]
      rfl
    rw [hα, ← cylinderι₁_app_app, ← NatTrans.comp_app, h₁]
  h_last_comp_δ_last n := by
    rw [Category.assoc, Category.assoc, ← SimplicialObject.δ_naturality Φ, cylinderι_δ_assoc,
      X.δ_comp_σ_succ'_assoc (Fin.succ_last n)]
    have hα : SimplexCategory.δ (Fin.last (n + 1)) ≫
          SimplexCategory.toMk₁ (Fin.last n).succ.castSucc =
        SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
      rw [SimplexCategory.δ_comp_toMk₁_of_le _ _ (by simp)]
      refine ConcreteCategory.hom_ext _ _ fun k ↦ ?_
      have hk : k.castSucc < Fin.last (n + 1) := Fin.castSucc_lt_last k
      simp [SimplexCategory.toMk₁_apply, hk]
      rfl
    rw [hα, ← cylinderι₀_app_app, ← NatTrans.comp_app, h₀]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    rw [Category.assoc, Category.assoc, ← SimplicialObject.δ_naturality Φ, cylinderι_δ_assoc,
      X.δ_comp_σ_of_le_assoc hij,
      SimplexCategory.δ_comp_toMk₁_of_lt _ _ (by simp [Fin.lt_def, Fin.le_def] at hij ⊢; lia)]
    congr 4
  h_succ_comp_δ_castSucc_succ j := by
    simp only [Category.assoc, ← SimplicialObject.δ_naturality Φ, cylinderι_δ_assoc]
    rw [X.δ_comp_σ_self'_assoc (by simp), X.δ_comp_σ_succ_assoc,
      SimplexCategory.δ_comp_toMk₁_of_lt _ _ (by simp),
      SimplexCategory.δ_comp_toMk₁_of_le _ _ (by simp)]
    congr 3
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    rw [Category.assoc, Category.assoc, ← SimplicialObject.δ_naturality Φ, cylinderι_δ_assoc,
      X.δ_comp_σ_of_gt_assoc hji,
      SimplexCategory.δ_comp_toMk₁_of_le _ _ (by simp [Fin.lt_def, Fin.le_def] at hji ⊢; lia)]
    congr 4
  h_comp_σ_castSucc_of_le i j hij := by
    rw [Category.assoc, Category.assoc, ← SimplicialObject.σ_naturality Φ, cylinderι_σ_assoc,
      X.σ_comp_σ_assoc hij,
      SimplexCategory.σ_comp_toMk₁_of_lt _ _
        (Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_succ_iff.mpr hij)),
      ← Fin.castSucc_succ j.succ]
  h_comp_σ_succ_of_lt i j hji := by
    rw [Category.assoc, Category.assoc, ← SimplicialObject.σ_naturality Φ, cylinderι_σ_assoc,
      ← X.σ_comp_σ_assoc hji,
      SimplexCategory.σ_comp_toMk₁_of_le _ _
        (Fin.castSucc_le_castSucc_iff.mpr (Fin.succ_le_succ_iff.mpr hji)),
      Fin.castSucc_succ]

@[simp]
lemma ofCylinderHom_h {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (Φ : (cylinder C).obj X ⟶ Y)
    (h₀ : (cylinderι₀ C).app X ≫ Φ = f) (h₁ : (cylinderι₁ C).app X ≫ Φ = g)
    {n : ℕ} (i : Fin (n + 1)) :
    (ofCylinderHom Φ h₀ h₁).h i =
      X.σ i ≫ cylinderι X (SimplexCategory.toMk₁ i.succ.castSucc) ≫ Φ.app (op ⦋n + 1⦌) :=
  (rfl)

end Homotopy

end Cylinder

end CategoryTheory.SimplicialObject
