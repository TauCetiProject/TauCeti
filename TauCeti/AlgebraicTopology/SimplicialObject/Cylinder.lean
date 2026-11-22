/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

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
* `CategoryTheory.SimplicialObject.Homotopy.ofCylinderHom`,
  `CategoryTheory.SimplicialObject.Homotopy.toCylinderHom`,
  `CategoryTheory.SimplicialObject.Homotopy.cylinderHomEquiv`: equivalence between combinatorial
  simplicial homotopies `Homotopy f g` and morphisms `(cylinder C).obj X ⟶ Y` with endpoints `f`
  and `g`.

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

private lemma const_zero_eq_toMk₁_last (Δ : SimplexCategory) :
    SimplexCategory.const Δ ⦋1⦌ 0 = SimplexCategory.toMk₁ (Fin.last (Δ.len + 1)) := by
  refine ConcreteCategory.hom_ext _ _ fun k ↦ ?_
  have hk : k.castSucc < Fin.last (Δ.len + 1) := Fin.castSucc_lt_last k
  simp [SimplexCategory.toMk₁_apply, hk]
  rfl

private lemma const_one_eq_toMk₁_zero (Δ : SimplexCategory) :
    SimplexCategory.const Δ ⦋1⦌ 1 = SimplexCategory.toMk₁ (0 : Fin (Δ.len + 2)) := by
  refine ConcreteCategory.hom_ext _ _ fun k ↦ ?_
  simp [SimplexCategory.toMk₁_apply]
  rfl

omit [HasFiniteCoproducts C] in
private def toCylinderHomTerm {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g)
    (n : ℕ) (k : Fin (n + 2)) : X _⦋n⦌ ⟶ Y _⦋n⦌ :=
  Fin.cases (g.app (op ⦋n⦌)) (fun j ↦ H.h j ≫ Y.δ j.succ) k

omit [HasFiniteCoproducts C] in
private lemma toCylinderHomTerm_δ {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g)
    {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 3)) :
    X.δ i ≫ toCylinderHomTerm H n
        (SimplexCategory.toMk₁Equiv.symm (SimplexCategory.δ i ≫ SimplexCategory.toMk₁ k)) =
      toCylinderHomTerm H (n + 1) k ≫ Y.δ i := by
  by_cases hki : k ≤ i.castSucc
  · rw [SimplexCategory.δ_comp_toMk₁_of_le k i hki, ← SimplexCategory.toMk₁Equiv_apply,
      Equiv.symm_apply_apply]
    cases k using Fin.cases with
    | zero => simp [toCylinderHomTerm]
    | succ j =>
      have hj_lt : (j : ℕ) < i := Nat.lt_of_succ_le hki
      have hj_ne_last : j ≠ Fin.last (n + 1) := by
        intro h; rw [h, Fin.val_last] at hj_lt; omega
      let j' : Fin (n + 1) := j.castPred hj_ne_last
      have hj' : j = j'.castSucc := (Fin.castSucc_castPred j hj_ne_last).symm
      have hj'_lt_i : j'.castSucc < i := Fin.lt_def.mpr (by simpa [j'] using hj_lt)
      have hk_pred :
          (j.succ).castPred (Fin.ne_last_of_lt (lt_of_le_of_lt hki i.castSucc_lt_succ)) =
            j'.succ :=
        Fin.ext (by simp [j'])
      rw [hk_pred]
      simp only [toCylinderHomTerm, Fin.cases_succ]
      rw [← Category.assoc, ← H.h_castSucc_comp_δ_succ_of_lt i j' hj'_lt_i, ← hj']
      have hij : j'.succ ≤ i := Fin.le_def.mpr (by
        have h : (j' : ℕ) < i := Fin.lt_def.mp hj'_lt_i
        simp only [Fin.val_succ]; omega)
      have hδ : Y.δ i.succ ≫ Y.δ j'.succ = Y.δ j'.castSucc.succ ≫ Y.δ i := by
        simpa [Fin.castSucc_succ] using Y.δ_comp_δ hij
      rw [Category.assoc, hδ, ← Category.assoc, hj']
  · simp only [not_le] at hki
    rw [SimplexCategory.δ_comp_toMk₁_of_lt k i hki, ← SimplexCategory.toMk₁Equiv_apply,
      Equiv.symm_apply_apply]
    cases k using Fin.cases with
    | zero => exact absurd hki (Fin.not_lt_zero _)
    | succ j =>
      simp only [Fin.pred_succ, toCylinderHomTerm, Fin.cases_succ]
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero]
        have hi0 : i = 0 := Fin.ext (by
          rcases i with ⟨_ | _, _⟩ <;> simp_all [Fin.lt_def])
        subst hi0
        have hδ : Y.δ 1 ≫ Y.δ (0 : Fin (n + 2)) = Y.δ 0 ≫ Y.δ 0 := by
          simpa using Y.δ_comp_δ (i := (0 : Fin (n + 2))) (j := 0) le_rfl
        rw [Fin.succ_zero_eq_one, Category.assoc, hδ, ← Category.assoc, H.h_zero_comp_δ_zero]
        simp
      | succ j' =>
        simp only [Fin.cases_succ]
        rcases le_or_gt i j'.castSucc with hij | hji
        · rw [← Category.assoc, ← H.h_succ_comp_δ_castSucc_of_lt i j' hij]
          have hij' : i ≤ j'.succ := le_trans hij (Fin.castSucc_le_succ _)
          have hδ : Y.δ i.castSucc ≫ Y.δ j'.succ = Y.δ j'.succ.succ ≫ Y.δ i := by
            simpa using (Y.δ_comp_δ hij').symm
          rw [Category.assoc, hδ, ← Category.assoc]
        · have hij : i = j'.succ := Fin.ext (by
            have h1 : (i : ℕ) < j'.val + 2 := by simpa [Fin.lt_def] using hki
            have h2 : j'.val < (i : ℕ) := by simpa [Fin.lt_def] using hji
            simp only [Fin.val_succ]; omega)
          subst hij
          rw [← Category.assoc,
            ← H.h_castSucc_comp_δ_succ_of_lt j'.succ j' Fin.castSucc_lt_succ]
          have hδ1 : Y.δ j'.succ.succ ≫ Y.δ j'.succ = Y.δ j'.castSucc.succ ≫ Y.δ j'.succ := by
            simpa [Fin.castSucc_succ] using Y.δ_comp_δ (i := j'.succ) (j := j'.succ) le_rfl
          rw [Category.assoc, hδ1, ← Category.assoc, ← H.h_succ_comp_δ_castSucc_succ,
            Category.assoc]
          have hδ2 : Y.δ j'.castSucc.succ ≫ Y.δ j'.succ = Y.δ j'.succ.succ ≫ Y.δ j'.succ := by
            simpa [Fin.castSucc_succ] using
              (Y.δ_comp_δ (i := j'.succ) (j := j'.succ) le_rfl).symm
          rw [hδ2, ← Category.assoc]

omit [HasFiniteCoproducts C] in
private lemma toCylinderHomTerm_σ {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g)
    {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) :
    X.σ i ≫ toCylinderHomTerm H (n + 1)
        (SimplexCategory.toMk₁Equiv.symm (SimplexCategory.σ i ≫ SimplexCategory.toMk₁ k)) =
      toCylinderHomTerm H n k ≫ Y.σ i := by
  by_cases hki : k ≤ i.castSucc
  · rw [SimplexCategory.σ_comp_toMk₁_of_le k i hki, ← SimplexCategory.toMk₁Equiv_apply,
      Equiv.symm_apply_apply]
    cases k using Fin.cases with
    | zero => simp [toCylinderHomTerm]
    | succ j =>
      have hji : j ≤ i := Fin.le_def.mpr (by
        have h : (j : ℕ) + 1 ≤ i := by simpa [Fin.le_def] using hki
        omega)
      simp only [Fin.castSucc_succ, toCylinderHomTerm, Fin.cases_succ]
      rw [← Category.assoc, ← H.h_comp_σ_succ_of_lt i j hji]
      have hj_le : j.succ ≤ i.castSucc := Fin.le_def.mpr hki
      have hσ : Y.σ i.succ ≫ Y.δ j.castSucc.succ = Y.δ j.succ ≫ Y.σ i := by
        simpa [Fin.castSucc_succ] using Y.δ_comp_σ_of_le (j := i) (i := j.succ) hj_le
      rw [Category.assoc, hσ, ← Category.assoc]
  · simp only [not_le] at hki
    rw [SimplexCategory.σ_comp_toMk₁_of_lt k i hki, ← SimplexCategory.toMk₁Equiv_apply,
      Equiv.symm_apply_apply]
    cases k using Fin.cases with
    | zero => exact absurd hki (Fin.not_lt_zero _)
    | succ j =>
      have hij : i ≤ j := Fin.le_def.mpr (Nat.lt_succ_iff.mp hki)
      simp only [toCylinderHomTerm, Fin.cases_succ]
      rw [← Category.assoc, ← H.h_comp_σ_castSucc_of_le i j hij]
      have hij' : i.castSucc < j.succ := Fin.lt_def.mpr (Nat.lt_succ_of_le hij)
      have hσ : Y.σ i.castSucc ≫ Y.δ j.succ.succ = Y.δ j.succ ≫ Y.σ i := by
        simpa using Y.δ_comp_σ_of_gt (j := i) (i := j.succ) hij'
      rw [Category.assoc, hσ, ← Category.assoc]

/-- Conversely, any combinatorial simplicial homotopy `H : Homotopy f g` assembles into a morphism
`(cylinder C).obj X ⟶ Y` restricting to `f` at `cylinderι₀` and to `g` at `cylinderι₁`. -/
def toCylinderHom {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g) :
    (cylinder C).obj X ⟶ Y where
  app Δ := cylinderDesc fun α ↦
    toCylinderHomTerm H Δ.unop.len (SimplexCategory.toMk₁Equiv.symm α)
  naturality _ _ θ := by
    let app : ∀ Δ : SimplexCategoryᵒᵖ, ((cylinder C).obj X).obj Δ ⟶ Y.obj Δ :=
      fun Δ ↦ cylinderDesc fun α ↦
        toCylinderHomTerm H Δ.unop.len (SimplexCategory.toMk₁Equiv.symm α)
    let W : MorphismProperty SimplexCategoryᵒᵖ := MorphismProperty.naturalityProperty app
    have hW : W.unop = ⊤ :=
      SimplexCategory.morphismProperty_eq_top W.unop
        (fun {n} i ↦ cylinder_hom_ext fun α ↦ by
          obtain ⟨k, rfl⟩ := SimplexCategory.toMk₁Equiv.surjective α
          change cylinderι X (SimplexCategory.toMk₁Equiv k) ≫
              ((cylinder C).obj X).δ i ≫
                cylinderDesc (fun α ↦ toCylinderHomTerm H n (SimplexCategory.toMk₁Equiv.symm α)) =
            cylinderι X (SimplexCategory.toMk₁Equiv k) ≫
              cylinderDesc (fun α ↦
                toCylinderHomTerm H (n + 1) (SimplexCategory.toMk₁Equiv.symm α)) ≫ Y.δ i
          simp only [cylinderι_δ_assoc, cylinderι_desc, cylinderι_desc_assoc]
          rw [Equiv.symm_apply_apply, SimplexCategory.toMk₁Equiv_apply]
          exact toCylinderHomTerm_δ H i k)
        (fun {n} i ↦ cylinder_hom_ext fun α ↦ by
          obtain ⟨k, rfl⟩ := SimplexCategory.toMk₁Equiv.surjective α
          change cylinderι X (SimplexCategory.toMk₁Equiv k) ≫
              ((cylinder C).obj X).σ i ≫
                cylinderDesc (fun α ↦
                  toCylinderHomTerm H (n + 1) (SimplexCategory.toMk₁Equiv.symm α)) =
            cylinderι X (SimplexCategory.toMk₁Equiv k) ≫
              cylinderDesc (fun α ↦ toCylinderHomTerm H n (SimplexCategory.toMk₁Equiv.symm α)) ≫
                Y.σ i
          simp only [cylinderι_σ_assoc, cylinderι_desc, cylinderι_desc_assoc]
          rw [Equiv.symm_apply_apply, SimplexCategory.toMk₁Equiv_apply]
          exact toCylinderHomTerm_σ H i k)
    exact MorphismProperty.of_eq_top hW θ.unop

/-- Restricting `H.toCylinderHom` along the `0`-end inclusion recovers `f`. -/
@[reassoc (attr := simp)]
lemma cylinderι₀_comp_toCylinderHom {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g) :
    (cylinderι₀ C).app X ≫ H.toCylinderHom = f := by
  ext Δ
  obtain ⟨Δ⟩ := Δ
  induction Δ using SimplexCategory.rec with | _ n
  simp only [NatTrans.comp_app, cylinderι₀_app_app, toCylinderHom, cylinderι_desc,
    const_zero_eq_toMk₁_last, ← SimplexCategory.toMk₁Equiv_apply, Equiv.symm_apply_apply]
  rw [← Fin.succ_last, toCylinderHomTerm, Fin.cases_succ, Fin.succ_last, H.h_last_comp_δ_last]

/-- Restricting `H.toCylinderHom` along the `1`-end inclusion recovers `g`. -/
@[reassoc (attr := simp)]
lemma cylinderι₁_comp_toCylinderHom {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g) :
    (cylinderι₁ C).app X ≫ H.toCylinderHom = g := by
  ext Δ
  obtain ⟨Δ⟩ := Δ
  induction Δ using SimplexCategory.rec with | _ n
  simp only [NatTrans.comp_app, cylinderι₁_app_app, toCylinderHom, cylinderι_desc,
    const_one_eq_toMk₁_zero, ← SimplexCategory.toMk₁Equiv_apply, Equiv.symm_apply_apply,
    toCylinderHomTerm, Fin.cases_zero]

/-- Extracting the homotopy of `H.toCylinderHom` recovers `H`. -/
@[simp]
lemma ofCylinderHom_toCylinderHom {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g) :
    ofCylinderHom H.toCylinderHom (cylinderι₀_comp_toCylinderHom H)
      (cylinderι₁_comp_toCylinderHom H) = H := by
  ext n i
  simp only [ofCylinderHom_h, toCylinderHom, cylinderι_desc, ← SimplexCategory.toMk₁Equiv_apply,
    Equiv.symm_apply_apply]
  rw [Fin.castSucc_succ i, toCylinderHomTerm, Fin.cases_succ, ← Category.assoc,
    ← H.h_comp_σ_succ_of_lt i i le_rfl, Category.assoc]
  have hδ : Y.σ i.succ ≫ Y.δ i.castSucc.succ = 𝟙 _ := by
    simpa [Fin.castSucc_succ] using Y.δ_comp_σ_self (i := i.succ)
  rw [hδ, Category.comp_id]

/-- Reassembling the cylinder map from `ofCylinderHom Φ h₀ h₁` recovers `Φ`. -/
@[simp]
lemma toCylinderHom_ofCylinderHom {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (Φ : (cylinder C).obj X ⟶ Y)
    (h₀ : (cylinderι₀ C).app X ≫ Φ = f) (h₁ : (cylinderι₁ C).app X ≫ Φ = g) :
    (ofCylinderHom Φ h₀ h₁).toCylinderHom = Φ := by
  ext Δ
  obtain ⟨Δ⟩ := Δ
  induction Δ using SimplexCategory.rec with | _ n
  refine cylinder_hom_ext fun α ↦ ?_
  obtain ⟨k, rfl⟩ := SimplexCategory.toMk₁Equiv.surjective α
  simp only [toCylinderHom, cylinderι_desc, Equiv.symm_apply_apply]
  cases k using Fin.cases with
  | zero =>
    rw [toCylinderHomTerm, Fin.cases_zero, ← h₁, NatTrans.comp_app, cylinderι₁_app_app,
      const_one_eq_toMk₁_zero, SimplexCategory.toMk₁Equiv_apply]
  | succ j =>
    simp only [toCylinderHomTerm, Fin.cases_succ, ofCylinderHom_h]
    rw [Category.assoc, Category.assoc, ← SimplicialObject.δ_naturality Φ, cylinderι_δ_assoc,
      X.δ_comp_σ_succ_assoc, SimplexCategory.toMk₁Equiv_apply,
      SimplexCategory.δ_comp_toMk₁_of_le _ _ (by simp)]
    have hpred : (j.succ.castSucc).castPred
        (Fin.ne_last_of_lt (lt_of_le_of_lt le_rfl j.succ.castSucc_lt_succ)) = j.succ :=
      Fin.ext (by simp)
    rw [hpred]

/-- Combinatorial simplicial homotopies `Homotopy f g` are in bijection with morphisms out of the
simplicial cylinder `(cylinder C).obj X ⟶ Y` restricting to `f` at `cylinderι₀` and `g` at
`cylinderι₁`. -/
def cylinderHomEquiv {X Y : SimplicialObject C} (f g : X ⟶ Y) :
    Homotopy f g ≃
      { Φ : (cylinder C).obj X ⟶ Y //
        (cylinderι₀ C).app X ≫ Φ = f ∧ (cylinderι₁ C).app X ≫ Φ = g } where
  toFun H := ⟨H.toCylinderHom, cylinderι₀_comp_toCylinderHom H, cylinderι₁_comp_toCylinderHom H⟩
  invFun Φ := ofCylinderHom Φ.val Φ.property.left Φ.property.right
  left_inv H := ofCylinderHom_toCylinderHom H
  right_inv Φ := Subtype.ext (toCylinderHom_ofCylinderHom Φ.val Φ.property.left Φ.property.right)

@[simp]
lemma cylinderHomEquiv_apply {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : Homotopy f g) :
    (cylinderHomEquiv f g H).val = H.toCylinderHom := (rfl)

@[simp]
lemma cylinderHomEquiv_symm_apply {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (Φ : { Φ : (cylinder C).obj X ⟶ Y //
      (cylinderι₀ C).app X ≫ Φ = f ∧ (cylinderι₁ C).app X ≫ Φ = g }) :
    (cylinderHomEquiv f g).symm Φ = ofCylinderHom Φ.val Φ.property.left Φ.property.right := (rfl)

end Homotopy

end Cylinder

end CategoryTheory.SimplicialObject
