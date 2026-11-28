/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# Equational flatness of modules over preadditive categories

A finite relation in a contravariant additive functor is trivial if its elements
are combinations of a new family of elements with coefficients annihilating the
original row of morphisms. Flatness means that every finite relation is trivial.
This is the condition in Oberst and Röhrl, *Flat and coherent functors*,
Theorem 3.2 (4), for abelian-group-valued functors. Its formulation requires
no smallness hypothesis and allows the value and morphism universes to differ.

Representable modules are flat. A finite system of relations in a flat module
can be trivialized using a common family of elements and coefficients.
Flatness is an object property containing zero and stable under retracts.
-/

public section

universe w v u

open CategoryTheory Limits Opposite BigOperators
open scoped ZeroObject

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A finite relation is trivial when the elements `y j` are combinations of a family `z i`
through a matrix of morphisms whose composite with the relation row `β` is zero. -/
def IsTrivialRelation (F : ModCat.{w} C) {X : C} {n : ℕ} {Y : Fin n → C}
    (β : ∀ j, X ⟶ Y j) (y : ∀ j, F.obj.obj (op (Y j))) : Prop :=
  ∃ (m : ℕ) (Z : Fin m → C) (z : ∀ i, F.obj.obj (op (Z i))) (α : ∀ i j, Y j ⟶ Z i),
    (∀ j, y j = ∑ i, F.obj.map (α i j).op (z i)) ∧ ∀ i, ∑ j, β j ≫ α i j = 0

/-- The witnesses to a trivial relation are new elements and a matrix annihilating its row of
morphisms. -/
theorem isTrivialRelation_def {F : ModCat.{w} C} {X : C} {n : ℕ} {Y : Fin n → C}
    {β : ∀ j, X ⟶ Y j} {y : ∀ j, F.obj.obj (op (Y j))} :
    F.IsTrivialRelation β y ↔
      ∃ (m : ℕ) (Z : Fin m → C) (z : ∀ i, F.obj.obj (op (Z i))) (α : ∀ i j, Y j ⟶ Z i),
        (∀ j, y j = ∑ i, F.obj.map (α i j).op (z i)) ∧ ∀ i, ∑ j, β j ≫ α i j = 0 :=
  Iff.rfl

/-- A module over a preadditive category is flat if every finite relation is trivial. -/
class Flat (F : ModCat.{w} C) : Prop where
  isTrivialRelation ⦃X : C⦄ ⦃n : ℕ⦄ ⦃Y : Fin n → C⦄ (β : ∀ j, X ⟶ Y j)
    (y : ∀ j, F.obj.obj (op (Y j))) :
    ∑ j, F.obj.map (β j).op (y j) = 0 → F.IsTrivialRelation β y

variable {F : ModCat.{w} C}

/-- Evaluating a module morphism on a relation sum commutes with forming the sum. -/
theorem map_relation_sum {G : ModCat.{w} C} (f : F ⟶ G) {X : C} {ι : Type*} [Fintype ι]
    {Y : ι → C} (β : ∀ j, X ⟶ Y j) (y : ∀ j, F.obj.obj (op (Y j))) :
    f.hom.app (op X) (∑ j, F.obj.map (β j).op (y j)) =
      ∑ j, G.obj.map (β j).op (f.hom.app (op (Y j)) (y j)) := by
  simp only [map_sum, f.hom.naturality_apply]

/-- A module morphism sends a trivial relation to a trivial relation with the same
coefficient matrix. -/
theorem IsTrivialRelation.map {F G : ModCat.{w} C} {X : C} {n : ℕ} {Y : Fin n → C}
    {β : ∀ j, X ⟶ Y j} {y : ∀ j, F.obj.obj (op (Y j))}
    (h : F.IsTrivialRelation β y) (f : F ⟶ G) :
    G.IsTrivialRelation β (fun j ↦ f.hom.app (op (Y j)) (y j)) := by
  obtain ⟨m, Z, z, α, hy, hα⟩ := isTrivialRelation_def.mp h
  refine isTrivialRelation_def.mpr ⟨m, Z, fun i ↦ f.hom.app (op (Z i)) (z i), α, ?_, hα⟩
  intro j
  rw [← map_relation_sum, hy j]

/-- The pointwise sum of two trivial relations for the same row is trivial. -/
theorem IsTrivialRelation.add {X : C} {n : ℕ} {Y : Fin n → C}
    {β : ∀ j, X ⟶ Y j} {y y' : ∀ j, F.obj.obj (op (Y j))}
    (h : F.IsTrivialRelation β y) (h' : F.IsTrivialRelation β y') :
    F.IsTrivialRelation β (fun j ↦ y j + y' j) := by
  obtain ⟨m, Z, z, α, hy, hα⟩ := isTrivialRelation_def.mp h
  obtain ⟨m', Z', z', α', hy', hα'⟩ := isTrivialRelation_def.mp h'
  let W : Fin m ⊕ Fin m' → C := Sum.elim Z Z'
  let t : ∀ i, F.obj.obj (op (W i)) := Sum.rec z z'
  let γ : ∀ i j, Y j ⟶ W i := Sum.rec α α'
  have ha : ∀ i : Fin m ⊕ Fin m', ∑ j, β j ≫ γ i j = 0
    | .inl i => hα i
    | .inr i => hα' i
  have hs (j : Fin n) : y j + y' j = ∑ i, F.obj.map (γ i j).op (t i) := by
    rw [Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) (hy j) (hy' j)
  let e : Fin (m + m') ≃ Fin m ⊕ Fin m' := finSumFinEquiv.symm
  refine isTrivialRelation_def.mpr
    ⟨m + m', W ∘ e, fun i ↦ t (e i), fun i ↦ γ (e i), fun j ↦ (hs j).trans ?_, fun i ↦ ha (e i)⟩
  exact (e.sum_comp fun i ↦ F.obj.map (γ i j).op (t i)).symm

/-- A retract of a flat module is flat. -/
theorem Flat.of_retract {F G : ModCat.{w} C} [G.Flat] (e : Retract F G) : F.Flat where
  isTrivialRelation {X n Y} β y h := by
    have hG : ∑ j, G.obj.map (β j).op (e.i.hom.app (op (Y j)) (y j)) = 0 := by
      rw [← map_relation_sum, h, map_zero]
    have hFG (j : Fin n) :
        e.r.hom.app (op (Y j)) (e.i.hom.app (op (Y j)) (y j)) = y j := by
      simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        ConcreteCategory.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
        ConcreteCategory.id_apply] using
        congrArg (fun f : F ⟶ F ↦ f.hom.app (op (Y j)) (y j)) e.retract
    simpa only [hFG] using (Flat.isTrivialRelation β _ hG).map e.r

/-- An isomorphism transports flatness from its source to its target. -/
theorem Flat.of_iso [F.Flat] {G : ModCat.{w} C} (e : F ≅ G) : G.Flat :=
  Flat.of_retract e.symm.retract

/-- Flatness is invariant under isomorphism. -/
theorem flat_iff_of_iso {G : ModCat.{w} C} (e : F ≅ G) : F.Flat ↔ G.Flat :=
  ⟨fun _ ↦ Flat.of_iso e, fun _ ↦ Flat.of_iso e.symm⟩

/-- A zero module is flat. -/
theorem Flat.of_isZero (hF : IsZero F) : F.Flat where
  isTrivialRelation {X n Y} β y _ := by
    refine isTrivialRelation_def.mpr
      ⟨0, Fin.elim0, (fun i ↦ i.elim0), (fun i ↦ i.elim0), ?_, fun i ↦ i.elim0⟩
    intro j
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    simpa only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ConcreteCategory.id_apply,
      ObjectProperty.zero_hom, NatTrans.app_zero, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using
      congrArg (fun f : F ⟶ F ↦ f.hom.app (op (Y j)) (y j)) ((IsZero.iff_id_eq_zero F).mp hF)

/-- Flatness as an object property on the category of modules. -/
abbrev flat (C : Type u) [Category.{v} C] [Preadditive C] : ObjectProperty (ModCat.{w} C) :=
  Flat

instance : (flat.{w} C).IsStableUnderRetracts where
  of_retract e h := by
    have : Flat _ := h
    exact Flat.of_retract e

instance : (flat.{w} C).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, Flat.of_isZero (isZero_zero _)⟩

private theorem sum_map_sum_map {X : C} {n m : ℕ} {Y : Fin n → C} {Z : Fin m → C}
    (β : ∀ j, X ⟶ Y j) (α : ∀ i j, Y j ⟶ Z i) (z : ∀ i, F.obj.obj (op (Z i))) :
    ∑ j, F.obj.map (β j).op (∑ i, F.obj.map (α i j).op (z i)) =
      ∑ i, F.obj.map (∑ j, β j ≫ α i j).op (z i) := by
  have := (additiveFunctor_iff F.obj).1 F.property
  simp only [map_sum, op_sum, Functor.map_sum, op_comp, Functor.map_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (map_sum ((AddMonoidHom.eval (z i)).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom)
    (fun j ↦ F.obj.map (α i j).op ≫ F.obj.map (β j).op) Finset.univ).symm

/-- The equation of a trivial relation holds. -/
theorem IsTrivialRelation.sum_eq_zero {X : C} {n : ℕ} {Y : Fin n → C} {β : ∀ j, X ⟶ Y j}
    {y : ∀ j, F.obj.obj (op (Y j))} (h : F.IsTrivialRelation β y) :
    ∑ j, F.obj.map (β j).op (y j) = 0 := by
  obtain ⟨m, Z, z, α, hy, hα⟩ := isTrivialRelation_def.mp h
  have := (additiveFunctor_iff F.obj).1 F.property
  simp only [hy, sum_map_sum_map]
  simp [hα]

/-- A representable module is flat, with the identity of the representing object as the
single witness element for every relation. -/
instance flat_yoneda_obj (Z : C) : Flat ((yoneda C).obj Z) where
  isTrivialRelation {X n Y} β y h := by
    refine isTrivialRelation_def.mpr ⟨1, fun _ ↦ Z, fun _ ↦ 𝟙 Z, fun _ j ↦ y j, ?_, ?_⟩
    · intro j
      rw [Fin.sum_univ_one]
      -- The carrier of a representable is definitionally a hom group. Writing the
      -- equation in that group lets the identity law see the composition.
      change y j = y j ≫ 𝟙 Z
      exact (Category.comp_id _).symm
    · intro _
      exact h

/-- In a flat module, finitely many relations on the same family of elements admit a common
trivialization. The same matrix kills every row of the system. -/
theorem Flat.exists_factorization_of_sum_eq_zero [F.Flat] {m n : ℕ} {X : Fin m → C}
    {Y : Fin n → C} (β : ∀ s j, X s ⟶ Y j) (y : ∀ j, F.obj.obj (op (Y j)))
    (h : ∀ s, ∑ j, F.obj.map (β s j).op (y j) = 0) :
    ∃ (k : ℕ) (Z : Fin k → C) (z : ∀ i, F.obj.obj (op (Z i))) (α : ∀ i j, Y j ⟶ Z i),
      (∀ j, y j = ∑ i, F.obj.map (α i j).op (z i)) ∧ ∀ s i, ∑ j, β s j ≫ α i j = 0 := by
  induction m generalizing n with
  | zero =>
    classical
    refine ⟨n, Y, y, fun i j ↦ if hij : j = i then eqToHom (congrArg Y hij) else 0, ?_, ?_⟩
    · intro j
      have := (additiveFunctor_iff F.obj).1 F.property
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        simp [Ne.symm hi]
      · simp
    · intro s
      exact s.elim0
  | succ m ih =>
    obtain ⟨k, Z, z, α, hy, hα⟩ :=
      isTrivialRelation_def.mp (Flat.isTrivialRelation (β 0) y (h 0))
    let γ (s : Fin m) (i : Fin k) : X s.succ ⟶ Z i := ∑ j, β s.succ j ≫ α i j
    have hγ (s : Fin m) : ∑ i, F.obj.map (γ s i).op (z i) = 0 :=
      (sum_map_sum_map (β s.succ) α z).symm.trans (by simpa only [← hy] using h s.succ)
    obtain ⟨l, W, t, δ, hz, hδ⟩ := ih γ z hγ
    refine ⟨l, W, t, fun a j ↦ ∑ i, α i j ≫ δ a i, ?_, ?_⟩
    · intro j
      rw [hy j]
      simpa only [← hz] using sum_map_sum_map (α · j) δ t
    · intro s a
      have hcomp : (∑ j, β s j ≫ ∑ i, α i j ≫ δ a i) =
          ∑ i, (∑ j, β s j ≫ α i j) ≫ δ a i := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        exact Finset.sum_comm
      rw [hcomp]
      refine Fin.cases ?_ (fun r ↦ hδ r a) s
      simp [hα]

end TauCeti.ModCat
