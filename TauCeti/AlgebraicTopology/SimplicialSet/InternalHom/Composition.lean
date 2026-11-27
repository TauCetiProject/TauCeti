/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom.Basic

/-!
# Composition of functors over a base

Relative internal homs have the composition and units induced by Mathlib's cartesian
closed enrichment. For two families with the same parameter, composition evaluates both
families at that parameter. Evaluation on a fibre gives a family of maps between fibres.
These constructions include all higher simplices, rather than only individual functors.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  Opposite Simplicial

universe u

namespace SSet.ihomOver

variable {B X Y Z W P : SSet.{u}} {p : X ⟶ B} {q : Y ⟶ B} {r : Z ⟶ B} {s : W ⟶ B}

/-- Compose families over the base, holding their common parameter fixed. -/
def compHom (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q) : P ⟶ ihomOver r p :=
  homEquiv.symm ⟨lift (homEquiv f).val (snd X P) ≫ (homEquiv g).val, by
    simp [Category.assoc, (homEquiv g).property, (homEquiv f).property]⟩

/-- The uncurried composite evaluates the first family and then the second, at the same
parameter. -/
@[simp]
lemma homEquiv_compHom_coe (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q) :
    (homEquiv (compHom f g)).val =
      lift (homEquiv f).val (snd X P) ≫ (homEquiv g).val := by
  simp [compHom]

/-- Relative composition is the restriction of simplicial composition. -/
@[reassoc (attr := simp)]
lemma compHom_ι (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q) :
    compHom f g ≫ (ihomOver r p).ι =
      lift (f ≫ (ihomOver q p).ι) (g ≫ (ihomOver r q).ι) ≫ MonoidalClosed.comp X Y Z := by
  apply uncurry_injective
  rw [← homEquiv_apply_coe, homEquiv_compHom_coe, uncurry_lift_comp,
    homEquiv_apply_coe, homEquiv_apply_coe]

/-- Composition of relative families is natural in the parameter. -/
@[simp]
lemma comp_compHom {P' : SSet.{u}} (a : P' ⟶ P)
    (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q) :
    a ≫ compHom f g = compHom (a ≫ f) (a ≫ g) := by
  rw [← cancel_mono (ihomOver r p).ι]
  simp [comp_lift_assoc]

/-- Associativity for families with a common parameter. -/
lemma compHom_assoc (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q)
    (h : P ⟶ ihomOver s r) : compHom (compHom f g) h = compHom f (compHom g h) := by
  apply homEquiv.injective
  apply Subtype.ext
  simp [homEquiv_compHom_coe, comp_lift_assoc]

/-- At each parameter vertex, composition of families is composition of functors.
Use this as an explicit rewrite in relative vertex coordinates. -/
lemma obj₀Equiv_compHom_app_coe (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q)
    (a : P _⦋0⦌) :
    (obj₀Equiv ((compHom f g).app _ a)).val =
      (obj₀Equiv (f.app _ a)).val ≫ (obj₀Equiv (g.app _ a)).val := by
  -- The subcomplex inclusion evaluates by forgetting the membership proof.
  have hf : (obj₀Equiv (f.app _ a)).val =
      lift (𝟙 X) (const a) ≫ uncurry (f ≫ (ihomOver q p).ι) := by
    rw [obj₀Equiv_apply_coe]
    exact ihomObj₀Equiv_app (f ≫ (ihomOver q p).ι) a
  have hg : (obj₀Equiv (g.app _ a)).val =
      lift (𝟙 Y) (const a) ≫ uncurry (g ≫ (ihomOver r q).ι) := by
    rw [obj₀Equiv_apply_coe]
    exact ihomObj₀Equiv_app (g ≫ (ihomOver r q).ι) a
  calc
    _ = lift (𝟙 X) (const a) ≫ uncurry (compHom f g ≫ (ihomOver r p).ι) := by
      rw [obj₀Equiv_apply_coe]
      exact ihomObj₀Equiv_app (compHom f g ≫ (ihomOver r p).ι) a
    _ = _ := by
      rw [compHom_ι, uncurry_lift_comp, hf, hg]
      simp [comp_lift_assoc, Category.assoc]

/-- The simplicial composition map for relative internal homs. -/
def comp (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) :
    (ihomOver q p : SSet) ⊗ (ihomOver r q : SSet) ⟶ ihomOver r p :=
  compHom (fst _ _) (snd _ _)

/-- After forgetting the base condition, composition is Mathlib's simplicial composition. -/
@[reassoc (attr := simp)]
lemma comp_ι (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) :
    comp p q r ≫ (ihomOver r p).ι =
      ((ihomOver q p).ι ⊗ₘ (ihomOver r q).ι) ≫ MonoidalClosed.comp X Y Z := by
  simp [comp, lift_fst_comp_snd_comp]

/-- Pairing two relative families and applying simplicial composition composes the families. -/
@[simp]
lemma lift_comp (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q) :
    lift f g ≫ comp p q r = compHom f g := by
  simp [comp, comp_compHom]

/-- The identity relative functor as a global element. -/
def id (p : X ⟶ B) : 𝟙_ SSet.{u} ⟶ ihomOver p p :=
  homEquiv.symm ⟨fst X _, rfl⟩

/-- Forgetting the base condition sends the identity to the identity of the closed
enrichment. -/
@[reassoc (attr := simp)]
lemma id_ι (p : X ⟶ B) : id p ≫ (ihomOver p p).ι = MonoidalClosed.id X := by
  rw [id, homEquiv_symm_apply_ι, MonoidalClosed.id_eq, rightUnitor_hom]

/-- The relative identity represents the identity map at its vertex.
Use this as an explicit rewrite in relative vertex coordinates. -/
lemma obj₀Equiv_id_app_coe (p : X ⟶ B) (a : (𝟙_ SSet.{u}) _⦋0⦌) :
    (obj₀Equiv ((id p).app _ a)).val = 𝟙 X := by
  -- Evaluate after the inclusion, which forgets the membership proof.
  calc
    _ = lift (𝟙 X) (const a) ≫ uncurry (id p ≫ (ihomOver p p).ι) := by
      rw [obj₀Equiv_apply_coe]
      exact ihomObj₀Equiv_app (id p ≫ (ihomOver p p).ι) a
    _ = _ := by
      rw [id_ι, MonoidalClosed.id_eq, uncurry_curry, rightUnitor_hom, lift_fst]

/-- Left unit law for relative simplicial composition. -/
@[reassoc (attr := simp)]
lemma id_comp (p : X ⟶ B) (q : Y ⟶ B) :
    (λ_ (ihomOver q p : SSet)).inv ≫ id p ▷ _ ≫ comp p p q = 𝟙 _ := by
  rw [← cancel_mono (ihomOver q p).ι]
  simp only [Category.assoc, comp_ι, tensorHom_def_assoc,
    ← comp_whiskerRight_assoc, id_ι]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
    MonoidalClosed.id_comp, Category.comp_id, Category.id_comp]

/-- Right unit law for relative simplicial composition. -/
@[reassoc (attr := simp)]
lemma comp_id (p : X ⟶ B) (q : Y ⟶ B) :
    (ρ_ (ihomOver q p : SSet)).inv ≫ _ ◁ id q ≫ comp p q q = 𝟙 _ := by
  rw [← cancel_mono (ihomOver q p).ι]
  simp only [Category.assoc, comp_ι, tensorHom_def_assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, id_ι,
    ← rightUnitor_inv_naturality_assoc, MonoidalClosed.comp_id,
    Category.comp_id, Category.id_comp]

/-- Associativity of relative composition. -/
@[reassoc]
lemma assoc (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) (s : W ⟶ B) :
    (α_ (ihomOver q p : SSet) (ihomOver r q : SSet) (ihomOver s r : SSet)).inv ≫
      comp p q r ▷ _ ≫ comp p r s = _ ◁ comp q r s ≫ comp p q s := by
  simp [comp, comp_compHom, compHom_assoc]

/-- Restrict the universal relative family to the fibre over a vertex of the base. -/
def evalFiber (p : X ⟶ B) (q : Y ⟶ B) (b : B _⦋0⦌) :
    (ihomOver q p : SSet) ⟶ (ihom (fiber p b : SSet)).obj (fiber q b : SSet) :=
  curry (fiber.lift (((fiber p b).ι ▷ _) ≫ (homEquiv (𝟙 (ihomOver q p : SSet))).val)
    q b (by simp [Category.assoc, (homEquiv (𝟙 (ihomOver q p : SSet))).property]))

/-- Fibre evaluation is the original family restricted to the source fibre. -/
@[reassoc (attr := simp)]
lemma uncurry_evalFiber_ι (p : X ⟶ B) (q : Y ⟶ B) (b : B _⦋0⦌) :
    uncurry (evalFiber p q b) ≫ (fiber q b).ι =
      (fiber p b).ι ▷ _ ≫ (homEquiv (𝟙 (ihomOver q p : SSet))).val := by
  simp [evalFiber]

/-- Fibre evaluation restricts any relative family to the source fibre. -/
@[reassoc (attr := simp)]
lemma uncurry_comp_evalFiber_ι (f : P ⟶ ihomOver q p) (b : B _⦋0⦌) :
    uncurry (f ≫ evalFiber p q b) ≫ (fiber q b).ι =
      (fiber p b).ι ▷ P ≫ (homEquiv f).val := by
  rw [uncurry_natural_left, Category.assoc, uncurry_evalFiber_ι, whisker_exchange_assoc]
  simp [homEquiv_apply_coe, uncurry_natural_left]

/-- Evaluation on a fibre commutes with composition of families. -/
lemma compHom_evalFiber (f : P ⟶ ihomOver q p) (g : P ⟶ ihomOver r q)
    (b : B _⦋0⦌) :
    compHom f g ≫ evalFiber p r b =
      lift (f ≫ evalFiber p q b) (g ≫ evalFiber q r b) ≫
        MonoidalClosed.comp (fiber p b : SSet) (fiber q b : SSet) (fiber r b : SSet) := by
  apply uncurry_injective
  rw [← cancel_mono (fiber r b).ι, uncurry_comp_evalFiber_ι,
    uncurry_lift_comp, Category.assoc, uncurry_comp_evalFiber_ι,
    lift_whiskerRight_assoc, uncurry_comp_evalFiber_ι, homEquiv_compHom_coe]
  simp [comp_lift_assoc]

/-- Evaluation on a fibre preserves simplicial composition. -/
@[reassoc]
lemma comp_evalFiber (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B) (b : B _⦋0⦌) :
    comp p q r ≫ evalFiber p r b =
      (evalFiber p q b ⊗ₘ evalFiber q r b) ≫
        MonoidalClosed.comp (fiber p b : SSet) (fiber q b : SSet) (fiber r b : SSet) := by
  rw [comp, compHom_evalFiber, lift_fst_comp_snd_comp]

/-- Evaluation on a fibre preserves the identity functor. -/
@[reassoc (attr := simp)]
lemma id_evalFiber (p : X ⟶ B) (b : B _⦋0⦌) :
    id p ≫ evalFiber p p b = MonoidalClosed.id (fiber p b : SSet) := by
  apply uncurry_injective
  rw [← cancel_mono (fiber p b).ι, uncurry_comp_evalFiber_ι]
  simp [id, MonoidalClosed.id_eq, rightUnitor_hom]

/-- On vertices, fibre evaluation is the usual induced map of fibres. -/
@[simp]
lemma ihomObj₀Equiv_evalFiber_app (b : B _⦋0⦌) (f : (ihomOver q p : SSet) _⦋0⦌) :
    dsimp% ihomObj₀Equiv _ _ ((evalFiber p q b).app _ f) =
      fiber.map (obj₀Equiv f).val (obj₀Equiv f).property b := by
  rw [← cancel_mono (fiber q b).ι, ihomObj₀Equiv_app, Category.assoc,
    uncurry_evalFiber_ι, ← Category.assoc, lift_whiskerRight]
  simp [homEquiv_apply_coe, uncurry_eq, ihomObj₀Equiv_apply, comp_lift_assoc,
    fiber.map_ι]

end SSet.ihomOver
