/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Equality transport, full-subcategory descent, and homotopy equivalences of simplicial objects

This file develops the categorical calculus around Fabian Odermatt's combinatorial simplicial
homotopy `CategoryTheory.SimplicialObject.Homotopy` and introduces combinatorial simplicial
homotopy equivalences `CategoryTheory.SimplicialObject.HomotopyEquiv`.

Because a combinatorial simplicial homotopy `H : Homotopy f g` is given purely by morphisms
`H.h i : X _⦋n⦌ ⟶ Y _⦋n + 1⦌` and simplicial identities, it is preserved by whiskering with an
arbitrary (not necessarily additive) functor `F : C ⥤ D` (`Homotopy.whiskerRight`) and descends
along any fully faithful functor (`Homotopy.ofFullyFaithful`). When `C` is preadditive, the
simplicial homotopy identities are affine-linear, so `Homotopy.symm`, `Homotopy.trans`, and
`HomotopyEquiv.trans` hold directly via `(refl f).h i + (refl g).h i - h.h i` and
`h₁.h i + h₂.h i - (refl f).h i` without finite coproducts or idempotent completeness.

## Main definitions and results

* `Homotopy.ofEq`, `Homotopy.congrLeft`, `Homotopy.congrRight`: equality transport for simplicial
  homotopies.
* `Homotopy.ofFullyFaithful`, `Homotopy.fullyFaithfulEquiv`: descent along fully faithful functors.
* `Homotopy.symm`, `Homotopy.trans`: symmetry and transitivity in any preadditive category.
* `HomotopyEquiv`: combinatorial simplicial homotopy equivalences, with `refl`, `symm`, `trans`
  (when `C` is preadditive), `ofIso`, `whiskerRight`, and `ofFullyFaithful`.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §1.15.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Opposite SimplexCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

namespace Homotopy

variable {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}

/-- Equal morphisms of simplicial objects are combinatorially simplicially homotopic via the
constant homotopy. -/
def ofEq {f g : X ⟶ Y} (h : f = g) : Homotopy f g := h ▸ refl f

/-- The components of `Homotopy.ofEq` are the degeneracies followed by `f`. -/
@[simp]
lemma ofEq_h {f g : X ⟶ Y} (h : f = g) {n : ℕ} (i : Fin (n + 1)) :
    (ofEq h).h i = X.σ i ≫ f.app (op ⦋n + 1⦌) := by subst h; rfl

/-- At `rfl`, `Homotopy.ofEq` is `Homotopy.refl`. -/
@[simp]
lemma ofEq_rfl (f : X ⟶ Y) : ofEq (rfl : f = f) = refl f := (rfl)

/-- Replace the source morphism of a combinatorial simplicial homotopy along an equality. -/
def congrLeft {f f' g : X ⟶ Y} (H : Homotopy f g) (h : f = f') : Homotopy f' g := h ▸ H

/-- Replacing the source morphism along an equality does not change the homotopy components. -/
@[simp]
lemma congrLeft_h {f f' g : X ⟶ Y} (H : Homotopy f g) (h : f = f') {n : ℕ} (i : Fin (n + 1)) :
    (H.congrLeft h).h i = H.h i := by subst h; rfl

/-- Replace the target morphism of a combinatorial simplicial homotopy along an equality. -/
def congrRight {f g g' : X ⟶ Y} (H : Homotopy f g) (h : g = g') : Homotopy f g' := h ▸ H

/-- Replacing the target morphism along an equality does not change the homotopy components. -/
@[simp]
lemma congrRight_h {f g g' : X ⟶ Y} (H : Homotopy f g) (h : g = g') {n : ℕ} (i : Fin (n + 1)) :
    (H.congrRight h).h i = H.h i := by subst h; rfl

section FullyFaithful

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] {f g : X ⟶ Y}

/-- A combinatorial simplicial homotopy between whiskered morphisms descends along a fully faithful
functor. -/
def ofFullyFaithful
    (H : Homotopy (((whiskering C D).obj F).map f) (((whiskering C D).obj F).map g)) :
    Homotopy f g where
  h i := F.preimage (H.h i)
  h_zero_comp_δ_zero n := F.map_injective <| by simpa [δ] using H.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := F.map_injective <| by simpa [δ] using H.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij :=
    F.map_injective <| by simpa [δ] using H.h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j :=
    F.map_injective <| by simpa [δ] using H.h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji :=
    F.map_injective <| by simpa [δ] using H.h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij :=
    F.map_injective <| by simpa [σ] using H.h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji :=
    F.map_injective <| by simpa [σ] using H.h_comp_σ_succ_of_lt i j hji

/-- Each component of `Homotopy.ofFullyFaithful` is the `F`-preimage of the corresponding
component. -/
@[simp]
lemma ofFullyFaithful_h
    (H : Homotopy (((whiskering C D).obj F).map f) (((whiskering C D).obj F).map g))
    {n : ℕ} (i : Fin (n + 1)) :
    (H.ofFullyFaithful F).h i = F.preimage (H.h i) := (rfl)

/-- Whiskering `Homotopy.ofFullyFaithful` recovers the original homotopy. -/
@[simp]
lemma whiskerRight_ofFullyFaithful
    (H : Homotopy (((whiskering C D).obj F).map f) (((whiskering C D).obj F).map g)) :
    (H.ofFullyFaithful F).whiskerRight F = H := by ext n i; simp

/-- Descending a whiskered homotopy along a fully faithful functor recovers the original
homotopy. -/
@[simp]
lemma ofFullyFaithful_whiskerRight (H : Homotopy f g) :
    (H.whiskerRight F).ofFullyFaithful F = H := by ext n i; simp

/-- Whiskering with a fully faithful functor induces a bijection on combinatorial simplicial
homotopies. -/
def fullyFaithfulEquiv (f g : X ⟶ Y) :
    Homotopy f g ≃ Homotopy (Functor.whiskerRight f F) (Functor.whiskerRight g F) where
  toFun H := H.whiskerRight F
  invFun H := H.ofFullyFaithful F
  left_inv H := H.ofFullyFaithful_whiskerRight F
  right_inv H := H.whiskerRight_ofFullyFaithful F

@[simp]
lemma fullyFaithfulEquiv_apply (H : Homotopy f g) :
    fullyFaithfulEquiv F f g H = H.whiskerRight F := (rfl)

@[simp]
lemma fullyFaithfulEquiv_symm_apply
    (H : Homotopy (Functor.whiskerRight f F) (Functor.whiskerRight g F)) :
    (fullyFaithfulEquiv F f g).symm H = H.ofFullyFaithful F := (rfl)

end FullyFaithful

section Preadditive

open Preadditive

variable [Preadditive C]

/-- Symmetry of combinatorial simplicial homotopies in any preadditive category, with components
`(refl f).h i + (refl g).h i - h.h i`. -/
@[symm]
def symm {f g : X ⟶ Y} (h : Homotopy f g) : Homotopy g f where
  h i := (refl f).h i + (refl g).h i - h.h i
  h_zero_comp_δ_zero _ := by simp [-refl_h, sub_comp, add_comp]
  h_last_comp_δ_last _ := by simp [-refl_h, sub_comp, add_comp]
  h_succ_comp_δ_castSucc_of_lt _ _ l := by
    simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]
  h_succ_comp_δ_castSucc_succ _ := by
    simp only [sub_comp, add_comp, (refl f).h_succ_comp_δ_castSucc_succ,
      (refl g).h_succ_comp_δ_castSucc_succ, h.h_succ_comp_δ_castSucc_succ]
  h_castSucc_comp_δ_succ_of_lt _ _ l := by
    simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]
  h_comp_σ_castSucc_of_le _ _ l := by simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]
  h_comp_σ_succ_of_lt _ _ l := by simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]

/-- Component formula for `Homotopy.symm`. -/
@[simp]
lemma symm_h {f g : X ⟶ Y} (h : Homotopy f g) {n : ℕ} (i : Fin (n + 1)) :
    h.symm.h i = X.σ i ≫ f.app (op ⦋n + 1⦌) + X.σ i ≫ g.app (op ⦋n + 1⦌) - h.h i := (rfl)

/-- `Homotopy.symm` is an involution. -/
@[simp]
lemma symm_symm {f g : X ⟶ Y} (h : Homotopy f g) : h.symm.symm = h := by
  ext n i; simp only [symm_h]; rw [add_comm (X.σ i ≫ g.app (op ⦋n + 1⦌)), sub_sub_cancel]

/-- The constant homotopy is symmetric. -/
@[simp]
lemma symm_refl (f : X ⟶ Y) : (refl f).symm = refl f := by
  ext n i; simp only [symm_h, refl_h, add_sub_cancel_right]

/-- Transitivity of combinatorial simplicial homotopies in any preadditive category, with components
`h₁.h i + h₂.h i - (refl f).h i`. -/
@[trans]
def trans {e f g : X ⟶ Y} (h₁ : Homotopy e f) (h₂ : Homotopy f g) : Homotopy e g where
  h i := h₁.h i + h₂.h i - (refl f).h i
  h_zero_comp_δ_zero _ := by simp [-refl_h, sub_comp, add_comp]
  h_last_comp_δ_last _ := by simp [-refl_h, sub_comp, add_comp]
  h_succ_comp_δ_castSucc_of_lt _ _ l := by
    simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]
  h_succ_comp_δ_castSucc_succ _ := by
    simp only [sub_comp, add_comp, h₁.h_succ_comp_δ_castSucc_succ,
      h₂.h_succ_comp_δ_castSucc_succ, (refl f).h_succ_comp_δ_castSucc_succ]
  h_castSucc_comp_δ_succ_of_lt _ _ l := by
    simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]
  h_comp_σ_castSucc_of_le _ _ l := by simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]
  h_comp_σ_succ_of_lt _ _ l := by simp [-refl_h, sub_comp, add_comp, comp_sub, comp_add, l]

/-- Component formula for `Homotopy.trans`. -/
@[simp]
lemma trans_h {e f g : X ⟶ Y} (h₁ : Homotopy e f) (h₂ : Homotopy f g)
    {n : ℕ} (i : Fin (n + 1)) :
    (h₁.trans h₂).h i = h₁.h i + h₂.h i - X.σ i ≫ f.app (op ⦋n + 1⦌) := (rfl)

/-- Composing with `refl` on the left is the identity on simplicial homotopies. -/
@[simp]
lemma refl_trans {f g : X ⟶ Y} (h : Homotopy f g) : (refl f).trans h = h := by
  ext n i; simp only [trans_h, refl_h, add_sub_cancel_left]

/-- Composing with `refl` on the right is the identity on simplicial homotopies. -/
@[simp]
lemma trans_refl {f g : X ⟶ Y} (h : Homotopy f g) : h.trans (refl g) = h := by
  ext n i; simp only [trans_h, refl_h, add_sub_cancel_right]

end Preadditive

end Homotopy

/-- A combinatorial simplicial homotopy equivalence between simplicial objects `X` and `Y`
consists of morphisms `hom : X ⟶ Y` and `inv : Y ⟶ X` together with combinatorial simplicial
homotopies from `hom ≫ inv` and `inv ≫ hom` to the respective identities. -/
structure HomotopyEquiv {C : Type u} [Category.{v} C] (X Y : SimplicialObject C) where
  /-- The forward morphism of simplicial objects. -/
  hom : X ⟶ Y
  /-- The backward morphism of simplicial objects. -/
  inv : Y ⟶ X
  /-- Combinatorial simplicial homotopy from `hom ≫ inv` to `𝟙 X`. -/
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 X)
  /-- Combinatorial simplicial homotopy from `inv ≫ hom` to `𝟙 Y`. -/
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 Y)

namespace HomotopyEquiv

variable {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}

/-- Every simplicial object is combinatorially simplicially homotopy equivalent to itself. -/
@[refl]
def refl (X : SimplicialObject C) : HomotopyEquiv X X where
  hom := 𝟙 X
  inv := 𝟙 X
  homotopyHomInvId := Homotopy.ofEq (Category.id_comp (𝟙 X))
  homotopyInvHomId := Homotopy.ofEq (Category.id_comp (𝟙 X))

@[simp]
lemma refl_hom (X : SimplicialObject C) : (refl X).hom = 𝟙 X := (rfl)

@[simp]
lemma refl_inv (X : SimplicialObject C) : (refl X).inv = 𝟙 X := (rfl)

instance (X : SimplicialObject C) : Inhabited (HomotopyEquiv X X) :=
  ⟨refl X⟩

/-- Symmetry of combinatorial simplicial homotopy equivalences. -/
@[symm]
def symm (e : HomotopyEquiv X Y) : HomotopyEquiv Y X where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

@[simp]
lemma symm_hom (e : HomotopyEquiv X Y) : e.symm.hom = e.inv := (rfl)

@[simp]
lemma symm_inv (e : HomotopyEquiv X Y) : e.symm.inv = e.hom := (rfl)

@[simp]
lemma symm_symm (e : HomotopyEquiv X Y) : e.symm.symm = e := (rfl)

/-- An isomorphism of simplicial objects induces a combinatorial simplicial homotopy
equivalence. -/
def ofIso (e : X ≅ Y) : HomotopyEquiv X Y where
  hom := e.hom
  inv := e.inv
  homotopyHomInvId := Homotopy.ofEq e.hom_inv_id
  homotopyInvHomId := Homotopy.ofEq e.inv_hom_id

@[simp]
lemma ofIso_hom (e : X ≅ Y) : (ofIso e).hom = e.hom := (rfl)

@[simp]
lemma ofIso_inv (e : X ≅ Y) : (ofIso e).inv = e.inv := (rfl)

/-- Any functor `F : C ⥤ D` applied levelwise preserves combinatorial simplicial homotopy
equivalences, with no additivity assumption on `F`. -/
def whiskerRight (e : HomotopyEquiv X Y) {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y) where
  hom := ((whiskering C D).obj F).map e.hom
  inv := ((whiskering C D).obj F).map e.inv
  homotopyHomInvId :=
    ((e.homotopyHomInvId.whiskerRight F).congrLeft
      (((whiskering C D).obj F).map_comp e.hom e.inv)).congrRight
      (((whiskering C D).obj F).map_id X)
  homotopyInvHomId :=
    ((e.homotopyInvHomId.whiskerRight F).congrLeft
      (((whiskering C D).obj F).map_comp e.inv e.hom)).congrRight
      (((whiskering C D).obj F).map_id Y)

@[simp]
lemma whiskerRight_hom (e : HomotopyEquiv X Y) {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (e.whiskerRight F).hom = ((whiskering C D).obj F).map e.hom := (rfl)

@[simp]
lemma whiskerRight_inv (e : HomotopyEquiv X Y) {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (e.whiskerRight F).inv = ((whiskering C D).obj F).map e.inv := (rfl)

/-- A combinatorial simplicial homotopy equivalence between whiskered objects descends along a
fully faithful functor. -/
def ofFullyFaithful {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    HomotopyEquiv X Y where
  hom := ((whiskering C D).obj F).preimage e.hom
  inv := ((whiskering C D).obj F).preimage e.inv
  homotopyHomInvId :=
    (e.homotopyHomInvId.congrLeft
      ((((whiskering C D).obj F).map_comp _ _).trans
        (by rw [Functor.map_preimage, Functor.map_preimage])).symm).congrRight
      (((whiskering C D).obj F).map_id X).symm |>.ofFullyFaithful F
  homotopyInvHomId :=
    (e.homotopyInvHomId.congrLeft
      ((((whiskering C D).obj F).map_comp _ _).trans
        (by rw [Functor.map_preimage, Functor.map_preimage])).symm).congrRight
      (((whiskering C D).obj F).map_id Y).symm |>.ofFullyFaithful F

/-- Whiskering the forward map of `HomotopyEquiv.ofFullyFaithful` recovers the original forward
map. -/
@[simp]
lemma whiskerRight_ofFullyFaithful_hom {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    Functor.whiskerRight (e.ofFullyFaithful F).hom F = e.hom :=
  ((whiskering C D).obj F).map_preimage e.hom

/-- Whiskering the backward map of `HomotopyEquiv.ofFullyFaithful` recovers the original backward
map. -/
@[simp]
lemma whiskerRight_ofFullyFaithful_inv {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    Functor.whiskerRight (e.ofFullyFaithful F).inv F = e.inv :=
  ((whiskering C D).obj F).map_preimage e.inv

section Preadditive

variable [Preadditive C]

/-- Transitivity of combinatorial simplicial homotopy equivalences in any preadditive category,
composing morphisms directly via precomposition and postcomposition of homotopies. -/
@[trans]
def trans {Z : SimplicialObject C} (e₁ : HomotopyEquiv X Y) (e₂ : HomotopyEquiv Y Z) :
    HomotopyEquiv X Z where
  hom := e₁.hom ≫ e₂.hom
  inv := e₂.inv ≫ e₁.inv
  homotopyHomInvId :=
    ((((e₂.homotopyHomInvId.precomp e₁.hom).postcomp e₁.inv).congrLeft
      (by simp [Category.assoc])).congrRight (by simp)).trans e₁.homotopyHomInvId
  homotopyInvHomId :=
    ((((e₁.homotopyInvHomId.precomp e₂.inv).postcomp e₂.hom).congrLeft
      (by simp [Category.assoc])).congrRight (by simp)).trans e₂.homotopyInvHomId

@[simp]
lemma trans_hom {Z : SimplicialObject C} (e₁ : HomotopyEquiv X Y) (e₂ : HomotopyEquiv Y Z) :
    (e₁.trans e₂).hom = e₁.hom ≫ e₂.hom := (rfl)

@[simp]
lemma trans_inv {Z : SimplicialObject C} (e₁ : HomotopyEquiv X Y) (e₂ : HomotopyEquiv Y Z) :
    (e₁.trans e₂).inv = e₂.inv ≫ e₁.inv := (rfl)

end Preadditive

end HomotopyEquiv

end CategoryTheory.SimplicialObject
