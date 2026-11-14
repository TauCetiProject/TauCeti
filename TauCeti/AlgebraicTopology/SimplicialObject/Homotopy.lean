/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Equality transport, full-subcategory descent, and homotopy equivalences of simplicial objects

This file develops the basic categorical calculus around Fabian Odermatt's combinatorial simplicial
homotopy `CategoryTheory.SimplicialObject.Homotopy` and introduces combinatorial simplicial
homotopy equivalences `CategoryTheory.SimplicialObject.HomotopyEquiv`.

Because a combinatorial simplicial homotopy `H : Homotopy f g` is given purely in terms of the
morphisms `H.h i : X _⦋n⦌ ⟶ Y _⦋n + 1⦌` and their simplicial identities, it is preserved by
whiskering with an arbitrary functor `F : C ⥤ D` (`Homotopy.whiskerRight`), with no additivity or
colimit preservation assumed on `F`, and descends along any fully faithful functor
(`Homotopy.ofFullyFaithful`). Packaging mutually inverse morphisms up to combinatorial simplicial
homotopy into `SimplicialObject.HomotopyEquiv` therefore gives homotopy equivalences that are
carried by every levelwise functor (`HomotopyEquiv.whiskerRight`).

## Main definitions and results

* `CategoryTheory.SimplicialObject.Homotopy.ofEq`,
  `CategoryTheory.SimplicialObject.Homotopy.congrLeft`,
  `CategoryTheory.SimplicialObject.Homotopy.congrRight`: equality transport for combinatorial
  simplicial homotopies.
* `CategoryTheory.SimplicialObject.Homotopy.ofFullyFaithful`,
  `CategoryTheory.SimplicialObject.Homotopy.fullyFaithfulEquiv`: combinatorial simplicial
  homotopies descend bijectively along fully faithful functors.
* `CategoryTheory.SimplicialObject.HomotopyEquiv`: combinatorial simplicial homotopy equivalences
  between simplicial objects, with `refl`, `symm`, `ofIso`, `whiskerRight`, and `ofFullyFaithful`.

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
def ofEq {f g : X ⟶ Y} (h : f = g) : Homotopy f g :=
  h ▸ refl f

/-- The components of `Homotopy.ofEq` are the degeneracies followed by `f`. -/
@[simp]
lemma ofEq_h {f g : X ⟶ Y} (h : f = g) {n : ℕ} (i : Fin (n + 1)) :
    (ofEq h).h i = X.σ i ≫ f.app (op ⦋n + 1⦌) := by
  subst h
  rfl

/-- At `rfl`, `Homotopy.ofEq` is `Homotopy.refl`. -/
@[simp]
lemma ofEq_rfl (f : X ⟶ Y) : ofEq (rfl : f = f) = refl f :=
  (rfl)

/-- Replace the source morphism of a combinatorial simplicial homotopy along an equality. -/
def congrLeft {f f' g : X ⟶ Y} (H : Homotopy f g) (h : f = f') : Homotopy f' g :=
  h ▸ H

/-- Replacing the source morphism along an equality does not change the homotopy components. -/
@[simp]
lemma congrLeft_h {f f' g : X ⟶ Y} (H : Homotopy f g) (h : f = f') {n : ℕ} (i : Fin (n + 1)) :
    (H.congrLeft h).h i = H.h i := by
  subst h
  rfl

/-- Replace the target morphism of a combinatorial simplicial homotopy along an equality. -/
def congrRight {f g g' : X ⟶ Y} (H : Homotopy f g) (h : g = g') : Homotopy f g' :=
  h ▸ H

/-- Replacing the target morphism along an equality does not change the homotopy components. -/
@[simp]
lemma congrRight_h {f g g' : X ⟶ Y} (H : Homotopy f g) (h : g = g') {n : ℕ} (i : Fin (n + 1)) :
    (H.congrRight h).h i = H.h i := by
  subst h
  rfl

section FullyFaithful

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] {f g : X ⟶ Y}

/-- A combinatorial simplicial homotopy between whiskered morphisms descends along a fully faithful
functor. -/
def ofFullyFaithful
    (H : Homotopy (((whiskering C D).obj F).map f) (((whiskering C D).obj F).map g)) :
    Homotopy f g where
  h i := F.preimage (H.h i)
  h_zero_comp_δ_zero n := F.map_injective <| by
    simpa [SimplicialObject.δ] using H.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := F.map_injective <| by
    simpa [SimplicialObject.δ] using H.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij := F.map_injective <| by
    simpa [SimplicialObject.δ] using H.h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := F.map_injective <| by
    simpa [SimplicialObject.δ] using H.h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := F.map_injective <| by
    simpa [SimplicialObject.δ] using H.h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij := F.map_injective <| by
    simpa [SimplicialObject.σ] using H.h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji := F.map_injective <| by
    simpa [SimplicialObject.σ] using H.h_comp_σ_succ_of_lt i j hji

/-- Each component of `Homotopy.ofFullyFaithful` is the `F`-preimage of the corresponding
component. -/
@[simp]
lemma ofFullyFaithful_h
    (H : Homotopy (((whiskering C D).obj F).map f) (((whiskering C D).obj F).map g))
    {n : ℕ} (i : Fin (n + 1)) :
    (H.ofFullyFaithful F).h i = F.preimage (H.h i) :=
  (rfl)

/-- Whiskering `Homotopy.ofFullyFaithful` recovers the original homotopy. -/
@[simp]
lemma whiskerRight_ofFullyFaithful
    (H : Homotopy (((whiskering C D).obj F).map f) (((whiskering C D).obj F).map g)) :
    (H.ofFullyFaithful F).whiskerRight F = H := by
  ext n i
  simp

/-- Descending a whiskered homotopy along a fully faithful functor recovers the original
homotopy. -/
@[simp]
lemma ofFullyFaithful_whiskerRight (H : Homotopy f g) :
    (H.whiskerRight F).ofFullyFaithful F = H := by
  ext n i
  simp

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
    fullyFaithfulEquiv F f g H = H.whiskerRight F :=
  (rfl)

@[simp]
lemma fullyFaithfulEquiv_symm_apply
    (H : Homotopy (Functor.whiskerRight f F) (Functor.whiskerRight g F)) :
    (fullyFaithfulEquiv F f g).symm H = H.ofFullyFaithful F :=
  (rfl)

end FullyFaithful

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
    (e.whiskerRight F).hom = ((whiskering C D).obj F).map e.hom :=
  (rfl)

@[simp]
lemma whiskerRight_inv (e : HomotopyEquiv X Y) {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (e.whiskerRight F).inv = ((whiskering C D).obj F).map e.inv :=
  (rfl)

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

lemma map_ofFullyFaithful_hom {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    ((whiskering C D).obj F).map (e.ofFullyFaithful F).hom = e.hom :=
  ((whiskering C D).obj F).map_preimage e.hom

lemma map_ofFullyFaithful_inv {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    ((whiskering C D).obj F).map (e.ofFullyFaithful F).inv = e.inv :=
  ((whiskering C D).obj F).map_preimage e.inv

@[simp]
lemma whiskerRight_ofFullyFaithful_hom {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    Functor.whiskerRight (e.ofFullyFaithful F).hom F = e.hom :=
  map_ofFullyFaithful_hom F e

@[simp]
lemma whiskerRight_ofFullyFaithful_inv {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful]
    (e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y)) :
    Functor.whiskerRight (e.ofFullyFaithful F).inv F = e.inv :=
  map_ofFullyFaithful_inv F e

end HomotopyEquiv

end CategoryTheory.SimplicialObject
