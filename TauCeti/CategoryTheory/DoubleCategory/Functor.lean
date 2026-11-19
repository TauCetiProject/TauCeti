/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import TauCeti.CategoryTheory.DoubleCategory.Basic

/-!
# Strict double functors and double isomorphisms

A strict double functor `F : D → D'` between strict double categories consists of one map on
objects, functorial maps on horizontal and on vertical edges over that object map, and a map on
cells sending a cell with boundary `(p, q, l, r)` to a cell with boundary
`(F p, F q, F l, F r)`. It preserves both identity cells and both pastings, after transporting
along the functoriality of the edge maps on the boundaries.

Strict double functors have identities and composites satisfying the category laws as equalities
of double functors. A double isomorphism is a pair of strict double functors whose two composites
are equal to the identity double functors; its inverse laws are equalities of double functors,
not equivalences of categories of cells. Applied to an object, an edge or a cell, these inverse
laws say that a double isomorphism followed by its inverse returns it, up to the equalities of
boundary objects provided by the same laws.

`TauCeti.StrictDoubleIso.ofCellEquiv` constructs a double isomorphism between two strict double
categories on the same edge categories, which is the identity on objects and on edges, from a
family of equivalences of cell types preserving identity cells and pastings.

## Main declarations

* `TauCeti.StrictDoubleFunctor`, with `TauCeti.StrictDoubleFunctor.id`,
  `TauCeti.StrictDoubleFunctor.comp` and `TauCeti.StrictDoubleFunctor.hext`;
* `TauCeti.StrictDoubleFunctor.hFunctor` and `TauCeti.StrictDoubleFunctor.vFunctor`: the edge
  functors in each direction;
* `TauCeti.StrictDoubleIso`, with `TauCeti.StrictDoubleIso.refl`,
  `TauCeti.StrictDoubleIso.symm`, `TauCeti.StrictDoubleIso.trans` and
  `TauCeti.StrictDoubleIso.ofCellEquiv`.
-/

@[expose] public section

universe s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄ h₁ h₂ h₃ h₄ v₁ v₂ v₃ v₄

namespace TauCeti

open CategoryTheory StrictDoubleCategory DoubleCategoryStruct

variable {O₁ : Type u₁} {H₁ : Category.{h₁} O₁} {V₁ : Category.{v₁} O₁}
  {O₂ : Type u₂} {H₂ : Category.{h₂} O₂} {V₂ : Category.{v₂} O₂}
  {O₃ : Type u₃} {H₃ : Category.{h₃} O₃} {V₃ : Category.{v₃} O₃}

/-- A strict double functor between strict double categories: a map on objects, functorial maps
on horizontal and vertical edges over it, and a map on cells over the edge maps preserving both
identity cells and both pastings. The preservation laws transport the image cell along the
functoriality of the edge maps on its boundary. -/
structure StrictDoubleFunctor (D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁)
    (D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂) where
  /-- The map on objects. -/
  obj : O₁ → O₂
  /-- The map on horizontal edges. -/
  hMap {a b : O₁} : Edge H₁ a b → Edge H₂ (obj a) (obj b)
  /-- The map on horizontal edges preserves identities. -/
  hMap_id (a : O₁) : hMap (edgeId H₁ a) = edgeId H₂ (obj a)
  /-- The map on horizontal edges preserves composition. -/
  hMap_comp {a b c : O₁} (f : Edge H₁ a b) (g : Edge H₁ b c) :
    hMap (edgeComp H₁ f g) = edgeComp H₂ (hMap f) (hMap g)
  /-- The map on vertical edges. -/
  vMap {a b : O₁} : Edge V₁ a b → Edge V₂ (obj a) (obj b)
  /-- The map on vertical edges preserves identities. -/
  vMap_id (a : O₁) : vMap (edgeId V₁ a) = edgeId V₂ (obj a)
  /-- The map on vertical edges preserves composition. -/
  vMap_comp {a b c : O₁} (f : Edge V₁ a b) (g : Edge V₁ b c) :
    vMap (edgeComp V₁ f g) = edgeComp V₂ (vMap f) (vMap g)
  /-- The map on cells, over the maps on edges. -/
  map {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c} {r : Edge V₁ b d} :
    D₁.Cell p q l r → D₂.Cell (hMap p) (hMap q) (vMap l) (vMap r)
  /-- The map on cells preserves horizontal identity cells. -/
  map_hId {a b : O₁} (f : Edge V₁ a b) :
    map (D₁.hId f) = (D₂.hId (vMap f)).cast (hMap_id a).symm (hMap_id b).symm rfl rfl
  /-- The map on cells preserves vertical identity cells. -/
  map_vId {a b : O₁} (f : Edge H₁ a b) :
    map (D₁.vId f) = (D₂.vId (hMap f)).cast rfl rfl (vMap_id a).symm (vMap_id b).symm
  /-- The map on cells preserves horizontal pasting. -/
  map_hComp {a b c d e f : O₁} {p : Edge H₁ a b} {q : Edge H₁ b c} {r : Edge H₁ d e}
    {t : Edge H₁ e f} {l : Edge V₁ a d} {m : Edge V₁ b e} {n : Edge V₁ c f}
    (α : D₁.Cell p r l m) (β : D₁.Cell q t m n) :
    map (D₁.hComp α β) =
      (D₂.hComp (map α) (map β)).cast (hMap_comp p q).symm (hMap_comp r t).symm rfl rfl
  /-- The map on cells preserves vertical pasting. -/
  map_vComp {a b c d e f : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {r : Edge H₁ e f}
    {l : Edge V₁ a c} {m : Edge V₁ b d} {n : Edge V₁ c e} {t : Edge V₁ d f}
    (α : D₁.Cell p q l m) (β : D₁.Cell q r n t) :
    map (D₁.vComp α β) =
      (D₂.vComp (map α) (map β)).cast rfl rfl (vMap_comp l n).symm (vMap_comp m t).symm

namespace StrictDoubleFunctor

attribute [simp] hMap_id hMap_comp vMap_id vMap_comp map_hId map_vId map_hComp map_vComp

variable {D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁} {D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂}
  {D₃ : StrictDoubleCategory.{s₃} O₃ H₃ V₃}

/-- The map on cells commutes with transport along equalities of boundary edges. -/
@[simp]
theorem map_cast (F : StrictDoubleFunctor D₁ D₂) {a b c d : O₁} {p p' : Edge H₁ a b}
    {q q' : Edge H₁ c d} {l l' : Edge V₁ a c} {r r' : Edge V₁ b d} (hp : p = p') (hq : q = q')
    (hl : l = l') (hr : r = r') (α : D₁.Cell p q l r) :
    F.map (α.cast hp hq hl hr) =
      (F.map α).cast (congrArg F.hMap hp) (congrArg F.hMap hq) (congrArg F.vMap hl)
        (congrArg F.vMap hr) := by
  subst hp hq hl hr
  rfl

/-- The functor of horizontal edges underlying a strict double functor. -/
def hFunctor (F : StrictDoubleFunctor D₁ D₂) : @Functor O₁ H₁ O₂ H₂ where
  obj := F.obj
  map := F.hMap
  map_id := F.hMap_id
  map_comp := F.hMap_comp

/-- The functor of vertical edges underlying a strict double functor. -/
def vFunctor (F : StrictDoubleFunctor D₁ D₂) : @Functor O₁ V₁ O₂ V₂ where
  obj := F.obj
  map := F.vMap
  map_id := F.vMap_id
  map_comp := F.vMap_comp

@[simp]
theorem hFunctor_obj (F : StrictDoubleFunctor D₁ D₂) (a : O₁) : F.hFunctor.obj a = F.obj a :=
  rfl

@[simp]
theorem hFunctor_map (F : StrictDoubleFunctor D₁ D₂) {a b : O₁} (f : Edge H₁ a b) :
    F.hFunctor.map f = F.hMap f :=
  rfl

@[simp]
theorem vFunctor_obj (F : StrictDoubleFunctor D₁ D₂) (a : O₁) : F.vFunctor.obj a = F.obj a :=
  rfl

@[simp]
theorem vFunctor_map (F : StrictDoubleFunctor D₁ D₂) {a b : O₁} (f : Edge V₁ a b) :
    F.vFunctor.map f = F.vMap f :=
  rfl

/-- Two strict double functors are equal when they agree on objects and, up to the resulting
heterogeneous equalities, on horizontal edges, vertical edges and cells. -/
theorem hext {F G : StrictDoubleFunctor D₁ D₂} (h_obj : ∀ a, F.obj a = G.obj a)
    (h_hMap : ∀ {a b : O₁} (f : Edge H₁ a b), F.hMap f ≍ G.hMap f)
    (h_vMap : ∀ {a b : O₁} (f : Edge V₁ a b), F.vMap f ≍ G.vMap f)
    (h_map : ∀ {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c}
      {r : Edge V₁ b d} (α : D₁.Cell p q l r), F.map α ≍ G.map α) : F = G := by
  -- Destructuring `F` and `G` changes the types of the hypotheses, so they are reintroduced.
  revert h_obj h_hMap h_vMap h_map
  rcases F with ⟨Fo, Fh, -, -, Fv, -, -, Fm, -, -, -, -⟩
  rcases G with ⟨Go, Gh, -, -, Gv, -, -, Gm, -, -, -, -⟩
  intro h_obj h_hMap h_vMap h_map
  obtain rfl : Fo = Go := funext h_obj
  obtain rfl : @Fh = @Gh := by
    funext a b f
    exact eq_of_heq (h_hMap f)
  obtain rfl : @Fv = @Gv := by
    funext a b f
    exact eq_of_heq (h_vMap f)
  obtain rfl : @Fm = @Gm := by
    funext a b c d p q l r α
    exact eq_of_heq (h_map α)
  rfl

/-- Equal strict double functors agree on objects. -/
theorem congr_obj {F G : StrictDoubleFunctor D₁ D₂} (h : F = G) (a : O₁) : F.obj a = G.obj a := by
  rw [h]

/-- Equal strict double functors agree on horizontal edges, up to heterogeneous equality. -/
theorem hcongr_hMap {F G : StrictDoubleFunctor D₁ D₂} (h : F = G) {a b : O₁} (f : Edge H₁ a b) :
    F.hMap f ≍ G.hMap f := by
  rw [h]

/-- Equal strict double functors agree on vertical edges, up to heterogeneous equality. -/
theorem hcongr_vMap {F G : StrictDoubleFunctor D₁ D₂} (h : F = G) {a b : O₁} (f : Edge V₁ a b) :
    F.vMap f ≍ G.vMap f := by
  rw [h]

/-- Equal strict double functors agree on cells, up to heterogeneous equality. -/
theorem hcongr_map {F G : StrictDoubleFunctor D₁ D₂} (h : F = G) {a b c d : O₁}
    {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c} {r : Edge V₁ b d}
    (α : D₁.Cell p q l r) : F.map α ≍ G.map α := by
  rw [h]

variable (D₁) in
/-- The identity strict double functor. -/
def id : StrictDoubleFunctor D₁ D₁ where
  obj a := a
  hMap f := f
  hMap_id _ := rfl
  hMap_comp _ _ := rfl
  vMap f := f
  vMap_id _ := rfl
  vMap_comp _ _ := rfl
  map α := α
  map_hId _ := rfl
  map_vId _ := rfl
  map_hComp _ _ := rfl
  map_vComp _ _ := rfl

@[simp]
theorem id_obj (a : O₁) : (id D₁).obj a = a :=
  rfl

@[simp]
theorem id_hMap {a b : O₁} (f : Edge H₁ a b) : (id D₁).hMap f = f :=
  rfl

@[simp]
theorem id_vMap {a b : O₁} (f : Edge V₁ a b) : (id D₁).vMap f = f :=
  rfl

@[simp]
theorem id_map {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c}
    {r : Edge V₁ b d} (α : D₁.Cell p q l r) : (id D₁).map α = α :=
  rfl

/-- The composite of two strict double functors, in diagrammatic order. -/
def comp (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) :
    StrictDoubleFunctor D₁ D₃ where
  obj a := G.obj (F.obj a)
  hMap f := G.hMap (F.hMap f)
  hMap_id a := by simp
  hMap_comp f g := by simp
  vMap f := G.vMap (F.vMap f)
  vMap_id a := by simp
  vMap_comp f g := by simp
  map α := G.map (F.map α)
  map_hId f := by simp
  map_vId f := by simp
  map_hComp α β := by simp
  map_vComp α β := by simp

@[simp]
theorem comp_obj (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) (a : O₁) :
    (F.comp G).obj a = G.obj (F.obj a) :=
  rfl

@[simp]
theorem comp_hMap (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) {a b : O₁}
    (f : Edge H₁ a b) : (F.comp G).hMap f = G.hMap (F.hMap f) :=
  rfl

@[simp]
theorem comp_vMap (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) {a b : O₁}
    (f : Edge V₁ a b) : (F.comp G).vMap f = G.vMap (F.vMap f) :=
  rfl

@[simp]
theorem comp_map (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃)
    {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c} {r : Edge V₁ b d}
    (α : D₁.Cell p q l r) : (F.comp G).map α = G.map (F.map α) :=
  rfl

@[simp]
theorem id_comp (F : StrictDoubleFunctor D₁ D₂) : (id D₁).comp F = F :=
  rfl

@[simp]
theorem comp_id (F : StrictDoubleFunctor D₁ D₂) : F.comp (id D₂) = F :=
  rfl

theorem comp_assoc {O₄ : Type u₄} {H₄ : Category.{h₄} O₄} {V₄ : Category.{v₄} O₄}
    {D₄ : StrictDoubleCategory.{s₄} O₄ H₄ V₄} (F : StrictDoubleFunctor D₁ D₂)
    (G : StrictDoubleFunctor D₂ D₃) (K : StrictDoubleFunctor D₃ D₄) :
    (F.comp G).comp K = F.comp (G.comp K) :=
  rfl

@[simp]
theorem id_hFunctor : (id D₁).hFunctor = @Functor.id O₁ H₁ :=
  rfl

@[simp]
theorem id_vFunctor : (id D₁).vFunctor = @Functor.id O₁ V₁ :=
  rfl

@[simp]
theorem comp_hFunctor (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) :
    (F.comp G).hFunctor = @Functor.comp O₁ H₁ O₂ H₂ O₃ H₃ F.hFunctor G.hFunctor :=
  rfl

@[simp]
theorem comp_vFunctor (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) :
    (F.comp G).vFunctor = @Functor.comp O₁ V₁ O₂ V₂ O₃ V₃ F.vFunctor G.vFunctor :=
  rfl

end StrictDoubleFunctor

/-- A double isomorphism between strict double categories: strict double functors in both
directions whose two composites are equal to the identity double functors. -/
structure StrictDoubleIso (D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁)
    (D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂) where
  /-- The forward double functor. -/
  hom : StrictDoubleFunctor D₁ D₂
  /-- The inverse double functor. -/
  inv : StrictDoubleFunctor D₂ D₁
  /-- The forward functor followed by the inverse is the identity. -/
  hom_inv_id : hom.comp inv = StrictDoubleFunctor.id D₁
  /-- The inverse functor followed by the forward functor is the identity. -/
  inv_hom_id : inv.comp hom = StrictDoubleFunctor.id D₂

namespace StrictDoubleIso

attribute [simp] hom_inv_id inv_hom_id

variable {D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁} {D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂}
  {D₃ : StrictDoubleCategory.{s₃} O₃ H₃ V₃}

/-- Two double isomorphisms with the same forward functor are equal. -/
@[ext]
theorem ext {e e' : StrictDoubleIso D₁ D₂} (h : e.hom = e'.hom) : e = e' := by
  have h_inv : e.inv = e'.inv := by
    calc e.inv = e.inv.comp (e'.hom.comp e'.inv) := by
          rw [e'.hom_inv_id, StrictDoubleFunctor.comp_id]
      _ = (e.inv.comp e.hom).comp e'.inv := by rw [← h, StrictDoubleFunctor.comp_assoc]
      _ = e'.inv := by rw [e.inv_hom_id, StrictDoubleFunctor.id_comp]
  cases e
  cases e'
  cases h
  cases h_inv
  rfl

variable (D₁) in
/-- The identity double isomorphism. -/
@[simps]
def refl : StrictDoubleIso D₁ D₁ where
  hom := StrictDoubleFunctor.id D₁
  inv := StrictDoubleFunctor.id D₁
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The inverse double isomorphism. -/
@[simps]
def symm (e : StrictDoubleIso D₁ D₂) : StrictDoubleIso D₂ D₁ where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

@[simp]
theorem symm_symm (e : StrictDoubleIso D₁ D₂) : e.symm.symm = e :=
  rfl

/-- The composite of two double isomorphisms, in diagrammatic order. -/
@[simps]
def trans (e : StrictDoubleIso D₁ D₂) (e' : StrictDoubleIso D₂ D₃) : StrictDoubleIso D₁ D₃ where
  hom := e.hom.comp e'.hom
  inv := e'.inv.comp e.inv
  hom_inv_id := by
    rw [StrictDoubleFunctor.comp_assoc, ← StrictDoubleFunctor.comp_assoc e'.hom,
      e'.hom_inv_id, StrictDoubleFunctor.id_comp, e.hom_inv_id]
  inv_hom_id := by
    rw [StrictDoubleFunctor.comp_assoc, ← StrictDoubleFunctor.comp_assoc e.inv,
      e.inv_hom_id, StrictDoubleFunctor.id_comp, e'.inv_hom_id]

@[simp]
theorem refl_symm : (refl D₁).symm = refl D₁ :=
  rfl

@[simp]
theorem trans_symm (e : StrictDoubleIso D₁ D₂) (e' : StrictDoubleIso D₂ D₃) :
    (e.trans e').symm = e'.symm.trans e.symm :=
  rfl

@[simp]
theorem refl_trans (e : StrictDoubleIso D₁ D₂) : (refl D₁).trans e = e :=
  rfl

@[simp]
theorem trans_refl (e : StrictDoubleIso D₁ D₂) : e.trans (refl D₂) = e :=
  rfl

@[simp]
theorem trans_assoc {O₄ : Type u₄} {H₄ : Category.{h₄} O₄} {V₄ : Category.{v₄} O₄}
    {D₄ : StrictDoubleCategory.{s₄} O₄ H₄ V₄} (e : StrictDoubleIso D₁ D₂)
    (e' : StrictDoubleIso D₂ D₃) (e'' : StrictDoubleIso D₃ D₄) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  rfl

@[simp]
theorem self_trans_symm (e : StrictDoubleIso D₁ D₂) : e.trans e.symm = refl D₁ :=
  ext e.hom_inv_id

@[simp]
theorem symm_trans_self (e : StrictDoubleIso D₁ D₂) : e.symm.trans e = refl D₂ :=
  ext e.inv_hom_id

/-- A double isomorphism followed by its inverse fixes every object. -/
@[simp]
theorem inv_obj_hom_obj (e : StrictDoubleIso D₁ D₂) (a : O₁) : e.inv.obj (e.hom.obj a) = a :=
  StrictDoubleFunctor.congr_obj e.hom_inv_id a

/-- The inverse of a double isomorphism followed by the isomorphism fixes every object. -/
@[simp]
theorem hom_obj_inv_obj (e : StrictDoubleIso D₁ D₂) (a : O₂) : e.hom.obj (e.inv.obj a) = a :=
  StrictDoubleFunctor.congr_obj e.inv_hom_id a

/-- A double isomorphism followed by its inverse fixes every horizontal edge, up to the
identification of its endpoints given by `inv_obj_hom_obj`. -/
theorem inv_hMap_hom_hMap_heq (e : StrictDoubleIso D₁ D₂) {a b : O₁} (f : Edge H₁ a b) :
    e.inv.hMap (e.hom.hMap f) ≍ f :=
  StrictDoubleFunctor.hcongr_hMap e.hom_inv_id f

/-- A double isomorphism followed by its inverse fixes every vertical edge, up to the
identification of its endpoints given by `inv_obj_hom_obj`. -/
theorem inv_vMap_hom_vMap_heq (e : StrictDoubleIso D₁ D₂) {a b : O₁} (f : Edge V₁ a b) :
    e.inv.vMap (e.hom.vMap f) ≍ f :=
  StrictDoubleFunctor.hcongr_vMap e.hom_inv_id f

/-- A double isomorphism followed by its inverse fixes every cell, up to the identification of
its boundary given by `inv_obj_hom_obj`, `inv_hMap_hom_hMap_heq` and `inv_vMap_hom_vMap_heq`. -/
theorem inv_map_hom_map_heq (e : StrictDoubleIso D₁ D₂) {a b c d : O₁} {p : Edge H₁ a b}
    {q : Edge H₁ c d} {l : Edge V₁ a c} {r : Edge V₁ b d} (α : D₁.Cell p q l r) :
    e.inv.map (e.hom.map α) ≍ α :=
  StrictDoubleFunctor.hcongr_map e.hom_inv_id α

/-- The inverse of a double isomorphism followed by the isomorphism fixes every horizontal edge,
up to the identification of its endpoints given by `hom_obj_inv_obj`. -/
theorem hom_hMap_inv_hMap_heq (e : StrictDoubleIso D₁ D₂) {a b : O₂} (f : Edge H₂ a b) :
    e.hom.hMap (e.inv.hMap f) ≍ f :=
  StrictDoubleFunctor.hcongr_hMap e.inv_hom_id f

/-- The inverse of a double isomorphism followed by the isomorphism fixes every vertical edge,
up to the identification of its endpoints given by `hom_obj_inv_obj`. -/
theorem hom_vMap_inv_vMap_heq (e : StrictDoubleIso D₁ D₂) {a b : O₂} (f : Edge V₂ a b) :
    e.hom.vMap (e.inv.vMap f) ≍ f :=
  StrictDoubleFunctor.hcongr_vMap e.inv_hom_id f

/-- The inverse of a double isomorphism followed by the isomorphism fixes every cell, up to the
identification of its boundary given by `hom_obj_inv_obj`, `hom_hMap_inv_hMap_heq` and
`hom_vMap_inv_vMap_heq`. -/
theorem hom_map_inv_map_heq (e : StrictDoubleIso D₁ D₂) {a b c d : O₂} {p : Edge H₂ a b}
    {q : Edge H₂ c d} {l : Edge V₂ a c} {r : Edge V₂ b d} (α : D₂.Cell p q l r) :
    e.hom.map (e.inv.map α) ≍ α :=
  StrictDoubleFunctor.hcongr_map e.inv_hom_id α

section OfCellEquiv

variable {D : StrictDoubleCategory.{s₁} O₁ H₁ V₁} {D' : StrictDoubleCategory.{s₂} O₁ H₁ V₁}

/-- The double isomorphism between two strict double categories on the same edge categories
that is the identity on objects and edges and is given on cells by a family of equivalences
preserving identity cells and both pastings. -/
-- The generated lemmas are not `simp` lemmas: rewriting the inner cell of a composite such as
-- `inv.map (hom.map α)` with `ofCellEquiv_hom_map` leaves a term that is type-correct only after
-- unfolding the edge maps of `ofCellEquiv`, and blocks `ofCellEquiv_inv_map_hom_map`.
@[simps -isSimp]
def ofCellEquiv
    (φ : ∀ {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c}
      {r : Edge V₁ b d}, D.Cell p q l r ≃ D'.Cell p q l r)
    (map_hId : ∀ {a b : O₁} (f : Edge V₁ a b), φ (D.hId f) = D'.hId f)
    (map_vId : ∀ {a b : O₁} (f : Edge H₁ a b), φ (D.vId f) = D'.vId f)
    (map_hComp : ∀ {a b c d e f : O₁} {p : Edge H₁ a b} {q : Edge H₁ b c} {r : Edge H₁ d e}
      {t : Edge H₁ e f} {l : Edge V₁ a d} {m : Edge V₁ b e} {n : Edge V₁ c f}
      (α : D.Cell p r l m) (β : D.Cell q t m n), φ (D.hComp α β) = D'.hComp (φ α) (φ β))
    (map_vComp : ∀ {a b c d e f : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {r : Edge H₁ e f}
      {l : Edge V₁ a c} {m : Edge V₁ b d} {n : Edge V₁ c e} {t : Edge V₁ d f}
      (α : D.Cell p q l m) (β : D.Cell q r n t), φ (D.vComp α β) = D'.vComp (φ α) (φ β)) :
    StrictDoubleIso D D' where
  hom :=
    { obj a := a
      hMap f := f
      hMap_id _ := rfl
      hMap_comp _ _ := rfl
      vMap f := f
      vMap_id _ := rfl
      vMap_comp _ _ := rfl
      map α := φ α
      map_hId := map_hId
      map_vId := map_vId
      map_hComp := map_hComp
      map_vComp := map_vComp }
  inv :=
    { obj a := a
      hMap f := f
      hMap_id _ := rfl
      hMap_comp _ _ := rfl
      vMap f := f
      vMap_id _ := rfl
      vMap_comp _ _ := rfl
      map α := φ.symm α
      map_hId f := φ.symm_apply_eq.2 (map_hId f).symm
      map_vId f := φ.symm_apply_eq.2 (map_vId f).symm
      map_hComp α β := φ.symm_apply_eq.2 (by simp [map_hComp])
      map_vComp α β := φ.symm_apply_eq.2 (by simp [map_vComp]) }
  hom_inv_id := StrictDoubleFunctor.hext (fun _ ↦ rfl) (fun _ ↦ .rfl) (fun _ ↦ .rfl)
    (fun α ↦ heq_of_eq (φ.symm_apply_apply α))
  inv_hom_id := StrictDoubleFunctor.hext (fun _ ↦ rfl) (fun _ ↦ .rfl) (fun _ ↦ .rfl)
    (fun α ↦ heq_of_eq (φ.apply_symm_apply α))

variable (φ : ∀ {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {l : Edge V₁ a c}
    {r : Edge V₁ b d}, D.Cell p q l r ≃ D'.Cell p q l r)
  (map_hId : ∀ {a b : O₁} (f : Edge V₁ a b), φ (D.hId f) = D'.hId f)
  (map_vId : ∀ {a b : O₁} (f : Edge H₁ a b), φ (D.vId f) = D'.vId f)
  (map_hComp : ∀ {a b c d e f : O₁} {p : Edge H₁ a b} {q : Edge H₁ b c} {r : Edge H₁ d e}
    {t : Edge H₁ e f} {l : Edge V₁ a d} {m : Edge V₁ b e} {n : Edge V₁ c f}
    (α : D.Cell p r l m) (β : D.Cell q t m n), φ (D.hComp α β) = D'.hComp (φ α) (φ β))
  (map_vComp : ∀ {a b c d e f : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d} {r : Edge H₁ e f}
    {l : Edge V₁ a c} {m : Edge V₁ b d} {n : Edge V₁ c e} {t : Edge V₁ d f}
    (α : D.Cell p q l m) (β : D.Cell q r n t), φ (D.vComp α β) = D'.vComp (φ α) (φ β))

/-- The double isomorphism `ofCellEquiv` followed by its inverse fixes every cell. Unlike
`inv_map_hom_map_heq`, this is an equality, since `ofCellEquiv` is the identity on objects and
edges. -/
@[simp]
theorem ofCellEquiv_inv_map_hom_map {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d}
    {l : Edge V₁ a c} {r : Edge V₁ b d} (α : D.Cell p q l r) :
    (ofCellEquiv φ map_hId map_vId map_hComp map_vComp).inv.map
      ((ofCellEquiv φ map_hId map_vId map_hComp map_vComp).hom.map α) = α :=
  φ.symm_apply_apply α

/-- The inverse of the double isomorphism `ofCellEquiv` followed by the isomorphism fixes every
cell. -/
@[simp]
theorem ofCellEquiv_hom_map_inv_map {a b c d : O₁} {p : Edge H₁ a b} {q : Edge H₁ c d}
    {l : Edge V₁ a c} {r : Edge V₁ b d} (α : D'.Cell p q l r) :
    (ofCellEquiv φ map_hId map_vId map_hComp map_vComp).hom.map
      ((ofCellEquiv φ map_hId map_vId map_hComp map_vComp).inv.map α) = α :=
  φ.apply_symm_apply α

end OfCellEquiv

end StrictDoubleIso

end TauCeti
