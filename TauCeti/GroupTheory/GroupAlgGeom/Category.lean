/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.WordMap
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The category of algebraic sets and the coordinate-group functor

Fix a coefficient homomorphism `ι : G →* H`. Algebraic sets `V_H(S)`, for systems `S ⊆ G[X]`,
form a category `TauCeti.GroupAlgGeom.AlgSetCat ι` whose morphisms are the maps given by tuples of
words (`TauCeti.GroupAlgGeom.IsWordMap`), composed as functions. The coordinate group is a
contravariant functor `TauCeti.GroupAlgGeom.coordGroupFunctor ι` from it to groups under `G`,
whose objects are groups with a homomorphism from `G` and whose morphisms are the
coefficient-preserving homomorphisms. It sends `V_H(S)` to `G_{R(S)}` with its coefficient map,
and a word map to the homomorphism of coordinate groups it induces.

The functor is fully faithful (`TauCeti.GroupAlgGeom.coordGroupFunctor.fullyFaithful`), so it is an
anti-equivalence of algebraic sets onto the full subcategory of coordinate groups, its essential
image. This holds for an arbitrary `ι`: no injectivity of `ι` and no nonemptiness of the algebraic
sets is assumed. Fullness is `TauCeti.GroupAlgGeom.CoordGroup.exists_wordMap_representation` and
faithfulness `TauCeti.GroupAlgGeom.CoordGroup.homOfMapsToWordMap_eq_iff`, packaged as
`TauCeti.GroupAlgGeom.CoordGroup.gHomEquivWordMap`.

The variables of the systems live in the universe of `G`, so that every coordinate group is a
group in that universe.

## Main definitions

* `TauCeti.GroupAlgGeom.AlgSetCat ι`: algebraic sets over `ι` with word maps.
* `TauCeti.GroupAlgGeom.coordGroupFunctor ι`: the contravariant coordinate-group functor
  `(AlgSetCat ι)ᵒᵖ ⥤ Under (GrpCat.of G)`.
* `TauCeti.GroupAlgGeom.coordGroupFunctor.fullyFaithful`: it is fully faithful.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.5, Theorem 4 and Corollary 9.
-/

public section

open CategoryTheory

namespace TauCeti.GroupAlgGeom

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- An algebraic set over the coefficient homomorphism `ι`, as an object of the category of
algebraic sets: a type of variables and a system of equations in them. Its points are
`V ι S`. -/
@[nolint unusedArguments]
structure AlgSetCat (ι : G →* H) where
  /-- The variables of the system. -/
  X : Type u
  /-- The system of equations, whose solution set is the algebraic set. -/
  S : Set (GX G X)

namespace AlgSetCat

variable {ι : G →* H}

/-- The points of an algebraic set. -/
abbrev Pt (A : AlgSetCat ι) : Type (max u v) := V ι A.S

/-- A morphism of algebraic sets: a map of points given by a tuple of words. -/
@[ext]
structure Hom (A B : AlgSetCat ι) where
  /-- The underlying map of points. -/
  toFun : A.Pt → B.Pt
  /-- The map is given by a tuple of words. -/
  isWordMap : IsWordMap toFun

/-- Algebraic sets with word maps as morphisms. -/
instance : Category (AlgSetCat ι) where
  Hom := Hom
  id _ := ⟨id, isWordMap_id⟩
  comp f g := ⟨g.toFun ∘ f.toFun, g.isWordMap.comp f.isWordMap⟩

@[ext]
theorem hom_ext {A B : AlgSetCat ι} {f g : A ⟶ B} (h : f.toFun = g.toFun) : f = g :=
  Hom.ext h

@[simp]
theorem id_toFun (A : AlgSetCat ι) : Hom.toFun (𝟙 A) = id :=
  (rfl)

@[simp]
theorem comp_toFun {A B C : AlgSetCat ι} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toFun (f ≫ g) = g.toFun ∘ f.toFun :=
  (rfl)

/-- The coefficient-preserving homomorphism `Γ(B) → Γ(A)` induced by a word map `A → B`. -/
noncomputable def Hom.coordGroupHom {A B : AlgSetCat ι} (f : Hom A B) :
    GHom (CoordGroup.coeff ι B.S) (CoordGroup.coeff ι A.S) :=
  (CoordGroup.gHomEquivWordMap ι A.S B.S).symm ⟨f.toFun, f.isWordMap⟩

/-- The word map induced by `f.coordGroupHom` is `f`. -/
@[simp]
theorem Hom.comap_coordGroupHom {A B : AlgSetCat ι} (f : Hom A B) :
    CoordGroup.comap f.coordGroupHom = f.toFun :=
  CoordGroup.comap_gHomEquivWordMap_symm _

/-- The word map induced by a coefficient-preserving homomorphism `Γ(B) → Γ(A)`. -/
def Hom.ofGHom {A B : AlgSetCat ι} (φ : GHom (CoordGroup.coeff ι B.S) (CoordGroup.coeff ι A.S)) :
    Hom A B :=
  ⟨CoordGroup.comap φ, CoordGroup.isWordMap_comap φ⟩

/-- The homomorphism induced by the word map of `φ` is `φ`. -/
@[simp]
theorem Hom.coordGroupHom_ofGHom {A B : AlgSetCat ι}
    (φ : GHom (CoordGroup.coeff ι B.S) (CoordGroup.coeff ι A.S)) :
    (Hom.ofGHom φ).coordGroupHom = φ :=
  CoordGroup.comap_injective (by rw [Hom.comap_coordGroupHom]; rfl)

/-- The identity word map induces the identity of the coordinate group. -/
theorem Hom.coordGroupHom_id (A : AlgSetCat ι) :
    Hom.coordGroupHom (𝟙 A) = GHom.id _ :=
  CoordGroup.comap_injective (by rw [Hom.comap_coordGroupHom, CoordGroup.comap_id]; rfl)

/-- A composite of word maps induces the composite of the induced homomorphisms, in the opposite
order. -/
theorem Hom.coordGroupHom_comp {A B C : AlgSetCat ι} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.coordGroupHom (f ≫ g) = f.coordGroupHom.comp g.coordGroupHom :=
  CoordGroup.comap_injective (by
    rw [Hom.comap_coordGroupHom, CoordGroup.comap_comp, Hom.comap_coordGroupHom,
      Hom.comap_coordGroupHom, comp_toFun])

end AlgSetCat

open AlgSetCat CoordGroup

variable (ι : G →* H)

/-- The coordinate group of an algebraic set, as a group under `G`. -/
abbrev coordGroupUnder (A : AlgSetCat ι) : Under (GrpCat.of G) :=
  Under.mk (GrpCat.ofHom (coeff ι A.S))

variable {ι} in
/-- A coefficient-preserving homomorphism of coordinate groups as a morphism of groups under `G`.
-/
def GHom.toUnderHom {A B : AlgSetCat ι} (φ : GHom (coeff ι B.S) (coeff ι A.S)) :
    coordGroupUnder ι B ⟶ coordGroupUnder ι A :=
  Under.homMk (GrpCat.ofHom φ.toMonoidHom) (by ext g; exact φ.map_coeff g)

variable {ι} in
/-- A morphism of groups under `G` between coordinate groups as a coefficient-preserving
homomorphism. -/
def GHom.ofUnderHom {A B : AlgSetCat ι} (φ : coordGroupUnder ι B ⟶ coordGroupUnder ι A) :
    GHom (coeff ι B.S) (coeff ι A.S) where
  toMonoidHom := φ.right.hom
  map_coeff' g := congrArg (fun f : GrpCat.of G ⟶ _ ↦ f.hom g) (Under.w φ)

variable {ι} in
/-- `GHom.ofUnderHom` is inverse to `GHom.toUnderHom`. -/
@[simp]
theorem GHom.toUnderHom_ofUnderHom {A B : AlgSetCat ι}
    (φ : coordGroupUnder ι B ⟶ coordGroupUnder ι A) : (GHom.ofUnderHom φ).toUnderHom = φ := by
  ext x
  rfl

variable {ι} in
/-- The identity homomorphism is the identity morphism under `G`. -/
@[simp]
theorem GHom.toUnderHom_id (A : AlgSetCat ι) :
    (GHom.id (coeff ι A.S)).toUnderHom = 𝟙 (coordGroupUnder ι A) := by
  ext x
  simp [GHom.toUnderHom]

variable {ι} in
/-- Composition of coefficient-preserving homomorphisms is composition under `G`. -/
theorem GHom.toUnderHom_comp {A B C : AlgSetCat ι} (ψ : GHom (coeff ι C.S) (coeff ι B.S))
    (φ : GHom (coeff ι B.S) (coeff ι A.S)) :
    (φ.comp ψ).toUnderHom = ψ.toUnderHom ≫ φ.toUnderHom := by
  ext x
  simp [GHom.toUnderHom]

/-- **The coordinate-group functor.** It sends an algebraic set `V_H(S)` to its coordinate group
`G_{R(S)}` under `G`, and a word map `V_H(S) → V_H(T)` to the induced coefficient-preserving
homomorphism `G_{R(T)} → G_{R(S)}`. -/
@[expose] noncomputable def coordGroupFunctor : (AlgSetCat ι)ᵒᵖ ⥤ Under (GrpCat.of G) where
  obj A := coordGroupUnder ι A.unop
  map f := f.unop.coordGroupHom.toUnderHom
  map_id A := by
    rw [unop_id, Hom.coordGroupHom_id, GHom.toUnderHom_id]
  map_comp f g := by
    rw [unop_comp, Hom.coordGroupHom_comp, GHom.toUnderHom_comp]

@[simp]
theorem coordGroupFunctor_obj (A : (AlgSetCat ι)ᵒᵖ) :
    (coordGroupFunctor ι).obj A = coordGroupUnder ι A.unop :=
  (rfl)

@[simp]
theorem coordGroupFunctor_map {A B : (AlgSetCat ι)ᵒᵖ} (f : A ⟶ B) :
    (coordGroupFunctor ι).map f = f.unop.coordGroupHom.toUnderHom :=
  (rfl)

/-- **The coordinate-group functor is fully faithful**, for an arbitrary coefficient
homomorphism: word maps `V_H(S) → V_H(T)` correspond to coefficient-preserving homomorphisms
`G_{R(T)} → G_{R(S)}` (Baumslag, Myasnikov and Remeslennikov, Theorem 4). -/
noncomputable def coordGroupFunctor.fullyFaithful : (coordGroupFunctor ι).FullyFaithful where
  preimage {A B} φ := (show B.unop ⟶ A.unop from Hom.ofGHom (GHom.ofUnderHom φ)).op
  map_preimage {A B} φ := by
    rw [coordGroupFunctor_map, Quiver.Hom.unop_op, Hom.coordGroupHom_ofGHom]
    exact GHom.toUnderHom_ofUnderHom (A := B.unop) (B := A.unop) φ
  preimage_map f := by
    apply Quiver.Hom.unop_inj
    apply AlgSetCat.hom_ext
    rw [Quiver.Hom.unop_op, coordGroupFunctor_map]
    change comap _ = _
    rw [← Hom.comap_coordGroupHom f.unop]
    congr 1

instance : (coordGroupFunctor ι).Full :=
  (coordGroupFunctor.fullyFaithful ι).full

instance : (coordGroupFunctor ι).Faithful :=
  (coordGroupFunctor.fullyFaithful ι).faithful

end TauCeti.GroupAlgGeom
