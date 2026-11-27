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

An object is an algebraic set `Y ⊆ H^X` that is the solution set of its ideal `I_H(Y)`, so
that its coordinate group `G[X] ⧸ I_H(Y)` depends only on the points; `V_H(S)` is the object
`TauCeti.GroupAlgGeom.AlgSetCat.of ι S`.

The variables of the systems live in the universe of `G`, so that every coordinate group is a
group in that universe.

## Main definitions

* `TauCeti.GroupAlgGeom.GHom.equivUnderHom`: `G`-homomorphisms are the morphisms of groups under
  `G`.
* `TauCeti.GroupAlgGeom.AlgSetCat ι`: algebraic sets over `ι` with word maps.
* `TauCeti.GroupAlgGeom.AlgSetCat.homEquiv`: word maps `A → B` are the coefficient-preserving
  homomorphisms `Γ(B) → Γ(A)`.
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

/-! ### `G`-homomorphisms as morphisms under `G` -/

section Under

variable {G H K L : Type u} [Group G] [Group H] [Group K] [Group L]
  {ιH : G →* H} {ιK : G →* K} {ιL : G →* L}

/-- `G`-homomorphisms `H → K` are the morphisms between `H` and `K` in the category of groups
under `G`. -/
def GHom.equivUnderHom :
    GHom ιH ιK ≃ (Under.mk (GrpCat.ofHom ιH) ⟶ Under.mk (GrpCat.ofHom ιK)) where
  toFun φ := Under.homMk (GrpCat.ofHom φ.toMonoidHom) (by ext g; exact φ.map_coeff g)
  invFun f :=
    { toMonoidHom := f.right.hom
      map_coeff' g := congrArg (fun f' : GrpCat.of G ⟶ _ ↦ f'.hom g) (Under.w f) }
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/-- The `G`-homomorphism of a morphism under `G` is its underlying homomorphism. -/
@[simp]
theorem coe_equivUnderHom_symm (f : Under.mk (GrpCat.ofHom ιH) ⟶ Under.mk (GrpCat.ofHom ιK)) :
    ⇑(GHom.equivUnderHom.symm f) = f.right.hom :=
  (rfl)

/-- The underlying homomorphism of the morphism under `G` of a `G`-homomorphism, pointwise. -/
@[simp]
theorem GHom.equivUnderHom_right_hom_apply (φ : GHom ιH ιK) (x : H) :
    -- Stated with the coercion in `H →* K`, the form `simp` puts the left-hand side in, rather
    -- than in `(Under.mk (GrpCat.ofHom ιH)).right →* (Under.mk (GrpCat.ofHom ιK)).right`.
    @DFunLike.coe (H →* K) H (fun _ ↦ K) _ (GHom.equivUnderHom φ).right.hom x = φ x :=
  (rfl)

/-- The identity `G`-homomorphism is the identity morphism under `G`. -/
@[simp]
theorem GHom.equivUnderHom_id :
    GHom.equivUnderHom (GHom.id ιH) = 𝟙 (Under.mk (GrpCat.ofHom ιH)) := by
  apply GHom.equivUnderHom.symm.injective
  rw [Equiv.symm_apply_apply]
  ext x
  simp

/-- Composition of `G`-homomorphisms is composition of morphisms under `G`. -/
@[simp]
theorem GHom.equivUnderHom_comp (ψ : GHom ιK ιL) (φ : GHom ιH ιK) :
    GHom.equivUnderHom (ψ.comp φ) = GHom.equivUnderHom φ ≫ GHom.equivUnderHom ψ := by
  apply GHom.equivUnderHom.symm.injective
  rw [Equiv.symm_apply_apply]
  ext x
  simp only [coe_comp, Function.comp_apply, coe_equivUnderHom_symm, Under.comp_right,
    GrpCat.hom_comp, MonoidHom.coe_comp]
  rfl

end Under

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- An algebraic set over the coefficient homomorphism `ι`, as an object of the category of
algebraic sets: a set `Y ⊆ H^X` of points that is the solution set of its own ideal,
`V_H(I_H(Y)) = Y`. Every solution set `V_H(S)` is one (`TauCeti.GroupAlgGeom.AlgSetCat.of`). -/
structure AlgSetCat (ι : G →* H) where
  /-- The variables. -/
  X : Type u
  /-- The points of the algebraic set. -/
  carrier : Set (X → H)
  /-- The set is algebraic: it is the solution set of its ideal. -/
  V_I_carrier : V ι (I ι carrier : Set (GX G X)) = carrier

namespace AlgSetCat

variable {ι : G →* H}

/-- The ideal `I_H(Y)` of an algebraic set `Y`, the equations vanishing on it. Its coordinate group
is `G[X] ⧸ I_H(Y)`, and its solution set is `Y` again. -/
abbrev ideal (A : AlgSetCat ι) : Set (GX G A.X) := I ι A.carrier

variable (ι) in
/-- The algebraic set `V_H(S)` of a system `S ⊆ G[X]`. -/
abbrev of {Y : Type u} (S : Set (GX G Y)) : AlgSetCat ι :=
  ⟨Y, V ι S, V_I_V S⟩

/-- The points of an algebraic set. -/
abbrev Pt (A : AlgSetCat ι) : Type (max u v) := V ι A.ideal

/-- Algebraic sets with word maps as morphisms. -/
instance : Category (AlgSetCat ι) where
  Hom A B := {f : A.Pt → B.Pt // IsWordMap f}
  id _ := ⟨id, isWordMap_id⟩
  comp f g := ⟨g.val ∘ f.val, g.property.comp f.property⟩

@[ext]
theorem hom_ext {A B : AlgSetCat ι} {f g : A ⟶ B} (h : f.val = g.val) : f = g :=
  Subtype.ext h

@[simp]
theorem id_val (A : AlgSetCat ι) : (𝟙 A : A ⟶ A).val = id :=
  (rfl)

@[simp]
theorem comp_val {A B C : AlgSetCat ι} (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).val = g.val ∘ f.val :=
  (rfl)

/-- Word maps `A → B` are the coefficient-preserving homomorphisms `Γ(B) → Γ(A)` of coordinate
groups: `CoordGroup.gHomEquivWordMap` read on hom-sets. -/
noncomputable def homEquiv (A B : AlgSetCat ι) :
    (A ⟶ B) ≃ GHom (CoordGroup.coeff ι B.ideal) (CoordGroup.coeff ι A.ideal) :=
  (CoordGroup.gHomEquivWordMap ι A.ideal B.ideal).symm

/-- The word map induced by `homEquiv A B f` is `f`. -/
@[simp]
theorem comap_homEquiv {A B : AlgSetCat ι} (f : A ⟶ B) :
    CoordGroup.comap (homEquiv A B f) = f.val :=
  CoordGroup.comap_gHomEquivWordMap_symm f

/-- The morphism corresponding to a coordinate-group homomorphism is the map it induces. -/
@[simp]
theorem homEquiv_symm_apply_val {A B : AlgSetCat ι}
    (φ : GHom (CoordGroup.coeff ι B.ideal) (CoordGroup.coeff ι A.ideal)) :
    ((homEquiv A B).symm φ).val = CoordGroup.comap φ := by
  rw [homEquiv, Equiv.symm_symm, CoordGroup.gHomEquivWordMap_apply]

/-- The identity word map induces the identity of the coordinate group. -/
@[simp]
theorem homEquiv_id (A : AlgSetCat ι) : homEquiv A A (𝟙 A) = GHom.id _ :=
  CoordGroup.comap_injective (by rw [comap_homEquiv, CoordGroup.comap_id, id_val])

/-- A composite of word maps induces the composite of the induced homomorphisms, in the opposite
order. -/
@[simp]
theorem homEquiv_comp {A B C : AlgSetCat ι} (f : A ⟶ B) (g : B ⟶ C) :
    homEquiv A C (f ≫ g) = (homEquiv A B f).comp (homEquiv B C g) :=
  CoordGroup.comap_injective (by
    rw [comap_homEquiv, CoordGroup.comap_comp, comap_homEquiv, comap_homEquiv, comp_val])

end AlgSetCat

open AlgSetCat CoordGroup

variable (ι : G →* H)

/-- **The coordinate-group functor.** It sends an algebraic set `Y` to its coordinate group
`G[X] ⧸ I_H(Y)` under `G`, and a word map `Y → Y'` to the induced coefficient-preserving
homomorphism of coordinate groups `Γ(Y') → Γ(Y)`. -/
-- The body is exposed so that `coordGroupFunctor_map` typechecks outside this declaration: its
-- two sides live in `(coordGroupFunctor ι).obj A ⟶ (coordGroupFunctor ι).obj B` and in the
-- hom-set between the explicit coordinate groups, which agree only by unfolding `obj`.
@[expose] noncomputable def coordGroupFunctor : (AlgSetCat ι)ᵒᵖ ⥤ Under (GrpCat.of G) where
  obj A := Under.mk (GrpCat.ofHom (coeff ι A.unop.ideal))
  map {A B} f := GHom.equivUnderHom (AlgSetCat.homEquiv B.unop A.unop f.unop)
  map_id A := by simp
  map_comp f g := by simp

@[simp]
theorem coordGroupFunctor_obj (A : (AlgSetCat ι)ᵒᵖ) :
    (coordGroupFunctor ι).obj A = Under.mk (GrpCat.ofHom (coeff ι A.unop.ideal)) :=
  (rfl)

@[simp]
theorem coordGroupFunctor_map {A B : (AlgSetCat ι)ᵒᵖ} (f : A ⟶ B) :
    (coordGroupFunctor ι).map f = GHom.equivUnderHom (AlgSetCat.homEquiv B.unop A.unop f.unop) :=
  (rfl)

/-- **The coordinate-group functor is fully faithful**, for an arbitrary coefficient
homomorphism: word maps `Y → Y'` correspond to coefficient-preserving homomorphisms
`Γ(Y') → Γ(Y)` (Baumslag, Myasnikov and Remeslennikov, Theorem 4). -/
noncomputable def coordGroupFunctor.fullyFaithful : (coordGroupFunctor ι).FullyFaithful where
  preimage {A B} φ := ((AlgSetCat.homEquiv B.unop A.unop).symm (GHom.equivUnderHom.symm φ)).op
  map_preimage {A B} φ := by
    rw [coordGroupFunctor_map, Quiver.Hom.unop_op, Equiv.apply_symm_apply]
    exact GHom.equivUnderHom.apply_symm_apply (β := Under.mk (GrpCat.ofHom
      (coeff ι A.unop.ideal)) ⟶ Under.mk (GrpCat.ofHom (coeff ι B.unop.ideal))) φ
  preimage_map {A B} f := by
    rw [coordGroupFunctor_map, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Quiver.Hom.op_unop]

instance : (coordGroupFunctor ι).Full :=
  (coordGroupFunctor.fullyFaithful ι).full

instance : (coordGroupFunctor ι).Faithful :=
  (coordGroupFunctor.fullyFaithful ι).faithful

end TauCeti.GroupAlgGeom
