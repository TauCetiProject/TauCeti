/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Morphisms and isomorphisms of pointed prestable families

A morphism of `n`-pointed prestable families over `S` is a morphism of total spaces over `S`
that carries the `i`th marking of the source to the `i`th marking of the target. With these
morphisms the `n`-pointed prestable families over `S` form a category. Its isomorphisms are the
isomorphisms of pointed curves used to compare families, and the automorphism group of a family
is the ordinary group `CategoryTheory.Aut P`.

Forgetting the markings is a faithful functor to schemes over `S` that reflects isomorphisms, so
a morphism of pointed families is an isomorphism exactly when its map of total spaces is one.
Automorphisms of a pointed family are thereby identified with the automorphisms of its total
space over `S` that fix every marking.

Base change along `g : T ⟶ S` and reindexing the markings are functors. Base change along the
identity and along a composite agree with the identity and with iterated base change up to
canonical natural isomorphisms, built from the canonical isomorphisms of pullbacks; these are
specified isomorphisms, not equalities of chosen pullbacks. Base change does not depend on the
chosen pullback either: a pointed family over `T` whose total space is a fibre product, compatibly
with the markings, is canonically isomorphic to the chosen base change.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.Hom`: morphisms of pointed prestable families.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.toOver`: the functor forgetting the markings.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.isoMk`: an isomorphism of pointed families
  from an isomorphism of total spaces over `S` preserving the markings.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.autToOver`: the injective homomorphism from
  the automorphism group of a pointed family to that of its total space over `S`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackFunctor`: base change as a functor.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackIdIso`,
  `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackCompIso`: the canonical isomorphisms
  `X ×_S S ≅ X` and `(X ×_S T) ×_T U ≅ X ×_S U` of pointed families.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackFunctorId`,
  `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullbackFunctorComp`: the canonical
  isomorphisms for base change along the identity and along a composite.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.isoPullback`: the canonical isomorphism from
  a pointed family over `T` presented by a fibre product to the chosen base change.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.reindexFunctor`: reindexing as a functor.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.isIso_iff_isIso_hom`: a morphism of pointed
  families is an isomorphism exactly when its map of total spaces is one.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.mem_range_autToOver_iff`: an automorphism of
  the total space over `S` comes from the pointed family exactly when it fixes every marking.

## Implementation notes

The morphisms, the category instance and the isomorphism criterion follow the existing
category API for models in `TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic` and
`TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Isomorphism`. The functoriality of base
change follows Mathlib's `CategoryTheory.Over.pullback` and uses its canonical isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`.

Only the functors `toOver`, `pullbackFunctor` and `reindexFunctor` expose their bodies, so that
their `simps` lemmas are definitional and the statements about `pullbackFunctor` typecheck.
`isoMk`, `pullbackMap`, the canonical isomorphisms, `isoPullback` and `autToOver` keep their
bodies private and are used through their characteristic lemmas.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, Definition 1.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {S T U : Scheme.{u}} {m n : ℕ}

/-- A **morphism of `n`-pointed prestable families** over `S`: a morphism of total spaces over
`S` carrying the `i`th marking of the source to the `i`th marking of the target. -/
@[ext]
structure Hom (P Q : PointedPrestableFamily S n) where
  /-- The morphism of total spaces. -/
  hom : P.total ⟶ Q.total
  /-- The morphism of total spaces lies over `S`. -/
  hom_comp_toBase : hom ≫ Q.toBase = P.toBase
  /-- The morphism of total spaces carries each marking to the corresponding marking. -/
  marking_comp_hom (i : Fin n) : P.marking i ≫ hom = Q.marking i

attribute [reassoc (attr := simp)] Hom.hom_comp_toBase Hom.marking_comp_hom

/-- The `n`-pointed prestable families over `S` form a category. -/
instance category : Category (PointedPrestableFamily S n) where
  Hom := Hom
  id P := ⟨𝟙 P.total, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by simp, by simp⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

variable {P Q R : PointedPrestableFamily S n}

/-- Morphisms of pointed prestable families are determined by their maps of total spaces. -/
@[ext]
theorem hom_ext {f g : P ⟶ Q} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
theorem id_hom (P : PointedPrestableFamily S n) : Hom.hom (𝟙 P) = 𝟙 P.total :=
  rfl

@[simp, reassoc]
theorem comp_hom (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- The functor sending a pointed prestable family to its total space over `S`, forgetting the
markings. -/
@[expose, simps]
def toOver : PointedPrestableFamily S n ⥤ Over S where
  obj P := Over.mk P.toBase
  map f := Over.homMk f.hom f.hom_comp_toBase

instance : (toOver (S := S) (n := n)).Faithful where
  map_injective h := hom_ext congr(($h).left)

/-- An isomorphism of pointed prestable families from an isomorphism of total spaces over `S`
carrying each marking to the corresponding marking. -/
def isoMk (e : P.total ≅ Q.total) (he : e.hom ≫ Q.toBase = P.toBase)
    (hm : ∀ i, P.marking i ≫ e.hom = Q.marking i) : P ≅ Q where
  hom := ⟨e.hom, he, hm⟩
  inv := ⟨e.inv, by rw [Iso.inv_comp_eq, he], fun i ↦ by rw [Iso.comp_inv_eq, hm]⟩

@[simp]
theorem isoMk_hom_hom (e : P.total ≅ Q.total) (he : e.hom ≫ Q.toBase = P.toBase)
    (hm : ∀ i, P.marking i ≫ e.hom = Q.marking i) : (isoMk e he hm).hom.hom = e.hom :=
  (rfl)

@[simp]
theorem isoMk_inv_hom (e : P.total ≅ Q.total) (he : e.hom ≫ Q.toBase = P.toBase)
    (hm : ∀ i, P.marking i ≫ e.hom = Q.marking i) : (isoMk e he hm).inv.hom = e.inv :=
  (rfl)

/-- A morphism of pointed prestable families is an isomorphism exactly when its map of total
spaces is an isomorphism. -/
theorem isIso_iff_isIso_hom (f : P ⟶ Q) : IsIso f ↔ IsIso f.hom :=
  ⟨fun _ ↦ ⟨(inv f).hom, congr(($(IsIso.hom_inv_id f)).hom), congr(($(IsIso.inv_hom_id f)).hom)⟩,
    fun _ ↦ (isoMk (asIso f.hom) f.hom_comp_toBase f.marking_comp_hom).isIso_hom⟩

instance isIso_hom_of_isIso (f : P ⟶ Q) [IsIso f] : IsIso f.hom :=
  (isIso_iff_isIso_hom f).1 ‹_›

instance isIso_of_isIso_hom (f : P ⟶ Q) [IsIso f.hom] : IsIso f :=
  (isIso_iff_isIso_hom f).2 ‹_›

instance : (toOver (S := S) (n := n)).ReflectsIsomorphisms where
  reflects f _ :=
    (isIso_iff_isIso_hom f).2 (by simpa using inferInstanceAs (IsIso (toOver.map f).left))

/-- Forgetting the markings, as a group homomorphism from the automorphisms of a pointed
prestable family to the automorphisms of its total space over `S`. -/
def autToOver (P : PointedPrestableFamily S n) : Aut P →* Aut (Over.mk P.toBase) :=
  toOver.mapAut P

@[simp]
theorem autToOver_apply_asIso_hom_left (e : Aut P) :
    (autToOver P e).asIso.hom.left = e.asIso.hom.hom := by
  unfold autToOver
  rfl

/-- An automorphism of a pointed prestable family is determined by its automorphism of the total
space. -/
theorem autToOver_injective (P : PointedPrestableFamily S n) :
    Function.Injective (autToOver P) :=
  fun _ _ h ↦ Aut.ext (Iso.ext (toOver.map_injective congr(($h).asIso.hom)))

/-- An automorphism of the total space of a pointed prestable family over `S` comes from an
automorphism of the pointed family exactly when it fixes every marking. -/
theorem mem_range_autToOver_iff (e : Aut (Over.mk P.toBase)) :
    e ∈ (autToOver P).range ↔ ∀ i, P.marking i ≫ e.asIso.hom.left = P.marking i := by
  refine ⟨?_, fun h ↦
    ⟨.of (isoMk ((Over.forget S).mapIso e.asIso) (Over.w e.asIso.hom) h), ?_⟩⟩
  · rintro ⟨e, rfl⟩ i
    exact e.asIso.hom.marking_comp_hom i
  · exact Aut.ext (Iso.ext (Over.OverMorphism.ext rfl))

/-! The proofs below about base change first unfold `PointedPrestableFamily.pullback`: the total
space `(P.pullback g).total` is only definitionally, not reducibly, equal to
`Limits.pullback P.toBase g`, so the pullback API does not apply to it before unfolding. -/

/-- The base change along `g : T ⟶ S` of a morphism of pointed prestable families over `S`. -/
def pullbackMap (g : T ⟶ S) (f : P ⟶ Q) : P.pullback g ⟶ Q.pullback g where
  hom := pullback.map P.toBase g Q.toBase g f.hom (𝟙 T) (𝟙 S) (by simp) (by simp)
  hom_comp_toBase := by
    dsimp only [pullback]
    simp
  marking_comp_hom i := by
    dsimp only [pullback]
    ext <;> simp

@[simp]
theorem pullbackMap_hom (g : T ⟶ S) (f : P ⟶ Q) :
    (pullbackMap g f).hom = pullback.map P.toBase g Q.toBase g f.hom (𝟙 T) (𝟙 S)
      (by simp) (by simp) :=
  (rfl)

/-- Base change along `g : T ⟶ S` as a functor from pointed prestable families over `S` to
pointed prestable families over `T`. -/
@[expose, simps]
def pullbackFunctor (g : T ⟶ S) : PointedPrestableFamily S n ⥤ PointedPrestableFamily T n where
  obj P := P.pullback g
  map f := pullbackMap g f
  map_id P := by
    ext1
    dsimp only [pullback]
    ext <;> simp
  map_comp f f' := by
    ext1
    simp only [comp_hom, pullbackMap_hom]
    dsimp only [pullback]
    ext <;> simp

/-- The canonical isomorphism from the base change of a pointed prestable family along the
identity of `S` to the family itself; on total spaces it is the first projection
`X ×_S S ⟶ X`. -/
def pullbackIdIso (P : PointedPrestableFamily S n) : P.pullback (𝟙 S) ≅ P :=
  isoMk (IsPullback.id_horiz P.toBase).isoPullback.symm
    (by
      dsimp only [pullback]
      simp)
    (fun i ↦ by
      dsimp only [pullback]
      rw [Iso.symm_hom, Iso.comp_inv_eq]
      ext <;> simp)

@[simp]
theorem pullbackIdIso_hom_hom (P : PointedPrestableFamily S n) :
    (pullbackIdIso P).hom.hom = pullback.fst P.toBase (𝟙 S) := by
  unfold pullbackIdIso
  exact (Category.comp_id _).symm.trans (IsPullback.id_horiz P.toBase).isoPullback_inv_fst

@[simp]
theorem pullbackIdIso_inv_hom (P : PointedPrestableFamily S n) :
    (pullbackIdIso P).inv.hom = (IsPullback.id_horiz P.toBase).isoPullback.hom := by
  unfold pullbackIdIso
  rfl

/-- The canonical isomorphism `pullbackIdIso` is natural in the family. -/
@[reassoc]
theorem pullbackIdIso_hom_naturality (f : P ⟶ Q) :
    pullbackMap (𝟙 S) f ≫ (pullbackIdIso Q).hom = (pullbackIdIso P).hom ≫ f := by
  ext1
  simp only [comp_hom, pullbackMap_hom, pullbackIdIso_hom_hom]
  dsimp only [pullback]
  simp

/-- Base change along the identity of `S` is canonically isomorphic to the identity functor. -/
def pullbackFunctorId : pullbackFunctor (𝟙 S) ≅ 𝟭 (PointedPrestableFamily S n) :=
  NatIso.ofComponents pullbackIdIso pullbackIdIso_hom_naturality

@[simp]
theorem pullbackFunctorId_app (P : PointedPrestableFamily S n) :
    pullbackFunctorId.app P = pullbackIdIso P := by
  unfold pullbackFunctorId
  rfl

/-- The canonical isomorphism from the iterated base change of a pointed prestable family along
`g : T ⟶ S` and `h : U ⟶ T` to its base change along `h ≫ g`; on total spaces it is the canonical
isomorphism `(X ×_S T) ×_T U ≅ X ×_S U`. -/
def pullbackCompIso (P : PointedPrestableFamily S n) (g : T ⟶ S) (h : U ⟶ T) :
    (P.pullback g).pullback h ≅ P.pullback (h ≫ g) :=
  isoMk (pullbackLeftPullbackSndIso P.toBase g h)
    (by
      dsimp only [pullback]
      simp)
    (fun i ↦ by
      dsimp only [pullback]
      ext <;> simp)

@[simp]
theorem pullbackCompIso_hom_hom (P : PointedPrestableFamily S n) (g : T ⟶ S) (h : U ⟶ T) :
    (pullbackCompIso P g h).hom.hom = (pullbackLeftPullbackSndIso P.toBase g h).hom := by
  unfold pullbackCompIso
  rfl

@[simp]
theorem pullbackCompIso_inv_hom (P : PointedPrestableFamily S n) (g : T ⟶ S) (h : U ⟶ T) :
    (pullbackCompIso P g h).inv.hom = (pullbackLeftPullbackSndIso P.toBase g h).inv := by
  unfold pullbackCompIso
  rfl

/-- The canonical isomorphism `pullbackCompIso` is natural in the family. -/
@[reassoc]
theorem pullbackCompIso_inv_naturality (g : T ⟶ S) (h : U ⟶ T) (f : P ⟶ Q) :
    pullbackMap (h ≫ g) f ≫ (pullbackCompIso Q g h).inv =
      (pullbackCompIso P g h).inv ≫ pullbackMap h (pullbackMap g f) := by
  exact hom_ext (pullbackLeftPullbackSndIso_inv_naturality
    P.toBase Q.toBase g h f.hom f.hom_comp_toBase)

/-- Base change along a composite `h ≫ g` is canonically isomorphic to base change along `g`
followed by base change along `h`. -/
def pullbackFunctorComp (g : T ⟶ S) (h : U ⟶ T) :
    pullbackFunctor (n := n) (h ≫ g) ≅ pullbackFunctor g ⋙ pullbackFunctor h :=
  NatIso.ofComponents (fun P ↦ (pullbackCompIso P g h).symm)
    (pullbackCompIso_inv_naturality g h)

@[simp]
theorem pullbackFunctorComp_app (g : T ⟶ S) (h : U ⟶ T) (P : PointedPrestableFamily S n) :
    (pullbackFunctorComp g h).app P = (pullbackCompIso P g h).symm := by
  unfold pullbackFunctorComp
  rfl

/-- **Base change does not depend on the chosen pullback.** Let `Q` be a pointed prestable family
over `T` and `a : Q.total ⟶ P.total` a morphism making `Q.total` a fibre product of `P.toBase`
and `g : T ⟶ S`, which carries each marking of `Q` to `g` followed by the corresponding marking
of `P`. Then `Q` is canonically isomorphic to the chosen base change `P.pullback g`; on total
spaces the isomorphism is the canonical isomorphism of fibre products. -/
def isoPullback (P : PointedPrestableFamily S n) (g : T ⟶ S) (Q : PointedPrestableFamily T n)
    (a : Q.total ⟶ P.total) (ha : IsPullback a Q.toBase P.toBase g)
    (hm : ∀ i, Q.marking i ≫ a = g ≫ P.marking i) : Q ≅ P.pullback g :=
  isoMk ha.isoPullback
    (by
      dsimp only [pullback]
      simp)
    (fun i ↦ by
      dsimp only [pullback]
      ext <;> simp [hm])

@[simp]
theorem isoPullback_hom_hom (P : PointedPrestableFamily S n) (g : T ⟶ S)
    (Q : PointedPrestableFamily T n) (a : Q.total ⟶ P.total)
    (ha : IsPullback a Q.toBase P.toBase g) (hm : ∀ i, Q.marking i ≫ a = g ≫ P.marking i) :
    (isoPullback P g Q a ha hm).hom.hom = ha.isoPullback.hom := by
  unfold isoPullback
  rfl

@[simp]
theorem isoPullback_inv_hom (P : PointedPrestableFamily S n) (g : T ⟶ S)
    (Q : PointedPrestableFamily T n) (a : Q.total ⟶ P.total)
    (ha : IsPullback a Q.toBase P.toBase g) (hm : ∀ i, Q.marking i ≫ a = g ≫ P.marking i) :
    (isoPullback P g Q a ha hm).inv.hom = ha.isoPullback.inv := by
  unfold isoPullback
  rfl

/-- Reindexing the markings along an injection `e : Fin m ↪ Fin n` as a functor; a morphism of
pointed families preserves in particular the reindexed markings. -/
@[expose, simps]
def reindexFunctor (e : Fin m ↪ Fin n) :
    PointedPrestableFamily S n ⥤ PointedPrestableFamily S m where
  obj P := P.reindex e
  map f := ⟨f.hom, f.hom_comp_toBase, fun i ↦ f.marking_comp_hom (e i)⟩

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry
