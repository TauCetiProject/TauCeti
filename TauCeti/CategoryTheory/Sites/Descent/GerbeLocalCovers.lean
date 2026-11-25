/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe

/-!
# The local covers of a gerbe

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor. This file names the three canonical
sieves behind the locality conditions of a gerbe (Stacks, Definition 8.11.1 (06NY)):

* `GerbeLocalCovers.objectCover F U`: the arrows `f : V ⟶ U` whose source fibre `F(V)` is
  nonempty;
* `GerbeLocalCovers.isomCover x y`, for objects `x y` over `U`: the arrows `f : V ⟶ U` along which
  `x` and `y` become isomorphic, `F(f) x ≅ F(f) y`;
* `GerbeLocalCovers.overlapCover i j x y`, for `i : T ⟶ V`, `j : T ⟶ W` and local objects `x` over
  `V`, `y` over `W`: the sieve on `T` on which `F(i) x` and `F(j) y` become isomorphic. No fibre
  products or terminal object are needed.

They are sieves for any pseudofunctor; the transport along composites uses the comparison
isomorphisms `F.mapComp'`, so `F` need not be strict. They are stable under pullback, and when `F`
is a gerbe for `J` they are `J`-covering, as are their intersections with any covering sieve. The
covering conclusion for `objectCover` does not produce an object over `U`: if `F(U)` is empty, the
identity of `U` is not in it.

This is the first part of AlgebraicModuliForArithmeticGeometry §4.17
(`GerbeLocalCovers.objectCover`, `GerbeLocalCovers.isomCover`, `GerbeLocalCovers.overlapCover`).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeLocalCovers`:

* `objectCover`, `pullback_objectCover`, `objectCover_mem`, `inf_objectCover_mem`,
  `id_notMem_objectCover`.
* `isomCover`, `isomCover_comm`, `isomCover_self`, `pullback_isomCover`, `isomCover_mem`,
  `inf_isomCover_mem`.
* `overlapCover`, `overlapCover_comm`, `overlapCover_mem`, `pullback_overlapCover_mem`.

## References

* [The Stacks Project, Definition 8.11.1 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeLocalCovers

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {J : GrothendieckTopology C}

/-- The comparison `F(g ≫ f) x ≅ F(g) (F(f) x)` of pullbacks along a composite. -/
noncomputable def compIso {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op U))) :
    (F.map (g ≫ f).op.toLoc).toFunctor.obj x ≅
      (F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x) :=
  (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc)).app x

/-! ### The object cover -/

/-- The **object cover** of `U`: the sieve of arrows `f : V ⟶ U` whose source fibre `F(V)` is
nonempty. -/
def objectCover (U : C) : Sieve U where
  arrows V _ := Nonempty (F.obj (.mk (op V)))
  downward_closed := fun ⟨x⟩ g ↦ ⟨(F.map g.op.toLoc).toFunctor.obj x⟩

variable {F}

@[simp]
theorem mem_objectCover_iff {U V : C} (f : V ⟶ U) :
    objectCover F U f ↔ Nonempty (F.obj (.mk (op V))) :=
  Iff.rfl

/-- The pullback of the object cover of `U` along `f : V ⟶ U` is the object cover of `V`. -/
@[simp]
theorem pullback_objectCover {U V : C} (f : V ⟶ U) :
    (objectCover F U).pullback f = objectCover F V :=
  Sieve.ext fun _ _ ↦ Iff.rfl

/-- For a gerbe, the object cover is covering. This does not produce an object over `U`. -/
theorem objectCover_mem [F.IsGerbe J] (U : C) : objectCover F U ∈ J U := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) U
  exact J.superset_covering (fun _ f hf ↦ h f hf) hR

/-- For a gerbe, the intersection of a covering sieve with the object cover is covering; each of
its members has a nonempty source fibre. -/
theorem inf_objectCover_mem [F.IsGerbe J] {U : C} {R : Sieve U} (hR : R ∈ J U) :
    R ⊓ objectCover F U ∈ J U :=
  J.intersection_covering hR (objectCover_mem U)

/-- If the fibre over `U` is empty, the identity of `U` is not in the object cover. -/
theorem id_notMem_objectCover {U : C} (h : IsEmpty (F.obj (.mk (op U)))) :
    ¬ objectCover F U (𝟙 U) :=
  fun ⟨x⟩ ↦ h.false x

/-! ### The isomorphism cover -/

/-- The **isomorphism cover** of objects `x y` over `U`: the sieve of arrows `f : V ⟶ U` along
which `x` and `y` become isomorphic. -/
def isomCover {U : C} (x y : F.obj (.mk (op U))) : Sieve U where
  arrows _ f := Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
  downward_closed {_ _} f := fun ⟨e⟩ g ↦
    ⟨compIso F f g x ≪≫ (F.map g.op.toLoc).toFunctor.mapIso e ≪≫ (compIso F f g y).symm⟩

@[simp]
theorem mem_isomCover_iff {U V : C} (x y : F.obj (.mk (op U))) (f : V ⟶ U) :
    isomCover x y f ↔
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :=
  Iff.rfl

/-- The isomorphism cover is symmetric. -/
theorem isomCover_comm {U : C} (x y : F.obj (.mk (op U))) : isomCover x y = isomCover y x :=
  Sieve.ext fun _ _ ↦ ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩

/-- The isomorphism cover of an object with itself is the maximal sieve, for any pseudofunctor. -/
@[simp]
theorem isomCover_self {U : C} (x : F.obj (.mk (op U))) : isomCover x x = ⊤ :=
  eq_top_iff.2 fun _ _ _ ↦ ⟨Iso.refl _⟩

/-- The pullback of the isomorphism cover of `x` and `y` along `f : V ⟶ U` is the isomorphism
cover of their pullbacks. -/
theorem pullback_isomCover {U V : C} (x y : F.obj (.mk (op U))) (f : V ⟶ U) :
    (isomCover x y).pullback f =
      isomCover ((F.map f.op.toLoc).toFunctor.obj x) ((F.map f.op.toLoc).toFunctor.obj y) :=
  Sieve.ext fun _ g ↦
    ⟨fun ⟨e⟩ ↦ ⟨(compIso F f g x).symm ≪≫ e ≪≫ compIso F f g y⟩,
      fun ⟨e⟩ ↦ ⟨compIso F f g x ≪≫ e ≪≫ (compIso F f g y).symm⟩⟩

/-- For a gerbe, the isomorphism cover of any two objects over `U` is covering; no global
isomorphism is assumed. -/
theorem isomCover_mem [F.IsGerbe J] {U : C} (x y : F.obj (.mk (op U))) : isomCover x y ∈ J U := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) x y
  exact J.superset_covering (fun _ f hf ↦ h f hf) hR

/-- For a gerbe, the intersection of a covering sieve with an isomorphism cover is covering. -/
theorem inf_isomCover_mem [F.IsGerbe J] {U : C} {R : Sieve U} (hR : R ∈ J U)
    (x y : F.obj (.mk (op U))) : R ⊓ isomCover x y ∈ J U :=
  J.intersection_covering hR (isomCover_mem x y)

/-! ### The overlap cover -/

/-- The **overlap cover** of local objects `x` over `V` and `y` over `W`, along `i : T ⟶ V` and
`j : T ⟶ W`: the sieve on `T` of arrows `q : S ⟶ T` along which `F(i) x` and `F(j) y` become
isomorphic. -/
def overlapCover {T V W : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) : Sieve T :=
  isomCover ((F.map i.op.toLoc).toFunctor.obj x) ((F.map j.op.toLoc).toFunctor.obj y)

theorem mem_overlapCover_iff {T V W S : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) (q : S ⟶ T) :
    overlapCover i j x y q ↔
      Nonempty ((F.map q.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj x) ≅
        (F.map q.op.toLoc).toFunctor.obj ((F.map j.op.toLoc).toFunctor.obj y)) :=
  Iff.rfl

/-- Swapping the two local charts leaves the overlap cover unchanged. -/
theorem overlapCover_comm {T V W : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) : overlapCover j i y x = overlapCover i j x y :=
  isomCover_comm _ _

/-- For a gerbe, every overlap cover is covering, even when the local objects lie over different
bases. -/
theorem overlapCover_mem [F.IsGerbe J] {T V W : C} (i : T ⟶ V) (j : T ⟶ W)
    (x : F.obj (.mk (op V))) (y : F.obj (.mk (op W))) : overlapCover i j x y ∈ J T :=
  isomCover_mem _ _

/-- For a gerbe, the pullback of an overlap cover along any `q : S ⟶ T` is covering. -/
theorem pullback_overlapCover_mem [F.IsGerbe J] {S T V W : C} (i : T ⟶ V) (j : T ⟶ W)
    (x : F.obj (.mk (op V))) (y : F.obj (.mk (op W))) (q : S ⟶ T) :
    (overlapCover i j x y).pullback q ∈ J S :=
  J.pullback_stable q (overlapCover_mem i j x y)

end CategoryTheory.Pseudofunctor.GerbeLocalCovers
