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
* `GerbeLocalCovers.isomCover F x y`, for objects `x y` over `U`: the arrows `f : V ⟶ U` along
  which `x` and `y` become isomorphic, `F(f) x ≅ F(f) y`;
* `GerbeLocalCovers.overlapCover F i j x y`, for `i : T ⟶ V`, `j : T ⟶ W` and local objects `x`
  over `V`, `y` over `W`: the sieve on `T` on which `F(i) x` and `F(j) y` become isomorphic. No
  fibre products or terminal object are needed.

They are sieves for any pseudofunctor; the transport along composites uses the comparison
isomorphisms `F.mapComp'`, so `F` need not be strict. They are stable under pullback, and
when `F` is a gerbe for `J` they are `J`-covering. The covering conclusion for `objectCover`
does not produce an object over `U`: if `F(U)` is empty, the identity of `U` is not in it.

These covers are where the local objects of a gerbe live: two local objects over different bases
are compared on their overlap cover. A member `q : S ⟶ T` of the overlap cover gives a chosen
isomorphism `F(q ≫ i) x ≅ F(q ≫ j) y` of the direct restrictions (`overlapIso`), and so the overlap
cover of the refined charts `q ≫ i`, `q ≫ j` is the maximal sieve.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeLocalCovers`:

* `objectCover`, `objectCover_eq_top_iff`, `objectCover_eq_bot_iff`, `pullback_objectCover`,
  `objectCover_mem`, `inf_objectCover_mem`, `id_notMem_objectCover`.
* `isomCover`, `isomCover_comm`, `isomCover_congr`, `isomCover_self`, `isomCover_eq_top_of_iso`,
  `pullback_isomCover`, `isomCover_mem`, `inf_isomCover_mem`.
* `overlapCover`, `overlapCover_comm`, `pullback_overlapCover`, `overlapCover_mem`,
  `inf_overlapCover_mem`, `pullback_overlapCover_mem`.
* `iteratedOverlapIso`, `overlapIso`, `overlapIso_hom`, `overlapIso_inv`: the chosen
  isomorphisms on a member of the overlap cover.
* `overlapCover_comp_eq_top`: the overlap cover of the refined charts is maximal.

## References

* [The Stacks Project, Definition 8.11.1 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeLocalCovers

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {J : GrothendieckTopology C}

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

/-- The object cover of `U` is maximal exactly when the fibre over `U` is nonempty. -/
theorem objectCover_eq_top_iff {U : C} : objectCover F U = ⊤ ↔ Nonempty (F.obj (.mk (op U))) :=
  Sieve.id_mem_iff_eq_top.symm

/-- The object cover of `U` is empty exactly when the fibre over every `V` mapping to `U` is
empty. -/
theorem objectCover_eq_bot_iff {U : C} :
    objectCover F U = ⊥ ↔ ∀ ⦃V : C⦄ (_ : V ⟶ U), IsEmpty (F.obj (.mk (op V))) :=
  ⟨fun h _ f ↦ ⟨fun x ↦ by simpa [h] using (mem_objectCover_iff f).2 ⟨x⟩⟩,
    fun h ↦ eq_bot_iff.2 fun _ f ⟨x⟩ ↦ (h f).false x⟩

/-- The pullback of the object cover of `U` along `f : V ⟶ U` is the object cover of `V`. -/
@[simp]
theorem pullback_objectCover {U V : C} (f : V ⟶ U) :
    (objectCover F U).pullback f = objectCover F V :=
  Sieve.ext fun _ _ ↦ Iff.rfl

/-- For a gerbe, the object cover is covering. This does not produce an object over `U`. -/
theorem objectCover_mem [F.IsGerbe J] (U : C) : objectCover F U ∈ J U := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) U
  exact J.superset_covering (fun _ f hf ↦ h f hf) hR

/-- For a gerbe, the common refinement of a covering sieve and the object cover is covering; each
of its members has a nonempty source fibre. -/
theorem inf_objectCover_mem [F.IsGerbe J] {U : C} {R : Sieve U} (hR : R ∈ J U) :
    R ⊓ objectCover F U ∈ J U :=
  J.intersection_covering hR (objectCover_mem U)

/-- If the fibre over `U` is empty, the identity of `U` is not in the object cover. -/
theorem id_notMem_objectCover {U : C} (h : IsEmpty (F.obj (.mk (op U)))) :
    ¬ objectCover F U (𝟙 U) :=
  fun ⟨x⟩ ↦ h.false x

/-! ### The isomorphism cover -/

variable (F) in
/-- The **isomorphism cover** of objects `x y` over `U`: the sieve of arrows `f : V ⟶ U` along
which `x` and `y` become isomorphic. -/
def isomCover {U : C} (x y : F.obj (.mk (op U))) : Sieve U where
  arrows _ f := Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
  downward_closed {_ _} f := fun ⟨e⟩ g ↦
    let c := Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc)
    ⟨c.app x ≪≫ (F.map g.op.toLoc).toFunctor.mapIso e ≪≫ (c.app y).symm⟩

@[simp]
theorem mem_isomCover_iff {U V : C} (x y : F.obj (.mk (op U))) (f : V ⟶ U) :
    isomCover F x y f ↔
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :=
  Iff.rfl

/-- The isomorphism cover is symmetric. -/
theorem isomCover_comm {U : C} (x y : F.obj (.mk (op U))) : isomCover F x y = isomCover F y x :=
  Sieve.ext fun _ _ ↦ ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩

/-- The isomorphism cover is unchanged when its two objects are replaced by isomorphic ones. -/
theorem isomCover_congr {U : C} {x x' y y' : F.obj (.mk (op U))} (e : x ≅ x') (e' : y ≅ y') :
    isomCover F x y = isomCover F x' y' :=
  Sieve.ext fun _ f ↦
    let m := (F.map f.op.toLoc).toFunctor
    ⟨fun ⟨g⟩ ↦ ⟨m.mapIso e.symm ≪≫ g ≪≫ m.mapIso e'⟩,
      fun ⟨g⟩ ↦ ⟨m.mapIso e ≪≫ g ≪≫ m.mapIso e'.symm⟩⟩

/-- The isomorphism cover of an object with itself is the maximal sieve, for any pseudofunctor. -/
@[simp]
theorem isomCover_self {U : C} (x : F.obj (.mk (op U))) : isomCover F x x = ⊤ :=
  eq_top_iff.2 fun _ _ _ ↦ ⟨Iso.refl _⟩

/-- The isomorphism cover of isomorphic objects is the maximal sieve, for any pseudofunctor. -/
theorem isomCover_eq_top_of_iso {U : C} {x y : F.obj (.mk (op U))} (e : x ≅ y) :
    isomCover F x y = ⊤ :=
  (isomCover_congr (Iso.refl x) e.symm).trans (isomCover_self x)

/-- The pullback of the isomorphism cover of `x` and `y` along `f : V ⟶ U` is the isomorphism
cover of their pullbacks. -/
@[simp]
theorem pullback_isomCover {U V : C} (x y : F.obj (.mk (op U))) (f : V ⟶ U) :
    (isomCover F x y).pullback f =
      isomCover F ((F.map f.op.toLoc).toFunctor.obj x) ((F.map f.op.toLoc).toFunctor.obj y) :=
  Sieve.ext fun _ g ↦
    let c := Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc)
    ⟨fun ⟨e⟩ ↦ ⟨(c.app x).symm ≪≫ e ≪≫ c.app y⟩, fun ⟨e⟩ ↦ ⟨c.app x ≪≫ e ≪≫ (c.app y).symm⟩⟩

/-- For a gerbe, the isomorphism cover of any two objects over `U` is covering; no global
isomorphism is assumed. -/
theorem isomCover_mem [F.IsGerbe J] {U : C} (x y : F.obj (.mk (op U))) :
    isomCover F x y ∈ J U := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) x y
  exact J.superset_covering (fun _ f hf ↦ h f hf) hR

/-- For a gerbe, the common refinement of a covering sieve and an isomorphism cover is
covering. -/
theorem inf_isomCover_mem [F.IsGerbe J] {U : C} {R : Sieve U} (hR : R ∈ J U)
    (x y : F.obj (.mk (op U))) : R ⊓ isomCover F x y ∈ J U :=
  J.intersection_covering hR (isomCover_mem x y)

/-! ### The overlap cover -/

variable (F) in
/-- The **overlap cover** of local objects `x` over `V` and `y` over `W`, along `i : T ⟶ V` and
`j : T ⟶ W`: the sieve on `T` of arrows `q : S ⟶ T` along which `F(i) x` and `F(j) y` become
isomorphic. -/
def overlapCover {T V W : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) : Sieve T :=
  isomCover F ((F.map i.op.toLoc).toFunctor.obj x) ((F.map j.op.toLoc).toFunctor.obj y)

@[simp]
theorem mem_overlapCover_iff {T V W S : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) (q : S ⟶ T) :
    overlapCover F i j x y q ↔
      Nonempty ((F.map q.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj x) ≅
        (F.map q.op.toLoc).toFunctor.obj ((F.map j.op.toLoc).toFunctor.obj y)) :=
  Iff.rfl

/-- Swapping the two local charts leaves the overlap cover unchanged. -/
theorem overlapCover_comm {T V W : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) : overlapCover F j i y x = overlapCover F i j x y :=
  isomCover_comm _ _

/-- The pullback of an overlap cover along `q : S ⟶ T` is the overlap cover of the restricted
charts `q ≫ i` and `q ≫ j`. -/
@[simp]
theorem pullback_overlapCover {S T V W : C} (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V)))
    (y : F.obj (.mk (op W))) (q : S ⟶ T) :
    (overlapCover F i j x y).pullback q = overlapCover F (q ≫ i) (q ≫ j) x y :=
  (pullback_isomCover _ _ q).trans <| isomCover_congr
    ((Cat.Hom.toNatIso (F.mapComp' i.op.toLoc q.op.toLoc (q ≫ i).op.toLoc)).app x).symm
    ((Cat.Hom.toNatIso (F.mapComp' j.op.toLoc q.op.toLoc (q ≫ j).op.toLoc)).app y).symm

/-- For a gerbe, every overlap cover is covering, even when the local objects lie over different
bases. -/
theorem overlapCover_mem [F.IsGerbe J] {T V W : C} (i : T ⟶ V) (j : T ⟶ W)
    (x : F.obj (.mk (op V))) (y : F.obj (.mk (op W))) : overlapCover F i j x y ∈ J T :=
  isomCover_mem _ _

/-- For a gerbe, the common refinement of a covering sieve and an overlap cover is covering. -/
theorem inf_overlapCover_mem [F.IsGerbe J] {T V W : C} {R : Sieve T} (hR : R ∈ J T)
    (i : T ⟶ V) (j : T ⟶ W) (x : F.obj (.mk (op V))) (y : F.obj (.mk (op W))) :
    R ⊓ overlapCover F i j x y ∈ J T :=
  J.intersection_covering hR (overlapCover_mem i j x y)

/-- For a gerbe, the pullback of an overlap cover along any `q : S ⟶ T` is covering. -/
theorem pullback_overlapCover_mem [F.IsGerbe J] {S T V W : C} (i : T ⟶ V) (j : T ⟶ W)
    (x : F.obj (.mk (op V))) (y : F.obj (.mk (op W))) (q : S ⟶ T) :
    (overlapCover F i j x y).pullback q ∈ J S :=
  J.pullback_stable q (overlapCover_mem i j x y)

/-! ### The chosen isomorphism on an overlap -/

/-- The chosen isomorphism `F(q) (F(i) x) ≅ F(q) (F(j) y)` of the iterated restrictions, on a
member `q` of the overlap cover. -/
noncomputable def iteratedOverlapIso {S T V W : C} {i : T ⟶ V} {j : T ⟶ W}
    {x : F.obj (.mk (op V))} {y : F.obj (.mk (op W))} {q : S ⟶ T}
    (hq : overlapCover F i j x y q) :
    (F.map q.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj x) ≅
      (F.map q.op.toLoc).toFunctor.obj ((F.map j.op.toLoc).toFunctor.obj y) :=
  ((mem_overlapCover_iff i j x y q).1 hq).some

/-- The **overlap isomorphism** on a member `q : S ⟶ T` of the overlap cover: the isomorphism
`F(q ≫ i) x ≅ F(q ≫ j) y` of the direct restrictions obtained from a chosen isomorphism
`F(q) (F(i) x) ≅ F(q) (F(j) y)` of the iterated restrictions (`iteratedOverlapIso`) through the
comparison isomorphisms of `F` for `q ≫ i` and `q ≫ j`. -/
noncomputable def overlapIso {S T V W : C} {i : T ⟶ V} {j : T ⟶ W} {x : F.obj (.mk (op V))}
    {y : F.obj (.mk (op W))} {q : S ⟶ T} (hq : overlapCover F i j x y q) :
    (F.map (q ≫ i).op.toLoc).toFunctor.obj x ≅ (F.map (q ≫ j).op.toLoc).toFunctor.obj y :=
  (Cat.Hom.toNatIso (F.mapComp' i.op.toLoc q.op.toLoc (q ≫ i).op.toLoc)).app x ≪≫
    iteratedOverlapIso hq ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' j.op.toLoc q.op.toLoc (q ≫ j).op.toLoc)).app y).symm

/-- The forward arrow of the overlap isomorphism: the `i`-side comparison, the chosen isomorphism
of the iterated restrictions, then the inverse of the `j`-side comparison. -/
theorem overlapIso_hom {S T V W : C} {i : T ⟶ V} {j : T ⟶ W} {x : F.obj (.mk (op V))}
    {y : F.obj (.mk (op W))} {q : S ⟶ T} (hq : overlapCover F i j x y q) :
    (overlapIso hq).hom =
      ((Cat.Hom.toNatIso (F.mapComp' i.op.toLoc q.op.toLoc (q ≫ i).op.toLoc)).app x).hom ≫
        (iteratedOverlapIso hq).hom ≫
          ((Cat.Hom.toNatIso (F.mapComp' j.op.toLoc q.op.toLoc (q ≫ j).op.toLoc)).app y).inv :=
  (rfl)

/-- The inverse arrow of the overlap isomorphism: the factors of the forward arrow, inverted, in
the reverse order. -/
theorem overlapIso_inv {S T V W : C} {i : T ⟶ V} {j : T ⟶ W} {x : F.obj (.mk (op V))}
    {y : F.obj (.mk (op W))} {q : S ⟶ T} (hq : overlapCover F i j x y q) :
    (overlapIso hq).inv =
      ((Cat.Hom.toNatIso (F.mapComp' j.op.toLoc q.op.toLoc (q ≫ j).op.toLoc)).app y).hom ≫
        (iteratedOverlapIso hq).inv ≫
          ((Cat.Hom.toNatIso (F.mapComp' i.op.toLoc q.op.toLoc (q ≫ i).op.toLoc)).app x).inv := by
  simp [overlapIso]

/-- **Refined charts.** If `q` is a member of the overlap cover, the overlap cover of the refined
charts `q ≫ i` and `q ≫ j` is the maximal sieve: every further `r : R ⟶ S` is a member, through
the image of `overlapIso` under `F(r)`. -/
theorem overlapCover_comp_eq_top {S T V W : C} {i : T ⟶ V} {j : T ⟶ W} {x : F.obj (.mk (op V))}
    {y : F.obj (.mk (op W))} {q : S ⟶ T} (hq : overlapCover F i j x y q) :
    overlapCover F (q ≫ i) (q ≫ j) x y = ⊤ :=
  isomCover_eq_top_of_iso (overlapIso hq)

end CategoryTheory.Pseudofunctor.GerbeLocalCovers
