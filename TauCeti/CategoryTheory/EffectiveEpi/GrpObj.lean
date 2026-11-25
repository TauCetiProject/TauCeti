/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.EffectiveEpi.Descent
public import TauCeti.CategoryTheory.Monoidal.Grp.DescentDatum
public import TauCeti.CategoryTheory.Monoidal.Grp.Faithful
import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Descent of group objects along effective epimorphisms

Let `p : S' ⟶ S` be a morphism in a category with pullbacks, all of whose base changes are
effective epimorphisms, and let `S'' = S' ×_S S'`. Group objects over `S` are group objects in the
cartesian monoidal category `Over S`, whose product is the fibre product over `S`. For `X` over
`S` write `X' = X ×_S S'`, the image of `X` under the base change functor `Over.pullback p`.

This file descends group structures on an object which has already been descended, both in terms of
morphisms whose two pullbacks to `S''` agree and in terms of effective descent data
(`TauCeti.DescentDatum`).

* If `X'` carries a monoid (group) object structure over `S'` whose unit, multiplication (and
  inverse) satisfy the descent condition of `TauCeti.descendHom`, then they descend to the unique
  monoid (group) object structure on `X` whose base change is the given one (`descendMonObj`,
  `descendGrpObj`).
* If `D` is a monoid-compatible descent datum (`D.IsMon`) on a monoid (group) object `Y` over `S'`,
  and `f : Hom (baseChange p X₀) D` is an isomorphism of descent data, then transporting the
  structure along `f⁻¹` and descending the bundled structure morphisms `oneHom D`, `mulHom D` (and
  `invHom D`) gives the unique monoid (group) object structure on `X₀` for which `f.hom` is a
  monoid homomorphism (`DescentDatum.Hom.descendMonObj`, `DescentDatum.Hom.descendGrpObj`).
* Descending a homomorphism gives a homomorphism (`isMonHom_descendHom`,
  `DescentDatum.Hom.isMonHom_descend`), uniqueness isomorphisms of descended group objects are
  group isomorphisms (`DescentDatum.Hom.descendGrpIso`), and commutativity descends as well.

The base change functor is faithful and monoidal, so the group axioms on `X` follow from those on
`X'` (`CategoryTheory.Functor.monObjOfFaithful`). Descent of morphisms supplies the structure
morphisms themselves.

For schemes, Mathlib shows that a flat surjective morphism which is quasi-compact, or locally of
finite presentation, is an effective epimorphism, and that these properties are stable under base
change (`Mathlib.AlgebraicGeometry.Sites.Fpqc`). Instance search therefore discharges the
hypothesis on `p` for any fpqc or fppf morphism of schemes, so the results are effective fpqc
(and fppf) descent of group schemes, group laws and their axioms, and homomorphisms.

## Main definitions

* `TauCeti.descendMonObj`, `TauCeti.descendGrpObj`: the monoid (group) object structure on `X`
  descended from one on `X ×_S S'` whose structure morphisms satisfy the descent condition.
* `TauCeti.DescentDatum.Hom.descendMonObj`, `TauCeti.DescentDatum.Hom.descendGrpObj`: the monoid
  (group) object structure on `X₀` descended along an isomorphism `baseChange p X₀ ⟶ D` to a
  monoid-compatible descent datum `D`.
* `TauCeti.DescentDatum.baseChangeGrpHomEquiv`, `TauCeti.DescentDatum.Hom.descendGrpIso`: full
  faithfulness of base change on `Grp (Over S)` into descent data and uniqueness up to unique
  group isomorphism of effective group-object descent.

## Main statements

* `TauCeti.monObjObj_descendMonObj`, `TauCeti.grpObjObj_descendGrpObj`: the base change of the
  descended structure is the given one.
* `TauCeti.eq_descendMonObj`, `TauCeti.eq_descendGrpObj`,
  `TauCeti.DescentDatum.Hom.eq_descendMonObj`, `TauCeti.DescentDatum.Hom.eq_descendGrpObj`:
  uniqueness of the descended structure.
* `TauCeti.isCommMonObj_descendMonObj`, `TauCeti.isCommMonObj_descendGrpObj`,
  `TauCeti.DescentDatum.Hom.isCommMonObj_of_mono`,
  `TauCeti.DescentDatum.Hom.isCommMonObj_descendMonObj`,
  `TauCeti.DescentDatum.Hom.isCommMonObj_descendGrpObj`: the descended structure is commutative if
  the given one is.
* `TauCeti.isMonHom_descendHom`, `TauCeti.DescentDatum.Hom.isMonHom_descend`,
  `TauCeti.DescentDatum.Hom.isMonHom_of_comp_eq_baseChangeHom`: a homomorphism satisfying the
  descent condition (or intertwining morphisms of descent data) descends to a homomorphism.
-/

public section

namespace TauCeti

open CategoryTheory Limits MonoidalCategory MonObj
open scoped Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)
  [∀ {Z : C} (g : Z ⟶ S), EffectiveEpi (pullback.fst g p)]

section MonObj

variable (X : Over S) [MonObj ((Over.pullback p).obj X)]

/-- **Descent of a monoid object.** Let `X` be an object over `S` such that `X ×_S S'` is a monoid
object over `S'`. If the unit and the multiplication of `X ×_S S'` satisfy the descent condition of
`TauCeti.descendHom` (their two pullbacks to `S' ×_S S'` agree), then they descend to a monoid
object structure on `X` over `S` (`monObjObj_descendMonObj`). -/
noncomputable abbrev descendMonObj
    (h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p)
    (h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p) :
    MonObj X :=
  (Over.pullback p).monObjOfFaithful X (descendHom p _ h_one) (descendHom p _ h_mul)
    (pullback_map_descendHom p _ h_one) (pullback_map_descendHom p _ h_mul)

variable
    {h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}
    {h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}

/-- **Effectiveness of descent of monoid objects.** The base change of the descended monoid
object structure is the given one. -/
theorem monObjObj_descendMonObj :
    letI := descendMonObj p X h_one h_mul
    Functor.monObjObj (F := Over.pullback p) X = ‹MonObj ((Over.pullback p).obj X)› :=
  (Over.pullback p).monObjObj_monObjOfFaithful X _ _ _ _

/-- **Uniqueness of descended monoid objects.** A monoid object structure on `X` whose base change
is the given one is the descended structure. -/
theorem eq_descendMonObj (h : MonObj X)
    (e : Functor.monObjObj (F := Over.pullback p) X = ‹MonObj ((Over.pullback p).obj X)›) :
    h = descendMonObj p X h_one h_mul :=
  (Over.pullback p).monObjObj_injective X <| e.trans (monObjObj_descendMonObj p X).symm

/-- **Descent of commutativity.** If the given monoid object structure on `X ×_S S'` is
commutative, so is the descended monoid object structure on `X`. -/
theorem isCommMonObj_descendMonObj [IsCommMonObj ((Over.pullback p).obj X)] :
    letI := descendMonObj p X h_one h_mul
    IsCommMonObj X := by
  let := descendMonObj p X h_one h_mul
  refine ((Over.pullback p).isCommMonObj_obj_iff X).1 ?_
  rw [monObjObj_descendMonObj p X]
  infer_instance

end MonObj

section GrpObj

variable (X : Over S) [GrpObj ((Over.pullback p).obj X)]

/-- **Descent of a group object.** Let `X` be an object over `S` such that `X ×_S S'` is a group
object over `S'`. If the unit, the multiplication and the inverse of `X ×_S S'` satisfy the descent
condition of `TauCeti.descendHom` (their two pullbacks to `S' ×_S S'` agree), then they descend to a
group object structure on `X` over `S` (`grpObjObj_descendGrpObj`). -/
noncomputable abbrev descendGrpObj
    (h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p)
    (h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p)
    (h_inv : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p) :
    GrpObj X :=
  (Over.pullback p).grpObjOfFaithful X (descendHom p _ h_one) (descendHom p _ h_mul)
    (descendHom p _ h_inv) (pullback_map_descendHom p _ h_one)
    (pullback_map_descendHom p _ h_mul) (pullback_map_descendHom p _ h_inv)

variable
    {h_one : pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (𝟙_ (Over S)).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}
    {h_mul : pullback.mapSnd (X ⊗ X).hom p _ (pullback.fst p p) rfl ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p =
      pullback.mapSnd (X ⊗ X).hom p _ (pullback.snd p p) pullback.condition.symm ≫
        (Functor.OplaxMonoidal.δ (Over.pullback p) X X ≫ μ[(Over.pullback p).obj X]).left ≫
          pullback.fst X.hom p}
    {h_inv : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫
        ι[(Over.pullback p).obj X].left ≫ pullback.fst X.hom p}

/-- **Effectiveness of descent of group objects.** The base change of the descended group object
structure is the given one. -/
theorem grpObjObj_descendGrpObj :
    letI := descendGrpObj p X h_one h_mul h_inv
    Functor.grpObjObj (F := Over.pullback p) (G := X) = ‹GrpObj ((Over.pullback p).obj X)› :=
  (Over.pullback p).grpObjObj_grpObjOfFaithful X _ _ _ _ _ _

/-- **Uniqueness of descended group objects.** A group object structure on `X` whose base change
is the given one is the descended structure. -/
theorem eq_descendGrpObj (h : GrpObj X)
    (e : Functor.grpObjObj (F := Over.pullback p) (G := X) = ‹GrpObj ((Over.pullback p).obj X)›) :
    h = descendGrpObj p X h_one h_mul h_inv :=
  (Over.pullback p).grpObjObj_injective X <| e.trans (grpObjObj_descendGrpObj p X).symm

/-- **Descent of commutativity.** If the given group object structure on `X ×_S S'` is
commutative, so is the descended group object structure on `X`. The underlying monoid object of
`descendGrpObj` is `descendMonObj` by construction, so this is `isCommMonObj_descendMonObj`. -/
theorem isCommMonObj_descendGrpObj [IsCommMonObj ((Over.pullback p).obj X)] :
    letI := descendGrpObj p X h_one h_mul h_inv
    IsCommMonObj X :=
  isCommMonObj_descendMonObj p X

end GrpObj

/-- **Descent of homomorphisms.** Let `X` and `Y` be monoid objects over `S`. A homomorphism
`φ : X ×_S S' ⟶ Y ×_S S'` of the base-changed monoid objects whose two pullbacks to `S' ×_S S'`
agree descends to a homomorphism `X ⟶ Y`. -/
instance isMonHom_descendHom {X Y : Over S} [MonObj X] [MonObj Y]
    (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y) [IsMonHom φ]
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    IsMonHom (descendHom p φ h) := by
  rw [← (Over.pullback p).isMonHom_map_iff, pullback_map_descendHom]
  infer_instance

namespace DescentDatum

variable {p}

/-- **Descent of homomorphisms of canonical descent data.** If `φ : baseChange p X ⟶ baseChange p Y`
is a morphism of canonical descent data whose underlying morphism in `Over S'` is a monoid
homomorphism, then its descended morphism `φ.descend : X ⟶ Y` in `Over S` is a monoid
homomorphism. -/
instance Hom.isMonHom_descend {X Y : Over S} [MonObj X] [MonObj Y]
    (φ : Hom (baseChange p X) (baseChange p Y)) [IsMonHom φ.hom] :
    IsMonHom φ.descend := by
  rw [← (Over.pullback p).isMonHom_map_iff, ← baseChangeHom_hom, baseChangeHom_descend]
  infer_instance

/-- **Compatibility of descended morphisms with monoid structures.** If `u : X ⟶ Y` in `Over S`
intertwines monoid-homomorphism morphisms of descent data `g : baseChange p X ⟶ D` and
`f : D ⟶ baseChange p Y` via `f.comp g = baseChangeHom p u`, then `u` is a monoid
homomorphism. -/
theorem Hom.isMonHom_of_comp_eq_baseChangeHom {X Y : Over S} [MonObj X] [MonObj Y]
    {Z : Over S'} [MonObj Z] {D : DescentDatum p Z}
    (f : Hom D (baseChange p Y)) (g : Hom (baseChange p X) D) [IsMonHom f.hom] [IsMonHom g.hom]
    {u : X ⟶ Y} (h : f.comp g = baseChangeHom p u) :
    IsMonHom u := by
  rw [← (Over.pullback p).isMonHom_map_iff, ← baseChangeHom_hom, ← h, Hom.comp_hom]
  infer_instance

/-- **Uniqueness isomorphism of descended monoid objects.** If `f : baseChange p X ⟶ D` and
`g : baseChange p Y ⟶ D` are isomorphisms of descent data whose underlying morphisms in `Over S'`
are monoid homomorphisms, then the comparison isomorphism `f.descendIso g : X ≅ Y` is a monoid
isomorphism. -/
instance Hom.isMonHom_descendIso_hom {X Y : Over S} [MonObj X] [MonObj Y]
    {W : Over S'} [MonObj W] {D : DescentDatum p W}
    (f : Hom (baseChange p X) D) (g : Hom (baseChange p Y) D)
    [IsIso f.hom] [IsIso g.hom] [IsMonHom f.hom] [IsMonHom g.hom] :
    IsMonHom (f.descendIso g).hom := by
  have : IsMonHom g.inv.hom := by
    have : IsMonHom (asIso g.hom).hom := ‹_›
    simpa [Hom.inv_hom] using (inferInstance : IsMonHom (asIso g.hom).inv)
  have : IsMonHom (g.inv.comp f).hom := by
    rw [Hom.comp_hom]
    infer_instance
  rw [Hom.descendIso_hom]
  infer_instance

section MonObj

variable {X₀ : Over S} {Y : Over S'} [MonObj Y] {D : DescentDatum p Y} [D.IsMon]
  (f : Hom (baseChange p X₀) D) [IsIso f.hom]

private theorem Hom.map_one_descend :
    (Over.pullback p).map (f.inv.comp ((oneHom D).comp (baseChangeUnitHom p))).descend =
      Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[Y] ≫ CategoryTheory.inv f.hom := by
  rw [← baseChangeHom_hom, baseChangeHom_descend]
  simp

private theorem Hom.map_mul_descend :
    (Over.pullback p).map
        (f.inv.comp ((mulHom D).comp ((f.prodMap f).comp (baseChangeProdHom p X₀ X₀)))).descend =
      Functor.OplaxMonoidal.δ (Over.pullback p) X₀ X₀ ≫
        (f.hom ⊗ₘ f.hom) ≫ μ[Y] ≫ CategoryTheory.inv f.hom := by
  rw [← baseChangeHom_hom, baseChangeHom_descend]
  simp

/-- **Descent of a monoid object along an effective descent datum.** Let `D` be a monoid-compatible
descent datum on a monoid object `Y` in `Over S'`, and let `f : baseChange p X₀ ⟶ D` be an
isomorphism of descent data. Then `X₀` carries a unique monoid object structure in `Over S` for
which `f.hom` is a monoid homomorphism (`Hom.isMonHom_hom_descendMonObj`,
`Hom.eq_descendMonObj`). -/
noncomputable abbrev Hom.descendMonObj : MonObj X₀ :=
  letI : MonObj ((Over.pullback p).obj X₀) := MonObj.ofIso (asIso f.hom).symm
  (Over.pullback p).monObjOfFaithful X₀
    (f.inv.comp ((oneHom D).comp (baseChangeUnitHom p))).descend
    (f.inv.comp ((mulHom D).comp ((f.prodMap f).comp (baseChangeProdHom p X₀ X₀)))).descend
    (by simpa [MonObj.ofIso_one] using f.map_one_descend)
    (by simpa [MonObj.ofIso_mul] using f.map_mul_descend)

/-- **Effectiveness of `Hom.descendMonObj`.** Base-changing `f.descendMonObj` along `p` recovers
the monoid structure on `X₀ ×_S S'` transported from `Y` along `f.hom⁻¹`. -/
theorem Hom.monObjObj_descendMonObj :
    letI := f.descendMonObj
    Functor.monObjObj (F := Over.pullback p) (X := X₀) = MonObj.ofIso (asIso f.hom).symm :=
  letI : MonObj ((Over.pullback p).obj X₀) := MonObj.ofIso (asIso f.hom).symm
  (Over.pullback p).monObjObj_monObjOfFaithful X₀ _ _ _ _

/-- With `f.descendMonObj` on `X₀`, the comparison `f.hom : X₀ ×_S S' ⟶ Y` is a monoid
homomorphism. -/
theorem Hom.isMonHom_hom_descendMonObj :
    letI := f.descendMonObj
    IsMonHom f.hom := by
  let := f.descendMonObj
  have h := f.monObjObj_descendMonObj
  let _ : MonObj ((Over.pullback p).obj X₀) := MonObj.ofIso (asIso f.hom).symm
  have hm : IsMonHom (M := (Over.pullback p).obj X₀) (N := Y) f.hom := by
    have : IsMonHom (asIso f.hom).symm.hom := inferInstance
    simpa using (inferInstance : IsMonHom (asIso f.hom).symm.inv)
  exact cast (by rw [h]) hm

/-- **Uniqueness of `Hom.descendMonObj`.** Any monoid object structure on `X₀` for which
`f.hom : X₀ ×_S S' ⟶ Y` is a monoid homomorphism coincides with `f.descendMonObj`. -/
theorem Hom.eq_descendMonObj (h : MonObj X₀) (hf : letI := h; IsMonHom f.hom) :
    h = f.descendMonObj :=
  (Over.pullback p).monObjObj_injective X₀
    (monObj_eq_of_mono f.hom _ _ hf f.isMonHom_hom_descendMonObj)

/-- **Descent of commutativity along a monomorphic comparison of descent data.** If
`f : baseChange p X₀ ⟶ D` is a morphism of descent data whose underlying morphism in `Over S'` is
a monomorphic monoid homomorphism and `Y` is a commutative monoid object, then `X₀` is a
commutative monoid object. -/
theorem Hom.isCommMonObj_of_mono {X₀ : Over S} [MonObj X₀] {Y : Over S'} [MonObj Y]
    [IsCommMonObj Y] {D : DescentDatum p Y} (f : Hom (baseChange p X₀) D)
    [Mono f.hom] [IsMonHom f.hom] :
    IsCommMonObj X₀ :=
  ((Over.pullback p).isCommMonObj_obj_iff X₀).1 (TauCeti.isCommMonObj_of_mono f.hom)

/-- **Descent of commutativity along an effective descent datum.** If `Y` is a commutative monoid
object, so is `X₀` equipped with `f.descendMonObj`. -/
theorem Hom.isCommMonObj_descendMonObj [IsCommMonObj Y] :
    letI := f.descendMonObj
    IsCommMonObj X₀ := by
  let := f.descendMonObj
  have := f.isMonHom_hom_descendMonObj
  exact f.isCommMonObj_of_mono

end MonObj

section GrpObj

variable {X₀ : Over S} {G : Over S'} [GrpObj G] {D : DescentDatum p G} [D.IsMon]
  (f : Hom (baseChange p X₀) D) [IsIso f.hom]

private theorem Hom.map_inv_descend :
    (Over.pullback p).map (f.inv.comp ((invHom D).comp f)).descend =
      f.hom ≫ ι[G] ≫ CategoryTheory.inv f.hom := by
  rw [← baseChangeHom_hom, baseChangeHom_descend]
  simp

/-- **Descent of a group object along an effective descent datum.** Let `D` be a monoid-compatible
descent datum on a group object `G` in `Over S'`, and let `f : baseChange p X₀ ⟶ D` be an
isomorphism of descent data. Then `X₀` carries a unique group object structure in `Over S` for
which `f.hom` is a monoid homomorphism (`Hom.isMonHom_hom_descendGrpObj`,
`Hom.eq_descendGrpObj`). -/
noncomputable abbrev Hom.descendGrpObj : GrpObj X₀ :=
  letI : GrpObj ((Over.pullback p).obj X₀) := GrpObj.ofIso (asIso f.hom).symm
  (Over.pullback p).grpObjOfFaithful X₀
    (f.inv.comp ((oneHom D).comp (baseChangeUnitHom p))).descend
    (f.inv.comp ((mulHom D).comp ((f.prodMap f).comp (baseChangeProdHom p X₀ X₀)))).descend
    (f.inv.comp ((invHom D).comp f)).descend
    (by simpa [MonObj.ofIso_one] using f.map_one_descend)
    (by simpa [MonObj.ofIso_mul] using f.map_mul_descend)
    (by simpa [GrpObj.ofIso_inv] using f.map_inv_descend)

/-- The monoid structure underlying `f.descendGrpObj` is `f.descendMonObj`. -/
theorem Hom.descendGrpObj_toMonObj : f.descendGrpObj.toMonObj = f.descendMonObj :=
  (rfl)

/-- **Effectiveness of `Hom.descendGrpObj`.** Base-changing `f.descendGrpObj` along `p` recovers
the group structure on `X₀ ×_S S'` transported from `G` along `f.hom⁻¹`. -/
theorem Hom.grpObjObj_descendGrpObj :
    letI := f.descendGrpObj
    Functor.grpObjObj (F := Over.pullback p) (G := X₀) = GrpObj.ofIso (asIso f.hom).symm :=
  letI : GrpObj ((Over.pullback p).obj X₀) := GrpObj.ofIso (asIso f.hom).symm
  (Over.pullback p).grpObjObj_grpObjOfFaithful X₀ _ _ _ _ _ _

/-- With `f.descendGrpObj` on `X₀`, the comparison `f.hom : X₀ ×_S S' ⟶ G` is a monoid
homomorphism. -/
theorem Hom.isMonHom_hom_descendGrpObj :
    letI := f.descendGrpObj
    IsMonHom f.hom :=
  f.isMonHom_hom_descendMonObj

/-- **Uniqueness of `Hom.descendGrpObj`.** Any group object structure on `X₀` for which
`f.hom : X₀ ×_S S' ⟶ G` is a monoid homomorphism coincides with `f.descendGrpObj`. -/
theorem Hom.eq_descendGrpObj (h : GrpObj X₀) (hf : letI := h; IsMonHom f.hom) :
    h = f.descendGrpObj :=
  GrpObj.ext _ _ (f.eq_descendMonObj h.toMonObj hf)

/-- **Descent of commutativity for group objects.** If `G` is a commutative group object, so is
`X₀` equipped with `f.descendGrpObj`. -/
theorem Hom.isCommMonObj_descendGrpObj [IsCommMonObj G] :
    letI := f.descendGrpObj
    IsCommMonObj X₀ :=
  f.isCommMonObj_descendMonObj

end GrpObj

section GrpCat

variable (p) in
/-- **Full faithfulness of base change on `Grp (Over S)` into descent data.** Base change along `p`
is a bijection from homomorphisms `G ⟶ H` in `Grp (Over S)` to morphisms of canonical descent data
`baseChange p G.X ⟶ baseChange p H.X` whose underlying morphism in `Over S'` is a monoid
homomorphism. -/
noncomputable def baseChangeGrpHomEquiv (G H : Grp (Over S)) :
    (G ⟶ H) ≃ {φ : Hom (baseChange p G.X) (baseChange p H.X) // IsMonHom φ.hom} where
  toFun u := ⟨baseChangeHom p u.hom.hom, by rw [baseChangeHom_hom]; infer_instance⟩
  invFun φ := haveI := φ.property; Grp.homMk φ.val.descend
  left_inv u := by ext1; exact Hom.descend_baseChangeHom p u.hom.hom
  right_inv φ := Subtype.ext (baseChangeHom_descend φ.val)

variable (p) in
/-- `baseChangeGrpHomEquiv` sends a group homomorphism over `S` to its base change. -/
@[simp]
theorem baseChangeGrpHomEquiv_apply_coe {G H : Grp (Over S)} (u : G ⟶ H) :
    (baseChangeGrpHomEquiv p G H u : Hom (baseChange p G.X) (baseChange p H.X)) =
      baseChangeHom p u.hom.hom :=
  (rfl)

/-- The inverse of `baseChangeGrpHomEquiv` descends the morphism of canonical descent data. -/
@[simp]
theorem baseChangeGrpHomEquiv_symm_apply_hom_hom {G H : Grp (Over S)}
    (φ : {φ : Hom (baseChange p G.X) (baseChange p H.X) // IsMonHom φ.hom}) :
    ((baseChangeGrpHomEquiv p G H).symm φ).hom.hom = φ.val.descend :=
  (rfl)

/-- **Uniqueness of effective descent of group objects.** Two group objects `G` and `H` in
`Grp (Over S)` whose canonical descent data are isomorphic as monoid-compatible descent data to the
same `(W, D)`, via `f` and `g`, are canonically isomorphic in `Grp (Over S)`; this is the unique
isomorphism carrying `f` to `g` (`Hom.eq_descendGrpIso`). -/
noncomputable def Hom.descendGrpIso {G H : Grp (Over S)} {W : Over S'} [GrpObj W]
    {D : DescentDatum p W} (f : Hom (baseChange p G.X) D) (g : Hom (baseChange p H.X) D)
    [IsIso f.hom] [IsIso g.hom] [IsMonHom f.hom] [IsMonHom g.hom] :
    G ≅ H :=
  Grp.mkIso (f.descendIso g) (IsMonHom.one_hom (f.descendIso g).hom)
    (IsMonHom.mul_hom (f.descendIso g).hom)

/-- The underlying morphism in `Over S` of `Hom.descendGrpIso f g` is `(f.descendIso g).hom`. -/
@[simp]
theorem Hom.descendGrpIso_hom_hom_hom {G H : Grp (Over S)} {W : Over S'} [GrpObj W]
    {D : DescentDatum p W} (f : Hom (baseChange p G.X) D) (g : Hom (baseChange p H.X) D)
    [IsIso f.hom] [IsIso g.hom] [IsMonHom f.hom] [IsMonHom g.hom] :
    (f.descendGrpIso g).hom.hom.hom = (f.descendIso g).hom :=
  (rfl)

/-- The underlying inverse in `Over S` of `Hom.descendGrpIso f g` is `(f.descendIso g).inv`. -/
@[simp]
theorem Hom.descendGrpIso_inv_hom_hom {G H : Grp (Over S)} {W : Over S'} [GrpObj W]
    {D : DescentDatum p W} (f : Hom (baseChange p G.X) D) (g : Hom (baseChange p H.X) D)
    [IsIso f.hom] [IsIso g.hom] [IsMonHom f.hom] [IsMonHom g.hom] :
    (f.descendGrpIso g).inv.hom.hom = (f.descendIso g).inv :=
  (rfl)

/-- The group isomorphism `Hom.descendGrpIso f g` carries `f` to `g`. -/
theorem Hom.comp_baseChangeHom_descendGrpIso {G H : Grp (Over S)} {W : Over S'} [GrpObj W]
    {D : DescentDatum p W} (f : Hom (baseChange p G.X) D) (g : Hom (baseChange p H.X) D)
    [IsIso f.hom] [IsIso g.hom] [IsMonHom f.hom] [IsMonHom g.hom] :
    g.comp (baseChangeHom p (f.descendGrpIso g).hom.hom.hom) = f :=
  f.comp_baseChangeHom_descendIso g

/-- `Hom.descendGrpIso f g` is the unique isomorphism `G ≅ H` in `Grp (Over S)` carrying `f` to
`g`. -/
theorem Hom.eq_descendGrpIso {G H : Grp (Over S)} {W : Over S'} [GrpObj W]
    {D : DescentDatum p W} (f : Hom (baseChange p G.X) D) (g : Hom (baseChange p H.X) D)
    [IsIso f.hom] [IsIso g.hom] [IsMonHom f.hom] [IsMonHom g.hom]
    (e : G ≅ H) (he : g.comp (baseChangeHom p e.hom.hom.hom) = f) :
    e = f.descendGrpIso g := by
  ext1
  exact Grp.hom_ext _ _ (congrArg Iso.hom (f.eq_descendIso g ((Grp.forget _).mapIso e) he))

end GrpCat

end DescentDatum

end TauCeti
