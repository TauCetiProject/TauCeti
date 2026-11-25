/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.Karoubi

/-!
# The dagger Karoubi envelope

The *dagger Karoubi envelope* `TauCeti.DaggerKaroubi C` of a dagger category `C` is the full
subcategory of the idempotent completion `Karoubi C` on the objects `(X, p)` whose idempotent `p`
is self-adjoint, that is, a projection. Unlike `Karoubi C` it is again a dagger category: the
dagger of a morphism `f : (X, p) ⟶ (Y, q)` is the dagger of its underlying arrow, which is
compatible with the projections because they are self-adjoint. When `C` is preadditive or linear
with a compatible dagger, so is `DaggerKaroubi C`.

The embedding `TauCeti.toDaggerKaroubi C : C ⥤ DaggerKaroubi C`, `X ↦ (X, 𝟙 X)`, is a fully
faithful dagger functor. Every object `P = (X, p)` is a *unitary* retract of the image of `X`: the
morphism `TauCeti.DaggerKaroubi.ι P` with underlying arrow `p` is an isometry with range
projection `p`. In `DaggerKaroubi C` every self-adjoint idempotent has a unitary splitting, and
`toDaggerKaroubi C` is essentially surjective through unitary isomorphisms exactly when every
self-adjoint idempotent of `C` has one.

The envelope has the universal property of a completion for unitary splittings. A dagger functor
`F : C ⥤ D` into a dagger category in which every self-adjoint idempotent has a unitary splitting
extends, along chosen splittings, to a dagger functor `TauCeti.DaggerKaroubi.lift F` on the
envelope, whose restriction to `C` is unitarily isomorphic to `F`. Every dagger functor on the
envelope with this property is unitarily isomorphic to the extension, which is therefore
independent of the chosen splittings up to unitary natural isomorphism. The extension is additive
or linear when `F` is.

For C*-categories, where every idempotent is similar to a projection, `DaggerKaroubi C` is
equivalent to `Karoubi C`; see `TauCeti/Analysis/CStarAlgebra/Category/Karoubi.lean`.

## Main declarations

* `TauCeti.DaggerKaroubi`: the dagger Karoubi envelope, with its dagger, additive and linear
  structures.
* `TauCeti.toDaggerKaroubi`: the fully faithful dagger embedding of `C`.
* `TauCeti.DaggerKaroubi.ι`: the isometry from an object `(X, p)` to `(X, 𝟙 X)`.
* `TauCeti.DaggerKaroubi.exists_isometry`: every self-adjoint idempotent of `DaggerKaroubi C`
  has a unitary splitting, so `DaggerKaroubi C` has unitary splittings.
* `TauCeti.exists_isUnitary_toDaggerKaroubi_obj_iff`: the objects of `DaggerKaroubi C` are
  unitarily isomorphic to objects of `C` exactly when `C` has unitary splittings.
* `TauCeti.exists_isUnitary_toDaggerKaroubi_obj`: when `C` has unitary splittings, every object
  of `DaggerKaroubi C` is unitarily isomorphic to an object of `C`, and `toDaggerKaroubi C` is an
  equivalence.
* `TauCeti.DaggerKaroubi.lift`: the extension of a dagger functor to the envelope, with
  `TauCeti.DaggerKaroubi.toDaggerKaroubiCompLiftIso` its unitary comparison with `F` on `C`.
* `TauCeti.DaggerKaroubi.liftUnique`: the extension is unique up to unitary natural isomorphism.

## References

* P. Selinger, *Idempotents in dagger categories*, Electron. Notes Theor. Comput. Sci. 210
  (2008), 107–122.
* C. Heunen, J. Vicary, *Categories for Quantum Theory*, Oxford University Press, 2019.
-/

public section

noncomputable section

open CategoryTheory Idempotents

universe w v v₂ u u₂

namespace TauCeti

variable (C : Type u) [Category.{v} C] [DaggerCategory C]

/-- The objects of the idempotent completion `Karoubi C` whose idempotent is self-adjoint. -/
@[expose] def isSelfAdjointKaroubi : ObjectProperty (Karoubi C) :=
  fun P => dagger P.p = P.p

variable {C} in
/-- An object of `Karoubi C` satisfies `isSelfAdjointKaroubi C` exactly when its idempotent is
self-adjoint. -/
@[simp] theorem isSelfAdjointKaroubi_iff (P : Karoubi C) :
    isSelfAdjointKaroubi C P ↔ dagger P.p = P.p := Iff.rfl

/-- The **dagger Karoubi envelope** of a dagger category `C`: the full subcategory of the
idempotent completion `Karoubi C` on the pairs `(X, p)` with `p` a self-adjoint idempotent. -/
abbrev DaggerKaroubi : Type (max u v) :=
  (isSelfAdjointKaroubi C).FullSubcategory

variable {C}

namespace DaggerKaroubi

/-- The idempotent of an object of the dagger Karoubi envelope is self-adjoint. -/
@[simp] theorem dagger_p (P : DaggerKaroubi C) : dagger P.obj.p = P.obj.p :=
  P.property

/-- The dagger Karoubi envelope is a dagger category, with the dagger of the underlying arrows. -/
instance instDaggerCategory : DaggerCategory (DaggerKaroubi C) where
  dagger {P Q} f := ObjectProperty.homMk ⟨dagger f.hom.f, by
    simpa only [dagger_comp, P.dagger_p, Q.dagger_p, Category.assoc] using
      congrArg dagger f.hom.comm⟩
  dagger_id P := by
    ext
    exact P.dagger_p
  dagger_comp f g := by
    ext
    exact dagger_comp f.hom.f g.hom.f
  dagger_dagger f := ObjectProperty.hom_ext _ (Karoubi.hom_ext _ _ (dagger_dagger f.hom.f))

/-- The underlying arrow of the dagger of a morphism is the dagger of its underlying arrow. -/
@[simp] theorem dagger_hom_f {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    (dagger f).hom.f = dagger f.hom.f := (rfl)

/-- Two morphisms of the dagger Karoubi envelope are equal when their underlying arrows are. -/
@[ext] theorem hom_ext {P Q : DaggerKaroubi C} {f g : P ⟶ Q} (h : f.hom.f = g.hom.f) : f = g :=
  ObjectProperty.hom_ext _ (Karoubi.hom_ext _ _ h)

/-- The underlying arrow of the identity of `(X, p)` is `p`. -/
@[simp] theorem id_hom_f (P : DaggerKaroubi C) : (𝟙 P : P ⟶ P).hom.f = P.obj.p := (rfl)

/-- Underlying arrows compose. -/
@[simp, reassoc] theorem comp_hom_f {P Q R : DaggerKaroubi C} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).hom.f = f.hom.f ≫ g.hom.f := (rfl)

section Preadditive

variable [Preadditive C]

/-- Underlying arrows add. -/
@[simp] theorem add_hom_f {P Q : DaggerKaroubi C} (f g : P ⟶ Q) :
    (f + g).hom.f = f.hom.f + g.hom.f := (rfl)

/-- The zero morphism has zero underlying arrow. -/
@[simp] theorem zero_hom_f (P Q : DaggerKaroubi C) : (0 : P ⟶ Q).hom.f = 0 := (rfl)

/-- The dagger of the envelope is additive when that of `C` is. -/
instance instDaggerPreadditive [DaggerPreadditive C] : DaggerPreadditive (DaggerKaroubi C) where
  dagger_add f g := by
    ext
    exact dagger_add f.hom.f g.hom.f

/-- Scalar multiplication acts on underlying arrows. Not a `simp` lemma: `simp` proves it from
`ObjectProperty.smul_hom` and `Karoubi.smul_f`. -/
theorem smul_hom_f {R : Type w} [Semiring R] [Linear R C] {P Q : DaggerKaroubi C} (r : R)
    (f : P ⟶ Q) : (r • f).hom.f = r • f.hom.f := (rfl)

/-- The dagger of the envelope conjugates scalars when that of `C` does. -/
instance instDaggerLinear {R : Type w} [Semiring R] [Star R] [Linear R C] [DaggerLinear R C] :
    DaggerLinear R (DaggerKaroubi C) where
  dagger_smul r f := by
    ext
    exact dagger_smul r f.hom.f

end Preadditive

end DaggerKaroubi

variable (C) in
/-- The embedding `X ↦ (X, 𝟙 X)` of a dagger category into its dagger Karoubi envelope. -/
@[expose, simps obj_obj, implicit_reducible]
def toDaggerKaroubi : C ⥤ DaggerKaroubi C where
  obj X := ⟨(toKaroubi C).obj X, dagger_id X⟩
  map f := ObjectProperty.homMk ((toKaroubi C).map f)

/-- The underlying arrow of the image of `f` in the dagger Karoubi envelope is `f`. -/
@[simp] theorem toDaggerKaroubi_map_hom_f {X Y : C} (f : X ⟶ Y) :
    ((toDaggerKaroubi C).map f).hom.f = f := (rfl)

variable (C) in
/-- The embedding into the dagger Karoubi envelope is fully faithful. -/
def fullyFaithfulToDaggerKaroubi : (toDaggerKaroubi C).FullyFaithful where
  preimage f := f.hom.f

instance : (toDaggerKaroubi C).Full := (fullyFaithfulToDaggerKaroubi C).full

instance : (toDaggerKaroubi C).Faithful := (fullyFaithfulToDaggerKaroubi C).faithful

/-- The embedding into the dagger Karoubi envelope preserves the dagger. -/
instance : (toDaggerKaroubi C).PreservesDagger where
  map_dagger _ := rfl

/-- The embedding into the dagger Karoubi envelope is additive. -/
instance [Preadditive C] : (toDaggerKaroubi C).Additive where

/-- The embedding into the dagger Karoubi envelope is linear. -/
instance {R : Type w} [Semiring R] [Preadditive C] [Linear R C] :
    (toDaggerKaroubi C).Linear R where

namespace DaggerKaroubi

/-- The isometry `(X, p) ⟶ (X, 𝟙 X)` whose underlying arrow is `p`. Its dagger, the coisometry
`(X, 𝟙 X) ⟶ (X, p)`, also has underlying arrow `p`. -/
def ι (P : DaggerKaroubi C) : P ⟶ (toDaggerKaroubi C).obj P.obj.X :=
  ObjectProperty.homMk (Karoubi.decompId_i P.obj)

/-- The underlying arrow of `ι P` is the idempotent of `P`. -/
@[simp] theorem ι_hom_f (P : DaggerKaroubi C) : (ι P).hom.f = P.obj.p := (rfl)

/-- The morphism `ι P` is an isometry. -/
@[reassoc (attr := simp)]
theorem ι_comp_dagger_ι (P : DaggerKaroubi C) : ι P ≫ dagger (ι P) = 𝟙 P := by
  ext
  simp

/-- The range projection of the isometry `ι P` is the image of the idempotent of `P`. -/
@[reassoc (attr := simp)]
theorem dagger_ι_comp_ι (P : DaggerKaroubi C) :
    dagger (ι P) ≫ ι P = (toDaggerKaroubi C).map P.obj.p := by
  ext
  simp

/-- The isometries `ι` intertwine a morphism `f : P ⟶ Q` with its underlying arrow. -/
@[reassoc]
theorem comp_ι {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    f ≫ ι Q = ι P ≫ (toDaggerKaroubi C).map f.hom.f := by
  ext
  simp

/-- The isometry `ι P` is fixed by the projection of `P`. -/
@[reassoc]
theorem ι_comp_map_p (P : DaggerKaroubi C) :
    ι P ≫ (toDaggerKaroubi C).map P.obj.p = ι P := by
  ext
  simp

/-- In the dagger Karoubi envelope every self-adjoint idempotent `q : P ⟶ P` has a unitary
splitting: an isometry `v : Q ⟶ P`, with `v ≫ dagger v = 𝟙 Q`, whose range projection
`dagger v ≫ v` is `q`. -/
theorem exists_isometry {P : DaggerKaroubi C} (q : P ⟶ P) (hq : dagger q = q) (hqq : q ≫ q = q) :
    ∃ (Q : DaggerKaroubi C) (v : Q ⟶ P), v ≫ dagger v = 𝟙 Q ∧ dagger v ≫ v = q := by
  have hq' : dagger q.hom.f = q.hom.f := by simpa using congrArg (fun f => f.hom.f) hq
  have hqq' : q.hom.f ≫ q.hom.f = q.hom.f := by simpa using congrArg (fun f => f.hom.f) hqq
  refine ⟨⟨⟨P.obj.X, q.hom.f, hqq'⟩, hq'⟩, ObjectProperty.homMk ⟨q.hom.f, by simp [hqq']⟩, ?_, ?_⟩
  · ext
    simp [hq', hqq']
  · ext
    simp [hq', hqq']

/-- The dagger Karoubi envelope has unitary splittings. -/
instance : HasUnitarySplittings (DaggerKaroubi C) :=
  ⟨fun _ q hq hqq => exists_isometry q hq hqq⟩

end DaggerKaroubi

/-- Every object of the dagger Karoubi envelope is unitarily isomorphic to an object of `C` exactly
when `C` has unitary splittings: every self-adjoint idempotent `p : X ⟶ X` of `C` has an isometry
`v : Y ⟶ X`, with `v ≫ dagger v = 𝟙 Y`, such that `dagger v ≫ v = p`. -/
theorem exists_isUnitary_toDaggerKaroubi_obj_iff :
    (∀ P : DaggerKaroubi C, ∃ (Y : C) (u : (toDaggerKaroubi C).obj Y ⟶ P), IsUnitary u) ↔
      HasUnitarySplittings C := by
  rw [hasUnitarySplittings_iff]
  constructor
  · -- A unitary `u : (Y, 𝟙 Y) ⟶ (X, p)` has underlying arrow an isometry with range projection `p`.
    intro h X p hp hpp
    obtain ⟨Y, u, hu⟩ := h ⟨⟨X, p, hpp⟩, hp⟩
    exact ⟨Y, u.hom.f, by simpa using congrArg (fun f => f.hom.f) hu.hom_dagger_id,
      by simpa using congrArg (fun f => f.hom.f) hu.dagger_hom_id⟩
  · -- An isometry `v : Y ⟶ X` with range projection `p` is a unitary `(Y, 𝟙 Y) ⟶ (X, p)`.
    intro h P
    obtain ⟨Y, v, hv, hvp⟩ := h P.obj.X P.obj.p P.dagger_p P.obj.idem
    have hvp' : v ≫ P.obj.p = v := by rw [← hvp, reassoc_of% hv]
    refine ⟨Y, ObjectProperty.homMk (X := (toDaggerKaroubi C).obj Y) ⟨v, by simpa using hvp'⟩,
      (isUnitary_iff _).2 ⟨?_, ?_⟩⟩
    · ext
      simpa using hv
    · ext
      simpa using hvp

/-- When `C` has unitary splittings, every object of the dagger Karoubi envelope is unitarily
isomorphic to the image of an object of `C`. -/
theorem exists_isUnitary_toDaggerKaroubi_obj [HasUnitarySplittings C] (P : DaggerKaroubi C) :
    ∃ (Y : C) (u : (toDaggerKaroubi C).obj Y ⟶ P), IsUnitary u :=
  exists_isUnitary_toDaggerKaroubi_obj_iff.2 ‹_› P

/-- The embedding of a dagger category with unitary splittings into its dagger Karoubi envelope is
essentially surjective. -/
instance [HasUnitarySplittings C] : (toDaggerKaroubi C).EssSurj where
  mem_essImage P :=
    have ⟨Y, _, hu⟩ := exists_isUnitary_toDaggerKaroubi_obj P
    ⟨Y, ⟨hu.toIso⟩⟩

/-- The embedding of a dagger category with unitary splittings into its dagger Karoubi envelope is
an equivalence. -/
instance [HasUnitarySplittings C] : (toDaggerKaroubi C).IsEquivalence where

section Lift

/-! ### The universal property

A dagger functor `F : C ⥤ D` into a dagger category in which every self-adjoint idempotent has a
unitary splitting extends along `toDaggerKaroubi C`: the extension `DaggerKaroubi.lift F` sends
`(X, p)` to the source of a chosen isometry `v` with range projection `F.map p`. The extension
restricts to `F` up to a unitary natural isomorphism, and any other dagger functor with this
property is unitarily isomorphic to it; in particular the extension does not depend on the chosen
splittings up to unitary natural isomorphism. -/

variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D] [HasUnitarySplittings D] (F : C ⥤ D)
  [F.PreservesDagger]

namespace DaggerKaroubi

/-- The image under `F` of the projection of an object of the envelope has a unitary splitting. -/
private theorem exists_isometry_map (P : DaggerKaroubi C) :
    ∃ (Y : D) (v : Y ⟶ F.obj P.obj.X), v ≫ dagger v = 𝟙 Y ∧ dagger v ≫ v = F.map P.obj.p :=
  HasUnitarySplittings.exists_isometry _ _ (by rw [← F.map_dagger, P.dagger_p])
    (by rw [← F.map_comp, P.obj.idem])

/-- For an object `P = (X, p)` of the envelope, the source of the chosen unitary splitting of
`F.map p`. -/
def liftObj (P : DaggerKaroubi C) : D :=
  (exists_isometry_map F P).choose

/-- For an object `P = (X, p)` of the envelope, the chosen isometry `liftObj F P ⟶ F.obj X`
with range projection `F.map p`. -/
def liftIsometry (P : DaggerKaroubi C) : liftObj F P ⟶ F.obj P.obj.X :=
  (exists_isometry_map F P).choose_spec.choose

/-- The chosen splitting of `F.map p` is an isometry. -/
@[reassoc (attr := simp)]
theorem liftIsometry_comp_dagger (P : DaggerKaroubi C) :
    liftIsometry F P ≫ dagger (liftIsometry F P) = 𝟙 (liftObj F P) :=
  (exists_isometry_map F P).choose_spec.choose_spec.1

/-- The range projection of the chosen splitting of `F.map p` is `F.map p`. -/
@[reassoc (attr := simp)]
theorem dagger_comp_liftIsometry (P : DaggerKaroubi C) :
    dagger (liftIsometry F P) ≫ liftIsometry F P = F.map P.obj.p :=
  (exists_isometry_map F P).choose_spec.choose_spec.2

/-- The chosen splitting of `F.map p` lies in the range of `F.map p`. -/
@[reassoc (attr := simp)]
theorem liftIsometry_comp_map_p (P : DaggerKaroubi C) :
    liftIsometry F P ≫ F.map P.obj.p = liftIsometry F P := by
  rw [← dagger_comp_liftIsometry, liftIsometry_comp_dagger_assoc]

/-- The dagger of the chosen splitting of `F.map p` vanishes off the range of `F.map p`. -/
@[reassoc (attr := simp)]
theorem map_p_comp_dagger_liftIsometry (P : DaggerKaroubi C) :
    F.map P.obj.p ≫ dagger (liftIsometry F P) = dagger (liftIsometry F P) := by
  rw [← dagger_comp_liftIsometry, Category.assoc, liftIsometry_comp_dagger, Category.comp_id]

/-- The extension of a dagger functor `F : C ⥤ D` to the dagger Karoubi envelope, along chosen
unitary splittings in `D`. It sends `(X, p)` to the source of the chosen isometry `v` with range
projection `F.map p`, and `f : (X, p) ⟶ (Y, q)` to `v ≫ F.map f ≫ dagger w`, where `w` is the
chosen isometry for `(Y, q)`. -/
@[expose, implicit_reducible]
def lift : DaggerKaroubi C ⥤ D where
  obj := liftObj F
  map {P Q} f := liftIsometry F P ≫ F.map f.hom.f ≫ dagger (liftIsometry F Q)
  map_id P := by simp
  map_comp f g := by
    simp only [comp_hom_f, Category.assoc, dagger_comp_liftIsometry_assoc]
    rw [← F.map_comp_assoc f.hom.f, Karoubi.comp_p, F.map_comp_assoc]

/-- The extension sends `P` to the source of its chosen splitting. -/
@[simp] theorem lift_obj (P : DaggerKaroubi C) : (lift F).obj P = liftObj F P := (rfl)

/-- The extension sends `f : P ⟶ Q` to `v ≫ F.map f ≫ dagger w` for the chosen splittings `v` of
`P` and `w` of `Q`. -/
@[simp] theorem lift_map {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    (lift F).map f = liftIsometry F P ≫ F.map f.hom.f ≫ dagger (liftIsometry F Q) := (rfl)

/-- The extension of a dagger functor is a dagger functor. -/
instance : (lift F).PreservesDagger where
  map_dagger f := by simp

/-- The extension of an additive dagger functor is additive. -/
instance [Preadditive C] [Preadditive D] [F.Additive] : (lift F).Additive where
  map_add := by simp

/-- The extension of a linear dagger functor is linear. -/
instance {R : Type w} [Semiring R] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    [F.Linear R] : (lift F).Linear R where
  map_smul f r := by simp [smul_hom_f]

/-- The chosen splittings of the objects `(X, 𝟙 X)` are unitary. -/
theorem isUnitary_liftIsometry_toDaggerKaroubi_obj (X : C) :
    IsUnitary (liftIsometry F ((toDaggerKaroubi C).obj X)) :=
  (isUnitary_iff _).2 ⟨liftIsometry_comp_dagger F _, by simp⟩

/-- The extension restricts to `F` along `toDaggerKaroubi C`, up to the unitary natural isomorphism
given by the chosen splittings of the objects `(X, 𝟙 X)`. -/
def toDaggerKaroubiCompLiftIso : toDaggerKaroubi C ⋙ lift F ≅ F :=
  NatTrans.unitaryIso
    { app X := liftIsometry F ((toDaggerKaroubi C).obj X)
      naturality X Y f := by simp }
    (isUnitary_liftIsometry_toDaggerKaroubi_obj F)

/-- The components of `toDaggerKaroubiCompLiftIso F` are the chosen splittings. -/
@[simp] theorem toDaggerKaroubiCompLiftIso_hom_app (X : C) :
    (toDaggerKaroubiCompLiftIso F).hom.app X = liftIsometry F ((toDaggerKaroubi C).obj X) := by
  simp [toDaggerKaroubiCompLiftIso]

/-- The inverse components of `toDaggerKaroubiCompLiftIso F` are the daggers of the chosen
splittings. -/
@[simp] theorem toDaggerKaroubiCompLiftIso_inv_app (X : C) :
    (toDaggerKaroubiCompLiftIso F).inv.app X =
      dagger (liftIsometry F ((toDaggerKaroubi C).obj X)) := by
  simp [toDaggerKaroubiCompLiftIso]

end DaggerKaroubi

end Lift

section LiftUnique

variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D] [HasUnitarySplittings D] {F : C ⥤ D}
  [F.PreservesDagger] {G : DaggerKaroubi C ⥤ D} [G.PreservesDagger]
  {α : toDaggerKaroubi C ⋙ G ⟶ F} (hα : ∀ X, IsUnitary (α.app X))

namespace DaggerKaroubi

include hα in
/-- The components of the comparison `G ≅ lift F` are unitary. -/
private theorem isUnitary_liftUnique_app (P : DaggerKaroubi C) :
    IsUnitary (G.map (ι P) ≫ α.app P.obj.X ≫ dagger (liftIsometry F P)) := by
  -- Conjugating by the unitary `α.app X` exchanges `G.map p` and `F.map p`.
  have h₁ := NatIso.naturality_1 (NatTrans.unitaryIso α hα) P.obj.p
  have h₂ := NatIso.naturality_2 (NatTrans.unitaryIso α hα) P.obj.p
  simp only [Functor.comp_map, NatTrans.unitaryIso_hom, NatTrans.unitaryIso_inv_app] at h₁ h₂
  refine (isUnitary_iff _).2 ⟨?_, ?_⟩
  · -- `α ≫ F.map p ≫ dagger α = G.map p`, and `G.map (ι ≫ p ≫ dagger ι) = 𝟙`.
    have hι : ι P ≫ (toDaggerKaroubi C).map P.obj.p ≫ dagger (ι P) = 𝟙 P := by
      simp [ι_comp_map_p_assoc]
    have hG := congrArg G.map hι
    simp only [Functor.map_comp, Functor.map_dagger] at hG
    simp [reassoc_of% h₂, hG]
  · -- `dagger (G.map ι) ≫ G.map ι = G.map p`, which `α` conjugates to `F.map p`.
    have hG := congrArg G.map (dagger_ι_comp_ι P)
    simp only [Functor.map_comp, Functor.map_dagger] at hG
    simp [reassoc_of% hG, reassoc_of% h₁]

/-- The natural transformation `G ⟶ lift F` with components
`G.map (ι P) ≫ α.app X ≫ dagger v`, for `P = (X, p)` with chosen splitting `v`. -/
private def liftUniqueHom : G ⟶ lift F where
  app P := G.map (ι P) ≫ α.app P.obj.X ≫ dagger (liftIsometry F P)
  naturality P Q f := by
    -- Move `f` past `ι` (`comp_ι`), then past `α` (naturality), where `p ≫ f = f` absorbs `p`.
    have hn := α.naturality f.hom.f
    have hG := congrArg G.map (comp_ι f)
    have hp := congrArg F.map (Karoubi.p_comp f.hom)
    simp only [Functor.comp_map, Functor.map_comp] at hn hG hp
    simp [reassoc_of% hG, reassoc_of% hn, reassoc_of% hp]

include hα in
/-- **Uniqueness of the extension.** A dagger functor `G : DaggerKaroubi C ⥤ D` whose restriction
along `toDaggerKaroubi C` is unitarily isomorphic to `F`, through `α` with unitary components, is
unitarily isomorphic to the extension `lift F`. The component at `P = (X, p)` is
`G.map (ι P) ≫ α.app X ≫ dagger v`, for the chosen splitting `v` of `F.map p`. -/
def liftUnique : G ≅ lift F :=
  NatTrans.unitaryIso (liftUniqueHom (α := α)) (isUnitary_liftUnique_app hα)

/-- The components of the comparison `G ≅ lift F`. -/
@[simp] theorem liftUnique_hom_app (P : DaggerKaroubi C) :
    (liftUnique hα).hom.app P =
      G.map (ι P) ≫ α.app P.obj.X ≫ dagger (liftIsometry F P) := by
  simp [liftUnique, liftUniqueHom]

/-- The inverse components of the comparison `G ≅ lift F` are the daggers of its components. -/
@[simp] theorem liftUnique_inv_app (P : DaggerKaroubi C) :
    (liftUnique hα).inv.app P =
      liftIsometry F P ≫ dagger (α.app P.obj.X) ≫ dagger (G.map (ι P)) := by
  simp [liftUnique, liftUniqueHom]

/-- The components of the comparison `G ≅ lift F` are unitary. -/
theorem isUnitary_liftUnique_hom_app (P : DaggerKaroubi C) :
    IsUnitary ((liftUnique hα).hom.app P) := by
  rw [liftUnique_hom_app]
  exact isUnitary_liftUnique_app hα P

end DaggerKaroubi

end LiftUnique

end TauCeti
