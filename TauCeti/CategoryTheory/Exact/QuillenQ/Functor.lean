/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.AdmissibleBaseChange
public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Exact.QuillenQ.Basic

/-!
# Universal property, functoriality, and duality of Quillen's Q-category

This file establishes the universal property of Quillen's Q-category `E.QuillenQ` and develops its
functoriality for conflation-exact functors and opposite exact categories.

A functor `E.QuillenQ ⥤ D` into an arbitrary category `D` is uniquely determined by:
1. an object assignment `obj : C → D`,
2. a covariant assignment on inflations preserving identities and composition,
3. a contravariant assignment on deflations preserving identities and composition, and
4. compatibility on admissible bicartesian squares.

No separate compatibility axiom for isomorphisms is needed: applying the bicartesian-square axiom
to the diagonal square of an isomorphism `e` forces the contravariant value on `e.hom` to coincide
with the covariant value on `e.inv`.

Using this universal property, every conflation-exact additive functor induces a functor between
Q-categories, strictly preserving identity and composition and sending natural isomorphisms of
exact functors to natural isomorphisms of Q-functors. In particular, an exact equivalence induces
an equivalence of Q-categories. Finally, applying the universal property to `E.op` yields the
self-duality equivalence `E.op.QuillenQ ≌ E.QuillenQ`, which interchanges inflations and reversed
deflations without reversing the direction of Q-morphisms.

## Main definitions

* `TauCeti.ExactStructure.QuillenQ.FunctorData`: the universal-property data specifying a functor
  out of `E.QuillenQ`.
* `TauCeti.ExactStructure.QuillenQ.lift` and `TauCeti.ExactStructure.QuillenQ.liftEquiv`: the
  extension of `FunctorData` to a functor `E.QuillenQ ⥤ D`, and the resulting bijection.
* `TauCeti.ExactStructure.QuillenQ.natTransMk` and `TauCeti.ExactStructure.QuillenQ.natIsoMk`:
  constructors for natural transformations and natural isomorphisms between functors out of
  `E.QuillenQ`.
* `TauCeti.ExactStructure.QuillenQ.map`, `TauCeti.ExactStructure.QuillenQ.mapNatIso`,
  `TauCeti.ExactStructure.QuillenQ.mapEquivalence`,
  `TauCeti.ExactStructure.QuillenQ.mapEquivalenceOfReflects`, and
  `TauCeti.ExactStructure.QuillenQ.transportEquivalence`: functoriality of `QuillenQ` for
  conflation-exact functors, natural isomorphisms, exact equivalences, and transported exact
  structures.
* `TauCeti.ExactStructure.QuillenQ.opTo`, `TauCeti.ExactStructure.QuillenQ.toOp`, and
  `TauCeti.ExactStructure.QuillenQ.opEquivalence`: the canonical isomorphism of categories
  `E.op.QuillenQ ≌ E.QuillenQ`.

## Main results

* `TauCeti.ExactStructure.QuillenQ.FunctorData.mapDeflation_of_iso`: the bicartesian-square axiom
  automatically determines `mapDeflation` on isomorphisms as `mapInflation` of the inverse.
* `TauCeti.ExactStructure.QuillenQ.functor_ext` and
  `TauCeti.ExactStructure.QuillenQ.functor_hext`: two functors out of `E.QuillenQ` agreeing on
  objects, inflations, and reversed deflations are equal.
* `TauCeti.ExactStructure.QuillenQ.map_id` and `TauCeti.ExactStructure.QuillenQ.map_comp`: strict
  identity and composition laws for exact-functor functoriality.
* `TauCeti.ExactStructure.QuillenQ.opTo_comp_toOp` and
  `TauCeti.ExactStructure.QuillenQ.toOp_comp_opTo`: the opposite-duality functors are strict
  inverses.

## References

* Daniel Quillen, *Higher algebraic K-theory: I*, Algebraic K-theory, I: Higher K-theories
  (Battelle Memorial Inst., Seattle, 1972), Lecture Notes in Math. **341**, Springer (1973),
  Section 2, pp. 99–104.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter IV, Sections
  6.1–6.2.
-/

public section

namespace TauCeti.ExactStructure.QuillenQ

open CategoryTheory CategoryTheory.Limits

universe v v' v'' u u' u''

section Universal

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D]

/-- The data specifying a functor `E.QuillenQ ⥤ D` by the universal property of Quillen's
Q-category: an object assignment, a covariant assignment on inflations, a contravariant assignment
on deflations, and compatibility on admissible bicartesian squares. -/
structure FunctorData (E : ExactStructure C) (D : Type u') [Category.{v'} D] where
  /-- The assignment on objects of `C`. -/
  obj : C → D
  /-- The covariant assignment on inflations. -/
  mapInflation : ∀ {X Y : C} (i : X ⟶ Y), E.IsInflation i → (obj X ⟶ obj Y)
  /-- The contravariant assignment on deflations. -/
  mapDeflation : ∀ {X Y : C} (p : Y ⟶ X), E.IsDeflation p → (obj X ⟶ obj Y)
  /-- Identity inflations map to identity morphisms. -/
  mapInflation_id : ∀ X : C, mapInflation (𝟙 X) (E.isInflation_id X) = 𝟙 (obj X)
  /-- Composition of inflations is preserved covariantly. -/
  mapInflation_comp : ∀ {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : E.IsInflation i) (hj : E.IsInflation j),
    mapInflation (i ≫ j) (E.isInflation_comp i j hi hj) =
      mapInflation i hi ≫ mapInflation j hj
  /-- Identity deflations map to identity morphisms. -/
  mapDeflation_id : ∀ X : C, mapDeflation (𝟙 X) (E.isDeflation_id X) = 𝟙 (obj X)
  /-- Composition of deflations is preserved contravariantly. -/
  mapDeflation_comp : ∀ {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y)
    (hp : E.IsDeflation p) (hq : E.IsDeflation q),
    mapDeflation (q ≫ p) (E.isDeflation_comp q p hq hp) =
      mapDeflation p hp ≫ mapDeflation q hq
  /-- Admissible bicartesian squares induce commuting composites in `D`. -/
  map_bicartesianSq : ∀ {P X Y Z : C} {p' : P ⟶ X} {i' : P ⟶ Z} {i : X ⟶ Y} {p : Z ⟶ Y}
    (hi : E.IsInflation i) (hp : E.IsDeflation p)
    (hp' : E.IsDeflation p') (hi' : E.IsInflation i'),
    BicartesianSq p' i' i p →
    mapInflation i hi ≫ mapDeflation p hp = mapDeflation p' hp' ≫ mapInflation i' hi'

namespace FunctorData

variable {E : ExactStructure C}

/-- Two `FunctorData` packages are equal when they agree on objects, inflations, and deflations. -/
@[ext (iff := false)]
theorem ext {d₁ d₂ : FunctorData E D}
    (h_obj : ∀ X : C, d₁.obj X = d₂.obj X)
    (h_inf : ∀ {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i),
      d₁.mapInflation i hi = eqToHom (h_obj X) ≫ d₂.mapInflation i hi ≫ eqToHom (h_obj Y).symm)
    (h_def : ∀ {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p),
      d₁.mapDeflation p hp = eqToHom (h_obj X) ≫ d₂.mapDeflation p hp ≫ eqToHom (h_obj Y).symm) :
    d₁ = d₂ := by
  cases d₁
  cases d₂
  have hobj : _ = _ := funext h_obj
  subst hobj
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h_inf h_def
  congr 1
  · funext X Y i hi
    exact h_inf i hi
  · funext X Y p hp
    exact h_def p hp

/-- The bicartesian-square axiom forces `mapDeflation` on an isomorphism `e` to agree with
`mapInflation` on its inverse `e.inv`. -/
theorem mapDeflation_of_iso (d : FunctorData E D) {X Y : C} (e : X ≅ Y) :
    d.mapDeflation e.hom (E.deflations.of_isIso e.hom) =
      d.mapInflation e.inv (E.inflations.of_isIso e.inv) := by
  have hpb : IsPullback (𝟙 X) (𝟙 X) e.hom e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hbc : BicartesianSq (𝟙 X) (𝟙 X) e.hom e.hom :=
    E.bicartesianSq_of_isPullback_of_isDeflation (E.deflations.of_isIso e.hom) hpb
  have h₁ : d.mapInflation e.hom (E.inflations.of_isIso e.hom) ≫
      d.mapDeflation e.hom (E.deflations.of_isIso e.hom) = 𝟙 (d.obj X) := by
    rw [d.map_bicartesianSq _ _ (E.isDeflation_id X) (E.isInflation_id X) hbc,
      d.mapDeflation_id, d.mapInflation_id, Category.id_comp]
  have h₂ : d.mapInflation e.inv (E.inflations.of_isIso e.inv) ≫
      d.mapInflation e.hom (E.inflations.of_isIso e.hom) = 𝟙 (d.obj Y) := by
    rw [← d.mapInflation_comp]
    simp only [Iso.inv_hom_id, d.mapInflation_id]
  calc
    d.mapDeflation e.hom (E.deflations.of_isIso e.hom)
        = 𝟙 (d.obj Y) ≫ d.mapDeflation e.hom (E.deflations.of_isIso e.hom) :=
      (Category.id_comp _).symm
    _ = (d.mapInflation e.inv (E.inflations.of_isIso e.inv) ≫
          d.mapInflation e.hom (E.inflations.of_isIso e.hom)) ≫
          d.mapDeflation e.hom (E.deflations.of_isIso e.hom) := by
      rw [h₂]
    _ = d.mapInflation e.inv (E.inflations.of_isIso e.inv) ≫
          (d.mapInflation e.hom (E.inflations.of_isIso e.hom) ≫
            d.mapDeflation e.hom (E.deflations.of_isIso e.hom)) :=
      Category.assoc _ _ _
    _ = d.mapInflation e.inv (E.inflations.of_isIso e.inv) := by
      rw [h₁, Category.comp_id]

/-- For an isomorphism `e : X ≅ Y`, the composite `mapDeflation e.hom ≫ mapInflation e.hom` is
the identity on `d.obj Y`. -/
theorem mapDeflation_comp_mapInflation_iso (d : FunctorData E D) {X Y : C} (e : X ≅ Y) :
    d.mapDeflation e.hom (E.deflations.of_isIso e.hom) ≫
      d.mapInflation e.hom (E.inflations.of_isIso e.hom) = 𝟙 (d.obj Y) := by
  rw [d.mapDeflation_of_iso e, ← d.mapInflation_comp]
  simp only [Iso.inv_hom_id, d.mapInflation_id]

/-- The `FunctorData` obtained by restricting a functor `F : E.QuillenQ ⥤ D` to objects,
inflations, and reversed deflations. -/
@[expose]
def ofFunctor (F : E.QuillenQ ⥤ D) : FunctorData E D where
  obj X := F.obj ⟨X⟩
  mapInflation i hi := F.map (ofInflation i hi)
  mapDeflation p hp := F.map (ofDeflation p hp)
  mapInflation_id X := by rw [ofInflation_id, F.map_id]
  mapInflation_comp i j hi hj := by rw [← ofInflation_comp, F.map_comp]
  mapDeflation_id X := by rw [ofDeflation_id, F.map_id]
  mapDeflation_comp p q hp hq := by rw [← ofDeflation_comp, F.map_comp]
  map_bicartesianSq hi hp _ _ hsq := by
    rw [← F.map_comp, ← F.map_comp,
      ofInflation_comp_ofDeflation_of_isPullback hi hp hsq.toIsPullback]

@[simp]
theorem ofFunctor_obj (F : E.QuillenQ ⥤ D) (X : C) :
    (ofFunctor F).obj X = F.obj ⟨X⟩ :=
  rfl

@[simp]
theorem ofFunctor_mapInflation (F : E.QuillenQ ⥤ D) {X Y : C}
    (i : X ⟶ Y) (hi : E.IsInflation i) :
    (ofFunctor F).mapInflation i hi = F.map (ofInflation i hi) :=
  rfl

@[simp]
theorem ofFunctor_mapDeflation (F : E.QuillenQ ⥤ D) {X Y : C}
    (p : Y ⟶ X) (hp : E.IsDeflation p) :
    (ofFunctor F).mapDeflation p hp = F.map (ofDeflation p hp) :=
  rfl

end FunctorData

variable {E : ExactStructure C}

private theorem lift_map_respectsIso (d : FunctorData E D) {X Y : C}
    (S₁ S₂ : Span E.deflations E.inflations X Y) (h : Nonempty (S₁ ≅ S₂)) :
    d.mapDeflation S₁.l S₁.wl ≫ d.mapInflation S₁.r S₁.wr =
      d.mapDeflation S₂.l S₂.wl ≫ d.mapInflation S₂.r S₂.wr := by
  obtain ⟨e⟩ := h
  let u : S₁.apex ≅ S₂.apex :=
    Span.SpanBicat.apexIso (Wₗ := E.deflations) (Wᵣ := E.inflations) (X := ⟨X⟩) (Y := ⟨Y⟩) e
  have : IsIso u.hom := u.isIso_hom
  have hl : S₁.l = u.hom ≫ S₂.l := e.hom.hom_l.symm
  have hr : S₁.r = u.hom ≫ S₂.r := e.hom.hom_r.symm
  have hdl : d.mapDeflation S₁.l S₁.wl =
      d.mapDeflation S₂.l S₂.wl ≫ d.mapDeflation u.hom (E.deflations.of_isIso u.hom) := by
    rw [← d.mapDeflation_comp]
    congr 1
  have hir : d.mapInflation S₁.r S₁.wr =
      d.mapInflation u.hom (E.inflations.of_isIso u.hom) ≫ d.mapInflation S₂.r S₂.wr := by
    rw [← d.mapInflation_comp]
    congr 1
  rw [hdl, hir, Category.assoc, ← Category.assoc (d.mapDeflation u.hom _),
    d.mapDeflation_comp_mapInflation_iso u, Category.id_comp]

private theorem lift_map_comp_aux (d : FunctorData E D) {X Y Z : C}
    (S₁ : Span E.deflations E.inflations X Y) (S₂ : Span E.deflations E.inflations Y Z) :
    d.mapDeflation (S₁.comp S₂).l (S₁.comp S₂).wl ≫
        d.mapInflation (S₁.comp S₂).r (S₁.comp S₂).wr =
      (d.mapDeflation S₁.l S₁.wl ≫ d.mapInflation S₁.r S₁.wr) ≫
        (d.mapDeflation S₂.l S₂.wl ≫ d.mapInflation S₂.r S₂.wr) := by
  have hpb : IsPullback (pullback.fst S₁.r S₂.l) (pullback.snd S₁.r S₂.l) S₁.r S₂.l :=
    IsPullback.of_hasPullback S₁.r S₂.l
  have hbc : BicartesianSq (pullback.fst S₁.r S₂.l) (pullback.snd S₁.r S₂.l) S₁.r S₂.l :=
    (E.bicartesianSq_of_isPullback_of_isDeflation S₂.wl hpb.flip).flip
  have hfst : E.IsDeflation (pullback.fst S₁.r S₂.l) :=
    E.isStableUnderBaseChange_deflations.of_isPullback hpb.flip S₂.wl
  have hsnd : E.IsInflation (pullback.snd S₁.r S₂.l) :=
    E.isInflation_of_isPullback_of_isDeflation S₂.wl S₁.wr hpb.flip
  dsimp only [Span.comp]
  rw [d.mapDeflation_comp S₁.l _ S₁.wl hfst, d.mapInflation_comp _ S₂.r hsnd S₂.wr,
    Category.assoc, ← Category.assoc (d.mapDeflation (pullback.fst S₁.r S₂.l) hfst),
    ← d.map_bicartesianSq S₁.wr S₂.wl hfst hsnd hbc, Category.assoc, Category.assoc]

/-- **Universal property of `Q(E)` (existence).** Extend `FunctorData E D` to a functor
`E.QuillenQ ⥤ D`, sending a span `X ↞ M ↣ Y` to `mapDeflation l ≫ mapInflation r`. -/
@[expose]
noncomputable def lift (d : FunctorData E D) : E.QuillenQ ⥤ D where
  obj X := d.obj X.as
  map := homLift (fun S ↦ d.mapDeflation S.l S.wl ≫ d.mapInflation S.r S.wr)
    (fun S₁ S₂ h ↦ by exact lift_map_respectsIso d S₁ S₂ h)
  map_id X := by
    rw [← homMk_id X.as, homLift_homMk]
    dsimp only [Span.id]
    rw [d.mapDeflation_id, d.mapInflation_id, Category.id_comp]
  map_comp f g := by
    refine hom_induction (fun S₁ ↦ ?_) f
    refine hom_induction (fun S₂ ↦ ?_) g
    rw [homMk_comp, homLift_homMk, homLift_homMk, homLift_homMk]
    exact lift_map_comp_aux d S₁ S₂

@[simp]
theorem lift_obj (d : FunctorData E D) (X : E.QuillenQ) :
    (lift d).obj X = d.obj X.as :=
  rfl

@[simp]
theorem lift_map_homMk (d : FunctorData E D) {X Y : C}
    (S : Span E.deflations E.inflations X Y) :
    (lift d).map (homMk S) = d.mapDeflation S.l S.wl ≫ d.mapInflation S.r S.wr :=
  homLift_homMk _ _ S

@[simp]
theorem lift_map_ofInflation (d : FunctorData E D) {X Y : C}
    (i : X ⟶ Y) (hi : E.IsInflation i) :
    (lift d).map (ofInflation i hi) = d.mapInflation i hi := by
  rw [ofInflation_eq_homMk, lift_map_homMk, d.mapDeflation_id, Category.id_comp]

@[simp]
theorem lift_map_ofDeflation (d : FunctorData E D) {X Y : C}
    (p : Y ⟶ X) (hp : E.IsDeflation p) :
    (lift d).map (ofDeflation p hp) = d.mapDeflation p hp := by
  rw [ofDeflation_eq_homMk, lift_map_homMk, d.mapInflation_id, Category.comp_id]

/-- **Universal property of `Q(E)` (uniqueness).** Two functors out of `E.QuillenQ` that agree on
objects, inflations, and reversed deflations are equal. -/
theorem functor_ext {F G : E.QuillenQ ⥤ D}
    (h_obj : ∀ X : C, F.obj ⟨X⟩ = G.obj ⟨X⟩)
    (h_inf : ∀ {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i),
      F.map (ofInflation i hi) =
        eqToHom (h_obj X) ≫ G.map (ofInflation i hi) ≫ eqToHom (h_obj Y).symm)
    (h_def : ∀ {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p),
      F.map (ofDeflation p hp) =
        eqToHom (h_obj X) ≫ G.map (ofDeflation p hp) ≫ eqToHom (h_obj Y).symm) :
    F = G := by
  refine CategoryTheory.Functor.ext (fun X ↦ h_obj X.as) fun X Y f ↦ ?_
  refine hom_induction (fun S ↦ ?_) f
  rw [homMk_eq_ofDeflation_comp_ofInflation, F.map_comp, G.map_comp, h_def S.l S.wl,
    h_inf S.r S.wr]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Heterogeneous extensionality for functors out of `E.QuillenQ`: two functors agreeing on
objects, inflations, and reversed deflations (up to heterogeneous equality) are equal. -/
theorem functor_hext {F G : E.QuillenQ ⥤ D}
    (h_obj : ∀ X : C, F.obj ⟨X⟩ = G.obj ⟨X⟩)
    (h_inf : ∀ {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i),
      F.map (ofInflation i hi) ≍ G.map (ofInflation i hi))
    (h_def : ∀ {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p),
      F.map (ofDeflation p hp) ≍ G.map (ofDeflation p hp)) :
    F = G :=
  functor_ext h_obj
    (fun i hi ↦ (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).mpr (h_inf i hi))
    (fun p hp ↦ (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).mpr (h_def p hp))

/-- **The universal property of `Q(E)` as a bijection.** Functors `E.QuillenQ ⥤ D` correspond
bijectively to `FunctorData E D`. -/
noncomputable def liftEquiv : FunctorData E D ≃ (E.QuillenQ ⥤ D) where
  toFun := lift
  invFun := FunctorData.ofFunctor
  left_inv d :=
    FunctorData.ext (fun _ ↦ rfl)
      (fun _ _ ↦ (conj_eqToHom_iff_heq _ _ rfl rfl).mpr (by simp))
      (fun _ _ ↦ (conj_eqToHom_iff_heq _ _ rfl rfl).mpr (by simp))
  right_inv F :=
    functor_hext (fun _ ↦ rfl)
      (fun _ _ ↦ by simp)
      (fun _ _ ↦ by simp)

@[simp]
theorem liftEquiv_apply (d : FunctorData E D) : liftEquiv d = lift d :=
  (rfl)

@[simp]
theorem liftEquiv_symm_apply (F : E.QuillenQ ⥤ D) :
    liftEquiv.symm F = FunctorData.ofFunctor F :=
  (rfl)

/-- Construct a natural transformation between functors out of `E.QuillenQ` by verifying naturality
on inflations and reversed deflations. -/
def natTransMk {F G : E.QuillenQ ⥤ D} (app : ∀ X : C, F.obj ⟨X⟩ ⟶ G.obj ⟨X⟩)
    (h_inf : ∀ {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i),
      F.map (ofInflation i hi) ≫ app Y = app X ≫ G.map (ofInflation i hi))
    (h_def : ∀ {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p),
      F.map (ofDeflation p hp) ≫ app Y = app X ≫ G.map (ofDeflation p hp)) :
    F ⟶ G where
  app X := app X.as
  naturality X Y f := by
    refine hom_induction (fun S ↦ ?_) f
    rw [homMk_eq_ofDeflation_comp_ofInflation, F.map_comp, G.map_comp,
      Category.assoc, h_inf S.r S.wr, reassoc_of% (h_def S.l S.wl)]

@[simp]
theorem natTransMk_app {F G : E.QuillenQ ⥤ D} (app : ∀ X : C, F.obj ⟨X⟩ ⟶ G.obj ⟨X⟩)
    (h_inf) (h_def) (X : E.QuillenQ) :
    (natTransMk app h_inf h_def).app X = app X.as :=
  (rfl)

/-- Construct a natural isomorphism between functors out of `E.QuillenQ` from objectwise
isomorphisms that are natural on inflations and reversed deflations. -/
noncomputable def natIsoMk {F G : E.QuillenQ ⥤ D} (app : ∀ X : C, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩)
    (h_inf : ∀ {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i),
      F.map (ofInflation i hi) ≫ (app Y).hom = (app X).hom ≫ G.map (ofInflation i hi))
    (h_def : ∀ {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p),
      F.map (ofDeflation p hp) ≫ (app Y).hom = (app X).hom ≫ G.map (ofDeflation p hp)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ app X.as) fun {_ _} f ↦
    (natTransMk (fun Z ↦ (app Z).hom) h_inf h_def).naturality f

@[simp]
theorem natIsoMk_hom_app {F G : E.QuillenQ ⥤ D} (app : ∀ X : C, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩)
    (h_inf) (h_def) (X : E.QuillenQ) :
    (natIsoMk app h_inf h_def).hom.app X = (app X.as).hom :=
  (rfl)

@[simp]
theorem natIsoMk_inv_app {F G : E.QuillenQ ⥤ D} (app : ∀ X : C, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩)
    (h_inf) (h_def) (X : E.QuillenQ) :
    (natIsoMk app h_inf h_def).inv.app X = (app X.as).inv :=
  (rfl)

end Universal

/-! ### Functoriality for conflation-exact functors -/

section Functoriality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {C' : Type u'} [Category.{v'} C'] [Preadditive C'] [HasZeroObject C']
  [HasBinaryBiproducts C']
variable {C'' : Type u''} [Category.{v''} C''] [Preadditive C''] [HasZeroObject C'']
  [HasBinaryBiproducts C'']

/-- A conflation-exact additive functor `F : C ⥤ C'` induces a functor `E.QuillenQ ⥤ E'.QuillenQ`
on Q-categories. -/
@[expose]
noncomputable def map {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) : E.QuillenQ ⥤ E'.QuillenQ :=
  lift
    { obj := fun X ↦ ⟨F.obj X⟩
      mapInflation := fun i hi ↦ ofInflation (F.map i) (hF.map_isInflation hi)
      mapDeflation := fun p hp ↦ ofDeflation (F.map p) (hF.map_isDeflation hp)
      mapInflation_id := fun X ↦ by simp
      mapInflation_comp := fun i j hi hj ↦ by simp
      mapDeflation_id := fun X ↦ by simp
      mapDeflation_comp := fun p q hp hq ↦ by simp
      map_bicartesianSq := fun hi hp _ _ hsq ↦ by
        have hpb : IsPullback (F.map _) (F.map _) (F.map _) (F.map _) :=
          (hF.map_isPullback hp hsq.toIsPullback.flip).flip
        exact ofInflation_comp_ofDeflation_of_isPullback
          (hF.map_isInflation hi) (hF.map_isDeflation hp) hpb }

@[simp]
theorem map_obj {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) (X : E.QuillenQ) :
    (map hF).obj X = ⟨F.obj X.as⟩ :=
  rfl

@[simp]
theorem map_ofInflation {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i) :
    (map hF).map (ofInflation i hi) = ofInflation (F.map i) (hF.map_isInflation hi) :=
  lift_map_ofInflation _ i hi

@[simp]
theorem map_ofDeflation {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p) :
    (map hF).map (ofDeflation p hp) = ofDeflation (F.map p) (hF.map_isDeflation hp) :=
  lift_map_ofDeflation _ p hp

@[simp]
theorem map_homMk {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) {X Y : C} (S : Span E.deflations E.inflations X Y) :
    (map hF).map (homMk S) =
      homMk ⟨F.obj S.apex, F.map S.l, F.map S.r,
        hF.map_isDeflation S.wl, hF.map_isInflation S.wr⟩ := by
  simp [homMk_eq_ofDeflation_comp_ofInflation]

@[simp]
theorem map_ofIso {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) {X Y : C} (e : X ≅ Y) :
    (map hF).mapIso (ofIso (E := E) e) = ofIso (E := E') (F.mapIso e) := by
  ext
  simp

/-- The identity exact functor induces the identity functor on `Q(E)`. -/
@[simp]
theorem map_id (E : ExactStructure C) :
    map (ExactStructure.IsConflationExact.id (E := E)) = 𝟭 E.QuillenQ :=
  functor_hext (fun _ ↦ rfl) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)

/-- Composition of conflation-exact functors strictly commutes with `QuillenQ.map`. -/
theorem map_comp {E : ExactStructure C} {E' : ExactStructure C'} {E'' : ExactStructure C''}
    {F : C ⥤ C'} {H : C' ⥤ C''} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H) :
    map (hF.comp hH) = map hF ⋙ map hH :=
  functor_hext (fun _ ↦ rfl) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)

/-- A natural isomorphism between conflation-exact functors induces a natural isomorphism between
the induced functors on Q-categories. -/
noncomputable def mapNatIso {E : ExactStructure C} {E' : ExactStructure C'} {F G : C ⥤ C'}
    [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G) :
    map hF ≅ map hG :=
  natIsoMk (fun X ↦ ofIso (E := E') (e.app X))
    (fun i _ ↦ by
      simp only [map_obj, map_ofInflation]
      exact ofInflation_comp_ofIso _ _ (e.app _) (e.app _) (e.hom.naturality i))
    (fun p _ ↦ by
      simp only [map_obj, map_ofDeflation]
      exact ofDeflation_comp_ofIso _ _ (e.app _) (e.app _) (e.hom.naturality p))

@[simp]
theorem mapNatIso_hom_app {E : ExactStructure C} {E' : ExactStructure C'} {F G : C ⥤ C'}
    [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (X : E.QuillenQ) :
    (mapNatIso hF hG e).hom.app X =
      ofInflation (e.hom.app X.as) (E'.inflations.of_isIso (e.hom.app X.as)) :=
  (ofIso_hom (e.app X.as))

@[simp]
theorem mapNatIso_inv_app {E : ExactStructure C} {E' : ExactStructure C'} {F G : C ⥤ C'}
    [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (X : E.QuillenQ) :
    (mapNatIso hF hG e).inv.app X =
      ofInflation (e.inv.app X.as) (E'.inflations.of_isIso (e.inv.app X.as)) :=
  (ofIso_inv (e.app X.as))

@[simp]
theorem mapNatIso_refl {E : ExactStructure C} {E' : ExactStructure C'} {F : C ⥤ C'} [F.Additive]
    (hF : E.IsConflationExact E' F) :
    mapNatIso hF hF (Iso.refl F) = Iso.refl (map hF) := by
  ext X
  simp

@[simp]
theorem mapNatIso_trans {E : ExactStructure C} {E' : ExactStructure C'} {F G H : C ⥤ C'}
    [F.Additive] [G.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G)
    (hH : E.IsConflationExact E' H) (e₁ : F ≅ G) (e₂ : G ≅ H) :
    mapNatIso hF hH (e₁ ≪≫ e₂) = mapNatIso hF hG e₁ ≪≫ mapNatIso hG hH e₂ := by
  ext X
  simp

@[simp]
theorem mapNatIso_symm {E : ExactStructure C} {E' : ExactStructure C'} {F G : C ⥤ C'}
    [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G) :
    mapNatIso hG hF e.symm = (mapNatIso hF hG e).symm := by
  ext X
  simp

/-- An additive equivalence whose forward and inverse functors are both conflation-exact induces
an equivalence between Q-categories. -/
@[expose]
noncomputable def mapEquivalence {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse) :
    E.QuillenQ ≌ E'.QuillenQ where
  functor := map hF
  inverse := map hG
  unitIso :=
    natIsoMk (fun X ↦ ofIso (E := E) (e.unitIso.app X))
      (fun i _ ↦ by
        simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
          map_obj, map_ofInflation]
        exact ofInflation_comp_ofIso _ _ (e.unitIso.app _) (e.unitIso.app _)
          (e.unit.naturality i))
      (fun p _ ↦ by
        simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
          map_obj, map_ofDeflation]
        exact ofDeflation_comp_ofIso _ _ (e.unitIso.app _) (e.unitIso.app _)
          (e.unit.naturality p))
  counitIso :=
    natIsoMk (fun Y ↦ ofIso (E := E') (e.counitIso.app Y))
      (fun i _ ↦ by
        simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
          map_obj, map_ofInflation]
        exact ofInflation_comp_ofIso _ _ (e.counitIso.app _) (e.counitIso.app _)
          (e.counit.naturality i))
      (fun p _ ↦ by
        simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
          map_obj, map_ofDeflation]
        exact ofDeflation_comp_ofIso _ _ (e.counitIso.app _) (e.counitIso.app _)
          (e.counit.naturality p))
  functor_unitIso_comp X := by
    dsimp only [natIsoMk, NatIso.ofComponents, map_obj]
    simp only [ofIso_hom, map_ofInflation, ofInflation_comp]
    rw [← ofInflation_id]
    exact (ofInflation_inj _ _).mpr (e.functor_unitIso_comp X.as)

@[simp]
theorem mapEquivalence_functor {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse) :
    (mapEquivalence e hF hG).functor = map hF :=
  rfl

@[simp]
theorem mapEquivalence_inverse {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse) :
    (mapEquivalence e hF hG).inverse = map hG :=
  rfl

@[simp]
theorem mapEquivalence_unitIso_hom_app {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse)
    (X : E.QuillenQ) :
    (mapEquivalence e hF hG).unitIso.hom.app X =
      ofInflation (e.unit.app X.as) (E.inflations.of_isIso (e.unit.app X.as)) :=
  (ofIso_hom (e.unitIso.app X.as))

@[simp]
theorem mapEquivalence_unitIso_inv_app {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse)
    (X : E.QuillenQ) :
    (mapEquivalence e hF hG).unitIso.inv.app X =
      ofInflation (e.unitInv.app X.as) (E.inflations.of_isIso (e.unitInv.app X.as)) :=
  (ofIso_inv (e.unitIso.app X.as))

@[simp]
theorem mapEquivalence_counitIso_hom_app {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse)
    (Y : E'.QuillenQ) :
    (mapEquivalence e hF hG).counitIso.hom.app Y =
      ofInflation (e.counit.app Y.as) (E'.inflations.of_isIso (e.counit.app Y.as)) :=
  (ofIso_hom (e.counitIso.app Y.as))

@[simp]
theorem mapEquivalence_counitIso_inv_app {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse)
    (Y : E'.QuillenQ) :
    (mapEquivalence e hF hG).counitIso.inv.app Y =
      ofInflation (e.counitInv.app Y.as) (E'.inflations.of_isIso (e.counitInv.app Y.as)) :=
  (ofIso_inv (e.counitIso.app Y.as))

/-- An additive equivalence that preserves and reflects conflations induces an equivalence of
Q-categories. -/
noncomputable def mapEquivalenceOfReflects {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hR : E.ReflectsConflations E' e.functor) :
    E.QuillenQ ≌ E'.QuillenQ :=
  mapEquivalence e hF (ExactStructure.isConflationExact_inverse_of_reflectsConflations e hR)

@[simp]
theorem mapEquivalenceOfReflects_functor {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hR : E.ReflectsConflations E' e.functor) :
    (mapEquivalenceOfReflects e hF hR).functor = map hF :=
  (rfl)

@[simp]
theorem mapEquivalenceOfReflects_inverse {E : ExactStructure C} {E' : ExactStructure C'}
    (e : C ≌ C') [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hR : E.ReflectsConflations E' e.functor) :
    (mapEquivalenceOfReflects e hF hR).inverse =
      map (ExactStructure.isConflationExact_inverse_of_reflectsConflations e hR) :=
  (rfl)

/-- Transporting an exact structure along an additive equivalence induces an equivalence of
Q-categories. -/
noncomputable def transportEquivalence (E : ExactStructure C) (e : C ≌ C') [e.functor.Additive] :
    E.QuillenQ ≌ (E.transport e).QuillenQ :=
  mapEquivalence e (E.isConflationExact_functor_transport e)
    (E.isConflationExact_inverse_transport e)

@[simp]
theorem transportEquivalence_functor (E : ExactStructure C) (e : C ≌ C') [e.functor.Additive] :
    (transportEquivalence E e).functor = map (E.isConflationExact_functor_transport e) :=
  (rfl)

@[simp]
theorem transportEquivalence_inverse (E : ExactStructure C) (e : C ≌ C') [e.functor.Additive] :
    (transportEquivalence E e).inverse = map (E.isConflationExact_inverse_transport e) :=
  (rfl)

end Functoriality

/-! ### Self-duality for the opposite exact category -/

section Opposite

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- The canonical functor `E.op.QuillenQ ⥤ E.QuillenQ`, interchanging inflations and reversed
deflations without reversing the direction of Q-morphisms. -/
@[expose]
noncomputable def opTo (E : ExactStructure C) : E.op.QuillenQ ⥤ E.QuillenQ :=
  lift
    { obj := fun X ↦ ⟨X.unop⟩
      mapInflation := fun i hi ↦ ofDeflation i.unop ((E.op_isInflation_iff i).mp hi)
      mapDeflation := fun p hp ↦ ofInflation p.unop ((E.op_isDeflation_iff p).mp hp)
      mapInflation_id := fun X ↦ by simp
      mapInflation_comp := fun i j hi hj ↦ by simp
      mapDeflation_id := fun X ↦ by simp
      mapDeflation_comp := fun p q hp hq ↦ by simp
      map_bicartesianSq := fun _ _ hp' hi' hsq ↦ by
        have hpb : IsPullback _ _ _ _ := hsq.toIsPushout.unop.flip
        exact (ofInflation_comp_ofDeflation_of_isPullback
          ((E.op_isDeflation_iff _).mp hp') ((E.op_isInflation_iff _).mp hi') hpb).symm }

/-- The canonical functor `E.QuillenQ ⥤ E.op.QuillenQ`, inverse to `opTo E`. -/
@[expose]
noncomputable def toOp (E : ExactStructure C) : E.QuillenQ ⥤ E.op.QuillenQ :=
  lift
    { obj := fun X ↦ ⟨Opposite.op X⟩
      mapInflation := fun i hi ↦ ofDeflation i.op ((E.op_isDeflation_iff i.op).mpr hi)
      mapDeflation := fun p hp ↦ ofInflation p.op ((E.op_isInflation_iff p.op).mpr hp)
      mapInflation_id := fun X ↦ by simp
      mapInflation_comp := fun i j hi hj ↦ by simp
      mapDeflation_id := fun X ↦ by simp
      mapDeflation_comp := fun p q hp hq ↦ by simp
      map_bicartesianSq := fun _ _ hp' hi' hsq ↦ by
        have hpb : IsPullback _ _ _ _ := hsq.toIsPushout.op.flip
        exact (ofInflation_comp_ofDeflation_of_isPullback (E := E.op)
          ((E.op_isInflation_iff _).mpr hp') ((E.op_isDeflation_iff _).mpr hi') hpb).symm }

@[simp]
theorem opTo_obj (E : ExactStructure C) (X : E.op.QuillenQ) :
    (opTo E).obj X = ⟨X.as.unop⟩ :=
  rfl

@[simp]
theorem opTo_map_ofInflation (E : ExactStructure C) {X Y : Cᵒᵖ}
    (i : X ⟶ Y) (hi : E.op.IsInflation i) :
    (opTo E).map (ofInflation i hi) = ofDeflation i.unop ((E.op_isInflation_iff i).mp hi) :=
  lift_map_ofInflation _ i hi

@[simp]
theorem opTo_map_ofDeflation (E : ExactStructure C) {X Y : Cᵒᵖ}
    (p : Y ⟶ X) (hp : E.op.IsDeflation p) :
    (opTo E).map (ofDeflation p hp) = ofInflation p.unop ((E.op_isDeflation_iff p).mp hp) :=
  lift_map_ofDeflation _ p hp

@[simp]
theorem toOp_obj (E : ExactStructure C) (X : E.QuillenQ) :
    (toOp E).obj X = ⟨Opposite.op X.as⟩ :=
  rfl

@[simp]
theorem toOp_map_ofInflation (E : ExactStructure C) {X Y : C}
    (i : X ⟶ Y) (hi : E.IsInflation i) :
    (toOp E).map (ofInflation i hi) = ofDeflation i.op ((E.op_isDeflation_iff i.op).mpr hi) :=
  lift_map_ofInflation _ i hi

@[simp]
theorem toOp_map_ofDeflation (E : ExactStructure C) {X Y : C}
    (p : Y ⟶ X) (hp : E.IsDeflation p) :
    (toOp E).map (ofDeflation p hp) = ofInflation p.op ((E.op_isInflation_iff p.op).mpr hp) :=
  lift_map_ofDeflation _ p hp

/-- `opTo E` followed by `toOp E` is strictly the identity functor on `E.op.QuillenQ`. -/
@[simp]
theorem opTo_comp_toOp (E : ExactStructure C) :
    opTo E ⋙ toOp E = 𝟭 E.op.QuillenQ :=
  functor_hext (fun _ ↦ rfl) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)

/-- `toOp E` followed by `opTo E` is strictly the identity functor on `E.QuillenQ`. -/
@[simp]
theorem toOp_comp_opTo (E : ExactStructure C) :
    toOp E ⋙ opTo E = 𝟭 E.QuillenQ :=
  functor_hext (fun _ ↦ rfl) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)

/-- **Self-duality of Quillen's Q-construction.** The Q-category of the opposite exact structure is
canonically equivalent (in fact strictly isomorphic via `opTo_comp_toOp` and `toOp_comp_opTo`) to
`E.QuillenQ`, interchanging inflations and reversed deflations without reversing the direction of
Q-morphisms. -/
@[expose]
noncomputable def opEquivalence (E : ExactStructure C) : E.op.QuillenQ ≌ E.QuillenQ where
  functor := opTo E
  inverse := toOp E
  unitIso := natIsoMk (fun X ↦ Iso.refl (⟨X⟩ : E.op.QuillenQ))
    (fun i hi ↦ by simp) (fun p hp ↦ by simp)
  counitIso := natIsoMk (fun X ↦ Iso.refl (⟨X⟩ : E.QuillenQ))
    (fun i hi ↦ by simp) (fun p hp ↦ by simp)
  functor_unitIso_comp X := by
    dsimp only [natIsoMk, NatIso.ofComponents, opTo_obj]
    simp

@[simp]
theorem opEquivalence_functor (E : ExactStructure C) :
    (opEquivalence E).functor = opTo E :=
  rfl

@[simp]
theorem opEquivalence_inverse (E : ExactStructure C) :
    (opEquivalence E).inverse = toOp E :=
  rfl

@[simp]
theorem opEquivalence_unitIso_hom_app (E : ExactStructure C) (X : E.op.QuillenQ) :
    (opEquivalence E).unitIso.hom.app X = 𝟙 X :=
  (rfl)

@[simp]
theorem opEquivalence_unitIso_inv_app (E : ExactStructure C) (X : E.op.QuillenQ) :
    (opEquivalence E).unitIso.inv.app X = 𝟙 X :=
  (rfl)

@[simp]
theorem opEquivalence_counitIso_hom_app (E : ExactStructure C) (X : E.QuillenQ) :
    (opEquivalence E).counitIso.hom.app X = 𝟙 X :=
  (rfl)

@[simp]
theorem opEquivalence_counitIso_inv_app (E : ExactStructure C) (X : E.QuillenQ) :
    (opEquivalence E).counitIso.inv.app X = 𝟙 X :=
  (rfl)

end Opposite

end TauCeti.ExactStructure.QuillenQ
