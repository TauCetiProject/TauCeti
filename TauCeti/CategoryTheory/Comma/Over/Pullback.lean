/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.EqToHom
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map

/-!
# Base change in over categories: coherence, commuting squares, faithfulness, and epimorphisms

Mathlib identifies base change `Over.pullback` along an identity with the identity functor
(`Over.pullbackId`) and base change along a composite with the composite of base changes
(`Over.pullbackComp`). This file records that these identifications are coherent, up to the
equalities `f ≫ 𝟙 Y = f`, `𝟙 X ≫ f = f` and `f ≫ g ≫ h = (f ≫ g) ≫ h`:

* `CategoryTheory.Over.mapPullbackAdj_homEquiv_apply_left`,
  `CategoryTheory.Over.mapPullbackAdj_homEquiv_symm_left`,
  `CategoryTheory.Over.pullback_map_left_fst`, and
  `CategoryTheory.Over.pullback_hom_ext`: computation and extensionality for `Over.mapPullbackAdj`
  and `Over.pullback`;
* `CategoryTheory.Over.pullbackComp_id_inv_app_comp_eqToHom`: `pullbackComp f (𝟙 Y)` is the base
  change along `f` of `pullbackId`;
* `CategoryTheory.Over.pullbackComp_id_left_hom_app_comp_pullbackId`: `pullbackComp (𝟙 X) f`
  followed by `pullbackId` is the identity of base change along `f`;
* `CategoryTheory.Over.pullbackCompIsoOfEq_hom_app_eq`: the two identifications of base
  change along `f ≫ g ≫ h` with the composite of the three base changes agree;
* `CategoryTheory.Over.pullbackCongr` and `CategoryTheory.Over.pullbackCompIsoOfEq`: natural
  isomorphisms of `Over.pullback` along equal base morphisms and along factorizations `f ≫ g = fg`,
  together with `pullbackTransport`, `pullbackTransportIso`, `Limits.pullback` projection,
  identity/composition and mixed composition rules, and symmetry-comparison lemmas
  (`pullbackHomOfFstEq`, `pullbackLeftSymm`, `pullbackCompIsoOfEq_conj_left_eq_pullbackMap`,
  `pullbackCompIsoOfEq_conj_hom_of_fstEq`, `pullbackCompIsoOfEq_inv_map_hom_fst_inv_fst`);
* `CategoryTheory.Over.pullback_map_left_of_eq_mk`: transports `((Over.pullback g).map φ).left`
  along identifications `Y₁ = Over.mk p₁` and `Y₂ = Over.mk p₂` to a `Limits.pullback.lift`;
* `CategoryTheory.Over.pullback_iso_triangle`: for an isomorphism `e : X ≅ Y`, the unit and
  counit built from `pullbackId` and `pullbackComp` satisfy the triangle identity for
  `pullback e.hom` and `pullback e.inv`.

For a commuting square `i' ≫ g = t ≫ i`, the natural isomorphism
`CategoryTheory.Over.pullbackPullbackIsoOfComm` identifies base change along `g` and then along
`i'` with base change along `i` and then along `t`;
when `i` and `i'` are points, this says the fiber at `i'` of the base change along `g` is the base
change along `t` of the fiber at `i`. For a commuting triangle `a ≫ b = d`, the natural isomorphism
`CategoryTheory.Over.pullbackCompIsoOfEq` identifies base change along `b` and then along `a` with
base change along `d`, coherently for three composable morphisms
(`CategoryTheory.Over.pullbackCompIsoOfEq_hom_app_eq`); in particular, morphisms which agree after
base change along `b` agree after base change along `d`
(`CategoryTheory.Over.pullback_map_eq_map_of_comp_eq`). For a cone `c` over a diagram `D`, the
predicate `CategoryTheory.Limits.Cone.LiftsAlong` says that a morphism between base changes to the
cone point is, up to these identifications, the base change of a morphism between base changes to a
member of `D`; lifts are stable under passage to later members
(`CategoryTheory.Limits.Cone.LiftsAlong.precomp`) and under composition
(`CategoryTheory.Limits.Cone.liftsAlong_comp`).

It also establishes faithfulness and epimorphism preservation for the base-change functors
`Over.pullback f : Over Y ⥤ Over X` and `Over.star X : C ⥤ Over X`:

* `CategoryTheory.Over.preservesEpimorphisms_pullback`: when epimorphisms in `C` are stable under
  base change and `Over.forget Y` preserves epimorphisms, `Over.pullback f` preserves epimorphisms;
* `CategoryTheory.Over.faithful_star` and `CategoryTheory.Over.jointlyFaithful_star`: `Over.star X`
  is faithful when the second projections `X ⨯ Y ⟶ Y` are epimorphisms (and jointly faithful for a
  family `U` whose second projections are jointly epimorphic);
* `CategoryTheory.Over.preservesEpimorphisms_star`: `Over.star X` preserves epimorphisms whenever
  `X ⨯ -` does (in particular when epimorphisms in `C` are stable under base change).

For a monomorphism `g`, the unit of `Over.map g ⊣ Over.pullback g` is an isomorphism
(`CategoryTheory.Over.isIso_mapPullbackAdj_unit_app`).

Finally, `CategoryTheory.IsPullback.overPullbackCompMapIso` is the Beck–Chevalley isomorphism of a
pullback square `fst ≫ f = snd ≫ g`: `Over.pullback fst ⋙ Over.map snd ≅ Over.map f ⋙
Over.pullback g`.
-/

public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Over

variable {C : Type u} [Category.{v} C]

section Adjunction

/-- Underlying morphism of `((Over.mapPullbackAdj f).homEquiv x y).symm v`. -/
@[simp] theorem mapPullbackAdj_homEquiv_symm_left {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {x : Over X} {y : Over Y} (v : x ⟶ (pullback f).obj y) :
    (((mapPullbackAdj f).homEquiv x y).symm v).left = v.left ≫ Limits.pullback.fst y.hom f := by
  simp [Adjunction.homEquiv_counit]

/-- Underlying morphism of `(Over.mapPullbackAdj f).homEquiv x y u` as a `Limits.pullback.lift`. -/
@[simp] theorem mapPullbackAdj_homEquiv_apply_left {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {x : Over X} {y : Over Y} (u : (Over.map f).obj x ⟶ y) :
    ((mapPullbackAdj f).homEquiv x y u).left = Limits.pullback.lift u.left x.hom (by simp) := by
  apply Limits.pullback.hom_ext
  · rw [Limits.pullback.lift_fst, ← mapPullbackAdj_homEquiv_symm_left, Equiv.symm_apply_apply]
  · simpa using Over.w ((mapPullbackAdj f).homEquiv x y u)

/-- First projection of `(Over.mapPullbackAdj f).homEquiv x y u`. -/
@[reassoc] theorem mapPullbackAdj_homEquiv_apply_left_fst {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {x : Over X} {y : Over Y} (u : (Over.map f).obj x ⟶ y) :
    ((mapPullbackAdj f).homEquiv x y u).left ≫ Limits.pullback.fst y.hom f = u.left := by
  simp

/-- Second projection of `(Over.mapPullbackAdj f).homEquiv x y u`. -/
@[reassoc] theorem mapPullbackAdj_homEquiv_apply_left_snd {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {x : Over X} {y : Over Y} (u : (Over.map f).obj x ⟶ y) :
    ((mapPullbackAdj f).homEquiv x y u).left ≫ Limits.pullback.snd y.hom f = x.hom := by
  simp

/-- Two morphisms into `(Over.pullback f).obj y` are equal if their compositions with
`Limits.pullback.fst y.hom f` agree (equivalently, their adjoints under `Over.mapPullbackAdj f`
agree). -/
theorem pullback_hom_ext {X Y : C} {f : X ⟶ Y} [HasPullbacksAlong f]
    {x : Over X} {y : Over Y} {v₁ v₂ : x ⟶ (pullback f).obj y}
    (h : v₁.left ≫ Limits.pullback.fst y.hom f = v₂.left ≫ Limits.pullback.fst y.hom f) :
    v₁ = v₂ :=
  ((mapPullbackAdj f).homEquiv x y).symm.injective <| Over.OverMorphism.ext <| by
    simpa [mapPullbackAdj_homEquiv_symm_left] using h

/-- First projection of `((Over.pullback f).map g).left`. -/
@[reassoc] theorem pullback_map_left_fst {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} (g : A ⟶ B) :
    ((pullback f).map g).left ≫ Limits.pullback.fst B.hom f =
      Limits.pullback.fst A.hom f ≫ g.left := by
  simp

end Adjunction

section Coherence

attribute [local instance] hasPullback_of_right_iso

/-- Base change along `f : X ⟶ Y` of the identification `pullbackId` of base change along the
identity is the composition isomorphism `pullbackComp f (𝟙 Y)`, up to the equality
`f ≫ 𝟙 Y = f`. -/
@[reassoc]
theorem pullbackComp_id_inv_app_comp_eqToHom {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    (A : Over Y) :
    (pullbackComp f (𝟙 Y)).inv.app A ≫ eqToHom (by simp) =
      (pullback f).map (pullbackId.hom.app A) := by
  -- The identity is checked on the two projections out of `A ×_Y X`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_fst A.hom (Category.comp_id f)]
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_snd A.hom (Category.comp_id f)]

/-- Base change along `f` followed by base change along `𝟙 X` is base change along `𝟙 X ≫ f`: the
composition isomorphism `pullbackComp (𝟙 X) f` followed by `pullbackId` is the identity, up to the
equality `𝟙 X ≫ f = f`. -/
@[reassoc]
theorem pullbackComp_id_left_hom_app_comp_pullbackId {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    (A : Over Y) :
    (pullbackComp (𝟙 X) f).hom.app A ≫ pullbackId.hom.app ((pullback f).obj A) =
      eqToHom (by simp) := by
  -- As above, the identity is checked on the two projections out of `A ×_Y X`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_fst A.hom (Category.id_comp f)]
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_snd A.hom (Category.id_comp f)]

/-- For an isomorphism `e : X ≅ Y`, the unit and counit built from `pullbackId` and `pullbackComp`
for `pullback e.hom` and `pullback e.inv` satisfy the triangle identity on every object `A` of
`Over Y`. -/
@[reassoc]
theorem pullback_iso_triangle {X Y : C} (e : X ≅ Y) (A : Over Y) :
    (pullback e.hom).map
        (pullbackId.inv.app A ≫ eqToHom (by simp) ≫ (pullbackComp e.inv e.hom).hom.app A) ≫
      (pullbackComp e.hom e.inv).inv.app ((pullback e.hom).obj A) ≫
        eqToHom (by simp) ≫ pullbackId.hom.app ((pullback e.hom).obj A) =
      𝟙 ((pullback e.hom).obj A) := by
  -- As above, the identity is checked on the two projections out of `A ×_Y X`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, pullbackId,
      eqToHom_comp_pullback_fst_assoc (pullback.snd A.hom e.hom) e.hom_inv_id,
      eqToHom_comp_pullback_fst A.hom e.inv_hom_id.symm]
  · exact (Over.w _).trans (Category.id_comp _).symm

end Coherence

section Congr

variable {X Y : C}

/-- Pullback functors on `Over` categories along equal base morphisms are naturally isomorphic. -/
noncomputable def pullbackCongr {f₁ f₂ : X ⟶ Y} [HasPullbacksAlong f₁] [HasPullbacksAlong f₂]
    (h : f₁ = f₂) : pullback f₁ ≅ pullback f₂ := eqToIso (by subst h; rfl)

/-- Along `rfl`, `pullbackCongr` is the identity natural isomorphism. -/
@[simp] theorem pullbackCongr_refl (f : X ⟶ Y) [HasPullbacksAlong f] :
    pullbackCongr (rfl : f = f) = Iso.refl (pullback f) := (rfl)

variable {f₁ f₂ : X ⟶ Y} [HasPullbacksAlong f₁] [HasPullbacksAlong f₂]

/-- `pullbackCongr` reverses along `Eq.symm`. -/
@[simp] theorem pullbackCongr_symm (h : f₁ = f₂) :
    (pullbackCongr h).symm = pullbackCongr h.symm := by subst h; rfl

/-- The components of `(pullbackCongr h).hom` are `eqToHom` along `h`. -/
theorem pullbackCongr_hom_app (h : f₁ = f₂) (A : Over Y) :
    (pullbackCongr h).hom.app A = eqToHom (by subst h; rfl) := by subst h; rfl

/-- The components of `(pullbackCongr h).inv` are `eqToHom` along `h.symm`. -/
theorem pullbackCongr_inv_app (h : f₁ = f₂) (A : Over Y) :
    (pullbackCongr h).inv.app A = eqToHom (by subst h; rfl) := by subst h; rfl

/-- First projection of `(pullbackCongr h).hom.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_hom_app_left_fst (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.fst A.hom f₂ =
      Limits.pullback.fst A.hom f₁ := by subst h; exact Category.id_comp _

/-- Second projection of `(pullbackCongr h).hom.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_hom_app_left_snd (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.snd A.hom f₂ =
      Limits.pullback.snd A.hom f₁ := by subst h; exact Category.id_comp _

/-- First projection of `(pullbackCongr h).inv.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_inv_app_left_fst (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.fst A.hom f₁ =
      Limits.pullback.fst A.hom f₂ := by subst h; exact Category.id_comp _

/-- Second projection of `(pullbackCongr h).inv.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_inv_app_left_snd (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.snd A.hom f₁ =
      Limits.pullback.snd A.hom f₂ := by subst h; exact Category.id_comp _

end Congr

section CommSquare

variable {S S' s s' : C} {g : S' ⟶ S} {i : s ⟶ S} {i' : s' ⟶ S'} {t : s' ⟶ s}
  [HasPullbacksAlong g] [HasPullbacksAlong i] [HasPullbacksAlong i'] [HasPullbacksAlong t]

/-- For a commuting square `i' ≫ g = t ≫ i`, base change along `g : S' ⟶ S` and then along
`i' : s' ⟶ S'` is naturally isomorphic to base change along `i : s ⟶ S` and then along
`t : s' ⟶ s`. When `i` and `i'` are points, this is the **fiber of a base change**: the fiber at
`i'` of the base change of `A` along `g` is the base change along `t` of the fiber of `A` at `i`. -/
noncomputable def pullbackPullbackIsoOfComm (h : i' ≫ g = t ≫ i) :
    pullback g ⋙ pullback i' ≅ pullback i ⋙ pullback t :=
  (pullbackComp i' g).symm ≪≫ eqToIso (by simp only [h]) ≪≫ pullbackComp t i

/-- `pullbackPullbackIsoOfComm` is `pullbackComp i' g` inverted, followed by `pullbackComp t i`,
up to the equality `i' ≫ g = t ≫ i`. -/
theorem pullbackPullbackIsoOfComm_hom_app (h : i' ≫ g = t ≫ i) (A : Over S) :
    (pullbackPullbackIsoOfComm h).hom.app A =
      (pullbackComp i' g).inv.app A ≫ eqToHom (by simp only [h]) ≫
        (pullbackComp t i).hom.app A := by
  simp [pullbackPullbackIsoOfComm, eqToHom_app]

/-- `pullbackPullbackIsoOfComm` commutes with the projections to `A`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIsoOfComm_hom_app_left_fst (h : i' ≫ g = t ≫ i) (A : Over S) :
    ((pullbackPullbackIsoOfComm h).hom.app A).left ≫ pullback.fst (pullback.snd A.hom i) t ≫
        pullback.fst A.hom i =
      pullback.fst (pullback.snd A.hom g) i' ≫ pullback.fst A.hom g := by
  simp only [pullbackPullbackIsoOfComm_hom_app, comp_left, eqToHom_left, Category.assoc]
  have h₁ : ((pullbackComp t i).hom.app A).left ≫ pullback.fst (pullback.snd A.hom i) t ≫
      pullback.fst A.hom i = pullback.fst A.hom (t ≫ i) := by
    simp [pullbackComp]
  have h₂ : ((pullbackComp i' g).inv.app A).left ≫ pullback.fst A.hom (i' ≫ g) =
      pullback.fst (pullback.snd A.hom g) i' ≫ pullback.fst A.hom g := by
    simp [pullbackComp]
  rw [h₁, eqToHom_comp_pullback_fst A.hom h, h₂]

/-- `pullbackPullbackIsoOfComm` commutes with the projections to `s'`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIsoOfComm_hom_app_left_snd (h : i' ≫ g = t ≫ i) (A : Over S) :
    ((pullbackPullbackIsoOfComm h).hom.app A).left ≫ pullback.snd (pullback.snd A.hom i) t =
      pullback.snd (pullback.snd A.hom g) i' :=
  Over.w ((pullbackPullbackIsoOfComm h).hom.app A)

end CommSquare

section Triangle

variable {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {d : X ⟶ Z} [HasPullbacksAlong a]
  [HasPullbacksAlong b] [HasPullbacksAlong d]

/-- For a commuting triangle `a ≫ b = d`, base change along `b` and then along `a` is naturally
isomorphic to base change along `d`. This is `pullbackComp a b`, inverted and transported along
the equality `a ≫ b = d`. -/
noncomputable def pullbackCompIsoOfEq (h : a ≫ b = d) : pullback b ⋙ pullback a ≅ pullback d :=
  (pullbackComp a b).symm ≪≫ eqToIso (by subst h; rfl)

/-- For a reflexive triangle, the comparison is the inverse of `pullbackComp`. -/
@[simp]
theorem pullbackCompIsoOfEq_rfl :
    pullbackCompIsoOfEq (a := a) (b := b) rfl = (pullbackComp a b).symm := by
  simp [pullbackCompIsoOfEq]

/-- The component of the triangle comparison is `pullbackComp` inverted, followed by transport
along the triangle equality. -/
theorem pullbackCompIsoOfEq_hom_app (h : a ≫ b = d) (A : Over Z) :
    (pullbackCompIsoOfEq h).hom.app A =
      (pullbackComp a b).inv.app A ≫ eqToHom (by subst h; rfl) := by
  simp [pullbackCompIsoOfEq, eqToHom_app]

/-- The inverse component of the triangle comparison is transport along the triangle equality,
followed by `pullbackComp`. -/
theorem pullbackCompIsoOfEq_inv_app (h : a ≫ b = d) (A : Over Z) :
    (pullbackCompIsoOfEq h).inv.app A =
      eqToHom (by subst h; rfl) ≫ (pullbackComp a b).hom.app A := by
  simp [pullbackCompIsoOfEq, eqToHom_app]

/-- `pullbackCompIsoOfEq` commutes with the projections to `A`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_hom_app_left_fst (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).hom.app A).left ≫ pullback.fst A.hom d =
      pullback.fst (pullback.snd A.hom b) a ≫ pullback.fst A.hom b := by
  subst h
  simp [pullbackCompIsoOfEq, pullbackComp]

/-- `pullbackCompIsoOfEq` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_hom_app_left_snd (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).hom.app A).left ≫ pullback.snd A.hom d =
      pullback.snd (pullback.snd A.hom b) a :=
  Over.w ((pullbackCompIsoOfEq h).hom.app A)

/-- The inverse of `pullbackCompIsoOfEq` commutes with the projections to `A`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_inv_app_left_fst_fst (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫ pullback.fst (pullback.snd A.hom b) a ≫
      pullback.fst A.hom b = pullback.fst A.hom d := by
  subst h
  simp [pullbackCompIsoOfEq, pullbackComp]

/-- First projection of `(pullbackCompIsoOfEq h).inv.app A`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_inv_app_left_fst (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫ Limits.pullback.fst (Limits.pullback.snd A.hom b) a =
      Limits.pullback.map A.hom d A.hom b (𝟙 _) a (𝟙 _) (by simp) (by simp [h]) := by
  subst h; apply Limits.pullback.hom_ext <;> simp [pullbackCompIsoOfEq, pullbackComp]

/-- The inverse of `pullbackCompIsoOfEq` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_inv_app_left_snd (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫ pullback.snd (pullback.snd A.hom b) a =
      pullback.snd A.hom d :=
  Over.w ((pullbackCompIsoOfEq h).inv.app A)

/-- The identifications `pullbackCompIsoOfEq` are coherent for three composable morphisms
`x ≫ a ≫ b`: identifying base change along `x ≫ (a ≫ b)` in one step agrees with identifying it
first along `a ≫ b` and then along `(x ≫ a) ≫ b`. -/
theorem pullbackCompIsoOfEq_hom_app_eq {W : C} {x : W ⟶ X} {y : W ⟶ Y} {v : X ⟶ Z} {w : W ⟶ Z}
    [HasPullbacksAlong x] [HasPullbacksAlong y] [HasPullbacksAlong v] [HasPullbacksAlong w]
    (hxa : x ≫ a = y) (hab : a ≫ b = v) (hyb : y ≫ b = w) (hxv : x ≫ v = w) (A : Over Z) :
    (pullbackCompIsoOfEq hxv).hom.app A =
      (pullback x).map ((pullbackCompIsoOfEq hab).inv.app A) ≫
        (pullbackCompIsoOfEq hxa).hom.app ((pullback b).obj A) ≫
          (pullbackCompIsoOfEq hyb).hom.app A := by
  -- The identity is checked on the two projections out of `A ×_Z W`; the projection lemmas for
  -- the middle factor are stated for `A ×_Z Y` as an object of `Over Y`.
  have h₁ := pullbackCompIsoOfEq_hom_app_left_fst_assoc hxa ((pullback b).obj A)
    (pullback.fst A.hom b)
  have h₂ := pullbackCompIsoOfEq_hom_app_left_snd hxa ((pullback b).obj A)
  dsimp only [pullback_obj_hom] at h₁ h₂
  ext1
  apply pullback.hom_ext
  · simp [h₁]
  · simp [h₂]

/-- Associativity of `pullbackCompIsoOfEq.hom`: composing `pullbackCompIsoOfEq hfg` and
`pullbackCompIsoOfEq hfgh₂` agrees with `pullbackCompIsoOfEq hgh` and
`pullbackCompIsoOfEq hfgh₁`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_comp_hom_app {W : C} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {fg : W ⟶ Y} {gh : X ⟶ Z} {fgh : W ⟶ Z}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    [HasPullbacksAlong fg] [HasPullbacksAlong gh] [HasPullbacksAlong fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh₁ : f ≫ gh = fgh) (hfgh₂ : fg ≫ h = fgh)
    (A : Over Z) :
    (pullbackCompIsoOfEq hfg).hom.app ((pullback h).obj A) ≫
        (pullbackCompIsoOfEq hfgh₂).hom.app A =
      (pullback f).map ((pullbackCompIsoOfEq hgh).hom.app A) ≫
        (pullbackCompIsoOfEq hfgh₁).hom.app A := by
  rw [pullbackCompIsoOfEq_hom_app_eq hfg hgh hfgh₂ hfgh₁ A, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

/-- Associativity of `pullbackCompIsoOfEq.inv`: decomposing `pullback fgh` via `fg ≫ h = fgh`
and `f ≫ g = fg` agrees with decomposing via `f ≫ gh = fgh` and `g ≫ h = gh`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_comp_inv_app {W : C} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {fg : W ⟶ Y} {gh : X ⟶ Z} {fgh : W ⟶ Z}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    [HasPullbacksAlong fg] [HasPullbacksAlong gh] [HasPullbacksAlong fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh₁ : f ≫ gh = fgh) (hfgh₂ : fg ≫ h = fgh)
    (A : Over Z) :
    (pullbackCompIsoOfEq hfgh₂).inv.app A ≫
        (pullbackCompIsoOfEq hfg).inv.app ((pullback h).obj A) =
      (pullbackCompIsoOfEq hfgh₁).inv.app A ≫
        (pullback f).map ((pullbackCompIsoOfEq hgh).inv.app A) := by
  rw [← cancel_mono ((pullbackCompIsoOfEq hfg).hom.app ((pullback h).obj A) ≫
    (pullbackCompIsoOfEq hfgh₂).hom.app A), Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.assoc, pullbackCompIsoOfEq_comp_hom_app hfg hgh hfgh₁ hfgh₂ A,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]

/-- For a commuting triangle `a ≫ b = d`, morphisms which agree after base change along `b` agree
after base change along `d`. -/
theorem pullback_map_eq_map_of_comp_eq (h : a ≫ b = d) {A B : Over Z} {u v : A ⟶ B}
    (huv : (pullback b).map u = (pullback b).map v) : (pullback d).map u = (pullback d).map v := by
  rw [← cancel_epi ((pullbackCompIsoOfEq h).hom.app A), ← (pullbackCompIsoOfEq h).hom.naturality,
    ← (pullbackCompIsoOfEq h).hom.naturality]
  simp [huv]

section IdLeft

attribute [local instance] hasPullback_of_right_iso

/-- Forward component of `pullbackCompIsoOfEq (Category.id_comp g)` is `pullbackId.hom`. -/
@[simp] theorem pullbackCompIsoOfEq_id_left_hom_app (g : X ⟶ Y) [HasPullbacksAlong g]
    (A : Over Y) :
    (pullbackCompIsoOfEq (Category.id_comp g)).hom.app A =
      pullbackId.hom.app ((pullback g).obj A) := by
  apply pullback_hom_ext
  simp [pullbackId]

/-- Inverse component of `pullbackCompIsoOfEq (Category.id_comp g)` is `pullbackId.inv`. -/
@[simp] theorem pullbackCompIsoOfEq_id_left_inv_app (g : X ⟶ Y) [HasPullbacksAlong g]
    (A : Over Y) :
    (pullbackCompIsoOfEq (Category.id_comp g)).inv.app A =
      pullbackId.inv.app ((pullback g).obj A) := by
  rw [← cancel_epi ((pullbackCompIsoOfEq (Category.id_comp g)).hom.app A),
    Iso.hom_inv_id_app, pullbackCompIsoOfEq_id_left_hom_app, Iso.hom_inv_id_app]; rfl

end IdLeft

end Triangle

section Transport

/-- Transport a morphism between `Over.pullback`s along `m : A ⟶ B` using identifications
`h₁ : m ≫ g₁ = a₁` and `h₂ : m ≫ g₂ = a₂`. -/
noncomputable def pullbackTransport {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    (pullback a₁).obj Y₁ ⟶ (pullback a₂).obj Y₂ :=
  (pullbackCompIsoOfEq h₁).inv.app Y₁ ≫ (pullback m).map φ ≫
    (pullbackCompIsoOfEq h₂).hom.app Y₂

/-- Transport an isomorphism between `Over.pullback`s along `m : A ⟶ B` using identifications
`h₁ : m ≫ g₁ = a₁` and `h₂ : m ≫ g₂ = a₂`. -/
noncomputable def pullbackTransportIso {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (e : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    (pullback a₁).obj Y₁ ≅ (pullback a₂).obj Y₂ :=
  ((pullbackCompIsoOfEq h₁).app Y₁).symm ≪≫ (pullback m).mapIso e ≪≫
    (pullbackCompIsoOfEq h₂).app Y₂

/-- Unfolding equation for `pullbackTransport`. -/
theorem pullbackTransport_def {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    pullbackTransport h₁ h₂ φ =
      (pullbackCompIsoOfEq h₁).inv.app Y₁ ≫ (pullback m).map φ ≫
        (pullbackCompIsoOfEq h₂).hom.app Y₂ :=
  (rfl)

/-- The forward morphism of `pullbackTransportIso h₁ h₂ e` is `pullbackTransport h₁ h₂ e.hom`. -/
@[simp] theorem pullbackTransportIso_hom {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (e : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    (pullbackTransportIso h₁ h₂ e).hom = pullbackTransport h₁ h₂ e.hom :=
  (rfl)

/-- The inverse morphism of `pullbackTransportIso h₁ h₂ e` is `pullbackTransport h₂ h₁ e.inv`. -/
@[simp] theorem pullbackTransportIso_inv {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (e : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    (pullbackTransportIso h₁ h₂ e).inv = pullbackTransport h₂ h₁ e.inv := by
  simp [pullbackTransportIso, pullbackTransport]

/-- Transporting the identity morphism recovers the identity morphism. -/
@[simp] theorem pullbackTransport_id {A B S : C} {m : A ⟶ B} {g : B ⟶ S} {a : A ⟶ S}
    [HasPullbacksAlong m] [HasPullbacksAlong g] [HasPullbacksAlong a]
    (h : m ≫ g = a) (Y : Over S) :
    pullbackTransport h h (𝟙 ((pullback g).obj Y)) = 𝟙 ((pullback a).obj Y) := by
  simp [pullbackTransport]

/-- Transporting a composite of morphisms equals the composite of their transports. -/
theorem pullbackTransport_comp_hom {A B S₁ S₂ S₃ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {g₃ : B ⟶ S₃} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂} {a₃ : A ⟶ S₃}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂] [HasPullbacksAlong g₃]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂] [HasPullbacksAlong a₃]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂) (h₃ : m ≫ g₃ = a₃)
    {Y₁ : Over S₁} {Y₂ : Over S₂} {Y₃ : Over S₃}
    (φ₁ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂)
    (φ₂ : (pullback g₂).obj Y₂ ⟶ (pullback g₃).obj Y₃) :
    pullbackTransport h₁ h₃ (φ₁ ≫ φ₂) =
      pullbackTransport h₁ h₂ φ₁ ≫ pullbackTransport h₂ h₃ φ₂ := by
  simp [pullbackTransport]

/-- Transporting the identity isomorphism gives `Iso.refl`. -/
@[simp] theorem pullbackTransportIso_refl {A B S : C} {m : A ⟶ B} {g : B ⟶ S} {a : A ⟶ S}
    [HasPullbacksAlong m] [HasPullbacksAlong g] [HasPullbacksAlong a]
    (h : m ≫ g = a) (Y : Over S) :
    pullbackTransportIso h h (Iso.refl ((pullback g).obj Y)) = Iso.refl ((pullback a).obj Y) := by
  ext1; simp

/-- Symmetry of `pullbackTransportIso` swaps the two transport equations and inverts the
isomorphism. -/
@[simp] theorem pullbackTransportIso_symm {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (e : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    (pullbackTransportIso h₁ h₂ e).symm = pullbackTransportIso h₂ h₁ e.symm := by
  ext1; simp

/-- Transporting a composition of isomorphisms equals the composition of their transports. -/
theorem pullbackTransportIso_trans {A B S₁ S₂ S₃ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {g₃ : B ⟶ S₃} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂} {a₃ : A ⟶ S₃}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂] [HasPullbacksAlong g₃]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂] [HasPullbacksAlong a₃]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂) (h₃ : m ≫ g₃ = a₃)
    {Y₁ : Over S₁} {Y₂ : Over S₂} {Y₃ : Over S₃}
    (e₁ : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂)
    (e₂ : (pullback g₂).obj Y₂ ≅ (pullback g₃).obj Y₃) :
    pullbackTransportIso h₁ h₃ (e₁ ≪≫ e₂) =
      pullbackTransportIso h₁ h₂ e₁ ≪≫ pullbackTransportIso h₂ h₃ e₂ := by
  ext1; exact pullbackTransport_comp_hom h₁ h₂ h₃ e₁.hom e₂.hom

/-- First projection of `(pullbackTransport h₁ h₂ φ).left`. -/
@[reassoc] theorem pullbackTransport_left_fst {A B S₁ S₂ : C} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    (pullbackTransport h₁ h₂ φ).left ≫ Limits.pullback.fst Y₂.hom a₂ =
      Limits.pullback.map Y₁.hom a₁ Y₁.hom g₁ (𝟙 _) m (𝟙 _) (by simp) (by simp [h₁]) ≫
        φ.left ≫ Limits.pullback.fst Y₂.hom g₂ := by
  simp [pullbackTransport]

/-- Transporting a morphism between pullbacks along `m₂` and then along `m₁` agrees with
transporting along `m = m₁ ≫ m₂`. -/
theorem pullbackTransport_comp {A B D S₁ S₂ : C}
    {m₁ : A ⟶ B} {m₂ : B ⟶ D} {m : A ⟶ D}
    {g₁ : D ⟶ S₁} {g₂ : D ⟶ S₂} {b₁ : B ⟶ S₁} {b₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m₁] [HasPullbacksAlong m₂] [HasPullbacksAlong m]
    [HasPullbacksAlong g₁] [HasPullbacksAlong g₂]
    [HasPullbacksAlong b₁] [HasPullbacksAlong b₂]
    [HasPullbacksAlong a₁] [HasPullbacksAlong a₂]
    (hm : m₁ ≫ m₂ = m) (hm₂₁ : m₂ ≫ g₁ = b₁) (hm₂₂ : m₂ ≫ g₂ = b₂)
    (hm₁₁ : m₁ ≫ b₁ = a₁) (hm₁₂ : m₁ ≫ b₂ = a₂) (ha₁ : m ≫ g₁ = a₁) (ha₂ : m ≫ g₂ = a₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂} (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    pullbackTransport hm₁₁ hm₁₂ (pullbackTransport hm₂₁ hm₂₂ φ) =
      pullbackTransport ha₁ ha₂ φ := by
  simp only [pullbackTransport, Functor.map_comp, Category.assoc]
  rw [← pullbackCompIsoOfEq_comp_inv_app_assoc hm hm₂₁ hm₁₁ ha₁,
    ← pullbackCompIsoOfEq_comp_hom_app hm hm₂₂ hm₁₂ ha₂]
  have hnat : (pullback m₁).map ((pullback m₂).map φ) ≫
      (pullbackCompIsoOfEq hm).hom.app ((pullback g₂).obj Y₂) =
      (pullbackCompIsoOfEq hm).hom.app ((pullback g₁).obj Y₁) ≫ (pullback m).map φ :=
    (pullbackCompIsoOfEq hm).hom.naturality φ
  rw [reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

/-- Transporting a morphism between pullbacks along a morphism equal to the identity recovers the
morphism. -/
theorem pullbackTransport_of_eq_id {B S₁ S₂ : C} {m : B ⟶ B} (hm : m = 𝟙 B)
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} [HasPullbacksAlong m] [HasPullbacksAlong g₁]
    [HasPullbacksAlong g₂] (h₁ : m ≫ g₁ = g₁) (h₂ : m ≫ g₂ = g₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂} (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    pullbackTransport h₁ h₂ φ = φ := by
  subst hm
  simp only [pullbackTransport, pullbackCompIsoOfEq_id_left_inv_app,
    pullbackCompIsoOfEq_id_left_hom_app]
  rw [← pullbackId.inv.naturality_assoc φ]
  simp

/-- Mixed composition rule: transporting a `pullbackCompIsoOfEq`-conjugate along `a : A ⟶ B`
commutes `pullbackTransport` inside `pullbackCompIsoOfEq`. -/
theorem pullbackTransport_pullbackCompIsoOfEq_conj {A B D S₁ S₂ : C}
    {a : A ⟶ B} {b : B ⟶ D} {ab : A ⟶ D}
    [HasPullbacksAlong a] [HasPullbacksAlong b] [HasPullbacksAlong ab] (hab : a ≫ b = ab)
    {f₁ : D ⟶ S₁} {f₂ : D ⟶ S₂} {bf₁ : B ⟶ S₁} {bf₂ : B ⟶ S₂} {abf₁ : A ⟶ S₁} {abf₂ : A ⟶ S₂}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂]
    [HasPullbacksAlong bf₁] [HasPullbacksAlong bf₂]
    [HasPullbacksAlong abf₁] [HasPullbacksAlong abf₂]
    (hbf₁ : b ≫ f₁ = bf₁) (hbf₂ : b ≫ f₂ = bf₂) (habf₁ : a ≫ bf₁ = abf₁) (habf₂ : a ≫ bf₂ = abf₂)
    (hflat₁ : ab ≫ f₁ = abf₁) (hflat₂ : ab ≫ f₂ = abf₂)
    {Y₁ : Over S₁} {Y₂ : Over S₂}
    (φ : (pullback b).obj ((pullback f₁).obj Y₁) ⟶ (pullback b).obj ((pullback f₂).obj Y₂)) :
    pullbackTransport habf₁ habf₂
        ((pullbackCompIsoOfEq hbf₁).inv.app Y₁ ≫ φ ≫
          (pullbackCompIsoOfEq hbf₂).hom.app Y₂) =
      (pullbackCompIsoOfEq hflat₁).inv.app Y₁ ≫
        pullbackTransport hab hab φ ≫
        (pullbackCompIsoOfEq hflat₂).hom.app Y₂ := by
  simp only [pullbackTransport, Functor.map_comp, Category.assoc]
  rw [← pullbackCompIsoOfEq_comp_inv_app_assoc hab hbf₁ habf₁ hflat₁ Y₁,
    ← pullbackCompIsoOfEq_comp_hom_app hab hbf₂ habf₂ hflat₂ Y₂]

/-- Mixed composition rule: precomposing `pullbackTransport hmi h₂ φ` with a mapped morphism
`e` commutes with `pullbackTransport hmij h₂`. -/
theorem pullbackTransport_comp_map_inv {A B D E S₂ : C}
    {m : A ⟶ B} {i₁ : B ⟶ D} {g₁ : A ⟶ D} {j₁ : D ⟶ E} {ij₁ : B ⟶ E} {gj₁ : A ⟶ E}
    {g₂ : B ⟶ S₂} {a₂ : A ⟶ S₂}
    [HasPullbacksAlong m] [HasPullbacksAlong i₁] [HasPullbacksAlong g₁] [HasPullbacksAlong j₁]
    [HasPullbacksAlong ij₁] [HasPullbacksAlong gj₁] [HasPullbacksAlong g₂] [HasPullbacksAlong a₂]
    (hmi : m ≫ i₁ = g₁) (hij : i₁ ≫ j₁ = ij₁) (hmij : m ≫ ij₁ = gj₁) (hgj : g₁ ≫ j₁ = gj₁)
    (h₂ : m ≫ g₂ = a₂) {Y₁ : Over E} {Y₂ : Over S₂}
    {V : Over D} (e : (pullback j₁).obj Y₁ ⟶ V)
    (φ : (pullback i₁).obj V ⟶ (pullback g₂).obj Y₂) :
    (pullbackCompIsoOfEq hgj).inv.app Y₁ ≫ (pullback g₁).map e ≫
        pullbackTransport hmi h₂ φ =
      pullbackTransport hmij h₂
        ((pullbackCompIsoOfEq hij).inv.app Y₁ ≫ (pullback i₁).map e ≫ φ) := by
  simp only [pullbackTransport]
  rw [reassoc_of% ((pullbackCompIsoOfEq hmi).inv.naturality e),
    pullbackCompIsoOfEq_comp_inv_app_assoc hmi hij hmij hgj Y₁,
    ← (pullback m).map_comp_assoc, ← (pullback m).map_comp_assoc, Category.assoc]

end Transport

section SymmetryBridge

/-- Conjugating a morphism `pullback f A.hom ⟶ pullback f B.hom` commuting with the first
projections by `pullbackSymmetry` yields a morphism commuting with the second projections, i.e. a
morphism in `Over X`. -/
theorem pullbackSymmetry_conj_snd {X Y : C} (f : X ⟶ Y)
    {A B : Over Y} [HasPullback A.hom f] [HasPullback B.hom f]
    [HasPullback f A.hom] [HasPullback f B.hom]
    (b : Limits.pullback f A.hom ⟶ Limits.pullback f B.hom)
    (hb : b ≫ Limits.pullback.fst f B.hom = Limits.pullback.fst f A.hom) :
    ((Limits.pullbackSymmetry A.hom f).hom ≫ b ≫ (Limits.pullbackSymmetry f B.hom).hom) ≫
        Limits.pullback.snd B.hom f =
      Limits.pullback.snd A.hom f := by
  simp [hb]

/-- Construct a morphism `(Over.pullback f).obj A ⟶ (Over.pullback f).obj B` in `Over X` from a
morphism `b : pullback f A.hom ⟶ pullback f B.hom` commuting with the first projections. -/
noncomputable def pullbackHomOfFstEq {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (b : Limits.pullback f A.hom ⟶ Limits.pullback f B.hom)
    (hb : b ≫ Limits.pullback.fst f B.hom = Limits.pullback.fst f A.hom) :
    (pullback f).obj A ⟶ (pullback f).obj B :=
  Over.homMk ((Limits.pullbackSymmetry A.hom f).hom ≫ b ≫
    (Limits.pullbackSymmetry f B.hom).hom) (pullbackSymmetry_conj_snd f b hb)

/-- Underlying morphism of `pullbackHomOfFstEq`. -/
@[simp] theorem pullbackHomOfFstEq_left {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (b : Limits.pullback f A.hom ⟶ Limits.pullback f B.hom)
    (hb : b ≫ Limits.pullback.fst f B.hom = Limits.pullback.fst f A.hom) :
    (pullbackHomOfFstEq f b hb).left =
      (Limits.pullbackSymmetry A.hom f).hom ≫ b ≫ (Limits.pullbackSymmetry f B.hom).hom := by
  simp [pullbackHomOfFstEq]

/-- First projection of `(pullbackHomOfFstEq f b hb).left`. -/
@[reassoc] theorem pullbackHomOfFstEq_left_fst {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (b : Limits.pullback f A.hom ⟶ Limits.pullback f B.hom)
    (hb : b ≫ Limits.pullback.fst f B.hom = Limits.pullback.fst f A.hom) :
    (pullbackHomOfFstEq f b hb).left ≫ Limits.pullback.fst B.hom f =
      (Limits.pullbackSymmetry A.hom f).hom ≫ b ≫ Limits.pullback.snd f B.hom := by
  simp

/-- Conjugate a morphism `(Over.pullback f).obj A ⟶ (Over.pullback f).obj B` by
`Limits.pullbackSymmetry` to obtain a morphism `pullback f A.hom ⟶ pullback f B.hom` over `X`. -/
noncomputable def pullbackLeftSymm {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (g : (pullback f).obj A ⟶ (pullback f).obj B) :
    Limits.pullback f A.hom ⟶ Limits.pullback f B.hom :=
  (Limits.pullbackSymmetry f A.hom).hom ≫ g.left ≫ (Limits.pullbackSymmetry B.hom f).hom

/-- First projection of `pullbackLeftSymm f g`. -/
@[reassoc (attr := simp)] theorem pullbackLeftSymm_fst {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (g : (pullback f).obj A ⟶ (pullback f).obj B) :
    pullbackLeftSymm f g ≫ Limits.pullback.fst f B.hom = Limits.pullback.fst f A.hom := by
  have hw : g.left ≫ Limits.pullback.snd B.hom f = Limits.pullback.snd A.hom f := Over.w g
  simp [pullbackLeftSymm, hw]

/-- Second projection of `pullbackLeftSymm f g`. -/
@[reassoc (attr := simp)] theorem pullbackLeftSymm_snd {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (g : (pullback f).obj A ⟶ (pullback f).obj B) :
    pullbackLeftSymm f g ≫ Limits.pullback.snd f B.hom =
      (Limits.pullbackSymmetry f A.hom).hom ≫ g.left ≫ Limits.pullback.fst B.hom f := by
  simp [pullbackLeftSymm]

/-- Conjugating `pullbackLeftSymm f g` back via `pullbackHomOfFstEq` recovers `g`. -/
@[simp] theorem pullbackHomOfFstEq_pullbackLeftSymm {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (g : (pullback f).obj A ⟶ (pullback f).obj B) :
    pullbackHomOfFstEq f (pullbackLeftSymm f g) (pullbackLeftSymm_fst f g) = g := by
  ext1; simp [pullbackLeftSymm]

/-- Conjugating `pullbackHomOfFstEq f b hb` via `pullbackLeftSymm` recovers `b`. -/
@[simp] theorem pullbackLeftSymm_pullbackHomOfFstEq {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (b : Limits.pullback f A.hom ⟶ Limits.pullback f B.hom)
    (hb : b ≫ Limits.pullback.fst f B.hom = Limits.pullback.fst f A.hom) :
    pullbackLeftSymm f (pullbackHomOfFstEq f b hb) = b := by
  simp [pullbackLeftSymm]

/-- Underlying isomorphism `pullback f A.hom ≅ pullback f B.hom` induced by an isomorphism
`e : (pullback f).obj A ≅ (pullback f).obj B`. -/
noncomputable def pullbackLeftSymmIso {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (e : (pullback f).obj A ≅ (pullback f).obj B) :
    Limits.pullback f A.hom ≅ Limits.pullback f B.hom :=
  Limits.pullbackSymmetry f A.hom ≪≫ (Over.forget X).mapIso e ≪≫
    Limits.pullbackSymmetry B.hom f

/-- The forward morphism of `pullbackLeftSymmIso f e` is `pullbackLeftSymm f e.hom`. -/
@[simp] theorem pullbackLeftSymmIso_hom {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (e : (pullback f).obj A ≅ (pullback f).obj B) :
    (pullbackLeftSymmIso f e).hom = pullbackLeftSymm f e.hom := by
  simp [pullbackLeftSymmIso, pullbackLeftSymm]

/-- The inverse morphism of `pullbackLeftSymmIso f e` is `pullbackLeftSymm f e.inv`. -/
@[simp] theorem pullbackLeftSymmIso_inv {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} [HasPullback f A.hom] [HasPullback f B.hom]
    (e : (pullback f).obj A ≅ (pullback f).obj B) :
    (pullbackLeftSymmIso f e).inv = pullbackLeftSymm f e.inv := by
  have h₁ : (Limits.pullbackSymmetry B.hom f).inv = (Limits.pullbackSymmetry f B.hom).hom :=
    congrArg Iso.hom (Limits.pullbackSymmetry_symm B.hom f)
  have h₂ : (Limits.pullbackSymmetry f A.hom).inv = (Limits.pullbackSymmetry A.hom f).hom :=
    congrArg Iso.hom (Limits.pullbackSymmetry_symm f A.hom)
  simp [pullbackLeftSymmIso, pullbackLeftSymm, h₁, h₂]

/-- Transporting `pullbackHomOfFstEq g b hb` along `h : m ≫ g = mg` yields on underlying objects
the `pullbackRightPullbackFstIsoOfEq`-conjugate of the raw pullback map of `b`, conjugated by
`pullbackSymmetry`. -/
theorem pullbackCompIsoOfEq_conj_left_eq_pullbackMap
    {A B S : C} {m : A ⟶ B} {g : B ⟶ S} {mg : A ⟶ S}
    [HasPullbacksAlong m] [HasPullbacksAlong g] [HasPullbacksAlong mg]
    (h : m ≫ g = mg) {Y₁ Y₂ : Over S}
    [HasPullback g Y₁.hom] [HasPullback g Y₂.hom]
    [HasPullback m (Limits.pullback.fst g Y₁.hom)]
    [HasPullback m (Limits.pullback.fst g Y₂.hom)]
    [HasPullback mg Y₁.hom] [HasPullback mg Y₂.hom]
    (b : Limits.pullback g Y₁.hom ⟶ Limits.pullback g Y₂.hom)
    (hb : b ≫ Limits.pullback.fst g Y₂.hom = Limits.pullback.fst g Y₁.hom) :
    (pullbackTransport h h (pullbackHomOfFstEq g b hb)).left =
      (Limits.pullbackSymmetry Y₁.hom mg).hom ≫
        (Limits.pullbackRightPullbackFstIsoOfEq m g mg h Y₁.hom).inv ≫
        Limits.pullback.map m (Limits.pullback.fst g Y₁.hom)
          m (Limits.pullback.fst g Y₂.hom) (𝟙 A) b (𝟙 B) (by simp) (by simp [hb]) ≫
        (Limits.pullbackRightPullbackFstIsoOfEq m g mg h Y₂.hom).hom ≫
        (Limits.pullbackSymmetry mg Y₂.hom).hom := by
  apply Limits.pullback.hom_ext
  · have hLHS : (pullbackTransport h h (pullbackHomOfFstEq g b hb)).left ≫
        Limits.pullback.fst Y₂.hom mg =
        (Limits.pullbackSymmetry Y₁.hom mg).hom ≫
          Limits.pullback.map mg Y₁.hom g Y₁.hom m (𝟙 _) (𝟙 _) (by simp [h]) (by simp) ≫
          b ≫ Limits.pullback.snd g Y₂.hom := by
      rw [pullbackTransport_left_fst, pullbackHomOfFstEq_left_fst,
        Limits.pullback_map_pullbackSymmetry_assoc]
    have hRHS : ((Limits.pullbackSymmetry Y₁.hom mg).hom ≫
          (Limits.pullbackRightPullbackFstIsoOfEq m g mg h Y₁.hom).inv ≫
          Limits.pullback.map m (Limits.pullback.fst g Y₁.hom)
            m (Limits.pullback.fst g Y₂.hom) (𝟙 A) b (𝟙 B) (by simp) (by simp [hb]) ≫
          (Limits.pullbackRightPullbackFstIsoOfEq m g mg h Y₂.hom).hom ≫
          (Limits.pullbackSymmetry mg Y₂.hom).hom) ≫
        Limits.pullback.fst Y₂.hom mg =
        (Limits.pullbackSymmetry Y₁.hom mg).hom ≫
          Limits.pullback.map mg Y₁.hom g Y₁.hom m (𝟙 _) (𝟙 _) (by simp [h]) (by simp) ≫
          b ≫ Limits.pullback.snd g Y₂.hom := by
      simp
    exact hLHS.trans hRHS.symm
  · have hw := Over.w (pullbackTransport h h (pullbackHomOfFstEq g b hb))
    refine hw.trans ?_
    simp

/-- Transporting `pullbackHomOfFstEq g b hb` along `h : m ≫ g = mg` recovers
`pullbackHomOfFstEq mg a ha` whenever `b` and `a` commute with the pullback transition map. -/
theorem pullbackCompIsoOfEq_conj_hom_of_fstEq
    {A B S : C} {m : A ⟶ B} {g : B ⟶ S} {mg : A ⟶ S}
    [HasPullbacksAlong m] [HasPullbacksAlong g] [HasPullbacksAlong mg]
    (h : m ≫ g = mg) {Y₁ Y₂ : Over S}
    [HasPullback g Y₁.hom] [HasPullback g Y₂.hom]
    [HasPullback m (Limits.pullback.fst g Y₁.hom)]
    [HasPullback m (Limits.pullback.fst g Y₂.hom)]
    [HasPullback mg Y₁.hom] [HasPullback mg Y₂.hom]
    {b : Limits.pullback g Y₁.hom ⟶ Limits.pullback g Y₂.hom}
    (hb : b ≫ Limits.pullback.fst g Y₂.hom = Limits.pullback.fst g Y₁.hom)
    {a : Limits.pullback mg Y₁.hom ⟶ Limits.pullback mg Y₂.hom}
    (ha : a ≫ Limits.pullback.fst mg Y₂.hom = Limits.pullback.fst mg Y₁.hom)
    (hcomp : Limits.pullback.map mg Y₁.hom g Y₁.hom m (𝟙 _) (𝟙 _) (by simp [h]) (by simp) ≫ b =
      a ≫ Limits.pullback.map mg Y₂.hom g Y₂.hom m (𝟙 _) (𝟙 _) (by simp [h]) (by simp)) :
    pullbackTransport h h (pullbackHomOfFstEq g b hb) =
      pullbackHomOfFstEq mg a ha := by
  ext1
  rw [pullbackCompIsoOfEq_conj_left_eq_pullbackMap h b hb,
    Limits.pullbackRightPullbackFstIsoOfEq_inv_map_hom_eq_assoc m g mg h hb ha hcomp]
  simp

/-- Projection cancellation for an isomorphism `e : (Over.pullback j).obj V' ≅ V` transported
along `pullbackCompIsoOfEq h`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_inv_map_hom_fst_inv_fst
    {Inf U UW : C} {f : Inf ⟶ U} {j : U ⟶ UW} {ij : Inf ⟶ UW}
    [HasPullbacksAlong f] [HasPullbacksAlong j] [HasPullbacksAlong ij]
    (h : f ≫ j = ij) {V' : Over UW} {V : Over U} (e : (pullback j).obj V' ≅ V) :
    ((pullbackCompIsoOfEq h).inv.app V' ≫ (pullback f).map e.hom).left ≫
        Limits.pullback.fst V.hom f ≫ e.inv.left ≫ Limits.pullback.fst V'.hom j =
      Limits.pullback.fst V'.hom ij := by
  rw [Over.comp_left, Category.assoc, pullback_map_left_fst_assoc]
  have hfst : e.hom.left ≫ e.inv.left ≫ Limits.pullback.fst V'.hom j =
      Limits.pullback.fst V'.hom j := by simp
  rw [hfst]
  simp only [Over.pullback_obj_hom, pullbackCompIsoOfEq_inv_app_left_fst_assoc,
    Limits.pullback.lift_fst, Category.comp_id]

end SymmetryBridge

/-- Transporting `((Over.pullback g).map φ).left` along identifications `Y₁ = Over.mk p₁` and
`Y₂ = Over.mk p₂` yields the canonical `Limits.pullback.lift` on the underlying pullbacks. -/
theorem pullback_map_left_of_eq_mk {S T : C} (g : T ⟶ S) [HasPullbacksAlong g]
    {Y₁ Y₂ : Over S} (φ : Y₁ ⟶ Y₂) {X₁ X₂ : C} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S}
    (h₁ : Y₁ = Over.mk p₁) (h₂ : Y₂ = Over.mk p₂) :
    eqToHom (by subst h₁; rfl) ≫ ((pullback g).map φ).left ≫ eqToHom (by subst h₂; rfl) =
      Limits.pullback.lift (f := p₂) (g := g) (Limits.pullback.fst p₁ g ≫
        eqToHom (congrArg Over.left h₁.symm) ≫ φ.left ≫ eqToHom (congrArg Over.left h₂))
        (Limits.pullback.snd p₁ g) (by
          have hw := Over.w φ; subst h₁ h₂
          simp only [Over.mk_left, Over.mk_hom] at hw; simp [hw, Limits.pullback.condition]) := by
  subst h₁ h₂; simp

/-- Two arrows agree after base change precisely when their underlying arrows agree after
precomposition with the projection from the base-changed source. -/
theorem pullback_map_eq_map_iff {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} (u v : A ⟶ B) :
    (pullback f).map u = (pullback f).map v ↔
      pullback.fst A.hom f ≫ u.left = pullback.fst A.hom f ≫ v.left := by
  constructor
  · intro h
    simpa using congrArg (fun w ↦ w.left ≫ pullback.fst B.hom f) h
  · intro h
    ext1
    apply pullback.hom_ext
    · simpa using h
    · simp

/-- Base change `Over.pullback f : Over Y ⥤ Over X` preserves epimorphisms whenever `Over.forget Y`
does and epimorphisms in `C` are stable under base change. -/
instance preservesEpimorphisms_pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [(forget Y).PreservesEpimorphisms]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] :
    (pullback f).PreservesEpimorphisms where
  preserves k _ :=
    have : Epi k.left := (forget Y).map_epi k
    (forget X).epi_of_epi_map <|
      MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
        (isPullback_pullback_map_left f k).flip ‹_›

/-- For a monomorphism `g`, the unit `A ⟶ g^*(g_! A)` of `Over.map g ⊣ Over.pullback g` is an
isomorphism: the square with sides `𝟙 A`, `A ⟶ X`, `A ⟶ Y` and `g` is a pullback. -/
instance isIso_mapPullbackAdj_unit_app {X Y : C} (g : X ⟶ Y) [HasPullbacksAlong g] [Mono g]
    (A : Over X) : IsIso ((mapPullbackAdj g).unit.app A) := by
  have h : IsPullback (𝟙 A.left) A.hom (A.hom ≫ g) g :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hl : ((mapPullbackAdj g).unit.app A).left = h.isoPullback.hom := by
    apply pullback.hom_ext <;> simp
  have : IsIso ((forget X).map ((mapPullbackAdj g).unit.app A)) := by
    rw [forget_map, hl]
    infer_instance
  exact isIso_of_reflects_iso _ (forget X)

section HasBinaryProducts

variable [HasBinaryProducts C]

/-- `Over.star X : C ⥤ Over X` is faithful when every second projection `X ⨯ Y ⟶ Y` is an
epimorphism. -/
instance faithful_star (X : C) [∀ Y : C, Epi (prod.snd : X ⨯ Y ⟶ Y)] : (star X).Faithful := by
  have (Y : C) : Epi ((forgetAdjStar X).counit.app Y) := by
    rw [forgetAdjStar_counit_app]
    exact inferInstanceAs (Epi (prod.snd : X ⨯ Y ⟶ Y))
  exact (forgetAdjStar X).faithful_R_of_epi_counit_app

/-- A family of base-change functors `Over.star (U i) : C ⥤ Over (U i)` is jointly faithful when
the second projections `U i ⨯ Z ⟶ Z` are jointly epimorphic for every `Z : C`. -/
theorem jointlyFaithful_star {I : Type*} (U : I → C)
    (hU : ∀ {Z W : C} (a b : Z ⟶ W),
      (∀ i, (prod.snd : U i ⨯ Z ⟶ Z) ≫ a = prod.snd ≫ b) → a = b) :
    JointlyFaithful (fun i ↦ star (U i)) where
  map_injective {Z W a b} h := hU a b fun i ↦ by
    have hi := ((forgetAdjStar (U i)).counit.naturality a).symm.trans <|
      (congrArg (fun k ↦ (forget (U i)).map k ≫ (forgetAdjStar (U i)).counit.app W) (h i)).trans
        ((forgetAdjStar (U i)).counit.naturality b)
    rwa [Functor.id_map, Functor.id_map, forgetAdjStar_counit_app] at hi

/-- `Over.star X : C ⥤ Over X` preserves epimorphisms whenever `X ⨯ -` does (in particular when
epimorphisms in `C` are stable under base change). -/
instance preservesEpimorphisms_star (X : C) [(prod.functor.obj X).PreservesEpimorphisms] :
    (star X).PreservesEpimorphisms where
  preserves f _ := (forget X).epi_of_epi_map ((prod.functor.obj X).map_epi f)

end HasBinaryProducts

end Over

namespace Limits.Cone

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : Type*} [Category* J] {D : J ⥤ C}

section LiftsAlong

variable (c : Cone D)

/-- The morphism `u` between base changes to the cone point lifts to a morphism between the base
changes to `D.obj k` along `g : k ⟶ i`: the base change of the lift to the cone point is `u`, up to
the comparison isomorphisms `Over.pullbackCompIsoOfEq`. -/
def LiftsAlong {i : J} {A B : Over (D.obj i)}
    (u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B) {k : J}
    (g : k ⟶ i) : Prop :=
  ∃ v : (Over.pullback (D.map g)).obj A ⟶ (Over.pullback (D.map g)).obj B,
    (Over.pullback (c.π.app k)).map v ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app B =
      (Over.pullbackCompIsoOfEq (c.w g)).hom.app A ≫ u

variable {c}

/-- A lift is a morphism whose base change agrees with the given arrow under the canonical
comparison isomorphisms. -/
theorem liftsAlong_iff {i : J} {A B : Over (D.obj i)}
    (u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B) {k : J}
    (g : k ⟶ i) : c.LiftsAlong u g ↔
      ∃ v : (Over.pullback (D.map g)).obj A ⟶ (Over.pullback (D.map g)).obj B,
        (Over.pullback (c.π.app k)).map v ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app B =
          (Over.pullbackCompIsoOfEq (c.w g)).hom.app A ≫ u := Iff.rfl

/-- Identity morphisms lift along every morphism to `i`. -/
@[simp]
theorem liftsAlong_id {i : J} (A : Over (D.obj i)) {k : J} (g : k ⟶ i) :
    c.LiftsAlong (𝟙 ((Over.pullback (c.π.app i)).obj A)) g :=
  ⟨𝟙 _, by simp⟩

/-- Lifts of two composable morphisms along the same morphism to `i` compose to a lift of their
composite. -/
theorem liftsAlong_comp {i : J} {A B E : Over (D.obj i)}
    {u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B}
    {u' : (Over.pullback (c.π.app i)).obj B ⟶ (Over.pullback (c.π.app i)).obj E} {k : J}
    {g : k ⟶ i} (hu : c.LiftsAlong u g) (hu' : c.LiftsAlong u' g) :
    c.LiftsAlong (u ≫ u') g := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hu'
  exact ⟨v ≫ v', by simp [hv', reassoc_of% hv]⟩

/-- A lift along `g` base changes to a lift along `h ≫ g`. -/
theorem LiftsAlong.precomp {i : J} {A B : Over (D.obj i)}
    {u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B} {k l : J}
    {g : k ⟶ i} (h : l ⟶ k) (hg : c.LiftsAlong u g) : c.LiftsAlong u (h ≫ g) := by
  obtain ⟨v, hv⟩ := hg
  let C := Over.pullbackCompIsoOfEq (D.map_comp h g).symm
  refine ⟨C.inv.app A ≫ (Over.pullback (D.map h)).map v ≫ C.hom.app B, ?_⟩
  have hcoh (Z : Over (D.obj i)) := Over.pullbackCompIsoOfEq_hom_app_eq (c.w h)
    (D.map_comp h g).symm (c.w g) (c.w (h ≫ g)) Z
  have hnat := (Over.pullbackCompIsoOfEq (c.w h)).hom.naturality v
  dsimp only [Functor.comp_map] at hnat
  rw [hcoh, hcoh]
  simp [C, reassoc_of% hnat, hv]

end LiftsAlong

end Limits.Cone

namespace IsPullback

variable {C : Type u} [Category.{v} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z} [HasPullbacksAlong fst] [HasPullbacksAlong g]

/-- The Beck–Chevalley isomorphism of a pullback square `fst ≫ f = snd ≫ g`: base change along
`fst` followed by composition with `snd` is composition with `f` followed by base change along
`g`. On an object `A ⟶ X` it identifies `A ×_X P`, regarded over `Y` through `snd`, with
`A ×_Z Y`. -/
noncomputable def overPullbackCompMapIso (sq : IsPullback fst snd f g) :
    Over.pullback fst ⋙ Over.map snd ≅ Over.map f ⋙ Over.pullback g :=
  NatIso.ofComponents
    (fun A ↦ Over.isoMk ((IsPullback.of_hasPullback A.hom fst).paste_vert sq).isoPullback
      (by simp))
    (fun u ↦ by ext1; apply pullback.hom_ext <;> simp)

@[reassoc (attr := simp)]
theorem overPullbackCompMapIso_hom_app_left_fst (sq : IsPullback fst snd f g) (A : Over X) :
    (sq.overPullbackCompMapIso.hom.app A).left ≫ pullback.fst (A.hom ≫ f) g =
      pullback.fst A.hom fst := by
  simp [overPullbackCompMapIso]

@[reassoc (attr := simp)]
theorem overPullbackCompMapIso_hom_app_left_snd (sq : IsPullback fst snd f g) (A : Over X) :
    (sq.overPullbackCompMapIso.hom.app A).left ≫ pullback.snd (A.hom ≫ f) g =
      pullback.snd A.hom fst ≫ snd := by
  simp [overPullbackCompMapIso]

end IsPullback

end CategoryTheory
