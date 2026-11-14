/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Localization of the small étale site

Let `S` be a scheme and `U` an object of its small étale site, that is, an étale morphism
`U.left ⟶ S`. The localized site `Over U`, with the topology `(smallEtaleTopology S).over U`
induced from `S`, is the small étale site of the scheme `U.left`
(`AlgebraicGeometry.Scheme.Etale.overEquiv`). An object `V ⟶ U` of `Over U` is a morphism between
étale `S`-schemes, so the underlying morphism of schemes `V.left.left ⟶ U.left` is étale and is an
object of `U.left.Etale`. Conversely, an étale `U.left`-scheme `W` is étale over `S` through the
composite `W.left ⟶ U.left ⟶ S`. The equivalence identifies the two topologies, because on both
sides a sieve covers exactly when the images of its members cover the underlying scheme
(`AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`,
`AlgebraicGeometry.Scheme.mem_over_smallEtaleTopology_iff`). Hence sheaves on the two sites agree
(`AlgebraicGeometry.Scheme.Etale.overSheafEquiv`).

Composing with Mathlib's restriction `GrothendieckTopology.overPullback` of sheaves to a localized
site gives the restriction of an étale sheaf on `S` to the small étale site of `U.left`
(`AlgebraicGeometry.Scheme.Etale.sheafRestrict`), whose sections over an étale `U.left`-scheme `W`
are the sections over `W`, regarded as an étale `S`-scheme. This is how étale-local statements
about sheaves on `S`, such as local constancy or local isomorphy, are expressed on the small étale
sites of the members of an étale covering. For instance, a morphism of étale sheaves on `S` is an
isomorphism as soon as its restrictions to the members of an étale covering are isomorphisms
(`AlgebraicGeometry.Scheme.Etale.isIso_iff_forall_isIso_sheafRestrict_map`). A family of étale
`S`-schemes covers the terminal object of the small étale site exactly when the images of their
structure morphisms cover `S` (`AlgebraicGeometry.Scheme.coversTop_smallEtaleTopology_iff`).

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.overEquiv U : Over U ≌ U.left.Etale`: the localization of the
  small étale site of `S` at `U` is the small étale site of `U.left`.
* `AlgebraicGeometry.Scheme.Etale.overSheafEquiv U A`: the corresponding equivalence of categories
  of sheaves with values in `A`.
* `AlgebraicGeometry.Scheme.Etale.sheafRestrict U A`: restriction of étale sheaves on `S` to the
  small étale site of `U.left`.

## Main results

* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`: a sieve on an object `X` of the small
  étale site covers if and only if every point of `X.left` lifts along one of its members.
* `AlgebraicGeometry.Scheme.coversTop_smallEtaleTopology_iff`: a family of étale `S`-schemes
  covers the small étale site if and only if their images cover `S`.
* `AlgebraicGeometry.Scheme.Etale.isIso_iff_forall_isIso_sheafRestrict_map`: a morphism of étale
  sheaves is an isomorphism if and only if its restrictions to the members of an étale covering
  are isomorphisms.

## References

* The Stacks Project, Chapter *Sites and Sheaves*, Section *Localization*, for localized sites and
  the restriction of sheaves to them.
* The Stacks Project, Chapter *Étale Cohomology*, Section *The étale site*, for the small étale
  site of a scheme.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- A sieve on an object `X` of the small étale site of `S` is a covering sieve if and only if
every point of `X.left` is the image of a point under one of the morphisms of the sieve. -/
theorem mem_smallEtaleTopology_iff {X : S.Etale} (R : Sieve X) :
    R ∈ smallEtaleTopology S X ↔
      ∀ x : X.left, ∃ (Y : S.Etale) (f : Y ⟶ X) (y : Y.left), R f ∧ f.left y = x := by
  obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
  simp only [Set.mem_iUnion, Set.mem_range, Sieve.mem_ofArrows_iff]
  refine forall_congr' fun x ↦ ⟨fun ⟨i, y, hy⟩ ↦ ⟨_, f i, y, ⟨i, 𝟙 _, by simp⟩, hy⟩, ?_⟩
  rintro ⟨Z, _, z, ⟨i, a, rfl⟩, rfl⟩
  -- Composition in `S.Etale` is composition of the underlying morphisms of schemes.
  exact ⟨i, a.left z, (Scheme.Hom.comp_apply a.left (f i).left z).symm⟩

/-- A sieve on an object `V` of the localization at `U` of the small étale site of `S` is a
covering sieve if and only if every point of the underlying scheme `V.left.left` is the image of a
point under one of the morphisms of the sieve. -/
theorem mem_over_smallEtaleTopology_iff {U : S.Etale} {V : Over U} (R : Sieve V) :
    R ∈ (smallEtaleTopology S).over U V ↔
      ∀ x : V.left.left,
        ∃ (W : Over U) (f : W ⟶ V) (w : W.left.left), R f ∧ f.left.left w = x := by
  rw [GrothendieckTopology.mem_over_iff, mem_smallEtaleTopology_iff]
  refine forall_congr' fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨Y, f, y, hf, hy⟩
    rw [Sieve.overEquiv_iff] at hf
    exact ⟨_, _, y, hf, hy⟩
  · rintro ⟨W, f, w, hf, hw⟩
    refine ⟨W.left, f.left, w, ?_, hw⟩
    rw [Sieve.overEquiv_apply]
    exact Sieve.image_mem_functorPushforward _ _ hf

/-- A family of étale `S`-schemes covers the small étale site of `S`, in the sense that it
generates a covering sieve of every object, if and only if every point of `S` lies in the image of
one of them. -/
theorem coversTop_smallEtaleTopology_iff {ι : Type*} (U : ι → S.Etale) :
    (smallEtaleTopology S).CoversTop U ↔ ∀ s : S, ∃ i, ∃ u : (U i).left, (U i).hom u = s := by
  have hT : IsTerminal (Etale.mk (𝟙 S)) :=
    IsTerminal.isTerminalOfObj (Etale.forget S) _ Over.mkIdTerminal
  -- The morphism from an étale `S`-scheme to the terminal object is its structure morphism.
  have h (i : ι) : (hT.from (U i)).left = (U i).hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w _)
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT,
    ← Sieve.ofArrows_eq_ofObjects hT U (fun i ↦ hT.from (U i)),
    ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
  simp only [h, Set.mem_iUnion, Set.mem_range]
  -- The underlying scheme of the terminal object `Etale.mk (𝟙 S)` is `S` itself.
  exact Iff.rfl

variable (U : S.Etale)

/-- The functor from the localization at `U` of the small étale site of `S` to the small étale
site of `U.left`, sending `V ⟶ U` to the underlying étale morphism of schemes. -/
@[expose, simps]
noncomputable def Etale.overForward : Over U ⥤ U.left.Etale where
  obj V := Etale.mk V.hom.left
  map {V W} f := MorphismProperty.Over.homMk f.left.left (congrArg (·.left) (Over.w f))

/-- The functor from the small étale site of `U.left` to the localization at `U` of the small
étale site of `S`, regarding an étale `U.left`-scheme as an étale `S`-scheme over `U`. -/
@[expose, simps]
noncomputable def Etale.overBackward : U.left.Etale ⥤ Over U where
  obj W := Over.mk (Y := Etale.mk (W.hom ≫ U.hom)) (MorphismProperty.Over.homMk W.hom)
  map {V W} f := Over.homMk (MorphismProperty.Over.homMk f.left
    (MorphismProperty.Over.w_assoc f U.hom))
    (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f))

/-- The localization at `U` of the small étale site of `S` is equivalent to the small étale site
of `U.left`. -/
@[expose]
noncomputable def Etale.overEquiv : Over U ≌ U.left.Etale where
  functor := Etale.overForward U
  inverse := Etale.overBackward U
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk (MorphismProperty.Over.isoMk
      (Iso.refl V.left.left) ((Category.id_comp _).trans (MorphismProperty.Over.w V.hom)))
      (MorphismProperty.Over.Hom.ext (Category.id_comp _)))
    (fun _ ↦ Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
  counitIso := NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl W.left)
      (Category.id_comp _))
    (fun _ ↦ MorphismProperty.Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  functor_unitIso_comp _ := MorphismProperty.Over.Hom.ext (Category.id_comp _)

@[simp]
theorem Etale.overEquiv_functor : (Etale.overEquiv U).functor = Etale.overForward U :=
  (rfl)

@[simp]
theorem Etale.overEquiv_inverse : (Etale.overEquiv U).inverse = Etale.overBackward U :=
  (rfl)

@[simp]
theorem Etale.overEquiv_unit_app_left_left (V : Over U) :
    ((Etale.overEquiv U).unit.app V).left.left = 𝟙 V.left.left :=
  (rfl)

@[simp]
theorem Etale.overEquiv_unitInv_app_left_left (V : Over U) :
    ((Etale.overEquiv U).unitInv.app V).left.left = 𝟙 V.left.left :=
  (rfl)

@[simp]
theorem Etale.overEquiv_counit_app_left (W : U.left.Etale) :
    ((Etale.overEquiv U).counit.app W).left = 𝟙 W.left :=
  (rfl)

@[simp]
theorem Etale.overEquiv_counitInv_app_left (W : U.left.Etale) :
    ((Etale.overEquiv U).counitInv.app W).left = 𝟙 W.left :=
  (rfl)

instance : (Etale.overEquiv U).functor.IsCocontinuous ((smallEtaleTopology S).over U)
    (smallEtaleTopology U.left) where
  cover_lift {V} R hR := by
    rw [mem_smallEtaleTopology_iff] at hR
    rw [mem_over_smallEtaleTopology_iff]
    intro x
    obtain ⟨W, f, w, hf, rfl⟩ := hR x
    -- The lift is `f` on underlying schemes, since the unit of `Etale.overEquiv` is the identity.
    refine ⟨_, (Etale.overEquiv U).inverse.map f ≫ (Etale.overEquiv U).unitInv.app V, w, ?_, rfl⟩
    -- The image of the lift of `f` is `f`, precomposed with the counit of the equivalence.
    have : (Etale.overEquiv U).functor.map
        ((Etale.overEquiv U).inverse.map f ≫ (Etale.overEquiv U).unitInv.app V) =
          (Etale.overEquiv U).counit.app W ≫ f := by
      simp
    rw [Sieve.functorPullback_apply, Presieve.functorPullback_mem, this]
    exact R.downward_closed hf _

instance : (Etale.overEquiv U).inverse.IsCocontinuous (smallEtaleTopology U.left)
    ((smallEtaleTopology S).over U) where
  cover_lift {W} R hR := by
    rw [mem_over_smallEtaleTopology_iff] at hR
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨V, f, v, hf, rfl⟩ := hR x
    -- The lift is `f` on underlying schemes, since the counit of `Etale.overEquiv` is the identity.
    refine ⟨_, (Etale.overEquiv U).functor.map f ≫ (Etale.overEquiv U).counit.app W, v, ?_, rfl⟩
    -- The image of the lift of `f` is `f`, precomposed with the inverse of the unit of the
    -- equivalence.
    have : (Etale.overEquiv U).inverse.map
        ((Etale.overEquiv U).functor.map f ≫ (Etale.overEquiv U).counit.app W) =
          (Etale.overEquiv U).unitInv.app V ≫ f := by
      simp
    rw [Sieve.functorPullback_apply, Presieve.functorPullback_mem, this]
    exact R.downward_closed hf _

instance : (Etale.overEquiv U).inverse.IsDenseSubsite (smallEtaleTopology U.left)
    ((smallEtaleTopology S).over U) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

instance : (Etale.overEquiv U).symm.inverse.IsDenseSubsite ((smallEtaleTopology S).over U)
    (smallEtaleTopology U.left) :=
  inferInstanceAs ((Etale.overEquiv U).functor.IsDenseSubsite ..)

instance : (Etale.overForward U).IsDenseSubsite ((smallEtaleTopology S).over U)
    (smallEtaleTopology U.left) :=
  inferInstanceAs ((Etale.overEquiv U).functor.IsDenseSubsite ..)

instance : (Etale.overBackward U).IsDenseSubsite (smallEtaleTopology U.left)
    ((smallEtaleTopology S).over U) :=
  inferInstanceAs ((Etale.overEquiv U).inverse.IsDenseSubsite ..)

variable (A : Type w) [Category.{v} A]

/-- Sheaves on the localization at `U` of the small étale site of `S` are equivalent to sheaves on
the small étale site of `U.left`. -/
@[expose, simps!]
noncomputable def Etale.overSheafEquiv :
    Sheaf ((smallEtaleTopology S).over U) A ≌ Sheaf (smallEtaleTopology U.left) A :=
  (Etale.overEquiv U).sheafCongr _ _ A

/-- The restriction of étale sheaves on `S` to the small étale site of `U.left`, for an étale
`S`-scheme `U`. -/
@[expose]
noncomputable def Etale.sheafRestrict :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (smallEtaleTopology U.left) A :=
  (smallEtaleTopology S).overPullback A U ⋙ (Etale.overSheafEquiv U A).functor

/-- The restriction of étale sheaves to the small étale site of `U.left` is restriction to the
localized site at `U`, followed by the equivalence `Etale.overSheafEquiv`. -/
theorem Etale.sheafRestrict_def :
    Etale.sheafRestrict U A =
      (smallEtaleTopology S).overPullback A U ⋙ (Etale.overSheafEquiv U A).functor :=
  (rfl)

instance [((smallEtaleTopology S).overPullback A U).IsRightAdjoint] :
    (Etale.sheafRestrict U A).IsRightAdjoint :=
  inferInstanceAs
    ((smallEtaleTopology S).overPullback A U ⋙ (Etale.overSheafEquiv U A).functor).IsRightAdjoint

/-- The sections of the restriction of `F` over an étale `U.left`-scheme `X` are the sections of
`F` over `X`, regarded as an étale `S`-scheme. -/
@[simp]
theorem Etale.sheafRestrict_obj_obj_obj (F : Sheaf (smallEtaleTopology S) A)
    (X : (U.left.Etale)ᵒᵖ) :
    ((Etale.sheafRestrict U A).obj F).obj.obj X =
      F.obj.obj (op (Etale.mk (X.unop.hom ≫ U.hom))) :=
  (rfl)

/-- The restriction maps of the restriction of `F` along a morphism `g` of étale `U.left`-schemes
are the restriction maps of `F` along `g`, regarded as a morphism of étale `S`-schemes. -/
@[simp]
theorem Etale.sheafRestrict_obj_obj_map (F : Sheaf (smallEtaleTopology S) A)
    {X Y : (U.left.Etale)ᵒᵖ} (g : X ⟶ Y) :
    ((Etale.sheafRestrict U A).obj F).obj.map g =
      F.obj.map ((Etale.overBackward U).map g.unop).left.op :=
  (rfl)

/-- The restriction of a morphism of sheaves acts on sections over an étale `U.left`-scheme `X`
as the original morphism on sections over `X`, regarded as an étale `S`-scheme. -/
@[simp]
theorem Etale.sheafRestrict_map_hom_app {F G : Sheaf (smallEtaleTopology S) A} (f : F ⟶ G)
    (X : (U.left.Etale)ᵒᵖ) :
    ((Etale.sheafRestrict U A).map f).hom.app X =
      f.hom.app (op (Etale.mk (X.unop.hom ≫ U.hom))) :=
  (rfl)

variable {A} in
/-- Being an isomorphism of étale sheaves is étale local: a morphism of sheaves on the small étale
site of `S` is an isomorphism if and only if its restrictions to the small étale sites of the
members of a family of étale `S`-schemes jointly covering `S` are isomorphisms. -/
theorem Etale.isIso_iff_forall_isIso_sheafRestrict_map {ι : Type*} {U : ι → S.Etale}
    (hU : ∀ s : S, ∃ i, ∃ u : (U i).left, (U i).hom u = s)
    {F G : Sheaf (smallEtaleTopology S) A} (f : F ⟶ G) :
    IsIso f ↔ ∀ i, IsIso ((Etale.sheafRestrict (U i) A).map f) := by
  rw [Sheaf.isIso_iff_of_coversTop ((coversTop_smallEtaleTopology_iff U).mpr hU)]
  refine forall_congr' fun i ↦ ?_
  rw [Etale.sheafRestrict_def, Functor.comp_map]
  exact (isIso_iff_of_reflects_iso _ (Etale.overSheafEquiv (U i) A).functor).symm

end AlgebraicGeometry.Scheme
