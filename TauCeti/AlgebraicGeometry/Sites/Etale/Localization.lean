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
(`AlgebraicGeometry.Scheme.Etale.restrictSheaf`), whose sections over an étale `U.left`-scheme `W`
are the sections over `W`, regarded as an étale `S`-scheme. This is how étale-local statements
about sheaves on `S`, such as local constancy or local isomorphy, are expressed on the small étale
sites of the members of an étale covering. For instance, a morphism of étale sheaves on `S` is an
isomorphism as soon as its restrictions to the members of an étale covering are isomorphisms
(`AlgebraicGeometry.Scheme.Etale.isIso_iff_forall_isIso_restrictSheaf_map`). A family of étale
`S`-schemes covers the terminal object of the small étale site exactly when the images of their
structure morphisms cover `S` (`AlgebraicGeometry.Scheme.coversTop_smallEtaleTopology_iff`).

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.overEquiv U : Over U ≌ U.left.Etale`: the localization of the
  small étale site of `S` at `U` is the small étale site of `U.left`.
* `AlgebraicGeometry.Scheme.Etale.overSheafEquiv U A`: the corresponding equivalence of categories
  of sheaves with values in `A`.
* `AlgebraicGeometry.Scheme.Etale.restrictSheaf U A`: restriction of étale sheaves on `S` to the
  small étale site of `U.left`.

## Main results

* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`: a sieve on an object `X` of the small
  étale site covers if and only if every point of `X.left` lifts along one of its members.
* `AlgebraicGeometry.Scheme.coversTop_smallEtaleTopology_iff`: a family of étale `S`-schemes
  covers the small étale site if and only if their images cover `S`.
* `AlgebraicGeometry.Scheme.Etale.isIso_iff_forall_isIso_restrictSheaf_map`: a morphism of étale
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
  -- Instance search does not recover this parent of the `IsMultiplicative` instance.
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  rw [show smallEtaleTopology S = (smallEtalePretopology S).toGrothendieck from
    smallGrothendieckTopology_eq_toGrothendieck_smallPretopology S le_rfl]
  refine (mem_toGrothendieck_smallPretopology X R).trans (forall_congr' fun x ↦ ⟨?_, ?_⟩)
  · rintro ⟨Y, f, y, hf, -, hy⟩
    exact ⟨Y, f, y, hf, hy⟩
  · rintro ⟨Y, f, y, hf, hy⟩
    exact ⟨Y, f, y, hf, inferInstance, hy⟩

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
    exact ⟨W.left, f.left, w, Sieve.image_mem_functorPushforward _ _ hf, hw⟩

/-- A family of étale `S`-schemes covers the small étale site of `S`, in the sense that it
generates a covering sieve of every object, if and only if every point of `S` lies in the image of
one of them. -/
theorem coversTop_smallEtaleTopology_iff {ι : Type*} (U : ι → S.Etale) :
    (smallEtaleTopology S).CoversTop U ↔ ∀ s : S, ∃ i, ∃ u : (U i).left, (U i).hom u = s := by
  refine ⟨fun h s ↦ ?_, fun h Y ↦ ?_⟩
  · obtain ⟨Z, f, z, ⟨i, ⟨g⟩⟩, hz⟩ :=
      (mem_smallEtaleTopology_iff _).mp (h (Etale.mk (𝟙 S))) s
    refine ⟨i, g.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w g, ← MorphismProperty.Over.w f,
      Scheme.Hom.comp_apply, hz]
    rfl
  · rw [mem_smallEtaleTopology_iff]
    intro y
    obtain ⟨i, u, hu⟩ := h (Y.hom y)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y u hu.symm
    exact ⟨Etale.mk (pullback.fst Y.hom (U i).hom ≫ Y.hom),
      MorphismProperty.Over.homMk (pullback.fst _ _), z,
      ⟨i, ⟨MorphismProperty.Over.homMk (pullback.snd _ _) pullback.condition.symm⟩⟩, hz⟩

variable (U : S.Etale)

/-- The functor from the localization at `U` of the small étale site of `S` to the small étale
site of `U.left`, sending `V ⟶ U` to the underlying étale morphism of schemes. -/
@[expose, simps]
noncomputable def Etale.overForward : Over U ⥤ U.left.Etale where
  obj V := Etale.mk V.hom.left
  map {V W} f := MorphismProperty.Over.homMk f.left.left
    (congrArg (fun g ↦ g.left) (Over.w f))

/-- The functor from the small étale site of `U.left` to the localization at `U` of the small
étale site of `S`, regarding an étale `U.left`-scheme as an étale `S`-scheme over `U`. -/
@[expose, simps]
noncomputable def Etale.overBackward : U.left.Etale ⥤ Over U where
  obj W := Over.mk (Y := Etale.mk (W.hom ≫ U.hom)) (MorphismProperty.Over.homMk W.hom)
  map {V W} f := Over.homMk (MorphismProperty.Over.homMk f.left
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (MorphismProperty.Over.w f))))
    (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f))

/-- The localization at `U` of the small étale site of `S` is equivalent to the small étale site
of `U.left`. -/
@[expose]
noncomputable def Etale.overEquiv : Over U ≌ U.left.Etale :=
  CategoryTheory.Equivalence.mk (Etale.overForward U) (Etale.overBackward U)
    (NatIso.ofComponents (fun V ↦ Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl V.left.left)
      ((Category.id_comp _).trans (MorphismProperty.Over.w V.hom)))
      (MorphismProperty.Over.Hom.ext (Category.id_comp _)))
      (fun f ↦ Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext
        ((Category.comp_id _).trans (Category.id_comp _).symm))))
    (NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl W.left))
      (fun f ↦ MorphismProperty.Over.Hom.ext
        ((Category.comp_id _).trans (Category.id_comp _).symm)))

@[simp]
theorem Etale.overEquiv_functor : (Etale.overEquiv U).functor = Etale.overForward U :=
  rfl

@[simp]
theorem Etale.overEquiv_inverse : (Etale.overEquiv U).inverse = Etale.overBackward U :=
  rfl

instance : (Etale.overForward U).IsCocontinuous ((smallEtaleTopology S).over U)
    (smallEtaleTopology U.left) where
  cover_lift {V} R hR := by
    rw [mem_smallEtaleTopology_iff] at hR
    rw [mem_over_smallEtaleTopology_iff]
    intro x
    obtain ⟨W, f, w, hf, rfl⟩ := hR x
    let g : (Etale.overBackward U).obj W ⟶ V :=
      Over.homMk (MorphismProperty.Over.homMk f.left
        ((congrArg (f.left ≫ ·) (MorphismProperty.Over.w V.hom)).symm.trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (MorphismProperty.Over.w f)))))
        (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f))
    refine ⟨_, g, w, ?_, rfl⟩
    -- The image of `g` is `f`, up to the identity of `W.left` regarded as a morphism between
    -- two presentations of `W` in the small étale site of `U.left`.
    let e : (Etale.overForward U).obj ((Etale.overBackward U).obj W) ⟶ W :=
      MorphismProperty.Over.homMk (𝟙 W.left) (Category.id_comp _)
    have : (Etale.overForward U).map g = e ≫ f :=
      MorphismProperty.Over.Hom.ext (Category.id_comp _).symm
    exact (this ▸ R.downward_closed hf e : R ((Etale.overForward U).map g))

instance : (Etale.overBackward U).IsCocontinuous (smallEtaleTopology U.left)
    ((smallEtaleTopology S).over U) where
  cover_lift {W} R hR := by
    rw [mem_over_smallEtaleTopology_iff] at hR
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨V, f, v, hf, rfl⟩ := hR x
    let g : (Etale.overForward U).obj V ⟶ W :=
      MorphismProperty.Over.homMk f.left.left
        (congrArg (fun h ↦ h.left) (Over.w f))
    refine ⟨_, g, v, ?_, rfl⟩
    -- The image of `g` is `f`, up to the identity of `V.left.left` regarded as a morphism between
    -- two presentations of `V` in `Over U`.
    let e : (Etale.overBackward U).obj ((Etale.overForward U).obj V) ⟶ V :=
      Over.homMk (MorphismProperty.Over.homMk (𝟙 V.left.left)
        ((Category.id_comp _).trans (MorphismProperty.Over.w V.hom).symm))
        (MorphismProperty.Over.Hom.ext (Category.id_comp _))
    have : (Etale.overBackward U).map g = e ≫ f :=
      Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext (Category.id_comp _).symm)
    exact (this ▸ R.downward_closed hf e : R ((Etale.overBackward U).map g))

instance : (Etale.overEquiv U).inverse.IsDenseSubsite (smallEtaleTopology U.left)
    ((smallEtaleTopology S).over U) :=
  have : (Etale.overEquiv U).functor.IsCocontinuous ((smallEtaleTopology S).over U)
      (smallEtaleTopology U.left) := inferInstanceAs ((Etale.overForward U).IsCocontinuous _ _)
  have : (Etale.overEquiv U).inverse.IsCocontinuous (smallEtaleTopology U.left)
      ((smallEtaleTopology S).over U) :=
    inferInstanceAs ((Etale.overBackward U).IsCocontinuous _ _)
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

variable (A : Type w) [Category.{v} A]

/-- Sheaves on the localization at `U` of the small étale site of `S` are equivalent to sheaves on
the small étale site of `U.left`. -/
@[expose]
noncomputable def Etale.overSheafEquiv :
    Sheaf ((smallEtaleTopology S).over U) A ≌ Sheaf (smallEtaleTopology U.left) A :=
  (Etale.overEquiv U).sheafCongr _ _ A

/-- The restriction of étale sheaves on `S` to the small étale site of `U.left`, for an étale
`S`-scheme `U`. -/
@[expose]
noncomputable def Etale.restrictSheaf :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (smallEtaleTopology U.left) A :=
  (smallEtaleTopology S).overPullback A U ⋙ (Etale.overSheafEquiv U A).functor

/-- The sections of the restriction of `F` over an étale `U.left`-scheme `W` are the sections of
`F` over `W`, regarded as an étale `S`-scheme. -/
@[simp]
theorem Etale.restrictSheaf_obj_obj_obj (F : Sheaf (smallEtaleTopology S) A)
    (W : U.left.Etale) :
    ((Etale.restrictSheaf U A).obj F).obj.obj (op W) =
      F.obj.obj (op (Etale.mk (W.hom ≫ U.hom))) :=
  rfl

/-- The restriction of a morphism of sheaves acts on sections over an étale `U.left`-scheme `W`
as the original morphism on sections over `W`, regarded as an étale `S`-scheme. -/
@[simp]
theorem Etale.restrictSheaf_map_hom_app {F G : Sheaf (smallEtaleTopology S) A} (f : F ⟶ G)
    (W : U.left.Etale) :
    ((Etale.restrictSheaf U A).map f).hom.app (op W) =
      f.hom.app (op (Etale.mk (W.hom ≫ U.hom))) :=
  rfl

variable {A} in
/-- Being an isomorphism of étale sheaves is étale local: a morphism of sheaves on the small étale
site of `S` is an isomorphism if and only if its restrictions to the small étale sites of the
members of a family of étale `S`-schemes jointly covering `S` are isomorphisms. -/
theorem Etale.isIso_iff_forall_isIso_restrictSheaf_map {ι : Type*} {U : ι → S.Etale}
    (hU : ∀ s : S, ∃ i, ∃ u : (U i).left, (U i).hom u = s)
    {F G : Sheaf (smallEtaleTopology S) A} (f : F ⟶ G) :
    IsIso f ↔ ∀ i, IsIso ((Etale.restrictSheaf (U i) A).map f) := by
  rw [Sheaf.isIso_iff_of_coversTop ((coversTop_smallEtaleTopology_iff U).mpr hU)]
  exact forall_congr' fun i ↦
    (isIso_iff_of_reflects_iso _ (Etale.overSheafEquiv (U i) A).functor).symm

end AlgebraicGeometry.Scheme
