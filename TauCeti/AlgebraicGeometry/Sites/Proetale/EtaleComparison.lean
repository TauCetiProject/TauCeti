/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
import TauCeti.CategoryTheory.Sites.Over.Basic

/-!
# The morphism of sites from the pro-étale site to the étale site

Let `X` be a scheme. An étale morphism is weakly étale, so the small étale site `X.Etale` of
étale `X`-schemes is a full subcategory of Mathlib's small pro-étale site `X.ProEt` of weakly étale
`X`-schemes. This file defines the inclusion `AlgebraicGeometry.Scheme.toProEt X : X.Etale ⥤
X.ProEt`, proves that it preserves finite limits and is continuous from the small étale topology
to the pro-étale topology, and so obtains the morphism of sites `ν : X_proét → X_ét` through its
direct image `AlgebraicGeometry.Scheme.proetalePushforward X A` (`ν_*`, restriction of a pro-étale
sheaf to the étale `X`-schemes) and, when it exists, its inverse image
`AlgebraicGeometry.Scheme.proetalePullback X A` (`ν^*`), left adjoint to the direct image
(`AlgebraicGeometry.Scheme.proetaleAdjunction`).

Continuity comes from comparing the two topologies after forgetting to `Over X`: both small
topologies are restricted from the big topologies on `Over X` along the forgetful functors, the
inclusion followed by the forgetful functor of `X.ProEt` is the forgetful functor of `X.Etale`,
and the big étale topology is coarser than the big pro-étale topology (Mathlib's
`AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology`).

The site `X.ProEt` is large (its objects form a type in the universe above that of its
morphisms), so the inverse image is defined under the hypothesis that the direct image is a right
adjoint. Mathlib's `CategoryTheory.Functor.sheafPullback` supplies it when the left Kan extensions
along the inclusion and pro-étale sheafification exist.

## Main declarations

* `AlgebraicGeometry.Scheme.toProEt`: the inclusion `X.Etale ⥤ X.ProEt`, fully faithful
  (`AlgebraicGeometry.Scheme.toProEtFullyFaithful`), with `toProEt_comp_forget`.
* `AlgebraicGeometry.Scheme.isEmpty_proEt_left`: a weakly étale scheme over an empty scheme is
  empty, as Mathlib's `AlgebraicGeometry.Scheme.isEmpty_etale_left` says for étale schemes.
* `AlgebraicGeometry.Scheme.preservesFiniteLimits_toProEt` and
  `AlgebraicGeometry.Scheme.isContinuous_toProEt`: the inclusion is a morphism of sites.
* `AlgebraicGeometry.Scheme.proetalePushforward`, `AlgebraicGeometry.Scheme.proetalePullback`,
  `AlgebraicGeometry.Scheme.proetaleAdjunction`: the direct and inverse images of `ν`.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, §5.1.
-/

public section

universe v' u u'

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The inclusion of the small étale site of `X` into its small pro-étale site: an étale
`X`-scheme is weakly étale. -/
-- Exposed so that the objects and morphisms of `toProEt X` are by definition those of `X.Etale`.
@[expose]
def toProEt : X.Etale ⥤ X.ProEt :=
  MorphismProperty.Over.changeProp X etale_le_weaklyEtale le_rfl

@[simp]
lemma toProEt_obj_left (V : X.Etale) : ((toProEt X).obj V).left = V.left :=
  rfl

@[simp]
lemma toProEt_obj_hom (V : X.Etale) : ((toProEt X).obj V).hom = V.hom :=
  rfl

@[simp]
lemma toProEt_map_left {V W : X.Etale} (f : V ⟶ W) : ((toProEt X).map f).left = f.left :=
  rfl

/-- The inclusion of the small étale site into the small pro-étale site, followed by the
forgetful functor of the pro-étale site, is the forgetful functor of the étale site. -/
lemma toProEt_comp_forget : toProEt X ⋙ ProEt.forget X = Etale.forget X :=
  rfl

/-- The inclusion of the small étale site into the small pro-étale site is fully faithful. -/
def toProEtFullyFaithful : (toProEt X).FullyFaithful :=
  MorphismProperty.Comma.fullyFaithfulChangeProp _ _ etale_le_weaklyEtale

instance : (toProEt X).Full :=
  (toProEtFullyFaithful X).full

instance : (toProEt X).Faithful :=
  (toProEtFullyFaithful X).faithful

/-- The inclusion of the small étale site into the small pro-étale site preserves finite limits:
after the fully faithful forgetful functor of the pro-étale site, it is the forgetful functor of
the étale site, which preserves them. -/
instance preservesFiniteLimits_toProEt : PreservesFiniteLimits (toProEt X) :=
  have : PreservesFiniteLimits (toProEt X ⋙ ProEt.forget X) := by
    rw [toProEt_comp_forget]
    infer_instance
  preservesFiniteLimits_of_reflects_of_preserves (toProEt X) (ProEt.forget X)

instance : RepresentablyFlat (toProEt X) :=
  flat_of_preservesFiniteLimits _

variable {X} in
/-- Every scheme weakly étale over an empty scheme is itself empty. -/
instance isEmpty_proEt_left [IsEmpty X] (V : X.ProEt) : IsEmpty V.left :=
  Function.isEmpty (β := X) V.hom

/-- The small pro-étale topology is restricted from the big pro-étale topology on `X`-schemes
along the forgetful functor. -/
lemma ProEt.topology_eq_restrictedTopology :
    ProEt.topology X = (ProEt.forget X).restrictedTopology (proetaleTopology.over X) := by
  -- Instance search does not find this instance from `IsMultiplicative`, as for `@Etale` in
  -- `TauCeti/AlgebraicGeometry/Sites/Etale/Subcanonical.lean`.
  have : MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _
    proetalePrecoverage_le_precoverage_weaklyEtale

/-- The inclusion of the small étale site into the small pro-étale site sends étale coverings to
pro-étale coverings. -/
lemma coverPreserving_toProEt :
    CoverPreserving (smallEtaleTopology X) (ProEt.topology X) (toProEt X) where
  cover_preserve {V R} hR := by
    have : RepresentablyFlat (Etale.forget X) := flat_of_preservesFiniteLimits _
    have h := ((Functor.isContinuous_iff_coverPreserving (F := Etale.forget X)
      (J := smallEtaleTopology X) (K := etaleTopology.over X)).mp inferInstance).cover_preserve hR
    rw [← toProEt_comp_forget] at h
    rw [ProEt.topology_eq_restrictedTopology]
    refine Functor.mem_restrictedTopology_of_functorPushforward_mem ?_
    rw [← Sieve.functorPushforward_comp]
    exact GrothendieckTopology.over_mono etaleTopology_le_proetaleTopology X _ h

/-- The inclusion of the small étale site into the small pro-étale site is continuous: it is the
morphism of sites `ν : X_proét → X_ét`. -/
instance isContinuous_toProEt :
    (toProEt X).IsContinuous (smallEtaleTopology X) (ProEt.topology X) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact coverPreserving_toProEt X

variable (A : Type u') [Category.{v'} A]

/-- The direct image `ν_*` of the morphism of sites `ν : X_proét → X_ét`: the restriction of a
pro-étale sheaf on `X` to the étale `X`-schemes. -/
abbrev proetalePushforward : Sheaf (ProEt.topology X) A ⥤ Sheaf (smallEtaleTopology X) A :=
  (toProEt X).sheafPushforwardContinuous A (smallEtaleTopology X) (ProEt.topology X)

/- The inverse image of `ν` exists when the left Kan extensions along the inclusion of étale
`X`-schemes among weakly étale ones and pro-étale sheafification exist, by Mathlib's construction
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`. -/
example [∀ F : X.Etaleᵒᵖ ⥤ A, (toProEt X).op.HasLeftKanExtension F]
    [HasWeakSheafify (ProEt.topology X) A] : (proetalePushforward X A).IsRightAdjoint :=
  inferInstance

variable [(proetalePushforward X A).IsRightAdjoint]

/-- The inverse image `ν^*` of the morphism of sites `ν : X_proét → X_ét`, Mathlib's pullback of
sheaves along the inclusion of the small étale site into the small pro-étale site. -/
noncomputable abbrev proetalePullback :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (ProEt.topology X) A :=
  (toProEt X).sheafPullback A (smallEtaleTopology X) (ProEt.topology X)

/-- The inverse image `ν^*` is left adjoint to the direct image `ν_*`. -/
noncomputable abbrev proetaleAdjunction : proetalePullback X A ⊣ proetalePushforward X A :=
  (toProEt X).sheafAdjunctionContinuous A (smallEtaleTopology X) (ProEt.topology X)

end AlgebraicGeometry.Scheme
