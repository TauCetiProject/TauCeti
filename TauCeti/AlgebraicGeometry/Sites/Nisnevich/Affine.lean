/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic

/-!
# The affine Nisnevich site and Nisnevich sheafification

Let `S` be a scheme. The category `S.AffineEtale` of affine schemes `Spec R` étale over `S` is
essentially small, and `Spec : S.AffineEtale ⥤ S.Etale` is fully faithful. Every étale
`S`-scheme is covered by its affine opens, and Zariski coverings are Nisnevich coverings, so this
functor exhibits `S.AffineEtale`, with the induced topology, as a `1`-hypercover dense subsite of
the small Nisnevich site of `S`. As for the small étale site
(`Mathlib.AlgebraicGeometry.Sites.AffineEtale`), the categories of sheaves on the two sites are
equivalent, and presheaves on the small Nisnevich site of `S : Scheme.{u}` can be sheafified with
values in any concrete category such as `Type u`, `AddCommGrpCat.{u}` or `ModuleCat.{u} Λ`.

## Main declarations

* `AlgebraicGeometry.Scheme.AffineEtale.nisnevichTopology S`: the topology on `S.AffineEtale`
  induced by `Spec` from the small Nisnevich topology.
* `AlgebraicGeometry.Scheme.AffineEtale.nisnevichSheafEquiv`: sheaves on the affine Nisnevich site
  are equivalent to sheaves on the small Nisnevich site.
* The instance `HasSheafify (smallNisnevichTopology S) A` for a concrete category `A` whose
  forgetful functor preserves limits and filtered colimits and reflects isomorphisms.
* `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallNisnevichTopology`: sheaves on the
  small Nisnevich site with values in a Grothendieck abelian category form a Grothendieck abelian
  category.
-/

@[expose] public noncomputable section

universe u u'

open CategoryTheory Limits MorphismProperty TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

namespace AffineEtale

/-- Every étale `S`-scheme has a Nisnevich covering by affine étale `S`-schemes: the members of
an affine open cover. -/
theorem exists_mem_smallNisnevichTopology (X : S.Etale) :
    ∃ (ι : Type u) (U : ι → S.AffineEtale) (f : ∀ i, (AffineEtale.Spec S).obj (U i) ⟶ X),
      Sieve.ofArrows _ f ∈ S.smallNisnevichTopology X := by
  let 𝒰 := X.left.affineOpenCover
  refine ⟨𝒰.I₀, fun i ↦ AffineEtale.mk (𝒰.f i ≫ X.hom),
    fun i ↦ Over.homMk (𝒰.f i) rfl trivial, ?_⟩
  exact (ofArrows_mem_smallNisnevichTopology_iff _).mpr
    (isNisnevichCovering_of_zariski 𝒰.openCover.mem₀)

instance isCoverDense_smallNisnevichTopology :
    (AffineEtale.Spec S).IsCoverDense S.smallNisnevichTopology where
  is_cover X := by
    obtain ⟨ι, U, f, hf⟩ := exists_mem_smallNisnevichTopology X
    refine GrothendieckTopology.superset_covering _ ?_ hf
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ Presieve.in_coverByImage _ (f i)

variable (S) in
/-- The topology on the small affine étale site induced by `Spec` from the small Nisnevich
site. -/
def nisnevichTopology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology S.smallNisnevichTopology

instance isDenseSubsite_nisnevichTopology :
    Functor.IsDenseSubsite (nisnevichTopology S) S.smallNisnevichTopology
    (AffineEtale.Spec S) := by
  dsimp [nisnevichTopology]
  infer_instance

instance isOneHypercoverDense_nisnevichTopology :
    Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
    (nisnevichTopology S) S.smallNisnevichTopology :=
  Functor.IsOneHypercoverDense.of_hasPullbacks exists_mem_smallNisnevichTopology

end AffineEtale

section

variable {A : Type u'} [Category.{u} A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

instance AffineEtale.hasSheafify_nisnevichTopology :
    HasSheafify (AffineEtale.nisnevichTopology S) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

instance AffineEtale.isEquivalence_sheafPushforwardContinuous_nisnevich :
    ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (AffineEtale.nisnevichTopology S) S.smallNisnevichTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

/-- Presheaves on the small Nisnevich site can be sheafified, with values in a concrete category
whose forgetful functor preserves limits and filtered colimits and reflects isomorphisms. -/
instance hasSheafify_smallNisnevichTopology : HasSheafify S.smallNisnevichTopology A :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.nisnevichTopology S) S.smallNisnevichTopology (AffineEtale.Spec S)

instance AffineEtale.wEqualsLocallyBijective_nisnevichTopology :
    (AffineEtale.nisnevichTopology S).WEqualsLocallyBijective A :=
  .ofEssentiallySmall (AffineEtale.nisnevichTopology S)

instance wEqualsLocallyBijective_smallNisnevichTopology :
    S.smallNisnevichTopology.WEqualsLocallyBijective A :=
  .transport _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.nisnevichTopology S) _
      (AffineEtale.Spec S))

-- The `IsGrothendieckAbelian` instances below are not found without the next two instances.
instance AffineEtale.instAbelianSheafNisnevichTopology [Abelian A] :
    Abelian (Sheaf (AffineEtale.nisnevichTopology S) A) :=
  inferInstance

instance instAbelianSheafSmallNisnevichTopology [Abelian A] :
    Abelian (Sheaf S.smallNisnevichTopology A) :=
  inferInstance

variable (S A)

/-- The category of sheaves on the affine Nisnevich site is equivalent to the category of
sheaves on the small Nisnevich site. -/
@[simps! inverse]
def AffineEtale.nisnevichSheafEquiv :
    Sheaf (AffineEtale.nisnevichTopology S) A ≌ Sheaf S.smallNisnevichTopology A :=
  ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (nisnevichTopology S) S.smallNisnevichTopology).asEquivalence.symm

instance AffineEtale.isGrothendieckAbelian_sheaf_nisnevichTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf (AffineEtale.nisnevichTopology S) A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Sheaves on the small Nisnevich site with values in a Grothendieck abelian category form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_sheaf_smallNisnevichTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallNisnevichTopology A) :=
  IsGrothendieckAbelian.of_equivalence (AffineEtale.nisnevichSheafEquiv S A)

end

end AlgebraicGeometry.Scheme
