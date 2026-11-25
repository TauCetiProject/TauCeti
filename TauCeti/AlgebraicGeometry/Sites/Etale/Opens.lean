/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Functor.Flat

/-!
# Open subschemes as étale schemes

Let `X` be a scheme. An open subscheme `U ⊆ X` is étale over `X`, which gives the functor
`AlgebraicGeometry.Scheme.opensToEtale X : X.Opens ⥤ X.Etale`. It has a left adjoint
`AlgebraicGeometry.Scheme.etaleToOpens X`, sending an étale `X`-scheme `V` to its image, which is
open because étale morphisms are open maps; a morphism `V ⟶ U` over `X` exists exactly when the
image of `V` lies in `U`. The counit of this adjunction is an isomorphism, so `opensToEtale X` is
fully faithful, and as a right adjoint it preserves limits, so it is representably flat.

## Main declarations

* `AlgebraicGeometry.Scheme.opensToEtale`: open subschemes as étale `X`-schemes.
* `AlgebraicGeometry.Scheme.etaleToOpens`: the image of an étale `X`-scheme.
* `AlgebraicGeometry.Scheme.etaleToOpensAdjunction`: `etaleToOpens X ⊣ opensToEtale X`.
* `AlgebraicGeometry.Scheme.fullyFaithfulOpensToEtale`: `opensToEtale X` is fully faithful.

## References

* The Stacks Project, Chapter *Étale Cohomology*, Section *Comparing topologies*.
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- An open subscheme `U` of `X`, as the étale `X`-scheme `U.ι : U ⟶ X`. -/
@[expose, simps! obj_left obj_hom map_left]
noncomputable def opensToEtale : X.Opens ⥤ X.Etale where
  obj U := Etale.mk U.ι
  map i := MorphismProperty.Over.homMk (X.homOfLE i.le) (X.homOfLE_ι i.le)
  map_id U := MorphismProperty.Over.Hom.ext (X.homOfLE_rfl U)
  map_comp i j := MorphismProperty.Over.Hom.ext (X.homOfLE_homOfLE i.le j.le).symm

/-- The image of an étale `X`-scheme `V`, an open subset of `X` since étale morphisms are open
maps. -/
noncomputable def etaleToOpens : X.Etale ⥤ X.Opens where
  obj V := ⟨Set.range V.hom, V.hom.isOpenMap.isOpen_range⟩
  map {V W} φ := homOfLE <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨φ.left x, by rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w φ]⟩

/-- The image of an étale `X`-scheme `V` is the set-theoretic range of `V ⟶ X`. -/
@[simp]
theorem coe_etaleToOpens_obj (V : X.Etale) :
    ((etaleToOpens X).obj V : Set X) = Set.range V.hom :=
  (rfl)

/-- A point lies in the image of an étale `X`-scheme `V` when it is the image of a point of `V`. -/
@[simp]
theorem mem_etaleToOpens_obj (V : X.Etale) (x : X) :
    x ∈ (etaleToOpens X).obj V ↔ ∃ y : V.left, V.hom y = x :=
  (Set.ext_iff.mp (coe_etaleToOpens_obj X V) x).trans Set.mem_range

/-- The image of the open subscheme `U`, as an étale `X`-scheme, is `U`. -/
@[simp]
theorem etaleToOpens_obj_opensToEtale_obj (U : X.Opens) :
    (etaleToOpens X).obj ((opensToEtale X).obj U) = U :=
  SetLike.coe_injective <| (coe_etaleToOpens_obj X _).trans U.range_ι

/-- There is at most one morphism over `X` from an étale `X`-scheme to an open subscheme of `X`,
since open immersions are monomorphisms. -/
instance subsingleton_hom_opensToEtale_obj (V : X.Etale) (U : X.Opens) :
    Subsingleton (V ⟶ (opensToEtale X).obj U) :=
  ⟨fun φ ψ ↦ MorphismProperty.Over.Hom.ext <| (cancel_mono (Scheme.Opens.ι U)).mp <|
    (MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w ψ).symm⟩

/-- An étale `X`-scheme `V` maps to the open subscheme `U` over `X` exactly when the image of `V`
lies in `U`: the image functor is left adjoint to `opensToEtale X`. -/
noncomputable def etaleToOpensAdjunction : etaleToOpens X ⊣ opensToEtale X :=
  Adjunction.mkOfHomEquiv
    { homEquiv (V : X.Etale) (U : X.Opens) :=
        { toFun i := MorphismProperty.Over.homMk
            -- The ascription makes `IsOpenImmersion U.ι` visible to instance search: the expected
            -- type `((opensToEtale X).obj U).left` only reduces to `U` by unfolding `Etale.mk`.
            (show V.left ⟶ U from IsOpenImmersion.lift U.ι V.hom
              (U.range_ι.symm ▸ (coe_etaleToOpens_obj X V).symm.subset.trans i.le))
            (IsOpenImmersion.lift_fac (Scheme.Opens.ι U) V.hom _)
          invFun φ := homOfLE <| by
            rw [← etaleToOpens_obj_opensToEtale_obj X U]
            exact ((etaleToOpens X).map φ).le
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right _ _ := Subsingleton.elim _ _ }

instance isRightAdjoint_opensToEtale : (opensToEtale X).IsRightAdjoint :=
  (etaleToOpensAdjunction X).isRightAdjoint

/-- The counit of `etaleToOpens X ⊣ opensToEtale X` is an isomorphism: the image of an open
subscheme `U` is `U`. -/
instance isIso_etaleToOpensAdjunction_counit : IsIso (etaleToOpensAdjunction X).counit :=
  have (U : X.Opens) : IsIso ((etaleToOpensAdjunction X).counit.app U) :=
    homOfLE_isIso_of_eq _ (etaleToOpens_obj_opensToEtale_obj X U)
  NatIso.isIso_of_isIso_app _

/-- The functor `opensToEtale X` is fully faithful. -/
noncomputable def fullyFaithfulOpensToEtale : (opensToEtale X).FullyFaithful :=
  (etaleToOpensAdjunction X).fullyFaithfulROfIsIsoCounit

instance full_opensToEtale : (opensToEtale X).Full :=
  (fullyFaithfulOpensToEtale X).full

instance faithful_opensToEtale : (opensToEtale X).Faithful :=
  (fullyFaithfulOpensToEtale X).faithful

instance representablyFlat_opensToEtale : RepresentablyFlat (opensToEtale X) :=
  flat_of_preservesFiniteLimits _

end AlgebraicGeometry.Scheme
