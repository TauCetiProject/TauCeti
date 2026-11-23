/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic

/-!
# The comparison morphism from Nisnevich sheaves to Zariski sheaves

Let `X` be a scheme. An open subscheme `U ⊆ X` is étale over `X`, which gives the functor
`AlgebraicGeometry.Scheme.opensToEtale X : X.Opens ⥤ X.Etale`. It has a left adjoint
`AlgebraicGeometry.Scheme.etaleToOpens X`, sending an étale `X`-scheme `V` to its image, which is
open because étale morphisms are open maps; a morphism `V ⟶ U` over `X` exists exactly when the
image of `V` lies in `U`. As a right adjoint, `opensToEtale X` preserves limits, and it sends
Zariski coverings to Nisnevich coverings, so it is continuous from the Zariski topology to the
small Nisnevich topology. This defines the comparison morphism of topoi `Sh(X_Nis) → Sh(X_Zar)`
through its two functors:

* its direct image `AlgebraicGeometry.Scheme.nisnevichToZariskiPushforward X A`, which restricts a
  Nisnevich sheaf to the open subschemes of `X`;
* its inverse image `AlgebraicGeometry.Scheme.nisnevichToZariskiPullback X A`, which sends a
  Zariski sheaf `F` to the Nisnevich sheafification of the presheaf `V ↦ F(image of V)`, and is
  left adjoint to the direct image (`AlgebraicGeometry.Scheme.nisnevichToZariskiAdjunction`).

On presheaves, precomposition with `etaleToOpens X` is left adjoint to restriction along
`opensToEtale X`, because `etaleToOpens X ⊣ opensToEtale X`. Precomposition preserves all limits,
so the inverse image preserves finite limits, that is, it is exact, whenever `A` has finite limits
and Nisnevich sheafification preserves them (`[HasSheafify (smallNisnevichTopology X) A]`).

## Main declarations

* `AlgebraicGeometry.Scheme.opensToEtale`: open subschemes as étale `X`-schemes.
* `AlgebraicGeometry.Scheme.etaleToOpens`: the image of an étale `X`-scheme.
* `AlgebraicGeometry.Scheme.etaleToOpensAdjunction`: `etaleToOpens X ⊣ opensToEtale X`.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiPushforward`: Nisnevich sheaves as Zariski
  sheaves.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiPullback`: the inverse image of Zariski sheaves.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiAdjunction`: the inverse image is left adjoint to
  the direct image.

## References

* The Stacks Project, Chapter *Étale Cohomology*, Section *Comparing topologies*.
* F. Morel, V. Voevodsky, *A¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

public section

universe v' u u'

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry.Scheme

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
@[expose]
noncomputable def etaleToOpens : X.Etale ⥤ X.Opens where
  obj V := ⟨Set.range V.hom, V.hom.isOpenMap.isOpen_range⟩
  map {V W} φ := homOfLE <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨φ.left x, by rw [← Scheme.Hom.comp_apply, MorphismProperty.Over.w φ]⟩

/-- The image of an étale `X`-scheme `V` is the set-theoretic range of `V ⟶ X`. -/
@[simp]
theorem coe_etaleToOpens_obj (V : X.Etale) :
    ((etaleToOpens X).obj V : Set X) = Set.range V.hom :=
  rfl

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
            (show V.left ⟶ U from IsOpenImmersion.lift U.ι V.hom
              (by rw [Scheme.Opens.range_ι]; exact i.le))
            (IsOpenImmersion.lift_fac (Scheme.Opens.ι U) V.hom _)
          invFun φ := homOfLE <| by
            rintro _ ⟨x, rfl⟩
            rw [← MorphismProperty.Over.w φ, Scheme.Hom.comp_apply]
            exact (φ.left x).property
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right _ _ := Subsingleton.elim _ _ }

instance isRightAdjoint_opensToEtale : (opensToEtale X).IsRightAdjoint :=
  (etaleToOpensAdjunction X).isRightAdjoint

instance representablyFlat_opensToEtale : RepresentablyFlat (opensToEtale X) :=
  flat_of_preservesFiniteLimits _

/-- The functor `opensToEtale X` sends Zariski coverings to Nisnevich coverings. -/
theorem coverPreserving_opensToEtale :
    CoverPreserving (Opens.grothendieckTopology X) (smallNisnevichTopology X) (opensToEtale X)
    where
  cover_preserve {U R} hR := by
    let ι := {p : Σ V : X.Opens, V ⟶ U // R p.snd}
    refine GrothendieckTopology.superset_covering _ (S := Sieve.ofArrows
      (fun i : ι ↦ (opensToEtale X).obj i.val.fst) (fun i ↦ (opensToEtale X).map i.val.snd)) ?_ ?_
    · rintro _ _ ⟨_, _, _, ⟨i⟩, rfl⟩
      exact Sieve.downward_closed _ (Sieve.image_mem_functorPushforward _ _ i.property) _
    · rw [ofArrows_mem_smallNisnevichTopology_iff]
      refine isNisnevichCovering_of_zariski ?_
      rw [AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, fun i ↦ inferInstanceAs (IsOpenImmersion (X.homOfLE i.val.snd.le))⟩
      obtain ⟨V, f, hf, hx⟩ := hR x.val x.property
      exact ⟨⟨⟨V, f⟩, hf⟩, ⟨x.val, hx⟩, Subtype.ext (X.homOfLE_apply f.le ⟨x.val, hx⟩)⟩

instance isContinuous_opensToEtale :
    (opensToEtale X).IsContinuous (Opens.grothendieckTopology X) (smallNisnevichTopology X) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (coverPreserving_opensToEtale X)

variable (A : Type u') [Category.{v'} A]

/-- The direct image of the comparison morphism of topoi `Sh(X_Nis) → Sh(X_Zar)`: the restriction
of a Nisnevich sheaf on `X` to the open subschemes of `X`. -/
noncomputable abbrev nisnevichToZariskiPushforward :
    Sheaf (smallNisnevichTopology X) A ⥤ Sheaf (Opens.grothendieckTopology X) A :=
  (opensToEtale X).sheafPushforwardContinuous A (Opens.grothendieckTopology X)
    (smallNisnevichTopology X)

section

variable [HasWeakSheafify (smallNisnevichTopology X) A]

/-- The inverse image of the comparison morphism of topoi `Sh(X_Nis) → Sh(X_Zar)`: the Nisnevich
sheafification of the presheaf `V ↦ F(image of V)` on étale `X`-schemes. -/
noncomputable abbrev nisnevichToZariskiPullback :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf (smallNisnevichTopology X) A :=
  sheafToPresheaf (Opens.grothendieckTopology X) A ⋙
    (Functor.whiskeringLeft _ _ A).obj (etaleToOpens X).op ⋙
      presheafToSheaf (smallNisnevichTopology X) A

/-- The inverse image of the comparison morphism `Sh(X_Nis) → Sh(X_Zar)` is left adjoint to its
direct image. -/
noncomputable def nisnevichToZariskiAdjunction :
    nisnevichToZariskiPullback X A ⊣ nisnevichToZariskiPushforward X A :=
  (((etaleToOpensAdjunction X).op.whiskerLeft A).comp
      (sheafificationAdjunction (smallNisnevichTopology X) A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

noncomputable instance isLeftAdjoint_nisnevichToZariskiPullback :
    (nisnevichToZariskiPullback X A).IsLeftAdjoint :=
  (nisnevichToZariskiAdjunction X A).isLeftAdjoint

end

/-- The inverse image of `Sh(X_Nis) → Sh(X_Zar)` is exact when `A` has finite limits and
Nisnevich sheafification preserves them. -/
instance preservesFiniteLimits_nisnevichToZariskiPullback [HasFiniteLimits A]
    [HasSheafify (smallNisnevichTopology X) A] :
    PreservesFiniteLimits (nisnevichToZariskiPullback X A) :=
  inferInstance

end AlgebraicGeometry.Scheme
