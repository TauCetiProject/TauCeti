/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.AlgebraicGeometry.Sites.Etale.Opens
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic

/-!
# The comparison morphism from Nisnevich sheaves to Zariski sheaves

Let `X` be a scheme. The functor `AlgebraicGeometry.Scheme.opensToEtale X : X.Opens ⥤ X.Etale`,
viewing an open subscheme as an étale `X`-scheme, is right adjoint to the image functor
`AlgebraicGeometry.Scheme.etaleToOpens X`, so it is representably flat, and it sends Zariski
coverings to Nisnevich coverings, so it is continuous from the Zariski topology to the small
Nisnevich topology. This defines the comparison morphism of topoi `Sh(X_Nis) → Sh(X_Zar)` through
its two functors:

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

* `AlgebraicGeometry.Scheme.coverPreserving_opensToEtale`: `opensToEtale X` sends Zariski
  coverings to Nisnevich coverings.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiPushforward`: Nisnevich sheaves as Zariski
  sheaves.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiPullback`: the inverse image of Zariski sheaves.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiAdjunction`: the inverse image is left adjoint to
  the direct image.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiPullbackIso`: the inverse image agrees with the
  general pullback `Functor.sheafPullback` along `opensToEtale X`.

## References

* The Stacks Project, Chapter *Étale Cohomology*, Section *Comparing topologies*.
* F. Morel, V. Voevodsky, *A¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

public section

universe v' u u'

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

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
      -- `((opensToEtale X).obj U).left` is `U` by definition, and its morphisms are the inclusions
      -- `X.homOfLE`. The `simps` lemmas for `opensToEtale` do not help here: rewriting with them
      -- leaves terms that are not type-correct at instance transparency.
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

noncomputable instance isRightAdjoint_nisnevichToZariskiPushforward :
    (nisnevichToZariskiPushforward X A).IsRightAdjoint :=
  (nisnevichToZariskiAdjunction X A).isRightAdjoint

/-- The inverse image `nisnevichToZariskiPullback X A` is the general pullback of sheaves along the
continuous functor `opensToEtale X`. -/
noncomputable def nisnevichToZariskiPullbackIso :
    (opensToEtale X).sheafPullback A (Opens.grothendieckTopology X) (smallNisnevichTopology X) ≅
      nisnevichToZariskiPullback X A :=
  ((opensToEtale X).sheafAdjunctionContinuous A _ _).leftAdjointUniq
    (nisnevichToZariskiAdjunction X A)

end

/- The inverse image of `Sh(X_Nis) → Sh(X_Zar)` is exact when `A` has finite limits and
Nisnevich sheafification preserves them. -/
example [HasFiniteLimits A] [HasSheafify (smallNisnevichTopology X) A] :
    PreservesFiniteLimits (nisnevichToZariskiPullback X A) :=
  inferInstance

end AlgebraicGeometry.Scheme
