/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.SmoothSheaf
public import TauCeti.CategoryTheory.Galois.Torsor.Classification
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Restrict

/-!
# Étale torsors over a field and continuous Galois cohomology

Let `K` be a field with separable closure `Ω`, and let `𝒢` be a sheaf of groups on the small
étale site of `Spec K`. Restricting along the inclusion `toEtale` of finite étale `K`-schemes,
which is a dense subsite, and along Galois theory `galoisEquivalence K Ω` identifies `𝒢` with a
sheaf of groups on finite continuous `Gal(Ω/K)`-sets for the jointly surjective topology. Both
functors are continuous, cocontinuous and representably flat, so restriction of torsors is a
bijection on classes (`CategoryTheory.Sheaf.NonabelianH1.restrictEquiv`). Composing with the
classification of torsors on finite continuous `Gal(Ω/K)`-sets by their stalks
(`ContAction.nonabelianH1EquivStalk`) gives the field-level Galois-cocycle description

  `Sheaf.NonabelianH1 𝒢 ≃ H¹(Gal(Ω/K), A)`,

with `A` the stalk of the restriction of `𝒢` at the point of the Galois site, with the discrete
topology (`TauCeti.FiniteEtaleScheme.nonabelianH1EquivGalois`): étale `𝒢`-torsors over `K` are
classified by continuous nonabelian Galois cohomology.

## Main declarations

* `TauCeti.FiniteEtaleScheme.galoisSiteFunctor K Ω`: the functor from finite continuous
  `Gal(Ω/K)`-sets to the small étale site of `Spec K`, `galoisEquivalence` followed by `toEtale`.
* `TauCeti.FiniteEtaleScheme.galoisSheaf K Ω 𝒢`: the restriction of `𝒢` to the Galois site.
* `TauCeti.FiniteEtaleScheme.nonabelianH1EquivGaloisSite K Ω 𝒢`: étale torsor classes are torsor
  classes on the Galois site.
* `TauCeti.FiniteEtaleScheme.nonabelianH1EquivGalois K Ω 𝒢`: étale torsor classes are continuous
  nonabelian Galois cohomology classes.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
* The Stacks Project, Tag 03QQ.
-/

public noncomputable section

open CategoryTheory Limits AlgebraicGeometry FintypeCatDiscrete

universe u

namespace TauCeti.FiniteEtaleScheme

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω]

/-- The functor from finite continuous `Gal(Ω/K)`-sets to the small étale site of `Spec K`:
Galois theory `galoisEquivalence K Ω` followed by the inclusion of finite étale `K`-schemes. -/
abbrev galoisSiteFunctor : ContAction FintypeCat.{u} Gal(Ω/K) ⥤ (Spec (.of K)).Etale :=
  (galoisEquivalence K Ω).inverse ⋙ toEtale (Spec (.of K))

instance isContinuous_galoisSiteFunctor :
    (galoisSiteFunctor K Ω).IsContinuous (ContAction.jointlySurjectiveTopology Gal(Ω/K))
      (Scheme.smallEtaleTopology _) :=
  Functor.isContinuous_comp _ _ (ContAction.jointlySurjectiveTopology Gal(Ω/K)) (fieldTopology K)
    (Scheme.smallEtaleTopology _)

instance isCocontinuous_galoisSiteFunctor :
    (galoisSiteFunctor K Ω).IsCocontinuous (ContAction.jointlySurjectiveTopology Gal(Ω/K))
      (Scheme.smallEtaleTopology _) :=
  isCocontinuous_comp (galoisEquivalence K Ω).inverse (toEtale _)
    (ContAction.jointlySurjectiveTopology Gal(Ω/K)) (fieldTopology K)

variable (𝒢 : Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) GrpCat.{u})

/-- The restriction of an étale sheaf of groups `𝒢` on `Spec K` to finite continuous
`Gal(Ω/K)`-sets along `galoisSiteFunctor K Ω`, a sheaf for the jointly surjective topology. -/
abbrev galoisSheaf : Sheaf (ContAction.jointlySurjectiveTopology Gal(Ω/K)) GrpCat.{u} :=
  ((galoisSiteFunctor K Ω).sheafPushforwardContinuous GrpCat.{u}
    (ContAction.jointlySurjectiveTopology Gal(Ω/K)) (Scheme.smallEtaleTopology _)).obj 𝒢

/-- **Étale torsors over a field are torsors on the Galois site.** Restriction along
`galoisSiteFunctor K Ω` is a bijection from the classes of étale `𝒢`-torsors over `Spec K` to
the classes of `galoisSheaf K Ω 𝒢`-torsors on finite continuous `Gal(Ω/K)`-sets. -/
def nonabelianH1EquivGaloisSite :
    Sheaf.NonabelianH1 𝒢 ≃ Sheaf.NonabelianH1 (galoisSheaf K Ω 𝒢) :=
  Sheaf.NonabelianH1.restrictEquiv _ (galoisSiteFunctor K Ω) 𝒢

/-- `nonabelianH1EquivGaloisSite K Ω 𝒢` sends the class of a torsor to the class of its
restriction. -/
@[simp]
lemma nonabelianH1EquivGaloisSite_mk (P : Sheaf.Torsor 𝒢) :
    nonabelianH1EquivGaloisSite K Ω 𝒢 (Sheaf.NonabelianH1.mk P) =
      Sheaf.NonabelianH1.mk (P.restrict _ (galoisSiteFunctor K Ω)) := by
  rw [nonabelianH1EquivGaloisSite, Sheaf.NonabelianH1.restrictEquiv_apply,
    Sheaf.NonabelianH1.restrict_mk]

variable [TopologicalSpace ((ContAction.point Gal(Ω/K)).GrpStalk (galoisSheaf K Ω 𝒢).obj)]
  [DiscreteTopology ((ContAction.point Gal(Ω/K)).GrpStalk (galoisSheaf K Ω 𝒢).obj)]

/-- **Étale torsors over a field are classified by continuous Galois cohomology.** For a field
`K` with separable closure `Ω` and an étale sheaf of groups `𝒢` on `Spec K`, the classes of étale
`𝒢`-torsors are in bijection with the continuous nonabelian cohomology `H¹(Gal(Ω/K), A)`, where
`A` is the stalk of `galoisSheaf K Ω 𝒢` (the restriction of `𝒢` to the Galois site) at its point,
with the discrete topology: restrict to finite continuous `Gal(Ω/K)`-sets, then take stalks. -/
def nonabelianH1EquivGalois :
    Sheaf.NonabelianH1 𝒢 ≃
      TauCeti.NonabelianH1 Gal(Ω/K)
        ((ContAction.point Gal(Ω/K)).GrpStalk (galoisSheaf K Ω 𝒢).obj) :=
  (nonabelianH1EquivGaloisSite K Ω 𝒢).trans (ContAction.nonabelianH1EquivStalk _)

/-- `nonabelianH1EquivGalois K Ω 𝒢` sends the class of an étale torsor to the class of the stalk
of its restriction to the Galois site. -/
@[simp]
lemma nonabelianH1EquivGalois_mk (P : Sheaf.Torsor 𝒢) :
    nonabelianH1EquivGalois K Ω 𝒢 (Sheaf.NonabelianH1.mk P) =
      (ContAction.torsorStalkSmoothTorsor (P.restrict _ (galoisSiteFunctor K Ω))).cls := by
  rw [nonabelianH1EquivGalois, Equiv.trans_apply, nonabelianH1EquivGaloisSite_mk,
    ContAction.nonabelianH1EquivStalk_mk]

end TauCeti.FiniteEtaleScheme
