/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars
import TauCeti.RepresentationTheory.Continuous.TopRep.EqToHom

/-!
# The cup product does not see the scalars

Let `P : TopPairing X Y Z` be a coefficient pairing of topological representations over a
topological commutative ring `R`. Forgetting the scalars gives a pairing `P.restrictScalarsInt` of
the underlying additive representations, with the same underlying biadditive map, and continuous
cohomology does not see the scalars either
(`TauCeti.ContCohomology.restrictScalarsIntEquiv`). This file proves that the two are compatible
in bidegree `(1, 1)`: the cup product of `P.restrictScalarsInt` is the cup product of `P`, read
through `restrictScalarsIntEquiv` (`TauCeti.TopPairing.cup_one_one_restrictScalarsInt`), and
already on one-cocycles (`TauCeti.TopPairing.cupCocycles_one_one_restrictScalarsInt`). The reason
is that both cup products are the Alexander–Whitney formula on the same iterated function spaces,
and the identification of the cocycles does not change their values.

The consequence this is for: the explicit low-degree cup products of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product`, given by cochain formulas on
inhomogeneous cocycles, agree with the canonical cup product of a pairing of *discrete*
representations over any scalars, under the comparison isomorphisms
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`
(`TauCeti.TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete`). The
agreement for the pairings `TauCeti.ofDiscreteModulePairing` of discrete `ℤ`-modules is
`TauCeti.ContCohomology.explicitAddEquiv_cup11`; the statement here removes the restriction to
`ℤ`, which is what the coefficient objects of the pro-`p` theory, objects of `TopRep (ZMod p) G`,
need in order to compute their cup product on explicit cocycles.

## Main definitions

* `TauCeti.TopPairing.restrictScalarsInt`: the coefficient pairing of the underlying additive
  representations.

## Main results

* `TauCeti.TopPairing.cupCocycles_one_one_restrictScalarsInt`,
  `TauCeti.TopPairing.cup_one_one_restrictScalarsInt`: **the cup product does not see the
  scalars**, on one-cocycles and on cohomology in bidegree `(1, 1)`.
* `TauCeti.TopPairing.cup_one_one_ofDiscreteModuleRestrictScalarsInt`: for discrete
  representations, the cup product of the associated pairing of discrete `ℤ`-modules is the cup
  product of `P`, under `TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv`.
* `TauCeti.TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete`: **the
  canonical cup product of a pairing of discrete representations over any scalars is the explicit
  `(1,1)` cup product on their carriers**, `(a ⌣ b) (g, h) = μ (a g) (g • b h)`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, for the
  Alexander–Whitney formula.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, for the inhomogeneous cup product formulas.
-/

public section

namespace TauCeti

open CategoryTheory TopRep TauCeti.ContCohomology _root_.ContinuousCohomology
open TauCeti.ContinuousCohomology (coeffMap coeffMap_eqToHom)

universe u v w

namespace TopPairing

section Pairing

variable {R : Type u} [CommRing R] [TopologicalSpace R] {G : Type v} [Monoid G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-- **The coefficient pairing of the underlying additive representations**: the pairing `P` with
its scalars forgotten, an `ℤ`-bilinear pairing with the same values. -/
def restrictScalarsInt :
    TopPairing (TopRep.restrictScalarsInt.obj X) (TopRep.restrictScalarsInt.obj Y)
      (TopRep.restrictScalarsInt.obj Z) where
  bil := P.bil.restrictScalars₁₂ ℤ ℤ
  cont := P.cont
  -- the operators of `restrictScalarsInt.obj _` are those of the original representations
  equivariant g x y :=
    ((congrArg₂ (fun a b ↦ P.bil a b) (restrictScalarsInt_obj_ρ_apply X g x)
      (restrictScalarsInt_obj_ρ_apply Y g y)).trans (P.equivariant g x y)).trans
      (restrictScalarsInt_obj_ρ_apply Z g _).symm

/-- The pairing with its scalars forgotten has the values of `P`. -/
-- The arguments are typed by the carriers of `restrictScalarsInt.obj _`, where the cup product of
-- `P.restrictScalarsInt` evaluates it.
@[simp]
theorem restrictScalarsInt_bil (x : (TopRep.restrictScalarsInt.obj X).V)
    (y : (TopRep.restrictScalarsInt.obj Y).V) :
    P.restrictScalarsInt.bil x y = P.bil x y :=
  (rfl)

end Pairing

section RestrictScalars

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-- **The cup product of one-cocycles does not see the scalars**: under
`TauCeti.ContCohomology.cocyclesRestrictScalarsIntEquiv`, the cup product of two one-cocycles for
the pairing of the underlying additive representations is their cup product for `P`. -/
theorem cupCocycles_one_one_restrictScalarsInt (a : cocycles (TopRep.restrictScalarsInt.obj X) 1)
    (b : cocycles (TopRep.restrictScalarsInt.obj Y) 1) :
    cocyclesRestrictScalarsIntEquiv Z (1 + 1) (P.restrictScalarsInt.cupCocycles 1 1 a b) =
      P.cupCocycles 1 1 (cocyclesRestrictScalarsIntEquiv X 1 a)
        (cocyclesRestrictScalarsIntEquiv Y 1 b) := by
  refine (homogeneousCochains Z).iCycles_injective (1 + 1) (Subtype.ext ?_)
  ext g₀ g₁ g₂
  -- both sides evaluated at `(g₀, g₁, g₂)` are `μ (a g₀ g₁) (b g₁ g₂)`: the identifications do not
  -- change the values of the cocycles, and both cup products are the Alexander–Whitney formula
  rw [iCycles_cocyclesRestrictScalarsIntEquiv_two_apply, iCycles_cupCocycles, iCycles_cupCocycles,
    coe_cupCochain, coe_cupCochain, resolutionCupPairing_one_one_apply,
    resolutionCupPairing_one_one_apply, restrictScalarsInt_bil,
    iCycles_cocyclesRestrictScalarsIntEquiv_one_apply,
    iCycles_cocyclesRestrictScalarsIntEquiv_one_apply]

/-- **The cup product in bidegree `(1, 1)` does not see the scalars**: under
`TauCeti.ContCohomology.restrictScalarsIntEquiv`, the cup product of the pairing of the underlying
additive representations is the cup product of `P`. -/
theorem cup_one_one_restrictScalarsInt
    (a : continuousCohomology 1 (TopRep.restrictScalarsInt.obj X))
    (b : continuousCohomology 1 (TopRep.restrictScalarsInt.obj Y)) :
    restrictScalarsIntEquiv Z (1 + 1) (P.restrictScalarsInt.cup 1 1 a b) =
      P.cup 1 1 (restrictScalarsIntEquiv X 1 a) (restrictScalarsIntEquiv Y 1 b) := by
  obtain ⟨a, rfl⟩ :=
    (homogeneousCochains (TopRep.restrictScalarsInt.obj X)).homologyπ_surjective 1 a
  obtain ⟨b, rfl⟩ :=
    (homogeneousCochains (TopRep.restrictScalarsInt.obj Y)).homologyπ_surjective 1 b
  rw [cup_π, restrictScalarsIntEquiv_π, restrictScalarsIntEquiv_π, restrictScalarsIntEquiv_π,
    cup_π, cupCocycles_one_one_restrictScalarsInt]

end RestrictScalars

/-! ### Discrete representations over any scalars -/

section OfDiscrete

-- The explicit comparisons of `ContCohomology.CohomologyComparison` put the group and the carriers
-- in one universe.
variable {k : Type w} [CommRing k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{u} k G} [DiscreteTopology X.V] [DiscreteTopology Y.V] [DiscreteTopology Z.V]

attribute [local instance] TopRep.distribMulAction

variable (P : TopPairing X Y Z) (μ : X.V →+ Y.V →+ Z.V) (hμ : ∀ x y, μ x y = P.bil x y)
include hμ

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology X.V] [DiscreteTopology Y.V]
  [DiscreteTopology Z.V] in
/-- A biadditive map with the values of `P` is equivariant for the actions read off from the
representations. -/
theorem equivariant_of_eq (g : G) (x : X.V) (y : Y.V) : μ (g • x) (g • y) = g • μ x y := by
  rw [hμ, hμ, TopRep.distribMulAction_smul, TopRep.distribMulAction_smul,
    TopRep.distribMulAction_smul, P.equivariant]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Under the identification of the underlying additive representation of a discrete `X` with the
discrete `ℤ`-module `X.V`, the pairing of `μ` on discrete `ℤ`-modules is the pairing of `P` with
its scalars forgotten: the three carriers are unchanged by the transports, so this is `hμ`. -/
theorem eqToHom_ofDiscreteModulePairing_bil (x : X.V) (y : Y.V) :
    eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj Z)
        ((ofDiscreteModulePairing μ (P.equivariant_of_eq μ hμ)).bil x y) =
      P.restrictScalarsInt.bil (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj X) x)
        (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj Y) y) :=
  -- Assembled as a term: the transported value is typed at `Z.V`, which is the carrier of
  -- `ofDiscreteModule ℤ G Z.V` only after unfolding, so `rw` does not see the transports. The
  -- three casts are along equalities of a type with itself, so they vanish.
  ((TopRep.eqToHom_hom_apply (ofDiscreteModule_eq_restrictScalarsInt_obj Z) _).trans
    ((congrArg (cast _) (ofDiscreteModulePairing_bil_apply μ (P.equivariant_of_eq μ hμ) x y)).trans
      (hμ x y))).trans
    (congrArg₂ (fun a b ↦ P.restrictScalarsInt.bil a b)
      (TopRep.eqToHom_hom_apply (ofDiscreteModule_eq_restrictScalarsInt_obj X) x).symm
      (TopRep.eqToHom_hom_apply (ofDiscreteModule_eq_restrictScalarsInt_obj Y) y).symm)

/-- **For discrete representations, the cup product of the pairing of discrete `ℤ`-modules is the
cup product of `P`**, under `TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv`, in
bidegree `(1, 1)`. -/
theorem cup_one_one_ofDiscreteModuleRestrictScalarsInt
    (a : continuousCohomology 1 (ofDiscreteModule ℤ G X.V))
    (b : continuousCohomology 1 (ofDiscreteModule ℤ G Y.V)) :
    ofDiscreteModuleRestrictScalarsIntEquiv Z (1 + 1)
        ((ofDiscreteModulePairing μ (P.equivariant_of_eq μ hμ)).cup 1 1 a b) =
      P.cup 1 1 (ofDiscreteModuleRestrictScalarsIntEquiv X 1 a)
        (ofDiscreteModuleRestrictScalarsIntEquiv Y 1 b) := by
  -- transport along the equality of objects, a coefficient map, then forget the scalars
  have key := (ofDiscreteModulePairing μ (P.equivariant_of_eq μ hμ)).cup_coeffMap
    P.restrictScalarsInt (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj X))
    (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj Y))
    (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj Z))
    (P.eqToHom_ofDiscreteModulePairing_bil μ hμ) 1 1 a b
  rw [coeffMap_eqToHom, coeffMap_eqToHom, coeffMap_eqToHom] at key
  rw [ofDiscreteModuleRestrictScalarsIntEquiv_apply X 1 a,
    ofDiscreteModuleRestrictScalarsIntEquiv_apply Y 1 b,
    ofDiscreteModuleRestrictScalarsIntEquiv_apply Z (1 + 1), key, cup_one_one_restrictScalarsInt]

variable [ContinuousSMul G X.V] [ContinuousSMul G Y.V] [ContinuousSMul G Z.V]
  [LocallyCompactSpace G]

/-- **The canonical cup product of a pairing of discrete representations over any scalars is the
explicit `(1,1)` cup product on their carriers.** Under the comparisons
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`, the cup product `TauCeti.TopPairing.cup`
in bidegree `(1, 1)` is `TauCeti.ContCohomology.explicitCup11` for the biadditive map `μ` with the
values of `P`, `(a ⌣ b) (g, h) = μ (a g) (g • b h)`. -/
theorem cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete (x : H1 G X.V) (y : H1 G Y.V) :
    P.cup 1 1 (X.explicitH1AddEquivContinuousCohomologyOfDiscrete x)
        (Y.explicitH1AddEquivContinuousCohomologyOfDiscrete y) =
      Z.explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitCup11 G X.V Y.V Z.V μ continuous_of_discreteTopology (P.equivariant_of_eq μ hμ)
          x y) :=
  -- Assembled as a term: rewriting with the evaluation lemmas of the comparisons makes `rw` try
  -- to unify the two comparisons, which unfolds the cohomology groups.
  (congrArg₂ (fun a b ↦ P.cup 1 1 a b)
    (TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply X x)
    (TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply Y y)).trans <|
    ((P.cup_one_one_ofDiscreteModuleRestrictScalarsInt μ hμ _ _).symm.trans
      (congrArg (ofDiscreteModuleRestrictScalarsIntEquiv Z (1 + 1))
        (explicitAddEquiv_cup11 G X.V Y.V Z.V μ (P.equivariant_of_eq μ hμ) x y))).trans
      (TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply Z _).symm

end OfDiscrete

end TopPairing

end TauCeti
