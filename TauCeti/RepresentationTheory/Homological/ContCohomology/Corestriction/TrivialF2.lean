/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# Corestriction with trivial `𝔽₂` coefficients

For an open subgroup `U` of finite index in a profinite group `G`, all-degree corestriction
`TauCeti.ContinuousCohomology.corestriction` is stated for the coefficient object
`ofDiscreteModule ℤ U M` of a discrete `G`-module `M`. With `M` the carrier of the trivial `𝔽₂`
object, both ends of that map are the trivial `𝔽₂` objects `trivialF2 U` and `trivialF2 G`, but
only up to propositional equalities of coefficient objects. This file reads corestriction through
those equalities, giving the map `Hⁿ(U, 𝔽₂) ⟶ Hⁿ(G, 𝔽₂)` that pairs with the trivial-coefficient
restriction `TauCeti.trivialF2ResMap`, and transports the identity `cor ∘ res = [G : U]`.

## Main definitions

* `TauCeti.trivialF2CorMap`: corestriction `Hⁿ(U, 𝔽₂) ⟶ Hⁿ(G, 𝔽₂)` with trivial coefficients.

## Main results

* `TauCeti.ofDiscreteModule_subgroup_trivialF2`: over a subgroup `U`, the coefficient dictionary
  recovers the trivial `𝔽₂` object of `U`.
* `TauCeti.trivialF2ResMap_comp_trivialF2CorMap`, `TauCeti.trivialF2CorMap_trivialF2ResMap`:
  restriction followed by corestriction is multiplication by the index `[G : U]`.
* `TauCeti.trivialF2CorMap_explicitH1AddEquivContinuousCohomology`: in degree one, corestriction
  is the explicit transversal formula on cocycles.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.7).
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the carrier of the trivial `𝔽₂` object, which is smooth discrete. -/
local instance continuousSMul_trivialF2 : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [U.FiniteIndex] in
/-- Over a subgroup `U`, the coefficient object of the carrier of `trivialF2 G` is `trivialF2 U`:
it is the restriction of `ofDiscreteModule ℤ G (trivialF2 G).V = trivialF2 G`
(`res_ofDiscreteModule`, `ofDiscreteModule_trivialF2`, `res_trivialF2`). This types the transport
of an operation stated for `ofDiscreteModule ℤ U M`, such as corestriction, to trivial `𝔽₂`
coefficients. -/
-- Not `@[simp]`: this is an equation between objects, used to type transports rather than to
-- rewrite inside them.
theorem ofDiscreteModule_subgroup_trivialF2 :
    ofDiscreteModule ℤ U (trivialF2 G).V = trivialF2 U := by
  rw [← res_ofDiscreteModule, ofDiscreteModule_trivialF2, res_trivialF2]

/-- **Corestriction with trivial `𝔽₂` coefficients**, `Hⁿ(U, 𝔽₂) ⟶ Hⁿ(G, 𝔽₂)`, for an open
finite-index subgroup `U` of a profinite group `G`: all-degree corestriction
`TauCeti.ContinuousCohomology.corestriction` at the carrier of `trivialF2 G`, read through the
identifications of both coefficient objects with the trivial `𝔽₂` objects. -/
noncomputable def trivialF2CorMap (n : ℕ) :
    continuousCohomology n (trivialF2 U) ⟶ continuousCohomology n (trivialF2 G) :=
  eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_subgroup_trivialF2 G U).symm) ≫
    ContinuousCohomology.corestriction U (trivialF2 G).V hU n ≫
      eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_trivialF2 G))

/-- The defining equation of corestriction with trivial `𝔽₂` coefficients. -/
theorem trivialF2CorMap_def (n : ℕ) :
    trivialF2CorMap G U hU n =
      eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_subgroup_trivialF2 G U).symm) ≫
        ContinuousCohomology.corestriction U (trivialF2 G).V hU n ≫
          eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_trivialF2 G)) :=
  (rfl)

/-- **`cor ∘ res = [G : U]` with trivial `𝔽₂` coefficients**, in every degree (NSW (1.5.7)). -/
theorem trivialF2ResMap_comp_trivialF2CorMap (n : ℕ) :
    trivialF2ResMap G U n ≫ trivialF2CorMap G U hU n =
      U.index • 𝟙 (continuousCohomology n (trivialF2 G)) := by
  -- Generalize the target coefficient object, so that its identification with
  -- `ofDiscreteModule ℤ G (trivialF2 G).V` can be substituted away; the claim is then the general
  -- identity `res_comp_corestriction`.
  have key : ∀ (X : TopRep ℤ G) (hX : ofDiscreteModule ℤ G (trivialF2 G).V = X),
      ContinuousCohomology.res U X n ≫
          eqToHom (congrArg (fun Z => continuousCohomology n (TopRep.res U.subtype Z))
            hX.symm) ≫
          ContinuousCohomology.corestriction U (trivialF2 G).V hU n ≫
            eqToHom (congrArg (continuousCohomology n) hX) =
        U.index • 𝟙 (continuousCohomology n X) := by
    rintro X rfl
    simp only [eqToHom_refl, Category.id_comp]
    -- Not `rw [Category.comp_id]`: the middle objects `TopRep.res U.subtype (ofDiscreteModule …)`
    -- and `ofDiscreteModule ℤ U …` agree only by unfolding (`res_ofDiscreteModule`), so the goal
    -- is not type-correct at the transparency `rw` abstracts at.
    exact (congrArg (ContinuousCohomology.res U _ n ≫ ·) (Category.comp_id _)).trans
      (ContinuousCohomology.res_comp_corestriction U (trivialF2 G).V hU n)
  rw [trivialF2ResMap_def, trivialF2CorMap_def, Category.assoc, eqToHom_trans_assoc]
  exact key _ (ofDiscreteModule_trivialF2 G)

/-- **`cor (res x) = [G : U] • x`** with trivial `𝔽₂` coefficients, for every class
`x ∈ Hⁿ(G, 𝔽₂)`. -/
@[simp]
theorem trivialF2CorMap_trivialF2ResMap (n : ℕ)
    (x : continuousCohomology n (trivialF2 G)) :
    trivialF2CorMap G U hU n (trivialF2ResMap G U n x) = U.index • x := by
  have h := ConcreteCategory.congr_hom (trivialF2ResMap_comp_trivialF2CorMap G U hU n) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

open ContCohomology in
/-- **Degree-one corestriction with trivial `𝔽₂` coefficients is the explicit transversal
formula.** A class of `H¹(U, 𝔽₂)` presented by an explicit cocycle valued in the carrier of
`trivialF2 G` is sent to the class of its explicit corestriction
`TauCeti.ContCohomology.explicitCor1`, both read in continuous cohomology through the
identifications of the coefficient objects with the trivial `𝔽₂` objects. -/
theorem trivialF2CorMap_explicitH1AddEquivContinuousCohomology (x : H1 U (trivialF2 G).V) :
    trivialF2CorMap G U hU 1
        ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_subgroup_trivialF2 G U))).hom
          (explicitH1AddEquivContinuousCohomology U (trivialF2 G).V x)) =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
        (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V
          (explicitCor1 G (trivialF2 G).V U hU x)) := by
  rw [trivialF2CorMap_def, ← ConcreteCategory.comp_apply, ← Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, ConcreteCategory.comp_apply,
    ContinuousCohomology.explicitH1AddEquivContinuousCohomology_corestriction]

end TauCeti
