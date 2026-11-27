/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Relative
public import TauCeti.Topology.VectorBundle.MayerVietoris.Twisted
public import TauCeti.Topology.VectorBundle.ZeroSection
import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Twisted homology of the Thom pair over finite trivializing unions

Let `E → B` be a fibre bundle whose fibres have a zero, with Thom pair `(E, E₀)`, `E₀` the
complement of the zero section, and let `L` be a local coefficient system on the total space. Every
compact subset of the total space projects into finitely many of the chosen trivializing open sets
(`IsCompact.exists_finset_subset_preimage_biUnion_baseSet`). So the relative homology `Hₖ(E, E₀; L)`
with coefficients in `L` is the filtered colimit, over finite sets `s` of base points, of the
relative homology of the Thom pairs `(E|_W, E₀|_W)` over the unions `W` of the trivializing sets at
the points of `s` (`TauCeti.isColimitThomPairFiniteTrivializingUnionTwistedHomologyCocone`), with
`L` restricted to each.

This is the local-coefficient form of the constant-coefficient colimit presentation
`TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`: the passage from
finite unions of trivializing sets to an arbitrary base in Milnor and Stasheff's proof of the Thom
isomorphism, for homology with local coefficients.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, the proof of Theorem 10.4 (finite trivializing unions and directed unions
  of chains).
* A. Hatcher, *Algebraic Topology*, Section 3.H (homology with local coefficients).
-/

public noncomputable section

open Bundle CategoryTheory Set

universe u w w'

namespace TauCeti

section Comparison

variable {B : Type w} {F : Type*} {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  {R : Type u} [Ring R] (L : LocalCoefficientSystem.{u, w, max w w'} R (TopCat.of (TotalSpace F E)))

/-- Comparing `TauCeti.thomPairOverTwistedHomologyMap` with
`TopPair.restrictPreimagePairTwistedChainComplexMap` in homology along the equality of coefficient
systems. -/
@[reassoc]
theorem thomPairOverTwistedHomologyMap_comp_eqToHom {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverTwistedHomologyMap L h n ≫
        (thomPairOver F E W').twistedHomologyCoefficientMap
          (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
            (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) W')) n =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
            (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) W)) n ≫
        HomologicalComplex.homologyMap (TopPair.restrictPreimagePairTwistedChainComplexMap
          (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) h) n := by
  rw [thomPairOverTwistedHomologyMap_def]
  exact TopPair.subsetPairTwistedHomologyMap_comp_eqToHom (X := TopCat.of (TotalSpace F E))
    (zeroSectionCompl F E) L (π F E) h n

/-- The twisted homology of the Thom pair over `Set.univ`, as a pair of subsets of the total space,
is isomorphic to the twisted homology of the Thom pair `(E, E₀)`. -/
def thomPairOverTwistedHomologyUnivIso (n : ℕ) :
    thomPairOverTwistedHomology L univ n ≅ (thomPair F E).twistedHomology L n :=
  have := TopCat.isIso_restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) (S := univ) fun _ ↦ trivial
  have := LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_isIso L
    (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
      (zeroSectionCompl F E) univ) n
  (thomPairOver F E univ).twistedHomologyCoefficientIso
      (eqToIso (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) univ)) n ≪≫
    asIso (TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) univ) L n)

/-- The forward morphism of `TauCeti.thomPairOverTwistedHomologyUnivIso` is the coefficient
transport followed by the homology map of `TopCat.restrictPreimagePairMap`. -/
@[simp]
theorem thomPairOverTwistedHomologyUnivIso_hom (n : ℕ) :
    (thomPairOverTwistedHomologyUnivIso L n).hom =
      (thomPairOver F E univ).twistedHomologyCoefficientMap
          (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
            (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) univ)) n ≫
        TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) univ) L n := by
  rw [thomPairOverTwistedHomologyUnivIso, Iso.trans_hom, asIso_hom]
  -- `erw`: `(thomPairOver F E univ).fst` matches `TopCat.of ↥(π F E ⁻¹' univ)` after unfolding.
  erw [TopPair.twistedHomologyCoefficientIso_hom, eqToIso.hom]

/-- Restriction from `W` to `Set.univ`, followed by `TauCeti.thomPairOverTwistedHomologyUnivIso`,
is the inclusion of the pair over `W` into `(E, E₀)` up to coefficient transport. -/
@[reassoc]
theorem thomPairOverTwistedHomologyMap_subset_univ_comp_thomPairOverTwistedHomologyUnivIso_hom
    (W : Set B) (n : ℕ) :
    thomPairOverTwistedHomologyMap L (subset_univ W) n ≫
        (thomPairOverTwistedHomologyUnivIso L n).hom =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
            (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) W)) n ≫
        TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) L n := by
  rw [thomPairOverTwistedHomologyUnivIso_hom, ← Category.assoc,
    thomPairOverTwistedHomologyMap_comp_eqToHom, Category.assoc]
  congr 1
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (TopPair.restrictPreimagePairTwistedChainComplexMap_comp_twistedChainComplexMap
        (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E) L (π F E) (subset_univ W)))

end Comparison

variable {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {R : Type u} [Ring R] (L : LocalCoefficientSystem.{u, w, max w w'} R (TopCat.of (TotalSpace F E)))
  (k : ℕ)

/-- **Twisted homology of the Thom pair over finite trivializing unions.** For a local coefficient
system `L` on the total space, `Hₖ(E, E₀; L)` is the filtered colimit of the groups
`Hₖ(E|_W, E₀|_W; L)` over the unions `W` of the trivializing sets at the points of finite subsets
of the base, with `L` restricted to each. -/
def isColimitThomPairFiniteTrivializingUnionTwistedHomologyCocone :
    Limits.IsColimit (TopPair.restrictPreimagePairTwistedHomologyCocone (zeroSectionCompl F E) L
      (π F E) (S := fun s : Finset B ↦ ⋃ b ∈ s, (trivializationAt F E b).baseSet)
      (fun _ _ h ↦ biUnion_subset_biUnion_left h) k) :=
  TopPair.isColimitRestrictPreimagePairTwistedHomologyCocone _ L _ _ k
    fun _ hK ↦ hK.exists_finset_subset_preimage_biUnion_baseSet

end TauCeti
