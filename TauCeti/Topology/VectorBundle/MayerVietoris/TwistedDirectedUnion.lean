/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Relative
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
