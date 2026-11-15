/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Map.DegreeTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Cup products and change of group across universes

The compatible-pair map `TauCeti.ContCohomology.continuousCohomologyMap2` permits its source
and target groups to live in independent universes. This file proves that it preserves the
canonical cup product in bidegree `(1, 1)`, for intertwined coefficient pairings.

The degree-one arguments are written through the surjective explicit-to-canonical comparison.
Their pullbacks use the existing `TauCeti.ContCohomology.explicitMap1`; thus the theorem applies
to all canonical degree-one classes, without requiring a separate canonical degree-one map.
Both the cocycle formula and the class formula are given. These allow transport of cup
products along identifications of Galois groups, including upward universe lifts.

The constructions used here are the explicit cup naturality theorem
`TauCeti.ContCohomology.explicitMap2_explicitCup11`, the canonical cup comparison
`TauCeti.ContCohomology.explicitAddEquiv_cup11`, and the compatible-pair degree-two map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.2):
  naturality of cup products in compatible coefficient maps.
-/

public section

namespace TauCeti.ContCohomology

universe u v

variable (G M N P : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [ContinuousSMul G N]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
  [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)
  (H M' N' P' : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H]
  [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
  [DistribMulAction H M'] [ContinuousSMul H M']
  [AddCommGroup N'] [TopologicalSpace N'] [DiscreteTopology N']
  [DistribMulAction H N'] [ContinuousSMul H N']
  [AddCommGroup P'] [TopologicalSpace P'] [DiscreteTopology P']
  [DistribMulAction H P'] [ContinuousSMul H P']
  (μ' : M' →+ N' →+ P')
  (hequiv' : ∀ (h : H) (m : M') (n : N'), μ' (h • m) (h • n) = h • μ' m n)
  (φ : H →ₜ* G) (fM : M →+ M') (fN : N →+ N') (fP : P →+ P')
  (hfM : ∀ (h : H) (m : M), fM (φ h • m) = h • fM m)
  (hfN : ∀ (h : H) (n : N), fN (φ h • n) = h • fN n)
  (hfP : ∀ (h : H) (p : P), fP (φ h • p) = h • fP p)
  (hpair : ∀ (m : M) (n : N), fP (μ m n) = μ' (fM m) (fN n))

include hpair in
/-- Pullback of a canonical cup cocycle is the cup of the pulled-back one-cocycles,
with source and target groups in independent universes. -/
theorem homogeneousCocyclesMap2_cup11 (a : Z1 G M) (b : Z1 G N) :
    homogeneousCocyclesMap2 G P H P' φ fP hfP
        ((ofDiscreteModulePairing μ hequiv).cupCocycles 1 1
          (cocycleEquiv1 G M a) (cocycleEquiv1 G N b)) =
      (ofDiscreteModulePairing μ' hequiv').cupCocycles 1 1
        (cocycleEquiv1 H M' (cocyclesMap1 G M H M' φ fM continuous_of_discreteTopology hfM a))
        (cocycleEquiv1 H N' (cocyclesMap1 G N H N' φ fN continuous_of_discreteTopology hfN b)) := by
  rw [← cocycleEquiv2_cup11, homogeneousCocyclesMap2_cocycleEquiv2,
    ← cocycleEquiv2_cup11]
  exact congrArg (cocycleEquiv2 H P')
    (cocyclesMap2_cup11 G M N P μ continuous_of_discreteTopology hequiv
      H M' N' P' μ' continuous_of_discreteTopology hequiv' φ fM fN fP
      continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
      hfM hfN hfP hpair a b)

include hpair in
/-- The cross-universe compatible-pair map on canonical second cohomology preserves the
`(1, 1)` cup product. The degree-one pullbacks are expressed through the explicit comparison,
which is an equivalence and therefore covers every canonical degree-one class. -/
theorem continuousCohomologyMap2_cup11 (a : H1 G M) (b : H1 G N) :
    continuousCohomologyMap2 G P H P' φ fP hfP
        ((ofDiscreteModulePairing μ hequiv).cup 1 1
          (explicitH1AddEquivContinuousCohomology G M a)
          (explicitH1AddEquivContinuousCohomology G N b)) =
      (ofDiscreteModulePairing μ' hequiv').cup 1 1
        (explicitH1AddEquivContinuousCohomology H M'
          (explicitMap1 G M H M' φ fM continuous_of_discreteTopology hfM a))
        (explicitH1AddEquivContinuousCohomology H N'
          (explicitMap1 G N H N' φ fN continuous_of_discreteTopology hfN b)) := by
  rw [explicitAddEquiv_cup11, explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2,
    explicitAddEquiv_cup11]
  exact congrArg (explicitH2AddEquivContinuousCohomology H P')
    (explicitMap2_explicitCup11 G M N P μ continuous_of_discreteTopology hequiv
      H M' N' P' μ' continuous_of_discreteTopology hequiv' φ fM fN fP
      continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
      hfM hfN hfP hpair a b)

end TauCeti.ContCohomology
