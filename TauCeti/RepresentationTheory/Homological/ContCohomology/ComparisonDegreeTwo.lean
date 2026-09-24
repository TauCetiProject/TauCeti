/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# Naturality of the degree-two comparison

The isomorphism between explicit `H²` and Mathlib's continuous cohomology is natural for
compatible pairs. In particular, it transports restriction to a subgroup and maps of discrete
coefficient modules. These squares let calculations on continuous two-cocycles be read as
statements about the canonical cohomology object, as in the restriction formula for the
index-two Evens graph class.

The additive comparison and its compatible-pair naturality are in `CohomologyComparison.lean`.
Here the equations are stated on the discrete carriers of the explicit groups and the
`TopModuleCat ℤ` isomorphisms. For restriction the subgroup has to be compact, so the degree-two
comparison exists on both sides.

The identification of inhomogeneous and homogeneous continuous cohomology follows
J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The degree-two comparison in `TopModuleCat ℤ` commutes with pullback along a compatible
pair of a continuous group homomorphism and an equivariant coefficient map. -/
@[simp]
theorem explicitIso_map2
    (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction H N] [ContinuousSMul H N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : DiscreteH2 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 2
        ((explicitH2IsoContinuousCohomology G M).hom x) =
      (explicitH2IsoContinuousCohomology H N).hom
        ((discreteH2Equiv H N).symm
          (explicitMap2 G M H N φ f continuous_of_discreteTopology hf
            (discreteH2Equiv G M x))) := by
  rw [explicitH2IsoContinuousCohomology_hom_apply,
    explicitH2IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply]
  exact explicitH2AddEquivContinuousCohomology_map G M H N φ f hf
    (discreteH2Equiv G M x)

/-- The degree-two comparison transports explicit restriction to canonical restriction. -/
@[simp]
theorem explicitIso_res2 (S : Subgroup G) [CompactSpace S] (x : DiscreteH2 G M) :
    TauCeti.ContinuousCohomology.res S (ofDiscreteModule ℤ G M) 2
        ((explicitH2IsoContinuousCohomology G M).hom x) =
      (explicitH2IsoContinuousCohomology S M).hom
        ((discreteH2Equiv S M).symm
          (explicitRes2 G M S (discreteH2Equiv G M x))) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype S : S →* G)
      (AddMonoidHom.id M).toIntLinearMap (fun _ _ ↦ rfl) =
      𝟙 (TopRep.res (S.subtype : S →* G) (ofDiscreteModule ℤ G M)) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [TauCeti.ContinuousCohomology.res_def, explicitRes2_eq_explicitMap2, ← hpair]
  exact explicitIso_map2 G M S M (ContinuousMonoidHom.subgroupSubtype S)
    (AddMonoidHom.id M) (fun _ _ ↦ rfl) x

/-- The degree-two comparison transports a continuous equivariant coefficient map to the
canonical map induced by the same homomorphism. -/
@[simp]
theorem explicitIso_coeffMap2
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N) (x : DiscreteH2 G M) :
    TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m) 2
        ((explicitH2IsoContinuousCohomology G M).hom x) =
      (explicitH2IsoContinuousCohomology G N).hom
        ((discreteH2Equiv G N).symm
          (explicitCoeff2 G M f continuous_of_discreteTopology
            (discreteH2Equiv G M x))) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      f.toAddMonoidHom.toIntLinearMap (fun g m ↦ map_smul f g m) =
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [TauCeti.ContinuousCohomology.coeffMap_def, explicitCoeff2_eq_explicitMap2, ← hpair]
  exact explicitIso_map2 G M G N (ContinuousMonoidHom.id G) f.toAddMonoidHom
    (fun g m ↦ map_smul f g m) x

end TauCeti.ContCohomology
