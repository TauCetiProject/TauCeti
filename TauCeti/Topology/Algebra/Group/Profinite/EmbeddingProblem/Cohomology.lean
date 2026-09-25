/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.ElementaryAbelian
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Pullback
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# The continuous cohomology obstruction to a finite embedding problem

For `G → Q ← E` with abelian kernel `N`, conjugation gives a `Q`-action on `N`, restricted to
`G` along `π`. The obstruction is the class of the pullback extension in canonical continuous
`H²(G, N)`. It vanishes exactly when the embedding problem has a solution with open kernel.

If canonical continuous `H²(G, M)` vanishes for every finite discrete abelian `G`-module
annihilated by `p`, then `HasElementaryAbelianSolutions p G` holds. This is the cohomological
input for solvability of embedding problems with finite `p`-group kernel.
-/

public section

open scoped IsMulCommutative

namespace TauCeti

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

namespace FiniteEmbeddingProblem

variable (P : FiniteEmbeddingProblem.{u, v, u} G)
  [TopologicalSpace P.E] [DiscreteTopology P.E]
  [TopologicalSpace P.Q] [DiscreteTopology P.Q]
  (hcomm : ∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, x * y = y * x)

/-- The class of the pullback extension in canonical continuous `H²(G, ker α)`, with the
conjugation action restricted along `π`. -/
noncomputable def obstruction :
    haveI := P.isMulCommutative_ker hcomm
    letI := P.kernelAction hcomm
    continuousCohomology 2 (ofDiscreteModule ℤ G (Additive P.α.ker)) := by
  haveI := P.isMulCommutative_ker hcomm
  letI := P.kernelAction hcomm
  letI := P.continuousSMul_kernelAction hcomm
  exact ContCohomology.explicitH2AddEquivContinuousCohomology G (Additive P.α.ker)
    (P.pullbackExtension hcomm).contCohomologyClass

/-- The obstruction is the image of the pullback extension's cohomology class under the
comparison isomorphism from explicit continuous `H²` to canonical continuous `H²`. -/
theorem obstruction_def :
    P.obstruction hcomm =
      haveI := P.isMulCommutative_ker hcomm
      letI := P.kernelAction hcomm
      letI := P.continuousSMul_kernelAction hcomm
      ContCohomology.explicitH2AddEquivContinuousCohomology G (Additive P.α.ker)
        (P.pullbackExtension hcomm).contCohomologyClass :=
  (rfl)

/-- An embedding problem with abelian kernel has a solution exactly when its canonical
continuous cohomology obstruction vanishes. -/
theorem exists_isSolution_iff_obstruction_eq_zero :
    (∃ β : G →* P.E, P.IsSolution β) ↔ P.obstruction hcomm = 0 := by
  have := P.isMulCommutative_ker hcomm
  let := P.kernelAction hcomm
  let := P.continuousSMul_kernelAction hcomm
  let X := P.pullbackExtension hcomm
  let := P.compactSpace_pullback
  let e := ContCohomology.explicitH2AddEquivContinuousCohomology G (Additive P.α.ker)
  calc
    (∃ β : G →* P.E, P.IsSolution β) ↔
        (∃ s : X.toGroupExtension.Splitting, Continuous ⇑s) :=
      P.exists_splitting_iff_hasSolution.symm
    _ ↔ X.contCohomologyClass = 0 := by
      rw [ProfiniteGroupExtension.contCohomologyClass_def]
      exact X.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero
        X.continuous_inl X.continuous_rightHom X.inducesAction
    _ ↔ P.obstruction hcomm = 0 := by
      rw [obstruction_def]
      exact (AddEquiv.map_eq_zero_iff e).symm

/-- Vanishing of canonical continuous `H²` for the actual kernel module solves the embedding
problem. -/
theorem exists_isSolution_of_subsingleton_continuousCohomology_two
    (h : haveI := P.isMulCommutative_ker hcomm
      letI := P.kernelAction hcomm
      Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G (Additive P.α.ker)))) :
    ∃ β : G →* P.E, P.IsSolution β := by
  apply (P.exists_isSolution_iff_obstruction_eq_zero hcomm).mpr
  let := h
  exact Subsingleton.elim _ _

end FiniteEmbeddingProblem

/-- If canonical continuous `H²(G, M)` vanishes for every finite discrete abelian `G`-module
annihilated by `p`, then every finite embedding problem for `G` with commutative kernel killed
by `p` has a solution. For prime `p` these are the elementary abelian `p`-primary modules. -/
theorem hasElementaryAbelianSolutions_of_subsingleton_continuousCohomology_two {p : ℕ}
    (h : ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      [DistribMulAction G M] [ContinuousSMul G M], (∀ m : M, p • m = 0) →
        Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G M))) :
    HasElementaryAbelianSolutions p G := by
  apply hasElementaryAbelianSolutions_iff.mpr
  intro P hpow hcomm
  let : TopologicalSpace P.E := ⊥
  let : DiscreteTopology P.E := ⟨rfl⟩
  let : TopologicalSpace P.Q := ⊥
  let : DiscreteTopology P.Q := ⟨rfl⟩
  have := P.isMulCommutative_ker hcomm
  let := P.kernelAction hcomm
  let := P.continuousSMul_kernelAction hcomm
  apply P.exists_isSolution_of_subsingleton_continuousCohomology_two hcomm
  apply h (Additive P.α.ker)
  intro m
  rw [← ofMul_toMul m, ← ofMul_pow, ofMul_eq_zero]
  exact Subtype.ext (hpow m.toMul m.toMul.property)

end TauCeti
