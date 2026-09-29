/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.ElementaryAbelian
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Extension
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

In the other direction, let `G` be a projective pro-`p` group (`TauCeti.IsProjective`). Every
profinite extension of `G` by a pro-`p` group splits
(`GroupExtension.exists_splitting_continuous_of_isProjective`), and read through the
classification of profinite extensions by continuous `H²` this is the vanishing of the second
continuous cohomology of `G` with coefficients in any profinite pro-`p` abelian `G`-module `M`
(`TauCeti.IsProjective.subsingleton_H2`): every class of the explicit `H²(G, M)` is the class of a
profinite extension of `G` by `M`, and the class of a split extension is zero. The extension
dictionary reads its abelian kernel multiplicatively, so the vanishing is first stated for a
`CommGroup` `M`; an `AddCommGroup` `M` is `Additive (Multiplicative M)`, and
`TauCeti.IsProjective.subsingleton_H2_of_isPPrimaryTorsion` restates the vanishing for it.
Transported through the degree-two comparison with Mathlib's `continuousCohomology`, the
statement takes its canonical form for a finite discrete `p`-primary `G`-module
(`TauCeti.IsProjective.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`), which is the
input to `cd_p G ≤ 1` in
`TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension`. The vanishing
of `H²` of a free pro-`p` group in `TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology` is
the instance of these statements at `freeProP p X`.

## Main results

* `TauCeti.FiniteEmbeddingProblem.obstruction`,
  `TauCeti.FiniteEmbeddingProblem.exists_isSolution_iff_obstruction_eq_zero`: the class of the
  pullback extension in `H²(G, ker α)` vanishes exactly when the embedding problem is solvable.
* `TauCeti.hasElementaryAbelianSolutions_of_subsingleton_continuousCohomology_two`: vanishing of
  `H²` on finite discrete modules killed by `p` solves the embedding problems with elementary
  abelian `p`-kernel.
* `TauCeti.IsProjective.subsingleton_H2`: **`H²(G, M) = 0`** for `G` projective pro-`p` and `M` a
  profinite pro-`p` abelian `G`-module.
* `TauCeti.IsProjective.subsingleton_H2_of_isPPrimaryTorsion`: the same for a profinite
  `p`-primary torsion abelian `G`-module written additively.
* `TauCeti.IsProjective.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`: the same in
  Mathlib's continuous cohomology, for a finite discrete `p`-primary `G`-module.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.4 and §5.9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.6.
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

/-! ### The vanishing of `H²` of a projective pro-`p` group -/

namespace IsProjective

open ContCohomology

variable {p : ℕ}

section Cohomology

variable {M : Type v} [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [CompactSpace M]
  [TotallyDisconnectedSpace M] [MulDistribMulAction G M] [ContinuousSMul G M]

/-- **`H²` of a projective pro-`p` group vanishes.** For `G` projective pro-`p` and `M` a profinite
pro-`p` abelian group with a continuous action of `G`, the explicit second continuous cohomology
group `H²(G, M)` is zero: every class is the class of a profinite extension of `G` by `M`, which
splits. -/
theorem subsingleton_H2 (hproj : IsProjective.{u, max u v, u} p G) (hG : IsProP p G)
    (hM : IsProP p M) : Subsingleton (H2 G (Additive M)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨Y, rfl⟩ := ProfiniteGroupExtension.exists_contCohomologyClass_eq c
  rw [ProfiniteGroupExtension.contCohomologyClass_def,
    ← Y.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]
  exact Y.toGroupExtension.exists_splitting_continuous_of_isProjective Y.continuous_inl
    Y.continuous_rightHom hM hG hproj

end Cohomology

section Additive

variable {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [TotallyDisconnectedSpace M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **`H²` of a projective pro-`p` group vanishes, additive form.** For `G` projective pro-`p` and
`M` a profinite `p`-primary torsion abelian group, written additively, with a continuous action of
`G`, the explicit second continuous cohomology group `H²(G, M)` is zero. -/
theorem subsingleton_H2_of_isPPrimaryTorsion (hproj : IsProjective.{u, max u v, u} p G)
    (hG : IsProP p G) (hM : IsPPrimaryTorsion p M) : Subsingleton (H2 G M) :=
  -- `Additive (Multiplicative M)` is `M` with the same instances, so the multiplicative statement
  -- applies as it stands; `isPPrimaryTorsion_additive_iff` reads the hypothesis the same way.
  hproj.subsingleton_H2 hG (M := Multiplicative M)
    (IsPGroup.isProP ((isPPrimaryTorsion_additive_iff (M := Multiplicative M)).1 hM))

end Additive

/-- **`H²` of a projective pro-`p` group vanishes on finite coefficients**, in Mathlib's continuous
cohomology: for `G` projective pro-`p` and `M` a finite discrete `p`-primary torsion abelian group
with a continuous action of `G`, the canonical `continuousCohomology 2` of the topological
representation attached to `M` is zero. -/
theorem subsingleton_continuousCohomology_two_of_isPPrimaryTorsion
    (hproj : IsProjective.{u, u, u} p G) (hG : IsProP p G) (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M] [DistribMulAction G M]
    [ContinuousSMul G M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G M)) :=
  haveI := hproj.subsingleton_H2_of_isPPrimaryTorsion hG hM
  (explicitH2AddEquivContinuousCohomology G M).toEquiv.symm.subsingleton

end IsProjective

end TauCeti
