/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction.Invariance
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass

/-!
# Non-formal quartic deformations of zigzag algebras

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). A quartic loop deformation
`TauCeti.zigzagLoopAInfinityAlgebra` is a minimal, strictly unital `A∞` structure on `Z` with the
same grading and product, `m₃ = 0`, and `m₄` a linear combination of loop operations of closed
walks. This file shows that such deformations can be **nontrivial modulo `A∞` isomorphism**, and
hence that `Z` is in general not intrinsically formal.

This combines two results. First, when `2` is invertible, a minimal `A∞`
structure with `m₃ = 0` which is `A∞` isomorphic to the graded algebra it deforms has a quartic
operation which is a Hochschild coboundary, even when the isomorphism has a nonzero quadratic
component
(`IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four` in
`TauCeti.AInfinityAlgebra`).
Second, when some vertex `v` of `G` has four distinct neighbours, the loop operation of a single
closed walk through two of them, of the shape `n₃ → v → n₀ → v → n₃`, is not a Hochschild
coboundary
(`TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single`).
Hence the loop deformation with coefficient one on that walk is not formal, equivalently not
`A∞` isomorphic to the strict zigzag algebra
(`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single`), and the strict zigzag algebra is not
intrinsically formal (`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra`). For
the affine `D₄` graph the walk is Liu--Wang's `β₄ α₁ β₁ α₄`; see
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD4`.

The results assume that `2` is invertible, as the invariance of the quartic obstruction does. They
cover the graphs with a vertex of valency at least four. In particular they cover the finite trees
containing the affine `D₄` graph, but not the other trees which are not Dynkin diagrams, such as
the affine `Dₙ` graphs for `n ≥ 5` and the affine `E₆`, `E₇` and `E₈` graphs.

## Main results

* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra`: when `2` is invertible, a loop deformation
  whose quartic operation is not a Hochschild coboundary of the strict zigzag algebra is not
  formal.
* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single`: the loop deformation of a single
  closed walk `n₃ → v → n₀ → v → n₃`, through two of four distinct neighbours of `v`, is not
  formal.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra`: the strict zigzag algebra of a
  graph with a vertex of valency at least four is not intrinsically formal.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4, for minimal `A∞` deformations of zigzag algebras and their intrinsic formality.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-- **A loop deformation whose quartic operation is not a coboundary is not formal**, when `2` is
invertible. If the quartic operation of the loop deformation with coefficients `c` is not the
Hochschild differential of a suspended cochain of degree zero of the strict zigzag algebra, then
the loop deformation is not formal. Equivalently it is not `A∞` isomorphic to the strict zigzag
algebra (`TauCeti.AInfinityAlgebra.IsMinimal.isFormal_iff_exists_isIso`). -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra [Invertible (2 : k)] (c : (Fin 4 → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hobs : ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal :=
  AInfinityAlgebra.IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four
    (isMinimal_zigzagLoopAInfinityAlgebra c hc) isMinimal_zigzagStrictAInfinityAlgebra
    (fun _ hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega))
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
    (zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by decide) (by decide)) hobs

/-- **A non-formal quartic deformation of a zigzag algebra.** Assume that `2` is invertible and
that the ring is nontrivial. Let `δ 0, …, δ 3` be four distinct darts with a common head `v`, for
instance the darts into `v` from four distinct neighbours. The loop deformation whose quartic
operation is the loop operation of the single closed walk `(δ 3).symm, δ 0, (δ 0).symm, δ 3` (in
product order) is a minimal, strictly unital `A∞` structure on the zigzag algebra, with its grading
and product, which is not formal: it is not `A∞` isomorphic to the strict zigzag algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_single [Nontrivial k] [Invertible (2 : k)]
    {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v) :
    ¬(zigzagLoopAInfinityAlgebra hns _
      (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk
        ((hv 3).trans (hv 0).symm) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single hδ hv)

/-- **The zigzag algebra of a graph with a vertex of valency at least four is not intrinsically
formal**, over every nontrivial commutative ring in which `2` is invertible: when four distinct
darts of `G` have a common head, some `A∞` algebra whose cohomology algebra is the path-graded
zigzag algebra is not formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra [Nontrivial k]
    [Invertible (2 : k)] {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V}
    (hv : ∀ i, (δ i).snd = v) :
    ¬(𝒵).IsIntrinsicallyFormal := fun h ↦
  not_isFormal_zigzagLoopAInfinityAlgebra_single hδ hv <| h.isFormal_of_isMinimal
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading _ _)
    (isMinimal_zigzagLoopAInfinityAlgebra _ _)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two _ _)

end TauCeti
