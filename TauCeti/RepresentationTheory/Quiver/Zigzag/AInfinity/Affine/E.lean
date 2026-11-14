/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.E
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal
import all TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.E

/-!
# Higher Hochschild classes and non-formality for affine `E₆`, `E₇` and `E₈`

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). This file shows that if `G` contains a copy of the affine
diagram `E₆`, `E₇` or `E₈`, not necessarily induced, then the Hochschild cohomology
`HH^{6, -4}(Z, Z)`, `HH^{8, -6}(Z, Z)` or `HH^{12, -10}(Z, Z)` respectively is nonzero, over every
nontrivial commutative ring, and that over every nontrivial `ℚ`-algebra the corresponding loop
deformation in arity `6`, `8` or `12` is not formal and `Z` is not intrinsically formal.

The affine diagrams `E₆`, `E₇` and `E₈` are stars with one branch node, so the quartic classes of
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass`, which need a node with four
neighbours or two branch nodes, do not reach them. Their classes and non-formal minimal
deformations live in higher arity instead.

## The classes

The class is that of the loop operation of a closed walk at the trivalent node `0`, made of
backtracks: through the nodes `1`, `1`, `3` for `E₆`, through `2`, `2`, `2`, `5` for `E₇`, and
through `1`, `2`, `4`, `4`, `4`, `2` for `E₈`, in product order, with the labelling of
`TauCeti.AffineDynkinType.graph`. The integer matrix representations of the signless
preprojective algebras of the three diagrams constructed in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.E` send these products of
backtracks to matrices of trace one; this is how the nonzero cyclic classes
`TauCeti.exists_mem_signlessPreprojectiveGrade_six_notMem_commutatorSubmodule` and its `eight` and
`twelve` companions are detected. The diagrams are trees, hence bipartite, so the trace twisted by
the bipartition is anticyclic on the arrows and detects the loop operation of the same walk
(`not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one`).
Over a `ℚ`-algebra, first-obstruction invariance
(`not_isFormal_zigzagLoopAInfinityAlgebra_of_not_exists_hochschildDifferential_eq_obstruction`)
turns this non-coboundary directly into a non-formal loop deformation. The arities `6`, `8` and
`12` are the degrees of the lowest-degree invariants of the binary tetrahedral, octahedral and
icosahedral groups.

## Main results

* `TauCeti.not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra`: if `G` contains a copy of
  the affine diagram `E₆`, then `HH^{6, -4}(Z, Z) ≠ 0`.
* `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6` and
  `TauCeti.not_isIntrinsicallyFormal_affineE6`: over a nontrivial `ℚ`-algebra, an arity-six loop
  deformation is not formal and `Z` is not intrinsically formal.
* `TauCeti.not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra`,
  `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7` and
  `TauCeti.not_isIntrinsicallyFormal_affineE7`: the same for affine `E₇` in arity eight.
* `TauCeti.not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra`,
  `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8` and
  `TauCeti.not_isIntrinsicallyFormal_affineE8`: the same for affine `E₈` in arity twelve.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the Hochschild cohomology of zigzag
  algebras of trees and its comparison with the cyclic quotient of the preprojective algebra.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction groups.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-! ### Affine `E₆` -/

/-- The closed walk of the backtracks through the nodes `1`, `1` and `3` at the trivalent node `0`
of the affine diagram `E₆`, in product order. -/
private def affineE6Walk : Fin 6 → AffineDynkinType.E6.graph.Dart :=
  ![⟨(1, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(0, 1), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(1, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(0, 1), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(3, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(0, 3), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩]

/-- **Graphs containing an affine `E₆` have nonzero Hochschild classes in arity six.** If `G`
contains a copy of the affine diagram `E₆`, not necessarily induced, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{6, -4}(Z, Z)` of the zigzag algebra `Z` of `G` is
nonzero: the loop operation of the image of the closed walk of backtracks through the nodes `1`,
`1` and `3` at the trivalent node `0` is a Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra [Nontrivial k]
    (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨6, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 4)
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
      AffineDynkinType.isBipartite_graph_E6 affineE6Matrix
      (by simp only [AffineDynkinType.graph_E6_adj]; decide)
      (by decide) (by norm_num) (w := affineE6Walk) (by decide) (by decide))

/-- **Graphs containing an affine `E₆` admit a non-formal sextic loop deformation**, over every
nontrivial `ℚ`-algebra: the loop deformation supported on the image of the closed walk of
backtracks through the nodes `1`, `1` and `3` at the trivalent node `0` is not formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E6.graph.IsContained G) :
    ∃ (c : (Fin 6 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _,
    not_isFormal_zigzagLoopAInfinityAlgebra_of_not_exists_hochschildDifferential_eq_obstruction
      (n := 4) _ _
      (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
        AffineDynkinType.isBipartite_graph_E6 affineE6Matrix
        (by simp only [AffineDynkinType.graph_E6_adj]; decide)
        (by decide) (by norm_num) (w := affineE6Walk) (by decide) (by decide))⟩

/-- **The strict zigzag algebra of a graph containing an affine `E₆` is not intrinsically formal**,
over every nontrivial `ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6 (k := k) (hns := hns) hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The affine `E₆` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_affineE6 [Nontrivial k] [Algebra ℚ k] :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E6) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6 .rfl

/-! ### Affine `E₇` -/

/-- The closed walk of the backtracks through the nodes `2`, `2`, `2` and `5` at the trivalent node
`0` of the affine diagram `E₇`, in product order. -/
private def affineE7Walk : Fin 8 → AffineDynkinType.E7.graph.Dart :=
  ![⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(5, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 5), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩]

/-- **Graphs containing an affine `E₇` have nonzero Hochschild classes in arity eight.** If `G`
contains a copy of the affine diagram `E₇`, not necessarily induced, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{8, -6}(Z, Z)` of the zigzag algebra `Z` of `G` is
nonzero: the loop operation of the image of the closed walk of backtracks through the nodes `2`,
`2`, `2` and `5` at the trivalent node `0` is a Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra [Nontrivial k]
    (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨8, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 6)
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
      AffineDynkinType.isBipartite_graph_E7 affineE7Matrix
      (by simp only [AffineDynkinType.graph_E7_adj]; decide)
      (by decide) (by norm_num) (w := affineE7Walk) (by decide) (by decide))

/-- **Graphs containing an affine `E₇` admit a non-formal octic loop deformation**, over every
nontrivial `ℚ`-algebra: the loop deformation supported on the image of the closed walk of
backtracks through the nodes `2`, `2`, `2` and `5` at the trivalent node `0` is not formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E7.graph.IsContained G) :
    ∃ (c : (Fin 8 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _,
    not_isFormal_zigzagLoopAInfinityAlgebra_of_not_exists_hochschildDifferential_eq_obstruction
      (n := 6) _ _
      (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
        AffineDynkinType.isBipartite_graph_E7 affineE7Matrix
        (by simp only [AffineDynkinType.graph_E7_adj]; decide)
        (by decide) (by norm_num) (w := affineE7Walk) (by decide) (by decide))⟩

/-- **The strict zigzag algebra of a graph containing an affine `E₇` is not intrinsically formal**,
over every nontrivial `ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7 (k := k) (hns := hns) hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The affine `E₇` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_affineE7 [Nontrivial k] [Algebra ℚ k] :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E7) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7 .rfl

/-! ### Affine `E₈` -/

/-- The closed walk of the backtracks through the nodes `1`, `2`, `4`, `4`, `4` and `2` at the
trivalent node `0` of the affine diagram `E₈`, in product order. -/
private def affineE8Walk : Fin 12 → AffineDynkinType.E8.graph.Dart :=
  ![⟨(1, 0), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(0, 1), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(2, 0), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(4, 0), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(0, 4), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(4, 0), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(0, 4), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(4, 0), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(0, 4), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(2, 0), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩]

/-- **Graphs containing an affine `E₈` have nonzero Hochschild classes in arity twelve.** If `G`
contains a copy of the affine diagram `E₈`, not necessarily induced, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{12, -10}(Z, Z)` of the zigzag algebra `Z` of `G` is
nonzero: the loop operation of the image of the closed walk of backtracks through the nodes `1`,
`2`, `4`, `4`, `4` and `2` at the trivalent node `0` is a Hochschild cocycle which is not a
coboundary. -/
theorem not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra [Nontrivial k]
    (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨12, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 10)
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
      AffineDynkinType.isBipartite_graph_E8 affineE8Matrix
      (by simp only [AffineDynkinType.graph_E8_adj]; decide)
      (by decide) (by norm_num) (w := affineE8Walk) (by decide) (by decide))

/-- **Graphs containing an affine `E₈` admit a non-formal dodecic loop deformation**, over every
nontrivial `ℚ`-algebra: the loop deformation supported on the image of the closed walk of
backtracks through the nodes `1`, `2`, `4`, `4`, `4` and `2` at the trivalent node `0` is not
formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E8.graph.IsContained G) :
    ∃ (c : (Fin 12 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _,
    not_isFormal_zigzagLoopAInfinityAlgebra_of_not_exists_hochschildDifferential_eq_obstruction
      (n := 10) _ _
      (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
        AffineDynkinType.isBipartite_graph_E8 affineE8Matrix
        (by simp only [AffineDynkinType.graph_E8_adj]; decide)
        (by decide) (by norm_num) (w := affineE8Walk) (by decide) (by decide))⟩

/-- **The strict zigzag algebra of a graph containing an affine `E₈` is not intrinsically formal**,
over every nontrivial `ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8 (k := k) (hns := hns) hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The affine `E₈` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_affineE8 [Nontrivial k] [Algebra ℚ k] :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E8) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8 .rfl

end TauCeti
