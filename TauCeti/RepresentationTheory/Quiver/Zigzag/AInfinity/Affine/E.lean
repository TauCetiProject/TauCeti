/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.E
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal

/-!
# Higher Hochschild classes and non-formality for affine `E₆`, `E₇` and `E₈` subgraphs

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). This file shows that if `G` contains a copy of the affine
diagram `E₆`, `E₇` or `E₈`, not necessarily induced, then:

1. Over every nontrivial commutative ring, the Hochschild cohomology `HH^{6, -4}(Z, Z)`,
   `HH^{8, -6}(Z, Z)` or `HH^{12, -10}(Z, Z)` respectively is nonzero.
2. Both over every nontrivial `ℚ`-algebra and over every commutative ring in which `(2 : k)` is not
   a unit (in particular in characteristic `2` and over `ℤ`), the single-walk loop deformation of
   arity `6`, `8` or `12` along the copy is not formal, and hence the strict and public zigzag
   algebras are not intrinsically formal.

The affine diagrams `E₆`, `E₇` and `E₈` are stars with one branch node, so the quartic classes and
deformations of `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass` and
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal`, which need a node with four
neighbours or two branch nodes, do not reach them. Their classes and non-formal minimal
deformations live in higher even arities `6`, `8` and `12` instead.

## The walks and deformations

The detecting deformation is the loop deformation of a single closed walk at the trivalent node
`0`, made of backtracks: through the nodes `1`, `1`, `3` for `E₆` (`TauCeti.affineE6Walk`), through
`2`, `2`, `2`, `5` for `E₇` (`TauCeti.affineE7Walk`), and through `1`, `2`, `4`, `4`, `4`, `2` for
`E₈` (`TauCeti.affineE8Walk`), in product order, with the labelling of
`TauCeti.AffineDynkinType.graph`. The integer matrix representations of the signless preprojective
algebras of the three diagrams constructed in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.E` send these products of
backtracks to matrices of trace one; this is how the nonzero cyclic classes
`TauCeti.exists_mem_signlessPreprojectiveGrade_six_notMem_commutatorSubmodule` and its `eight` and
`twelve` companions are detected. Since the diagrams are trees, hence bipartite, the trace twisted
by the bipartition is anticyclic on the arrows and evaluates to `±1` on the single walk: over a
nontrivial `ℚ`-algebra this obstructs formality via invariance of the first obstruction
(`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one`), while when `(2 : k)` is not a
unit it obstructs formality because formal even-arity obstructions pair into `2 k`
(`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one_of_not_isUnit_two`). The arities
`6`, `8` and `12` are the degrees of the lowest-degree invariants of the binary tetrahedral,
octahedral and icosahedral groups.

## Main definitions

* `TauCeti.affineE6Walk`, `TauCeti.affineE7Walk`, `TauCeti.affineE8Walk`: the closed walks of
  lengths `6`, `8` and `12` at the branch node `0` of the affine `E₆`, `E₇` and `E₈` diagrams.

## Main results

* `TauCeti.not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra`,
  `TauCeti.not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra`,
  `TauCeti.not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra`: if `G` contains a copy of
  `E₆`, `E₇` or `E₈`, then `HH^{6, -4}(Z, Z)`, `HH^{8, -6}(Z, Z)` or `HH^{12, -10}(Z, Z)` is
  nonzero over every nontrivial commutative ring.
* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk`,
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk`,
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk` (and their
  `_of_not_isUnit_two` companions): the single-walk loop deformations in arities `6`, `8` and `12`
  along a copy of `E₆`, `E₇` or `E₈` are not formal, over any nontrivial `ℚ`-algebra or when
  `(2 : k)` is not a unit.
* `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6`,
  `TauCeti.not_isIntrinsicallyFormal_affineE6`,
  `TauCeti.not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6` and
  `TauCeti.not_isZigzagAlgebraIntrinsicallyFormal_affineE6` (with `_of_not_isUnit_two`
  companions): non-formal arity-six loop deformations and non-intrinsic formality for affine `E₆`.
* `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7`,
  `TauCeti.not_isIntrinsicallyFormal_affineE7`,
  `TauCeti.not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7` and
  `TauCeti.not_isZigzagAlgebraIntrinsicallyFormal_affineE7` (with `_of_not_isUnit_two`
  companions): the same for affine `E₇` in arity eight.
* `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8`,
  `TauCeti.not_isIntrinsicallyFormal_affineE8`,
  `TauCeti.not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8` and
  `TauCeti.not_isZigzagAlgebraIntrinsicallyFormal_affineE8` (with `_of_not_isUnit_two`
  companions): the same for affine `E₈` in arity twelve.

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

/-- **The closed walk of length six on the affine `E₆` diagram**: the backtracks through the nodes
`1`, `1` and `3` at the trivalent node `0`, in product order. -/
def affineE6Walk : Fin 6 → AffineDynkinType.E6.graph.Dart :=
  ![⟨(1, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(0, 1), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(1, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(0, 1), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(3, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
    ⟨(0, 3), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩]

/-- Unfolding `affineE6Walk` as the six-dart backtrack walk through `1`, `1` and `3` at `0`. -/
theorem affineE6Walk_def :
    affineE6Walk =
      ![⟨(1, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
        ⟨(0, 1), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
        ⟨(1, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
        ⟨(0, 1), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
        ⟨(3, 0), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
        ⟨(0, 3), (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩] := by
  rw [affineE6Walk]

/-- Consecutive darts of `affineE6Walk` are cyclically composable in product order. -/
theorem affineE6Walk_fst_eq_snd (i : Fin 6) :
    (affineE6Walk i).fst = (affineE6Walk (i + 1)).snd := by
  revert i; decide

/-- The matrix product of `affineE6Matrix` along `affineE6Walk` has trace `1`. -/
theorem trace_affineE6Matrix_affineE6Walk :
    Matrix.trace (List.ofFn fun t ↦
      affineE6Matrix (affineE6Walk t).fst (affineE6Walk t).snd).prod = 1 := by
  simpa [List.ofFn_succ, affineE6Walk, mul_assoc] using trace_affineE6Matrix_backtracks

/-- **Graphs containing an affine `E₆` have nonzero Hochschild classes in arity six.** If `G`
contains a copy of the affine diagram `E₆`, not necessarily induced, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{6, -4}(Z, Z)` of the zigzag algebra `Z` of `G` is
nonzero: the loop operation of the image of `affineE6Walk` is a Hochschild cocycle which is not a
coboundary. -/
theorem not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra [Nontrivial k]
    (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨6, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 4)
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
      AffineDynkinType.isBipartite_graph_E6 affineE6Matrix
      (fun _ _ ↦ affineE6Matrix_eq_zero_of_not_adj) sum_affineE6Matrix_mul_affineE6Matrix
      (by norm_num) (w := affineE6Walk) affineE6Walk_fst_eq_snd trace_affineE6Matrix_affineE6Walk)

/-- **The arity-six loop deformation of `affineE6Walk` along a copy of `E₆` is not formal** over
every nontrivial `ℚ`-algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk [Nontrivial k] [Algebra ℚ k]
    (f : AffineDynkinType.E6.graph.Copy G) :
    ¬(zigzagLoopAInfinityAlgebra hns
      (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE6Walk t)) (1 : k))
      (fst_eq_snd_of_mem_support_single
        (fun i ↦ congrArg f (affineE6Walk_fst_eq_snd i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one f AffineDynkinType.isBipartite_graph_E6
    affineE6Matrix (fun _ _ ↦ affineE6Matrix_eq_zero_of_not_adj)
    sum_affineE6Matrix_mul_affineE6Matrix (n := 4) (by norm_num) affineE6Walk_fst_eq_snd
    trace_affineE6Matrix_affineE6Walk

/-- **The arity-six loop deformation of `affineE6Walk` along a copy of `E₆` is not formal** whenever
`(2 : k)` is not a unit (in particular in characteristic `2` or over `ℤ`). -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (f : AffineDynkinType.E6.graph.Copy G) :
    ¬(zigzagLoopAInfinityAlgebra hns
      (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE6Walk t)) (1 : k))
      (fst_eq_snd_of_mem_support_single
        (fun i ↦ congrArg f (affineE6Walk_fst_eq_snd i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one_of_not_isUnit_two h2 f
    AffineDynkinType.isBipartite_graph_E6 affineE6Matrix
    (fun _ _ ↦ affineE6Matrix_eq_zero_of_not_adj) sum_affineE6Matrix_mul_affineE6Matrix
    (r := 2) (by norm_num) affineE6Walk_fst_eq_snd trace_affineE6Matrix_affineE6Walk

/-- **Graphs containing an affine `E₆` admit a non-formal sextic loop deformation**, over every
nontrivial `ℚ`-algebra: the loop deformation supported on the image of the closed walk of
backtracks through the nodes `1`, `1` and `3` at the trivalent node `0` is not formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E6.graph.IsContained G) :
    ∃ (c : (Fin 6 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk f⟩

/-- **Graphs containing an affine `E₆` admit a non-formal sextic loop deformation** whenever
`(2 : k)` is not a unit (in particular in characteristic `2` or over `ℤ`). -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : AffineDynkinType.E6.graph.IsContained G) :
    ∃ (c : (Fin 6 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk_of_not_isUnit_two h2 f⟩

/-- **The strict zigzag algebra of a graph containing an affine `E₆` is not intrinsically formal**,
over every nontrivial `ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6 (k := k) (hns := hns) hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The strict zigzag algebra of a graph containing an affine `E₆` is not intrinsically formal**
whenever `(2 : k)` is not a unit. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6_of_not_isUnit_two
      (k := k) (hns := hns) h2 hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The affine `E₆` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_affineE6 [Nontrivial k] [Algebra ℚ k] :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E6) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6 .rfl

/-- **The affine `E₆` zigzag algebra is not intrinsically formal** whenever `(2 : k)` is not a
unit. -/
theorem not_isIntrinsicallyFormal_affineE6_of_not_isUnit_two (h2 : ¬IsUnit (2 : k)) :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E6) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E6_of_not_isUnit_two h2 .rfl

/-- **Connected graphs containing a copy of affine `E₆` are not intrinsically formal**, over every
nontrivial `ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6 [Nontrivial k] [Algebra ℚ k]
    (hconn : G.Connected) (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V :=
    AffineDynkinType.nontrivial_of_graph_isContained AffineDynkinType.valid_E6 hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6
    (k := k) (hns := hconn.preconnected.exists_adj_of_nontrivial) hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₆` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE6 [Nontrivial k] [Algebra ℚ k] :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E6.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-- **Connected graphs containing a copy of affine `E₆` are not intrinsically formal** whenever
`(2 : k)` is not a unit. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hconn : G.Connected) (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V :=
    AffineDynkinType.nontrivial_of_graph_isContained AffineDynkinType.valid_E6 hG
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6_of_not_isUnit_two
      (k := k) (hns := hconn.preconnected.exists_adj_of_nontrivial) h2 hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₆` zigzag algebra is not intrinsically formal** whenever `(2 : k)` is not
a unit. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE6_of_not_isUnit_two (h2 : ¬IsUnit (2 : k)) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E6.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6_of_not_isUnit_two h2
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-! ### Affine `E₇` -/

/-- **The closed walk of length eight on the affine `E₇` diagram**: the backtracks through the nodes
`2`, `2`, `2` and `5` at the trivalent node `0`, in product order. -/
def affineE7Walk : Fin 8 → AffineDynkinType.E7.graph.Dart :=
  ![⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(5, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
    ⟨(0, 5), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩]

/-- Unfolding `affineE7Walk` as the eight-dart backtrack walk through `2`, `2`, `2` and `5` at
`0`. -/
theorem affineE7Walk_def :
    affineE7Walk =
      ![⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(2, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(0, 2), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(5, 0), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
        ⟨(0, 5), (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩] := by
  rw [affineE7Walk]

/-- Consecutive darts of `affineE7Walk` are cyclically composable in product order. -/
theorem affineE7Walk_fst_eq_snd (i : Fin 8) :
    (affineE7Walk i).fst = (affineE7Walk (i + 1)).snd := by
  revert i; decide

/-- The matrix product of `affineE7Matrix` along `affineE7Walk` has trace `1`. -/
theorem trace_affineE7Matrix_affineE7Walk :
    Matrix.trace (List.ofFn fun t ↦
      affineE7Matrix (affineE7Walk t).fst (affineE7Walk t).snd).prod = 1 := by
  simpa [List.ofFn_succ, affineE7Walk, mul_assoc] using trace_affineE7Matrix_backtracks

/-- **Graphs containing an affine `E₇` have nonzero Hochschild classes in arity eight.** If `G`
contains a copy of the affine diagram `E₇`, not necessarily induced, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{8, -6}(Z, Z)` of the zigzag algebra `Z` of `G` is
nonzero: the loop operation of the image of `affineE7Walk` is a Hochschild cocycle which is not a
coboundary. -/
theorem not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra [Nontrivial k]
    (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨8, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 6)
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
      AffineDynkinType.isBipartite_graph_E7 affineE7Matrix
      (fun _ _ ↦ affineE7Matrix_eq_zero_of_not_adj) sum_affineE7Matrix_mul_affineE7Matrix
      (by norm_num) (w := affineE7Walk) affineE7Walk_fst_eq_snd trace_affineE7Matrix_affineE7Walk)

/-- **The arity-eight loop deformation of `affineE7Walk` along a copy of `E₇` is not formal** over
every nontrivial `ℚ`-algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk [Nontrivial k] [Algebra ℚ k]
    (f : AffineDynkinType.E7.graph.Copy G) :
    ¬(zigzagLoopAInfinityAlgebra hns
      (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE7Walk t)) (1 : k))
      (fst_eq_snd_of_mem_support_single
        (fun i ↦ congrArg f (affineE7Walk_fst_eq_snd i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one f AffineDynkinType.isBipartite_graph_E7
    affineE7Matrix (fun _ _ ↦ affineE7Matrix_eq_zero_of_not_adj)
    sum_affineE7Matrix_mul_affineE7Matrix (n := 6) (by norm_num) affineE7Walk_fst_eq_snd
    trace_affineE7Matrix_affineE7Walk

/-- **The arity-eight loop deformation of `affineE7Walk` along a copy of `E₇` is not formal**
whenever `(2 : k)` is not a unit. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (f : AffineDynkinType.E7.graph.Copy G) :
    ¬(zigzagLoopAInfinityAlgebra hns
      (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE7Walk t)) (1 : k))
      (fst_eq_snd_of_mem_support_single
        (fun i ↦ congrArg f (affineE7Walk_fst_eq_snd i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one_of_not_isUnit_two h2 f
    AffineDynkinType.isBipartite_graph_E7 affineE7Matrix
    (fun _ _ ↦ affineE7Matrix_eq_zero_of_not_adj) sum_affineE7Matrix_mul_affineE7Matrix
    (r := 3) (by norm_num) affineE7Walk_fst_eq_snd trace_affineE7Matrix_affineE7Walk

/-- **Graphs containing an affine `E₇` admit a non-formal octic loop deformation**, over every
nontrivial `ℚ`-algebra: the loop deformation supported on the image of the closed walk of
backtracks through the nodes `2`, `2`, `2` and `5` at the trivalent node `0` is not formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E7.graph.IsContained G) :
    ∃ (c : (Fin 8 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk f⟩

/-- **Graphs containing an affine `E₇` admit a non-formal octic loop deformation** whenever
`(2 : k)` is not a unit. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : AffineDynkinType.E7.graph.IsContained G) :
    ∃ (c : (Fin 8 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk_of_not_isUnit_two h2 f⟩

/-- **The strict zigzag algebra of a graph containing an affine `E₇` is not intrinsically formal**,
over every nontrivial `ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7 (k := k) (hns := hns) hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The strict zigzag algebra of a graph containing an affine `E₇` is not intrinsically formal**
whenever `(2 : k)` is not a unit. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7_of_not_isUnit_two
      (k := k) (hns := hns) h2 hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The affine `E₇` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_affineE7 [Nontrivial k] [Algebra ℚ k] :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E7) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7 .rfl

/-- **The affine `E₇` zigzag algebra is not intrinsically formal** whenever `(2 : k)` is not a
unit. -/
theorem not_isIntrinsicallyFormal_affineE7_of_not_isUnit_two (h2 : ¬IsUnit (2 : k)) :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E7) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E7_of_not_isUnit_two h2 .rfl

/-- **Connected graphs containing a copy of affine `E₇` are not intrinsically formal**, over every
nontrivial `ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7 [Nontrivial k] [Algebra ℚ k]
    (hconn : G.Connected) (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V :=
    AffineDynkinType.nontrivial_of_graph_isContained AffineDynkinType.valid_E7 hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7
    (k := k) (hns := hconn.preconnected.exists_adj_of_nontrivial) hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₇` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE7 [Nontrivial k] [Algebra ℚ k] :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E7.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-- **Connected graphs containing a copy of affine `E₇` are not intrinsically formal** whenever
`(2 : k)` is not a unit. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hconn : G.Connected) (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V :=
    AffineDynkinType.nontrivial_of_graph_isContained AffineDynkinType.valid_E7 hG
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7_of_not_isUnit_two
      (k := k) (hns := hconn.preconnected.exists_adj_of_nontrivial) h2 hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₇` zigzag algebra is not intrinsically formal** whenever `(2 : k)` is not
a unit. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE7_of_not_isUnit_two (h2 : ¬IsUnit (2 : k)) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E7.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7_of_not_isUnit_two h2
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-! ### Affine `E₈` -/

/-- **The closed walk of length twelve on the affine `E₈` diagram**: the backtracks through the
nodes `1`, `2`, `4`, `4`, `4` and `2` at the trivalent node `0`, in product order. -/
def affineE8Walk : Fin 12 → AffineDynkinType.E8.graph.Dart :=
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

/-- Unfolding `affineE8Walk` as the twelve-dart backtrack walk through `1`, `2`, `4`, `4`, `4` and
`2` at `0`. -/
theorem affineE8Walk_def :
    affineE8Walk =
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
        ⟨(0, 2), (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩] := by
  rw [affineE8Walk]

/-- Consecutive darts of `affineE8Walk` are cyclically composable in product order. -/
theorem affineE8Walk_fst_eq_snd (i : Fin 12) :
    (affineE8Walk i).fst = (affineE8Walk (i + 1)).snd := by
  revert i; decide

/-- The matrix product of `affineE8Matrix` along `affineE8Walk` has trace `1`. -/
theorem trace_affineE8Matrix_affineE8Walk :
    Matrix.trace (List.ofFn fun t ↦
      affineE8Matrix (affineE8Walk t).fst (affineE8Walk t).snd).prod = 1 := by
  simpa [List.ofFn_succ, affineE8Walk, mul_assoc] using trace_affineE8Matrix_backtracks

/-- **Graphs containing an affine `E₈` have nonzero Hochschild classes in arity twelve.** If `G`
contains a copy of the affine diagram `E₈`, not necessarily induced, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{12, -10}(Z, Z)` of the zigzag algebra `Z` of `G` is
nonzero: the loop operation of the image of `affineE8Walk` is a Hochschild cocycle which is not a
coboundary. -/
theorem not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra [Nontrivial k]
    (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨12, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 10)
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one f
      AffineDynkinType.isBipartite_graph_E8 affineE8Matrix
      (fun _ _ ↦ affineE8Matrix_eq_zero_of_not_adj) sum_affineE8Matrix_mul_affineE8Matrix
      (by norm_num) (w := affineE8Walk) affineE8Walk_fst_eq_snd trace_affineE8Matrix_affineE8Walk)

/-- **The arity-twelve loop deformation of `affineE8Walk` along a copy of `E₈` is not formal** over
every nontrivial `ℚ`-algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk [Nontrivial k] [Algebra ℚ k]
    (f : AffineDynkinType.E8.graph.Copy G) :
    ¬(zigzagLoopAInfinityAlgebra hns
      (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE8Walk t)) (1 : k))
      (fst_eq_snd_of_mem_support_single
        (fun i ↦ congrArg f (affineE8Walk_fst_eq_snd i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one f AffineDynkinType.isBipartite_graph_E8
    affineE8Matrix (fun _ _ ↦ affineE8Matrix_eq_zero_of_not_adj)
    sum_affineE8Matrix_mul_affineE8Matrix (n := 10) (by norm_num) affineE8Walk_fst_eq_snd
    trace_affineE8Matrix_affineE8Walk

/-- **The arity-twelve loop deformation of `affineE8Walk` along a copy of `E₈` is not formal**
whenever `(2 : k)` is not a unit. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (f : AffineDynkinType.E8.graph.Copy G) :
    ¬(zigzagLoopAInfinityAlgebra hns
      (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE8Walk t)) (1 : k))
      (fst_eq_snd_of_mem_support_single
        (fun i ↦ congrArg f (affineE8Walk_fst_eq_snd i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one_of_not_isUnit_two h2 f
    AffineDynkinType.isBipartite_graph_E8 affineE8Matrix
    (fun _ _ ↦ affineE8Matrix_eq_zero_of_not_adj) sum_affineE8Matrix_mul_affineE8Matrix
    (r := 5) (by norm_num) affineE8Walk_fst_eq_snd trace_affineE8Matrix_affineE8Walk

/-- **Graphs containing an affine `E₈` admit a non-formal dodecic loop deformation**, over every
nontrivial `ℚ`-algebra: the loop deformation supported on the image of the closed walk of
backtracks through the nodes `1`, `2`, `4`, `4`, `4` and `2` at the trivalent node `0` is not
formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E8.graph.IsContained G) :
    ∃ (c : (Fin 12 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk f⟩

/-- **Graphs containing an affine `E₈` admit a non-formal dodecic loop deformation** whenever
`(2 : k)` is not a unit. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : AffineDynkinType.E8.graph.IsContained G) :
    ∃ (c : (Fin 12 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  obtain ⟨f⟩ := hG
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk_of_not_isUnit_two h2 f⟩

/-- **The strict zigzag algebra of a graph containing an affine `E₈` is not intrinsically formal**,
over every nontrivial `ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8
    [Nontrivial k] [Algebra ℚ k] (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8 (k := k) (hns := hns) hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The strict zigzag algebra of a graph containing an affine `E₈` is not intrinsically formal**
whenever `(2 : k)` is not a unit. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8_of_not_isUnit_two
      (k := k) (hns := hns) h2 hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The affine `E₈` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isIntrinsicallyFormal_affineE8 [Nontrivial k] [Algebra ℚ k] :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E8) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8 .rfl

/-- **The affine `E₈` zigzag algebra is not intrinsically formal** whenever `(2 : k)` is not a
unit. -/
theorem not_isIntrinsicallyFormal_affineE8_of_not_isUnit_two (h2 : ¬IsUnit (2 : k)) :
    ¬(zigzagStrictAInfinityAlgebra k
      (AffineDynkinType.exists_adj_graph (t := .E8) (by decide))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_E8_of_not_isUnit_two h2 .rfl

/-- **Connected graphs containing a copy of affine `E₈` are not intrinsically formal**, over every
nontrivial `ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8 [Nontrivial k] [Algebra ℚ k]
    (hconn : G.Connected) (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V :=
    AffineDynkinType.nontrivial_of_graph_isContained AffineDynkinType.valid_E8 hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8
    (k := k) (hns := hconn.preconnected.exists_adj_of_nontrivial) hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₈` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE8 [Nontrivial k] [Algebra ℚ k] :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E8.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-- **Connected graphs containing a copy of affine `E₈` are not intrinsically formal** whenever
`(2 : k)` is not a unit. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hconn : G.Connected) (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V :=
    AffineDynkinType.nontrivial_of_graph_isContained AffineDynkinType.valid_E8 hG
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8_of_not_isUnit_two
      (k := k) (hns := hconn.preconnected.exists_adj_of_nontrivial) h2 hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₈` zigzag algebra is not intrinsically formal** whenever `(2 : k)` is not
a unit. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE8_of_not_isUnit_two (h2 : ¬IsUnit (2 : k)) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E8.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8_of_not_isUnit_two h2
    (AffineDynkinType.graph_connected (by decide)) .rfl

end TauCeti
