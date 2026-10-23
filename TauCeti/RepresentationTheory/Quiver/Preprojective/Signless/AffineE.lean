/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.MatrixRepresentation

/-!
# Nonzero cyclic classes from affine `E₆`, `E₇` and `E₈` subgraphs

Let `G` be a finite simple graph containing a copy of one of the affine diagrams `E₆`, `E₇` or
`E₈`, not necessarily induced. This file shows that the cyclic quotient
`Π⁺(G) / [Π⁺(G), Π⁺(G)]` of the signless preprojective algebra of `G`, its zeroth Hochschild
homology, is nonzero in path degree `6`, `8` or `12` respectively, over every nontrivial
commutative ring. For a bipartite graph, such as a tree, `Π⁺(G)` is isomorphic to the additive
preprojective algebra of any orientation of `G`
(`SimpleGraph.IsBipartite.signlessPreprojectiveAlgebraEquiv`).

Together with the affine `Dₙ` case
(`TauCeti.exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule`), this covers
every finite tree which is not a Dynkin diagram, since such a tree contains a copy of an affine
`Dₙ`, `E₆`, `E₇` or `E₈`; that classical graph-theoretic fact is not formalized here. For a quiver
whose underlying graph is a tree, Liu and Wang identify the degree-`(q + 2)` piece of this cyclic
quotient with the second Hochschild cohomology `HH^{2,q}` of the two-dimensional Ginzburg algebra
`Π₂(Q)`, which controls the `A∞` deformations of the zigzag algebra of the tree.

## The representations

The three diagrams are stars, labelled as in `TauCeti.AffineDynkinType.graph`: the trivalent node
is `0`, and the arms are numbered outwards. The representation puts `kᵐ` at every node, where `m`
is the mark of the trivalent node: `3`, `4` and `6`. At the trivalent node, the backtracks
`B₁, B₂, B₃` through the three arms are nilpotent integer matrices with `B₁ + B₂ + B₃ = 0`, of
Jordan types

```text
E₆ :  (3), (3), (3)        E₇ :  (2, 2), (4), (4)        E₈ :  (2, 2, 2), (3, 3), (6)
```

so that the matrix `B` of an arm with `L` edges has `c = m / (L + 1)` Jordan blocks of size
`L + 1`. Write `N` for the shift sending each basis vector `e_{i+c}` to `e_i` and the last `c`
basis vectors to zero, `Eᵣ` for the coordinate projection onto the first `r` basis vectors, and
`B = P N P⁻¹` with `P` invertible over `ℤ`. Along the arm, the first arrow away from the trivalent
node is `N P⁻¹` and the arrow back is `P E_{m-c}`, so that the backtrack at the trivalent node is
`P E_{m-c} N P⁻¹ = B`. Along the `s`-th edge of the arm, for `s ≥ 2`, the arrow away from the
trivalent node is `± N`, with signs alternating along the arm, and the arrow back is `E_{m-sc}`.
At the `s`-th node of the arm both backtracks are `± N E_{m-sc} = ± E_{m-(s+1)c} N`, with
opposite signs, and at the end of the arm the backtrack is `± N E_c = 0`. The representation over
a general commutative ring is the image of the one over `ℤ`.

A product of backtracks at the trivalent node acts there by the corresponding product of the
`Bᵢ`. The product `B₁ B₁ B₂` for `E₆`, `B₂ B₂ B₂ B₃` for `E₇` and `B₁ B₂ B₃ B₃ B₃ B₂` for `E₈`
has trace one. Since the trace of a representation vanishes on commutators, the class of this
product of backtracks in the cyclic quotient is nonzero. Its path degrees `6`, `8` and `12` are
the degrees of the lowest-degree invariants of the binary tetrahedral, octahedral and icosahedral
groups, which correspond to these diagrams under the McKay correspondence.

## Implementation notes

The matrices at the trivalent node were found by a computer search; for `E₈` the search was
restricted to matrices compatible with a `ℤ/3`-grading of `ℤ⁶ = ℤ² ⊕ ℤ² ⊕ ℤ²`. The relations, the
vanishing off the edges and the traces are checked by `decide` on the integer matrices.

## Main results

* `TauCeti.exists_mem_signlessPreprojectiveGrade_six_notMem_commutatorSubmodule`: if `G`
  contains a copy of the affine diagram `E₆`, some element of path degree six of `Π⁺(G)` does
  not lie in `[Π⁺(G), Π⁺(G)]`.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_eight_notMem_commutatorSubmodule`: the same for
  affine `E₇`, in path degree eight.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_twelve_notMem_commutatorSubmodule`: the same
  for affine `E₈`, in path degree twelve.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the role of the cyclic quotient of the preprojective
  algebra.
* W. Crawley-Boevey and M. P. Holland, *Noncommutative deformations of Kleinian singularities*,
  Duke Math. J. 92 (1998), for the preprojective algebra of an extended Dynkin quiver and the
  Kleinian singularities.
-/

public section

namespace TauCeti

open _root_.Matrix

universe u w

/-! ### The arm matrices -/

/-- The shift `N` on `ℤᵐ` sending the basis vector `e_{i+c}` to `e_i` and the last `c` basis
vectors to zero. -/
private def armShift (m c : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  of fun i j => if (j : ℕ) = i + c then 1 else 0

/-- The coordinate projection of `ℤᵐ` onto the span of its first `r` basis vectors. -/
private def armProj (m r : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  of fun i j => if i = j ∧ (i : ℕ) < r then 1 else 0

/-! ### Integer matrices satisfying the signless relations -/

section Integer

variable (k : Type w) [CommRing k] {W : Type*} [Fintype W] {H : SimpleGraph W}
  {m : Type*} [Fintype m] [DecidableEq m]

/-- An integer matrix family which vanishes off the edges of `H` and satisfies the signless
relations, as sums over all vertices, satisfies them over every commutative ring. -/
private theorem sum_mapMatrix_intCast_mul_mapMatrix_intCast [DecidableRel H.Adj]
    (β : W → W → Matrix m m ℤ)
    (h₀ : ∀ v w, ¬H.Adj v w → β v w = 0) (h : ∀ v, ∑ w, β w v * β v w = 0) (v : W) :
    ∑ w ∈ H.neighborFinset v,
      (Int.castRingHom k).mapMatrix (β w v) * (Int.castRingHom k).mapMatrix (β v w) = 0 := by
  rw [Finset.sum_subset (Finset.subset_univ _) fun w _ hw => by
      rw [h₀ v w (by simpa using hw), map_zero, mul_zero]]
  simp_rw [← map_mul, ← map_sum, h, map_zero]

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An integer matrix family on `H` satisfying the signless relations, together with a nonempty
product of backtracks at a vertex of trace one, gives a nonzero cyclic class of `Π⁺(G)` along any
copy of `H` in `G`. -/
private theorem exists_notMem_commutatorSubmodule_of_intMatrix [Nontrivial k] (f : H.Copy G)
    (β : W → W → Matrix m m ℤ) (h₀ : ∀ v w, ¬H.Adj v w → β v w = 0)
    (h : ∀ v, ∑ w, β w v * β v w = 0) {c : W} (l : List {a // H.Adj c a}) (hl : l ≠ [])
    (htr : trace (l.map fun a => β a.1 c * β c a.1).prod = 1) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) (2 * l.length),
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  refine exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_trace_ne_zero f
    (fun i j => (Int.castRingHom k).mapMatrix (β i j))
    (sum_mapMatrix_intCast_mul_mapMatrix_intCast k β h₀ h) l hl ?_
  have hmap : (l.map fun a => (Int.castRingHom k).mapMatrix (β a.1 c) *
      (Int.castRingHom k).mapMatrix (β c a.1)) =
      (l.map fun a => β a.1 c * β c a.1).map (Int.castRingHom k).mapMatrix := by
    simp only [List.map_map, Function.comp_def, map_mul]
  rw [hmap, ← map_list_prod, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, htr, map_one]
  exact one_ne_zero

end Integer

variable {k : Type w} [CommRing k] {V : Type u} [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

/-! ### Affine `E₆` -/

/-- The integer matrix assigned to the arrow `i → j` of the doubled affine diagram `E₆` by the
representation of this file; it is zero unless `i` and `j` are adjacent. -/
private def affineE6Matrix (i j : Fin AffineDynkinType.E6.nodes) : Matrix (Fin 3) (Fin 3) ℤ :=
  match (i : ℕ), (j : ℕ) with
  | 0, 1 => armShift 3 1
  | 1, 0 => armProj 3 2
  | 1, 2 => -armShift 3 1
  | 2, 1 => armProj 3 1
  | 0, 3 => !![0, 0, 1; 1, 0, 0; 0, 0, 0]
  | 3, 0 => !![0, 0, 0; -1, 0, 0; 0, 1, 0]
  | 3, 4 => -armShift 3 1
  | 4, 3 => armProj 3 1
  | 0, 5 => !![-1, 0, 0; 0, 1, 0; 0, 0, 0]
  | 5, 0 => !![0, -1, 0; 0, 0, 0; 1, 0, 0]
  | 5, 6 => -armShift 3 1
  | 6, 5 => armProj 3 1
  | _, _ => 0

/-- **Graphs containing an affine `E₆` have nonzero cyclic classes in degree six.** If `G`
contains a copy of the affine diagram `E₆`, not necessarily induced, then over every nontrivial
commutative ring some element of path degree six of the signless preprojective algebra `Π⁺(G)`
does not lie in the commutator submodule `[Π⁺(G), Π⁺(G)]`: its class in the cyclic quotient is
nonzero.

The element is the product of the backtracks `0 → 1 → 0`, `0 → 1 → 0` and `0 → 3 → 0` at the
image of the trivalent node `0`; its image under the representation of this file has trace one. -/
theorem exists_mem_signlessPreprojectiveGrade_six_notMem_commutatorSubmodule [Nontrivial k]
    (hG : AffineDynkinType.E6.graph.IsContained G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 6,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨f⟩ := hG
  simpa using exists_notMem_commutatorSubmodule_of_intMatrix k f affineE6Matrix
    (by simp only [AffineDynkinType.graph_E6_adj]; decide) (by decide) (c := 0)
    [⟨1, (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
      ⟨1, (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩,
      ⟨3, (AffineDynkinType.graph_E6_adj _ _).2 (by decide)⟩] (by simp)
    (by decide)

/-! ### Affine `E₇` -/

/-- The integer matrix assigned to the arrow `i → j` of the doubled affine diagram `E₇` by the
representation of this file; it is zero unless `i` and `j` are adjacent. -/
private def affineE7Matrix (i j : Fin AffineDynkinType.E7.nodes) : Matrix (Fin 4) (Fin 4) ℤ :=
  match (i : ℕ), (j : ℕ) with
  | 0, 1 => armShift 4 2
  | 1, 0 => armProj 4 2
  | 0, 2 => !![0, -1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 0, 0]
  | 2, 0 => !![0, 0, 0, 0; 0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0]
  | 2, 3 => -armShift 4 1
  | 3, 2 => armProj 4 2
  | 3, 4 => armShift 4 1
  | 4, 3 => armProj 4 1
  | 0, 5 => !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 0]
  | 5, 0 => !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0; -1, 0, 0, 0]
  | 5, 6 => -armShift 4 1
  | 6, 5 => armProj 4 2
  | 6, 7 => armShift 4 1
  | 7, 6 => armProj 4 1
  | _, _ => 0

/-- **Graphs containing an affine `E₇` have nonzero cyclic classes in degree eight.** If `G`
contains a copy of the affine diagram `E₇`, not necessarily induced, then over every nontrivial
commutative ring some element of path degree eight of the signless preprojective algebra `Π⁺(G)`
does not lie in the commutator submodule `[Π⁺(G), Π⁺(G)]`: its class in the cyclic quotient is
nonzero.

The element is the product of three backtracks `0 → 2 → 0` and the backtrack `0 → 5 → 0` at the
image of the trivalent node `0`; its image under the representation of this file has trace one. -/
theorem exists_mem_signlessPreprojectiveGrade_eight_notMem_commutatorSubmodule [Nontrivial k]
    (hG : AffineDynkinType.E7.graph.IsContained G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 8,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨f⟩ := hG
  simpa using exists_notMem_commutatorSubmodule_of_intMatrix k f affineE7Matrix
    (by simp only [AffineDynkinType.graph_E7_adj]; decide) (by decide) (c := 0)
    [⟨2, (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
      ⟨2, (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
      ⟨2, (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩,
      ⟨5, (AffineDynkinType.graph_E7_adj _ _).2 (by decide)⟩] (by simp) (by decide)

/-! ### Affine `E₈` -/

/-- The integer matrix assigned to the arrow `i → j` of the doubled affine diagram `E₈` by the
representation of this file; it is zero unless `i` and `j` are adjacent. -/
private def affineE8Matrix (i j : Fin AffineDynkinType.E8.nodes) : Matrix (Fin 6) (Fin 6) ℤ :=
  match (i : ℕ), (j : ℕ) with
  | 0, 1 => !![0, 0, 0, 0, 0, -1;
               0, 0, 0, -1, 0, 1;
               -1, 0, 0, 1, 0, 0;
               0, 0, 0, 0, 0, 0;
               0, 0, 0, 0, 0, 0;
               0, 0, 0, 0, 0, 0]
  | 1, 0 => !![0, 0, 0, 0, 0, 0;
               -1, 0, 0, 0, 0, 0;
               -1, -1, -1, 0, 0, 0;
               0, 0, 0, 0, 0, 0;
               -1, -1, 0, 0, 0, 0;
               0, 0, 0, 0, 0, 0]
  | 0, 2 => !![-1, 1, 0, 0, 0, 0;
               0, 0, 0, 0, -1, 1;
               0, 0, 0, 0, -1, 0;
               0, 0, -1, 1, 0, 0;
               0, 0, 0, 0, 0, 0;
               0, 0, 0, 0, 0, 0]
  | 2, 0 => !![0, -1, 0, 0, 0, 0;
               0, -1, 1, 0, 0, 0;
               1, 0, 0, 0, 0, 0;
               1, 0, 0, 0, 0, 0;
               0, 0, 0, 0, 0, 0;
               0, 0, 0, 1, 0, 0]
  | 2, 3 => -armShift 6 2
  | 3, 2 => armProj 6 2
  | 0, 4 => !![0, 0, 0, 1, 0, 0;
               1, -1, 0, 0, 0, 0;
               0, 0, 0, 0, -1, 1;
               0, 0, 1, 0, 0, 0;
               0, -1, 0, 0, 0, 0;
               0, 0, 0, 0, 0, 0]
  | 4, 0 => !![0, 0, 1, 0, 0, 0;
               0, 0, 0, 0, 0, 0;
               0, 0, 0, 0, 1, 0;
               0, 1, 0, 0, 0, 0;
               -1, 0, 0, 0, 0, 0;
               -1, 0, 0, 1, 0, 0]
  | 4, 5 => -armShift 6 1
  | 5, 4 => armProj 6 4
  | 5, 6 => armShift 6 1
  | 6, 5 => armProj 6 3
  | 6, 7 => -armShift 6 1
  | 7, 6 => armProj 6 2
  | 7, 8 => armShift 6 1
  | 8, 7 => armProj 6 1
  | _, _ => 0

/-- **Graphs containing an affine `E₈` have nonzero cyclic classes in degree twelve.** If `G`
contains a copy of the affine diagram `E₈`, not necessarily induced, then over every nontrivial
commutative ring some element of path degree twelve of the signless preprojective algebra `Π⁺(G)`
does not lie in the commutator submodule `[Π⁺(G), Π⁺(G)]`: its class in the cyclic quotient is
nonzero.

The element is the product of the backtracks through the nodes `1`, `2`, `4`, `4`, `4`, `2` at the
image of the trivalent node `0`; its image under the representation of this file has trace one. -/
theorem exists_mem_signlessPreprojectiveGrade_twelve_notMem_commutatorSubmodule [Nontrivial k]
    (hG : AffineDynkinType.E8.graph.IsContained G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 12,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨f⟩ := hG
  simpa using exists_notMem_commutatorSubmodule_of_intMatrix k f affineE8Matrix
    (by simp only [AffineDynkinType.graph_E8_adj]; decide) (by decide) (c := 0)
    [⟨1, (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
      ⟨2, (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
      ⟨4, (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
      ⟨4, (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
      ⟨4, (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩,
      ⟨2, (AffineDynkinType.graph_E8_adj _ _).2 (by decide)⟩] (by simp) (by decide)

end TauCeti
