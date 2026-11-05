/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing

/-!
# Hochschild classes of zigzag algebras from matrix representations

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, regarded as an
`A∞` algebra whose only operation is the product (`TauCeti.zigzagStrictAInfinityAlgebra`). This file
turns the matrix representations of the signless preprojective algebra `Π⁺(G)`, which detect nonzero
classes in its cyclic quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]`
(`TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_trace_ne_zero`), into
nonzero Hochschild classes of `Z` when they live on a bipartite subgraph of `G`: a closed walk of
length `n + 2 ≥ 3` acting with nonzero trace gives `HH^{n + 2, -n}(Z, Z) ≠ 0`. This is the passage,
through the quadratic duality between `Z` and `Π⁺(G)`, from cyclic classes of the preprojective
algebra to Hochschild classes of the zigzag algebra which Liu and Wang use to decide intrinsic
formality.

## The functional

Let `γ i j` be the matrix of the arrow `i → j` in a representation of `Π⁺(G)` with `kᵐ` at every
vertex, so that `∑_{w ∼ v} γ w v * γ v w = 0` at every vertex `v`. The block matrices
`β d = E_{d.snd, d.fst} ⊗ γ d.fst d.snd` of the darts satisfy the signless relations in the form
required by the word pairing (`TauCeti.zigzagWordPairing`). A sign `ε : V → {±1}` which changes
along every dart carrying a nonzero matrix, such as a two-colouring of a bipartite subgraph
supporting the representation, gives the block sign matrix `S = diag(ε)`, which anticommutes with
every `β d`, so that the supertrace `y ↦ tr(S y)` is anticyclic on the `β d`. On the product of the
`β` along a closed walk `w` based at `v` it takes the value `ε v · tr(γ_w)`, for `γ_w` the product
of the `γ` along `w`. So when `tr(γ_w) ≠ 0`, the loop operation of `w` is a Hochschild cocycle of
`Z` which is not a coboundary
(`not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_anticyclic`).

## Affine diagrams and trees

The representations of the affine diagrams `E₆`, `E₇` and `E₈` constructed for the cyclic quotient
(`TauCeti.affineE6Matrix`, `TauCeti.affineE7Matrix` and `TauCeti.affineE8Matrix`) have products of
backtracks of trace one at the trivalent node, in path degrees `6`, `8` and `12`. Since these
diagrams are bipartite, every graph containing a copy of one of them has `HH^{6, -4}`, `HH^{8, -6}`
or `HH^{12, -10}` nonzero, over every nontrivial commutative ring. With the representation of affine
`Dₙ` (`TauCeti.affineDMatrix`) in path degree four, this covers every finite tree which is not a
Dynkin diagram, since such a tree contains a copy of one of these affine diagrams
(`SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Consequently
Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply to
the zigzag algebra of any finite non-Dynkin tree.

## Main results

* `TauCeti.not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero`: a matrix
  representation of the signless preprojective algebra of a bipartite subgraph of `G`, in which a
  closed walk of length `n + 2 ≥ 3` acts with nonzero trace, gives
  `HH^{n + 2, -n}(Z, Z) ≠ 0` for the zigzag algebra `Z` of `G`.
* `TauCeti.not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_eq_one`: the same for an
  integer matrix family whose product along the closed walk has trace one, over every nontrivial
  commutative ring.
* `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`,
  `TauCeti.not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra`,
  `TauCeti.not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra` and
  `TauCeti.not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra`: the graphs containing
  an affine `Dₙ`, `E₆`, `E₇` or `E₈`.
* `SimpleGraph.IsTree.exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra`: the zigzag
  algebra of a finite non-Dynkin tree has a nonzero Hochschild class in `HH^{n, 2 - n}` for some
  `n ∈ {4, 6, 8, 12}`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the comparison of zigzag Hochschild
  cohomology with the cyclic quotient of the preprojective algebra.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4, for the
  signless preprojective algebra as the quadratic dual of the zigzag algebra.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
-/

public section

namespace TauCeti

open _root_.Matrix
open scoped Kronecker

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} {hns : ∀ i : V, ∃ j, G.Adj i j}
  {m : Type*} [Fintype m] [DecidableEq m]

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-! ### Block matrices of darts -/

section Blocks

variable [Fintype V] [DecidableEq V]

/-- The block matrix of a dart `d`: the matrix `γ d.fst d.snd`, from the block of `d.fst` to the
block of `d.snd`. -/
private def blockArrow (γ : V → V → Matrix m m k) (d : G.Dart) : Matrix (V × m) (V × m) k :=
  single d.snd d.fst 1 ⊗ₖ γ d.fst d.snd

/-- The block sign matrix of a function `ε` on the vertices. -/
private def blockSign (ε : V → k) : Matrix (V × m) (V × m) k :=
  diagonal fun p ↦ ε p.1

omit [DecidableEq m] in
/-- Matrices satisfying the signless relations give block matrices of darts satisfying them in the
form of the word pairing. -/
private theorem sum_blockArrow_mul_blockArrow_symm [DecidableRel G.Adj] (γ : V → V → Matrix m m k)
    (hγ : ∀ v, ∑ w ∈ G.neighborFinset v, γ w v * γ v w = 0) (v : V) :
    ∑ d : G.Dart with d.snd = v, blockArrow γ d * blockArrow γ d.symm = 0 := by
  have h (d : G.Dart) (hd : d ∈ Finset.univ.filter fun d : G.Dart ↦ d.snd = v) :
      blockArrow γ d * blockArrow γ d.symm = single v v 1 ⊗ₖ (γ d.fst v * γ v d.fst) := by
    rw [(Finset.mem_filter.1 hd).2.symm]
    simp [blockArrow, ← mul_kronecker_mul]
  -- Pull the block at `v` out of the sum.
  have hsum : ∑ d : G.Dart with d.snd = v, single v v (1 : k) ⊗ₖ (γ d.fst v * γ v d.fst) =
      single v v 1 ⊗ₖ ∑ d : G.Dart with d.snd = v, γ d.fst v * γ v d.fst := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [Matrix.sum_apply, Finset.mul_sum]
  -- The darts with head `v` are indexed by their tails, the neighbours of `v`.
  have hbij : ∑ d : G.Dart with d.snd = v, γ d.fst v * γ v d.fst =
      ∑ w ∈ G.neighborFinset v, γ w v * γ v w := by
    refine Finset.sum_bij (fun d _ ↦ d.fst) (fun d hd ↦ ?_) (fun d₁ hd₁ d₂ hd₂ h ↦ ?_)
      (fun w hw ↦ ?_) fun _ _ ↦ rfl
    · rw [Finset.mem_filter] at hd
      rw [SimpleGraph.mem_neighborFinset, ← hd.2]
      exact d.adj.symm
    · rw [Finset.mem_filter] at hd₁ hd₂
      exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h (hd₁.2.trans hd₂.2.symm))
    · rw [SimpleGraph.mem_neighborFinset] at hw
      exact ⟨⟨(w, v), hw.symm⟩, by simp, rfl⟩
  rw [Finset.sum_congr rfl h, hsum, hbij, hγ v, kronecker_zero]

/-- The product of the block matrices along a walk is the block, from the tail of the walk to its
head, of the product of the matrices along the walk. -/
private theorem list_prod_blockArrow (γ : V → V → Matrix m m k) {N : ℕ}
    (u : Fin (N + 1) → G.Dart) (hu : ∀ i : Fin N, (u i.castSucc).fst = (u i.succ).snd) :
    (List.ofFn fun t ↦ blockArrow γ (u t)).prod =
      single (u 0).snd (u (Fin.last N)).fst 1 ⊗ₖ
        (List.ofFn fun t ↦ γ (u t).fst (u t).snd).prod := by
  induction N with
  | zero => simp [blockArrow]
  | succ N ih =>
    -- The second dart starts where the first one ends.
    have h₀ : (u (Fin.succ 0)).snd = (u 0).fst := by simpa using (hu 0).symm
    rw [List.ofFn_succ, List.prod_cons, ih (fun t ↦ u t.succ) fun i ↦ hu i.succ,
      List.ofFn_succ (n := N + 1), List.prod_cons, blockArrow, ← mul_kronecker_mul, h₀]
    simp only [single_mul_single_same, mul_one, Fin.succ_last]

/-- **The supertrace is anticyclic on the block matrices of darts.** For a function `ε` on the
vertices which changes sign along a dart `d`, unless the matrix of `d` vanishes, the functional
`y ↦ tr(S y)`, for `S` the block sign matrix of `ε`, is anticyclic on the block matrix of `d`. -/
private theorem trace_blockSign_mul_mul_blockArrow (ε : V → k) (γ : V → V → Matrix m m k)
    (d : G.Dart) (hd : γ d.fst d.snd ≠ 0 → ε d.fst = -ε d.snd) (y : Matrix (V × m) (V × m) k) :
    trace (blockSign ε * (y * blockArrow γ d)) = -trace (blockSign ε * (blockArrow γ d * y)) := by
  by_cases h : γ d.fst d.snd = 0
  · simp [blockArrow, h]
  -- The sign matrix acts on the block of `d` by `ε d.fst` on the right and `ε d.snd` on the left.
  have hr : blockArrow γ d * blockSign ε = ε d.fst • blockArrow γ d :=
    single_kronecker_mul_diagonal ε _ _ _ _
  have hl : blockSign ε * blockArrow γ d = ε d.snd • blockArrow γ d :=
    diagonal_mul_single_kronecker ε _ _ _ _
  rw [← mul_assoc, trace_mul_comm, ← mul_assoc, ← mul_assoc, hr, hl, hd h]
  simp only [neg_smul, neg_mul, smul_mul_assoc, trace_neg, trace_smul]

omit [DecidableEq V] in
/-- **Closed walks detected by a matrix representation of the signless preprojective algebra.**
For a sign `ε` on the vertices which changes along every dart carrying a nonzero matrix, the
supertrace of the block matrices of the darts is an anticyclic functional; it detects a closed walk
along which the matrices have nonzero trace. -/
private theorem not_hochschildVanishesAt_of_trace_ne_zero [DecidableRel G.Adj]
    (γ : V → V → Matrix m m k)
    (hγ : ∀ v, ∑ w ∈ G.neighborFinset v, γ w v * γ v w = 0) (ε : V → ℤˣ)
    (hε : ∀ i j, γ i j ≠ 0 → ε i = -ε j) {n : ℕ}
    (hn : 1 ≤ n) {w : Fin (n + 2) → G.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ γ (w t).fst (w t).snd).prod ≠ 0) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  -- The supertrace `y ↦ tr(S y)`.
  let s : V → k := fun v ↦ ((ε v : ℤ) : k)
  let f : Matrix (V × m) (V × m) k →ₗ[k] k :=
    traceLinearMap (V × m) k k ∘ₗ LinearMap.mulLeft k (blockSign s)
  have hf (y : Matrix (V × m) (V × m) k) : f y = trace (blockSign s * y) := rfl
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_anticyclic hn (blockArrow γ)
    (sum_blockArrow_mul_blockArrow_symm γ hγ) f
    (fun e y ↦ trace_blockSign_mul_mul_blockArrow s γ e (fun h ↦ by simp [s, hε _ _ h]) y) hw ?_
  -- The product along the closed walk is a block at its base vertex.
  have hlast : (w (Fin.last (n + 1))).fst = (w 0).snd := by
    simpa using hw (Fin.last (n + 1))
  have hprod := list_prod_blockArrow γ w fun i ↦ by simpa [Fin.coeSucc_eq_succ] using hw i.castSucc
  rw [hlast] at hprod
  rw [hf, hprod, blockSign, diagonal_mul_single_kronecker]
  simp only [trace_smul, trace_kronecker, trace_single_eq_same, one_mul, smul_eq_mul]
  exact mt ((ε (w 0).snd).isUnit.map (Int.castRingHom k)).mul_right_eq_zero.1 htr

end Blocks

/-! ### Detection by matrix representations of subgraphs -/

section Subgraph

variable [Finite V] {W : Type*} [Fintype W] {H : SimpleGraph W}

/-- **Hochschild classes of zigzag algebras from matrix representations of a subgraph.** Let `G` be
a graph with no isolated vertex, `f` a copy of a bipartite graph `H` in `G`, not necessarily
induced, and `β` a family of matrices on `H` satisfying the signless relations
`∑_{y ∼ x} β y x * β x y = 0`, a representation of `Π⁺(H)`. If the product of the matrices along a
closed walk `u` of length `n + 2 ≥ 3` in `H`, read in product order, has nonzero trace, then the
loop operation of the image of `u` in `G` is a Hochschild cocycle of the strict zigzag algebra
`Z` of `G` which is not a coboundary: `HH^{n + 2, -n}(Z, Z) ≠ 0`. -/
theorem not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero [DecidableRel H.Adj]
    (β : W → W → Matrix m m k) (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0)
    (f : H.Copy G) (hH : H.IsBipartite) {n : ℕ} (hn : 1 ≤ n) {u : Fin (n + 2) → H.Dart}
    (hu : ∀ i, (u i).fst = (u (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (u t).fst (u t).snd).prod ≠ 0) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c⟩ := hH
  -- The sign of a two-colouring of `H`, extended arbitrarily off the copy.
  let ε : V → ℤˣ := Function.extend f (fun x ↦ (-1) ^ (c x : ℕ)) 1
  have hε (x : W) : ε (f x) = (-1) ^ (c x : ℕ) := f.injective.extend_apply _ _ x
  refine not_hochschildVanishesAt_of_trace_ne_zero (f.extendByZero β)
    (f.sum_extendByZero_mul_extendByZero β hβ) ε (fun i j hij ↦ ?_) hn
    (w := fun t ↦ f.toHom.mapDart (u t)) (fun i ↦ by simp [SimpleGraph.Hom.mapDart_apply, hu i]) ?_
  · -- A nonzero entry of the extension sits on the image of an edge of `H`, whose ends have
    -- different colours.
    obtain ⟨x, rfl⟩ : i ∈ Set.range f := by
      by_contra hi
      exact hij (f.extendByZero_eq_zero_of_notMem_range_left β hi j)
    obtain ⟨y, rfl⟩ : j ∈ Set.range f := by
      by_contra hj
      exact hij (f.extendByZero_eq_zero_of_notMem_range_right β _ hj)
    have hxy : H.Adj x y := by
      by_contra hxy
      exact hij (f.extendByZero_apply_apply_of_not_adj β hxy)
    have hc := c.valid hxy
    rw [hε, hε]
    generalize c x = a at hc ⊢
    generalize c y = b at hc ⊢
    fin_cases a <;> fin_cases b <;> simp at hc ⊢
  simpa [SimpleGraph.Hom.mapDart_apply, SimpleGraph.Copy.extendByZero_apply_apply_of_adj,
    SimpleGraph.Dart.adj] using htr

/-- The integer version of
`TauCeti.not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero`: an integer
matrix family on a bipartite subgraph `H` of `G`, vanishing off the edges of `H` and satisfying the
signless relations, whose product along a closed walk of length `n + 2 ≥ 3` has trace one, gives
`HH^{n + 2, -n}(Z, Z) ≠ 0` over every nontrivial commutative ring. -/
theorem not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_eq_one [Nontrivial k]
    (β : W → W → Matrix m m ℤ) (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0)
    (h : ∀ x, ∑ y, β y x * β x y = 0) (f : H.Copy G) (hH : H.IsBipartite) {n : ℕ} (hn : 1 ≤ n)
    {u : Fin (n + 2) → H.Dart} (hu : ∀ i, (u i).fst = (u (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (u t).fst (u t).snd).prod = 1) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero
    (fun x y ↦ (Int.castRingHom k).mapMatrix (β x y))
    (sum_mapMatrix_intCast_mul_mapMatrix_intCast k β h₀ h) f hH hn hu ?_
  have hmap : (List.ofFn fun t ↦ (Int.castRingHom k).mapMatrix (β (u t).fst (u t).snd)) =
      (List.ofFn fun t ↦ β (u t).fst (u t).snd).map (Int.castRingHom k).mapMatrix := by
    simp [List.map_ofFn, Function.comp_def]
  rw [hmap, ← map_list_prod, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, htr, map_one]
  exact one_ne_zero

end Subgraph

/-! ### Affine diagrams -/

section Affine

variable [Finite V]

/-- The closed walk `0 → 3 → 0 → 1 → 0 → 1 → 0` at the trivalent node of the affine diagram `E₆`,
in product order: the product of the backtracks through `1`, `1` and `3`. -/
private def affineE6Walk : Fin 6 → AffineDynkinType.E6.graph.Dart :=
  ![⟨(1, 0), by simp⟩, ⟨(0, 1), by simp⟩, ⟨(1, 0), by simp⟩, ⟨(0, 1), by simp⟩,
    ⟨(3, 0), by simp⟩, ⟨(0, 3), by simp⟩]

/-- The closed walk at the trivalent node of the affine diagram `E₇`, in product order, which is
the product of the backtracks through `2`, `2`, `2` and `5`. -/
private def affineE7Walk : Fin 8 → AffineDynkinType.E7.graph.Dart :=
  ![⟨(2, 0), by simp⟩, ⟨(0, 2), by simp⟩, ⟨(2, 0), by simp⟩, ⟨(0, 2), by simp⟩,
    ⟨(2, 0), by simp⟩, ⟨(0, 2), by simp⟩, ⟨(5, 0), by simp⟩, ⟨(0, 5), by simp⟩]

/-- The closed walk at the trivalent node of the affine diagram `E₈`, in product order, which is
the product of the backtracks through `1`, `2`, `4`, `4`, `4` and `2`. -/
private def affineE8Walk : Fin 12 → AffineDynkinType.E8.graph.Dart :=
  ![⟨(1, 0), by simp⟩, ⟨(0, 1), by simp⟩, ⟨(2, 0), by simp⟩, ⟨(0, 2), by simp⟩,
    ⟨(4, 0), by simp⟩, ⟨(0, 4), by simp⟩, ⟨(4, 0), by simp⟩, ⟨(0, 4), by simp⟩,
    ⟨(4, 0), by simp⟩, ⟨(0, 4), by simp⟩, ⟨(2, 0), by simp⟩, ⟨(0, 2), by simp⟩]

variable [Nontrivial k]

/-- **Graphs containing an affine `E₆` have `HH^{6, -4}` nonzero.** If a graph `G` with no isolated
vertex contains a copy of the affine diagram `E₆`, not necessarily induced, then over every
nontrivial commutative ring the Hochschild cohomology `HH^{6, -4}` of the strict zigzag algebra of
`G` is nonzero: the loop operation of the closed walk of length six through the backtracks
`0 → 1 → 0`, `0 → 1 → 0` and `0 → 3 → 0` at the image of the trivalent node is a Hochschild cocycle
which is not a coboundary. -/
theorem not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra
    (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨6, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_eq_one
    affineE6Matrix (fun _ _ ↦ affineE6Matrix_eq_zero_of_not_adj)
    sum_affineE6Matrix_mul_affineE6Matrix f AffineDynkinType.isBipartite_graph_E6
    (n := 4) (by norm_num) (u := affineE6Walk) (by decide)
    (by simpa [List.ofFn_succ, affineE6Walk, mul_assoc] using trace_affineE6Matrix_backtracks)

/-- **Graphs containing an affine `E₇` have `HH^{8, -6}` nonzero.** If a graph `G` with no isolated
vertex contains a copy of the affine diagram `E₇`, not necessarily induced, then over every
nontrivial commutative ring the Hochschild cohomology `HH^{8, -6}` of the strict zigzag algebra of
`G` is nonzero: the loop operation of the closed walk of length eight through three backtracks
`0 → 2 → 0` and the backtrack `0 → 5 → 0` at the image of the trivalent node is a Hochschild
cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra
    (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨8, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_eq_one
    affineE7Matrix (fun _ _ ↦ affineE7Matrix_eq_zero_of_not_adj)
    sum_affineE7Matrix_mul_affineE7Matrix f AffineDynkinType.isBipartite_graph_E7
    (n := 6) (by norm_num) (u := affineE7Walk) (by decide)
    (by simpa [List.ofFn_succ, affineE7Walk, mul_assoc] using trace_affineE7Matrix_backtracks)

/-- **Graphs containing an affine `E₈` have `HH^{12, -10}` nonzero.** If a graph `G` with no
isolated vertex contains a copy of the affine diagram `E₈`, not necessarily induced, then over every
nontrivial commutative ring the Hochschild cohomology `HH^{12, -10}` of the strict zigzag algebra of
`G` is nonzero: the loop operation of the closed walk of length twelve through the backtracks at the
image of the trivalent node through the nodes `1`, `2`, `4`, `4`, `4` and `2` is a Hochschild
cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra
    (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨12, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_eq_one
    affineE8Matrix (fun _ _ ↦ affineE8Matrix_eq_zero_of_not_adj)
    sum_affineE8Matrix_mul_affineE8Matrix f AffineDynkinType.isBipartite_graph_E8
    (n := 10) (by norm_num) (u := affineE8Walk) (by decide)
    (by simpa [List.ofFn_succ, affineE8Walk, mul_assoc] using trace_affineE8Matrix_backtracks)

/-- **Graphs containing an affine `Dₙ` have `HH^{4, -2}` nonzero.** If a graph `G` with no isolated
vertex contains a copy of the affine diagram `Dₙ` (`n ≥ 4`), not necessarily induced, then over
every nontrivial commutative ring the Hochschild cohomology `HH^{4, -2}` of the strict zigzag
algebra of `G` is nonzero: the loop operation of the closed walk `1 → 0 → 1 → (n - 1) → 1` at the
image of the branch node `1` is a Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained {n : ℕ}
    (hn : 4 ≤ n) (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  have hnodes := AffineDynkinType.nodes_D n
  let c : Fin (AffineDynkinType.D n).nodes := ⟨1, by omega⟩
  let a : Fin (AffineDynkinType.D n).nodes := ⟨0, by omega⟩
  let b : Fin (AffineDynkinType.D n).nodes := ⟨n - 1, by omega⟩
  have h1n : 1 ≤ n - 2 := by omega
  have h₁ : (AffineDynkinType.D n).graph.Adj c a :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inl ⟨rfl, h1n⟩))
  have h₂ : (AffineDynkinType.D n).graph.Adj c b :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero
    (fun i j : Fin (AffineDynkinType.D n).nodes ↦ affineDMatrix k n i j)
    (sum_affineDMatrix_mul_affineDMatrix k hn) f (AffineDynkinType.isBipartite_graph_D hn)
    (n := 2) (by norm_num)
    (u := ![⟨(b, c), h₂.symm⟩, ⟨(c, b), h₂⟩, ⟨(a, c), h₁.symm⟩, ⟨(c, a), h₁⟩])
    (fun i ↦ by fin_cases i <;> rfl) ?_
  have htr := trace_affineDMatrix_backtracks k hn
  simp only [mul_assoc] at htr
  simp [List.ofFn_succ, c, a, b, htr]

end Affine

end TauCeti

/-! ### Trees -/

namespace SimpleGraph.IsTree

open TauCeti

variable {k : Type*} [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
  {hns : ∀ i : V, ∃ j, G.Adj i j}

/-- **The zigzag algebra of a non-Dynkin tree has a nonzero higher Hochschild class.** If a finite
tree `G` is not isomorphic to the diagram of any valid Dynkin type, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{n, 2 - n}` of the strict zigzag algebra of `G` is
nonzero for some `n ∈ {4, 6, 8, 12}`: some loop operation of a closed walk of length `n` is a
Hochschild cocycle which is not a coboundary. In particular Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply. -/
theorem exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ n : {n : ℕ // 1 < n}, (n : ℕ) ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ¬(zigzagStrictAInfinityAlgebra k hns).HochschildVanishesAt n := by
  classical
  have := Fintype.ofFinite V
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨n, hn, h⟩ | h | h | h
  · exact ⟨⟨4, by norm_num⟩, by simp,
      not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained hn h⟩
  · exact ⟨⟨6, by norm_num⟩, by simp,
      not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨8, by norm_num⟩, by simp,
      not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨12, by norm_num⟩, by simp,
      not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra h⟩

end SimpleGraph.IsTree
