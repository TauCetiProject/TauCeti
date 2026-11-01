/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing

/-!
# Hochschild classes of zigzag algebras from matrix representations

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, regarded as an
`A∞` algebra whose only operation is the product (`TauCeti.zigzagStrictAInfinityAlgebra`). This
file turns the matrix representations of the signless preprojective algebra `Π⁺(G)`, which detect
nonzero classes in its cyclic quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]`
(`TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_trace_ne_zero`),
into nonzero Hochschild classes of `Z` when `G` is bipartite: a closed walk of length `n + 2 ≥ 3`
acting with nonzero trace gives `HH^{n + 2, -n}(Z, Z) ≠ 0`. This is the passage, through the
quadratic duality between `Z` and `Π⁺(G)`, from cyclic classes of the preprojective algebra to
Hochschild classes of the zigzag algebra which Liu and Wang use to decide intrinsic formality.

## The functional

Let `γ i j` be the matrix of the arrow `i → j` in a representation of `Π⁺(G)` with `kᵐ` at every
vertex, so that `∑_{w ∼ v} γ w v * γ v w = 0` at every vertex `v`. The block matrices
`β d = E_{d.snd, d.fst} ⊗ γ d.fst d.snd` of the darts satisfy the signless relations in the
form required by the word pairing (`TauCeti.zigzagWordPairing`). A two-colouring `ε : V → {±1}` of
`G` gives the block sign matrix `S = diag(ε)`, which anticommutes with every `β d`, so that the
supertrace `y ↦ tr(S y)` is anticyclic on the `β d`. On the product of the `β` along a closed walk
`w` based at `v` it takes the value `ε v · tr(γ_w)`, for `γ_w` the product of the `γ` along `w`.
So when `tr(γ_w) ≠ 0`, the loop operation of `w` is a Hochschild cocycle of `Z` which is not a
coboundary
(`not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_anticyclic`).

## Affine diagrams and trees

The representations of the affine diagrams `E₆`, `E₇` and `E₈` constructed for the cyclic quotient
(`TauCeti.affineE6Matrix`, `TauCeti.affineE7Matrix` and `TauCeti.affineE8Matrix`) have products of
backtracks of trace one at the trivalent node, in path degrees `6`, `8` and `12`. Hence a bipartite
graph containing a copy of one of these diagrams has `HH^{6, -4}`, `HH^{8, -6}` or `HH^{12, -10}`
nonzero, over every nontrivial commutative ring. With the representation of affine `Dₙ`
(`TauCeti.affineDMatrix`) in path degree four, this covers every finite tree which is not a Dynkin
diagram, since such a tree contains a copy of one of these affine diagrams
(`SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Consequently
Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply to
the zigzag algebra of any finite non-Dynkin tree.

## Main results

* `TauCeti.not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero`: a matrix
  representation of the signless preprojective algebra of a subgraph of a bipartite graph `G`, in
  which a closed walk of length `n + 2 ≥ 3` acts with nonzero trace, gives
  `HH^{n + 2, -n}(Z, Z) ≠ 0` for the zigzag algebra `Z` of `G`.
* `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`,
  `TauCeti.not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra`,
  `TauCeti.not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra` and
  `TauCeti.not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra`: the bipartite graphs
  containing an affine `Dₙ`, `E₆`, `E₇` or `E₈`.
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

/-- The block sign matrix acts on the left of a block in the row of `a` by `ε a`. -/
private theorem blockSign_mul_single_kronecker (ε : V → k) (a b : V) (X : Matrix m m k) :
    blockSign ε * (single a b 1 ⊗ₖ X) = ε a • (single a b 1 ⊗ₖ X) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [blockSign]
  · simp [blockSign, h]

/-- The block sign matrix acts on the right of a block in the column of `b` by `ε b`. -/
private theorem single_kronecker_mul_blockSign (ε : V → k) (a b : V) (X : Matrix m m k) :
    (single a b 1 ⊗ₖ X) * blockSign ε = ε b • (single a b 1 ⊗ₖ X) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [blockSign, mul_comm]
  · simp [blockSign, h]

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
    rw [List.ofFn_succ, List.prod_cons, ih (fun t ↦ u t.succ) fun i ↦ hu i.succ,
      List.ofFn_succ (n := N + 1), List.prod_cons, blockArrow, ← mul_kronecker_mul,
      show (u (Fin.succ 0)).snd = (u 0).fst by simpa using (hu 0).symm, single_mul_single_same,
      mul_one, Fin.succ_last]

omit [DecidableEq V] in
/-- **Closed walks detected by a matrix representation of the signless preprojective algebra of a
bipartite graph.** The supertrace of the block matrices of the darts, for a two-colouring of `G`,
is an anticyclic functional; it detects a closed walk along which the matrices have nonzero
trace. -/
private theorem not_hochschildVanishesAt_of_trace_ne_zero [DecidableRel G.Adj]
    (γ : V → V → Matrix m m k)
    (hγ : ∀ v, ∑ w ∈ G.neighborFinset v, γ w v * γ v w = 0) (hG : G.IsBipartite) {n : ℕ}
    (hn : 1 ≤ n) {w : Fin (n + 2) → G.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ γ (w t).fst (w t).snd).prod ≠ 0) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  obtain ⟨c⟩ := hG
  -- The sign of the colouring changes along every edge.
  set ε : V → k := fun v ↦ if c v = 0 then 1 else -1 with hεdef
  have hε (d : G.Dart) : ε d.fst = -ε d.snd := by
    have h := c.valid d.adj
    simp only [hεdef]
    generalize c d.fst = a at h ⊢
    generalize c d.snd = b at h ⊢
    fin_cases a <;> fin_cases b <;> simp at h ⊢
  -- The supertrace `y ↦ tr(S y)`.
  let f : Matrix (V × m) (V × m) k →ₗ[k] k :=
    traceLinearMap (V × m) k k ∘ₗ LinearMap.mulLeft k (blockSign ε)
  have hf (y : Matrix (V × m) (V × m) k) : f y = trace (blockSign ε * y) := rfl
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_anticyclic hn (blockArrow γ)
    (sum_blockArrow_mul_blockArrow_symm γ hγ) f (fun e y ↦ ?_) hw ?_
  · rw [hf, hf, ← mul_assoc, trace_mul_comm, ← mul_assoc, blockArrow,
      single_kronecker_mul_blockSign, ← mul_assoc (blockSign ε), blockSign_mul_single_kronecker,
      smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul, hε, neg_mul]
  · -- The product along the closed walk is a block at its base vertex.
    have hlast : (w (Fin.last (n + 1))).fst = (w 0).snd := by
      simpa using hw (Fin.last (n + 1))
    rw [hf, list_prod_blockArrow γ w fun i ↦ by simpa [Fin.coeSucc_eq_succ] using hw i.castSucc,
      hlast, blockSign_mul_single_kronecker, trace_smul, trace_kronecker, trace_single_eq_same,
      one_mul, smul_eq_mul]
    by_cases h : c (w 0).snd = 0 <;> simpa [hεdef, h] using htr

end Blocks

/-! ### Detection by matrix representations of subgraphs -/

section Subgraph

variable [Finite V] {W : Type*} [Fintype W] {H : SimpleGraph W}

/-- **Hochschild classes of zigzag algebras from matrix representations of a subgraph.** Let `G` be
a bipartite graph with no isolated vertex, `f` a copy of a graph `H` in `G`, not necessarily
induced, and `β` a family of matrices on `H` satisfying the signless relations
`∑_{y ∼ x} β y x * β x y = 0`, a representation of `Π⁺(H)`. If the product of the matrices along a
closed walk `u` of length `n + 2 ≥ 3` in `H`, read in product order, has nonzero trace, then the
loop operation of the image of `u` in `G` is a Hochschild cocycle of the strict zigzag algebra
`Z` of `G` which is not a coboundary: `HH^{n + 2, -n}(Z, Z) ≠ 0`. -/
theorem not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero [DecidableRel H.Adj]
    (β : W → W → Matrix m m k) (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0)
    (f : H.Copy G) (hG : G.IsBipartite) {n : ℕ} (hn : 1 ≤ n) {u : Fin (n + 2) → H.Dart}
    (hu : ∀ i, (u i).fst = (u (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (u t).fst (u t).snd).prod ≠ 0) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  have := Fintype.ofFinite V
  refine not_hochschildVanishesAt_of_trace_ne_zero (f.extendByZero β)
    (f.sum_extendByZero_mul_extendByZero β hβ) hG hn (w := fun t ↦ f.toHom.mapDart (u t))
    (fun i ↦ by simp [SimpleGraph.Hom.mapDart_apply, hu i]) ?_
  simpa [SimpleGraph.Hom.mapDart_apply, SimpleGraph.Copy.extendByZero_apply_apply_of_adj,
    SimpleGraph.Dart.adj] using htr

/-- The integer version of
`TauCeti.not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero`: an integer
matrix family on `H` vanishing off the edges and satisfying the signless relations, whose product
along a closed walk has trace one, gives a nonzero Hochschild class over every nontrivial
commutative ring. -/
private theorem not_hochschildVanishesAt_of_trace_eq_one [Nontrivial k]
    (β : W → W → Matrix m m ℤ) (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0)
    (h : ∀ x, ∑ y, β y x * β x y = 0) (f : H.Copy G) (hG : G.IsBipartite) {n : ℕ} (hn : 1 ≤ n)
    {u : Fin (n + 2) → H.Dart} (hu : ∀ i, (u i).fst = (u (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (u t).fst (u t).snd).prod = 1) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero
    (fun x y ↦ (Int.castRingHom k).mapMatrix (β x y))
    (sum_mapMatrix_intCast_mul_mapMatrix_intCast k β h₀ h) f hG hn hu ?_
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

/-- **Bipartite graphs containing an affine `E₆` have `HH^{6, -4}` nonzero.** If a bipartite
graph `G` with no isolated vertex contains a copy of the affine diagram `E₆`, not necessarily
induced, then over every nontrivial commutative ring the Hochschild cohomology `HH^{6, -4}` of the
strict zigzag algebra of `G` is nonzero: the loop operation of the closed walk of length six through
the backtracks `0 → 1 → 0`, `0 → 1 → 0` and `0 → 3 → 0` at the image of the trivalent node is a
Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra (hb : G.IsBipartite)
    (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨6, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_of_trace_eq_one affineE6Matrix
    (fun _ _ ↦ affineE6Matrix_eq_zero_of_not_adj) sum_affineE6Matrix_mul_affineE6Matrix f hb
    (n := 4) (by norm_num) (u := affineE6Walk) (by decide)
    (by simpa [List.ofFn_succ, affineE6Walk, mul_assoc] using trace_affineE6Matrix_backtracks)

/-- **Bipartite graphs containing an affine `E₇` have `HH^{8, -6}` nonzero.** If a bipartite
graph `G` with no isolated vertex contains a copy of the affine diagram `E₇`, not necessarily
induced, then over every nontrivial commutative ring the Hochschild cohomology `HH^{8, -6}` of the
strict zigzag algebra of `G` is nonzero: the loop operation of the closed walk of length eight
through three backtracks `0 → 2 → 0` and the backtrack `0 → 5 → 0` at the image of the trivalent
node is a Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra (hb : G.IsBipartite)
    (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨8, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_of_trace_eq_one affineE7Matrix
    (fun _ _ ↦ affineE7Matrix_eq_zero_of_not_adj) sum_affineE7Matrix_mul_affineE7Matrix f hb
    (n := 6) (by norm_num) (u := affineE7Walk) (by decide)
    (by simpa [List.ofFn_succ, affineE7Walk, mul_assoc] using trace_affineE7Matrix_backtracks)

/-- **Bipartite graphs containing an affine `E₈` have `HH^{12, -10}` nonzero.** If a bipartite
graph `G` with no isolated vertex contains a copy of the affine diagram `E₈`, not necessarily
induced, then over every nontrivial commutative ring the Hochschild cohomology `HH^{12, -10}` of
the strict zigzag algebra of `G` is nonzero: the loop operation of the closed walk of length twelve
through the backtracks at the image of the trivalent node through the nodes `1`, `2`, `4`, `4`,
`4` and `2` is a Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra (hb : G.IsBipartite)
    (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨12, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  exact not_hochschildVanishesAt_of_trace_eq_one affineE8Matrix
    (fun _ _ ↦ affineE8Matrix_eq_zero_of_not_adj) sum_affineE8Matrix_mul_affineE8Matrix f hb
    (n := 10) (by norm_num) (u := affineE8Walk) (by decide)
    (by simpa [List.ofFn_succ, affineE8Walk, mul_assoc] using trace_affineE8Matrix_backtracks)

/-- **Bipartite graphs containing an affine `Dₙ` have `HH^{4, -2}` nonzero.** If a bipartite graph
`G` with no isolated vertex contains a copy of the affine diagram `Dₙ` (`n ≥ 4`), not necessarily
induced, then over every nontrivial commutative ring the Hochschild cohomology `HH^{4, -2}` of the
strict zigzag algebra of `G` is nonzero: the loop operation of the closed walk
`1 → 0 → 1 → (n - 1) → 1` at the image of the branch node `1` is a Hochschild cocycle which is not
a coboundary. -/
theorem not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained
    (hb : G.IsBipartite) {n : ℕ}
    (hn : 4 ≤ n) (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  have hnodes := AffineDynkinType.nodes_D n
  let c : Fin (AffineDynkinType.D n).nodes := ⟨1, by omega⟩
  let a : Fin (AffineDynkinType.D n).nodes := ⟨0, by omega⟩
  let b : Fin (AffineDynkinType.D n).nodes := ⟨n - 1, by omega⟩
  have h₁ : (AffineDynkinType.D n).graph.Adj c a :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inl ⟨rfl, show 1 ≤ n - 2 by omega⟩))
  have h₂ : (AffineDynkinType.D n).graph.Adj c b :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero
    (fun i j : Fin (AffineDynkinType.D n).nodes ↦ affineDMatrix k n i j)
    (sum_affineDMatrix_mul_affineDMatrix k hn) f hb
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
      not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained hG.isBipartite hn h⟩
  · exact ⟨⟨6, by norm_num⟩, by simp,
      not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra hG.isBipartite h⟩
  · exact ⟨⟨8, by norm_num⟩, by simp,
      not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra hG.isBipartite h⟩
  · exact ⟨⟨12, by norm_num⟩, by simp,
      not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra hG.isBipartite h⟩

end SimpleGraph.IsTree
