/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.LinearAlgebra.Matrix.Diagonal
public import TauCeti.LinearAlgebra.Matrix.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.MatrixRepresentation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Higher Hochschild classes and non-formal deformations from matrix representations

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). This file turns a matrix representation of the signless
preprojective algebra of a bipartite subgraph of `G` into Hochschild classes and non-formal loop
deformations of `Z`: a closed walk whose matrix product has nonzero (or unit, or non-even) trace has
a loop operation which is not a Hochschild coboundary and, under the corresponding obstruction
hypotheses, defines a minimal `A∞` deformation not isomorphic to `Z`.

Let `f` be a copy of a bipartite graph `H` in `G`, not necessarily induced, and let `β x y` be
matrices on the arrows of `H` satisfying the signless relations `∑_{y ∼ x} β y x * β x y = 0`.
Extend `β` by zero to `G` (`SimpleGraph.Copy.extendByZero`) and send each dart `d` of `G` to the
block matrix `E_{d.snd, d.fst} ⊗ β d.fst d.snd`, indexed by pairs of a vertex of `G` and a matrix
index. These block matrices satisfy the signless relations of `G`, which are the local relations of
the quadratic dual of `Z`. Twist the trace by the diagonal matrix `D` with the sign `±1` of the
bipartition of `H` along the copy, and `1` elsewhere:

```text
F(Y) = tr(D Y).
```

Moving the block matrix of a dart `d` across `D` changes the sign `ε d.fst` into `ε d.snd`, which
is its negative whenever the block is nonzero, since then `d` is the image of an edge of `H`. So
`F` is anticyclic on the block matrices, and its word pairing vanishes on Hochschild coboundaries
(`TauCeti.zigzagWordPairing_hochschildDifferential_eq_zero_of_anticyclic`) while mapping formal
even-arity obstructions into `2 k`
(`TauCeti.exists_zigzagWordPairing_obstruction_eq_two_mul_of_anticyclic_of_isFormal`). On the loop
operation of the image of a closed walk `w` of `H`, of length `n + 2`, it takes the value
`±tr(β (w 0) ⋯ β (w (n + 1)))`, in Tau Ceti's later-factor-first order.

This is the Hochschild and `A∞`-deformation counterpart of
`TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_trace_ne_zero`, which
reads the same trace as a nonzero class in the cyclic quotient of the signless preprojective
algebra. Liu and Wang identify that cyclic quotient with the second Hochschild cohomology of the
two-dimensional Ginzburg algebra, and through derived Koszul duality with the Hochschild classes
of `Z` which obstruct its intrinsic formality.

## Main results

* `not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero` and
  `not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one`:
  the loop operation of the image of a closed walk of a bipartite subgraph with nonzero trace (or,
  over every nontrivial commutative ring, integer trace one) is not a Hochschild coboundary.
* `not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_ne_zero` and
  `not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one`: over a `ℚ`-algebra (respectively, over
  every nontrivial `ℚ`-algebra for integer trace one), the corresponding loop deformation is not
  formal in any arity `n + 2 ≥ 3`.
* `not_isFormal_zigzagLoopAInfinityAlgebra_of_not_even_trace` and
  `not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one_of_not_isUnit_two`: in any even arity
  `2 r + 2 ≥ 4`, the corresponding loop deformation is not formal whenever its trace is not even
  (in particular, whenever the integer trace is one and `(2 : k)` is not a unit).
* `not_isFormal_zigzagLoopAInfinityAlgebra_four_of_isUnit_trace` and
  `not_isFormal_zigzagLoopAInfinityAlgebra_four_of_trace_eq_one`: in arity four, a unit trace (or
  integer trace one) gives a non-formal loop deformation over every nontrivial commutative ring.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the comparison of zigzag Hochschild
  cohomology with the cyclic quotient of the preprojective algebra.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 6.1, for the
  quadratic dual of the zigzag algebra.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords _root_.Matrix
open scoped Kronecker

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
  {W : Type*} [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]
  {m : Type*} [Fintype m]

/-! ### Block matrices of darts -/

section Blocks

variable [Fintype V] [DecidableEq V] [DecidableEq m]

/-- The block matrix of the arrow of a dart `d`: the block `β d.fst d.snd` from the block of
`d.fst` to the block of `d.snd`. -/
private noncomputable def dartMatrix (β : V → V → Matrix m m k) (d : G.Dart) :
    Matrix (V × m) (V × m) k :=
  Matrix.single d.snd d.fst 1 ⊗ₖ β d.fst d.snd

omit [DecidableEq m] in
/-- The block matrices of the darts satisfy the signless relations when `β` does. -/
private theorem sum_dartMatrix_mul_dartMatrix_symm [DecidableRel G.Adj]
    (β : V → V → Matrix m m k) (hβ : ∀ v, ∑ w ∈ G.neighborFinset v, β w v * β v w = 0) (v : V) :
    ∑ d : G.Dart with d.snd = v, dartMatrix β d * dartMatrix β d.symm = 0 := by
  have hd (d : G.Dart) (hd : d.snd = v) : dartMatrix β d * dartMatrix β d.symm =
      Matrix.single v v 1 ⊗ₖ (β d.fst v * β v d.fst) := by
    subst hd
    simp [dartMatrix, ← mul_kronecker_mul, SimpleGraph.Dart.symm]
  -- The darts with head `v` are the darts from the neighbours of `v`.
  have hre : ∑ d : G.Dart with d.snd = v, Matrix.single v v (1 : k) ⊗ₖ (β d.fst v * β v d.fst) =
      ∑ w ∈ G.neighborFinset v, Matrix.single v v (1 : k) ⊗ₖ (β w v * β v w) :=
    Finset.sum_bij' (fun d _ ↦ d.fst)
      (fun w hw ↦ ⟨(w, v), ((G.mem_neighborFinset v w).1 hw).symm⟩)
      (fun d hd ↦ (G.mem_neighborFinset _ _).2 ((Finset.mem_filter.1 hd).2 ▸ d.adj.symm))
      (fun w _ ↦ by simp)
      (fun d hd ↦ (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext rfl (Finset.mem_filter.1 hd).2.symm))
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  rw [Finset.sum_congr rfl fun d h ↦ hd d (Finset.mem_filter.1 h).2, hre]
  have hsum : ∑ w ∈ G.neighborFinset v, Matrix.single v v (1 : k) ⊗ₖ (β w v * β v w) =
      Matrix.single v v 1 ⊗ₖ ∑ w ∈ G.neighborFinset v, β w v * β v w := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [Matrix.sum_apply, Finset.mul_sum]
  rw [hsum, hβ, kronecker_zero]

/-- **The twisted trace is anticyclic** on the block matrices of the darts, for a sign `ε` which
changes along every dart carrying a nonzero block. -/
private theorem trace_twist_mul_dartMatrix (β : V → V → Matrix m m k) (ε : V → k)
    (hε : ∀ d : G.Dart, β d.fst d.snd ≠ 0 → ε d.fst = -ε d.snd) (d : G.Dart)
    (Y : Matrix (V × m) (V × m) k) :
    trace ((diagonal ε ⊗ₖ 1) * (Y * dartMatrix β d)) =
      -trace ((diagonal ε ⊗ₖ 1) * (dartMatrix β d * Y)) := by
  by_cases h : β d.fst d.snd = 0
  · simp [dartMatrix, h]
  have hr : dartMatrix β d * (diagonal ε ⊗ₖ 1) = ε d.fst • dartMatrix β d := by
    simp [dartMatrix, ← mul_kronecker_mul, ← smul_kronecker]
  have hl : (diagonal ε ⊗ₖ 1) * dartMatrix β d = ε d.snd • dartMatrix β d := by
    simp [dartMatrix, ← mul_kronecker_mul, ← smul_kronecker]
  rw [trace_mul_cycle', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hr, hl, hε d h]
  simp

omit [Fintype m] [Fintype V] [DecidableEq m] in
/-- Along a copy, the block matrix of the image of a dart of `H` is the block of the dart. -/
private theorem dartMatrix_extendByZero_mapDart (f : H.Copy G) (β : W → W → Matrix m m k)
    (d : H.Dart) :
    dartMatrix (f.extendByZero β) (f.toHom.mapDart d) =
      Matrix.single (f d.snd) (f d.fst) 1 ⊗ₖ β d.fst d.snd := by
  simp [dartMatrix, d.adj]

/-- Extending a bipartition of `H` by `1` outside a copy `f : H.Copy G` produces a linear functional
anticyclic on the block matrices of `f.extendByZero β`, evaluating to
`±tr(β (w 0) ⋯ β (w (n + 1)))` on the single walk `f.mapDart ∘ w`. -/
private theorem exists_bipartite_sign_dartMatrix [DecidableRel G.Adj]
    (f : H.Copy G) (hH : H.IsBipartite)
    (β : W → W → Matrix m m k) {n : ℕ} {w : Fin (n + 2) → H.Dart}
    (hw : ∀ i, (w i).fst = (w (i + 1)).snd) :
    ∃ F : Matrix (V × m) (V × m) k →ₗ[k] k,
      (∀ (e : G.Dart) (Y : Matrix (V × m) (V × m) k),
        F (Y * dartMatrix (f.extendByZero β) e) = -F (dartMatrix (f.extendByZero β) e * Y)) ∧
      ((∑ w' : Fin (n + 2) → G.Dart,
          F (List.ofFn fun t ↦ dartMatrix (f.extendByZero β) (w' t)).prod *
            Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k) w') =
        trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod ∨
      (∑ w' : Fin (n + 2) → G.Dart,
          F (List.ofFn fun t ↦ dartMatrix (f.extendByZero β) (w' t)).prod *
            Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k) w') =
        -trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod) := by
  classical
  obtain ⟨C⟩ := hH
  let s : W → k := fun x ↦ if C x = 0 then 1 else -1
  have hs (x y : W) (h : H.Adj x y) : s x = -s y := by
    have hC := C.valid h
    have h01 : ∀ a b : Fin 2, a ≠ b → a = 0 ∨ b = 0 := by decide
    rcases h01 _ _ hC with h0 | h0
    · have hCy : C y ≠ 0 := h0 ▸ hC.symm
      simp [s, h0, hCy]
    · have hCx : C x ≠ 0 := h0 ▸ hC
      simp [s, h0, hCx]
  let ε : V → k := Function.extend f s 1
  have hεf (x : W) : ε (f x) = s x := f.injective.extend_apply s 1 x
  refine ⟨traceLinearMap _ k k ∘ₗ LinearMap.mulLeft k (diagonal ε ⊗ₖ 1),
    fun e Y ↦ trace_twist_mul_dartMatrix _ ε (fun d hd ↦ ?_) e Y, ?_⟩
  · by_cases h₁ : d.fst ∈ Set.range f
    swap
    · exact absurd (f.extendByZero_eq_zero_of_notMem_range_left β h₁ _) hd
    by_cases h₂ : d.snd ∈ Set.range f
    swap
    · exact absurd (f.extendByZero_eq_zero_of_notMem_range_right β _ h₂) hd
    obtain ⟨x, hx⟩ := h₁
    obtain ⟨y, hy⟩ := h₂
    rw [← hx, ← hy, f.extendByZero_apply_apply] at hd
    rw [← hx, ← hy, hεf, hεf]
    split_ifs at hd with hxy
    · exact hs x y hxy
    · exact absurd rfl hd
  · have hsum : (∑ w' : Fin (n + 2) → G.Dart,
        (traceLinearMap _ k k ∘ₗ LinearMap.mulLeft k (diagonal ε ⊗ₖ 1))
            (List.ofFn fun t ↦ dartMatrix (f.extendByZero β) (w' t)).prod *
          Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k) w') =
        ε (f (w 0).snd) * trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod := by
      rw [Finset.sum_eq_single (fun t ↦ f.toHom.mapDart (w t)) (fun w' _ hw' ↦ by
        rw [Finsupp.single_eq_of_ne hw', mul_zero]) (by simp), Finsupp.single_eq_same, mul_one]
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, traceLinearMap_apply,
        dartMatrix_extendByZero_mapDart]
      rw [list_prod_ofFn_single_kronecker (fun t ↦ f (w t).snd) (fun t ↦ f (w t).fst)
        (fun t ↦ β (w t).fst (w t).snd) fun i ↦ by rw [hw i.castSucc, Fin.coeSucc_eq_succ]]
      have hlast : (w (Fin.last (n + 1))).fst = (w 0).snd := by rw [hw, Fin.last_add_one]
      simp [hlast, ← mul_kronecker_mul, trace_kronecker]
    rw [hsum, hεf]
    simp only [s]
    split_ifs
    · exact Or.inl (one_mul _)
    · exact Or.inr (neg_one_mul _)

end Blocks

/-! ### Non-coboundaries and non-formal deformations from closed walks -/

variable [Finite V] {hns : ∀ i : V, ∃ j, G.Adj i j} [DecidableEq m]

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

omit [DecidableRel H.Adj] [Finite V] [Fintype W] in
/-- Casting an integer matrix product along `Int.castRingHom k` preserves trace `1`. -/
private theorem trace_list_ofFn_mapMatrix_intCast {l : ℕ} (β : W → W → Matrix m m ℤ)
    (w : Fin l → H.Dart) (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod = 1) :
    trace (List.ofFn fun t ↦ (Int.castRingHom k).mapMatrix (β (w t).fst (w t).snd)).prod = 1 := by
  have hmap : (List.ofFn fun t ↦ (Int.castRingHom k).mapMatrix (β (w t).fst (w t).snd)) =
      (List.ofFn fun t ↦ β (w t).fst (w t).snd).map (Int.castRingHom k).mapMatrix :=
    (List.map_ofFn ..).symm
  rw [hmap, trace_list_prod_map_mapMatrix, htr, map_one]

/-- **Higher Hochschild classes of a zigzag algebra from a matrix representation of a bipartite
subgraph.** Let `f` be a copy of a bipartite graph `H` in `G`, not necessarily induced, and let
`β` be a family of matrices on `H` satisfying the signless relations
`∑_{y ∼ x} β y x * β x y = 0`. Let `w` be a closed walk of `H` of length `n + 2`, with `n ≥ 1`,
read in product order, such that `β (w 0) ⋯ β (w (n + 1))` has nonzero trace. Then the loop
operation of the image of `w` in `G`, the operation of arity `n + 2` of the loop deformation with
coefficient one on that walk, is a Hochschild cocycle of the strict zigzag algebra of `G`
(`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`) which is not the
Hochschild differential of any suspended cochain of degree zero. -/
theorem not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero
    (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m k)
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0) {n : ℕ} (hn : 1 ≤ n)
    {w : Fin (n + 2) → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod ≠ 0) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) 1)
            (fst_eq_snd_of_mem_support_single (fun i ↦ by simp [hw i]) 1)).obstruction 𝒵
            ⟨n + 2, by omega⟩ := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨F, hanti, heval⟩ := exists_bipartite_sign_dartMatrix f hH β hw
  refine not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_anticyclic
    hn (dartMatrix (f.extendByZero β))
    (sum_dartMatrix_mul_dartMatrix_symm _ (f.sum_extendByZero_mul_extendByZero β hβ))
    F hanti _ _ ?_
  rcases heval with h | h <;> rw [h]
  · exact htr
  · exact neg_ne_zero.mpr htr

omit [DecidableRel H.Adj] in
/-- **Higher Hochschild classes from an integer matrix representation of a bipartite
subgraph.** An integer matrix family on a bipartite graph `H` which vanishes off the edges and
satisfies the signless relations, together with a closed walk of `H` of length `n + 2`, with
`n ≥ 1`, whose matrix product has trace one, gives along any copy of `H` in `G` a loop operation
of the strict zigzag algebra of `G` which is not a Hochschild coboundary, over every nontrivial
commutative ring. -/
theorem not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one
    [Nontrivial k] (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m ℤ)
    (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0) (hβ : ∀ x, ∑ y, β y x * β x y = 0) {n : ℕ}
    (hn : 1 ≤ n) {w : Fin (n + 2) → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod = 1) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) 1)
            (fst_eq_snd_of_mem_support_single (fun i ↦ by simp [hw i]) 1)).obstruction 𝒵
            ⟨n + 2, by omega⟩ := by
  classical
  refine
    not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero f
      hH (fun x y ↦ (Int.castRingHom k).mapMatrix (β x y))
      (sum_mapMatrix_intCast_mul_mapMatrix_intCast k β h₀ hβ) hn hw ?_
  rw [trace_list_ofFn_mapMatrix_intCast β w htr]
  exact one_ne_zero

/-- **Non-formal higher loop deformations from a matrix representation over a `ℚ`-algebra.** Over a
`ℚ`-algebra, a closed walk of length `n + 2` (`n ≥ 1`) in a bipartite subgraph `H` whose matrix
product in a signless representation has nonzero trace defines a non-formal loop deformation of the
zigzag algebra of `G`. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_ne_zero [Algebra ℚ k]
    (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m k)
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0) {n : ℕ} (hn : 1 ≤ n)
    {w : Fin (n + 2) → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod ≠ 0) :
    ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k))
      (fst_eq_snd_of_mem_support_single (fun i ↦ congrArg f (hw i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_not_exists_hochschildDifferential_eq_obstruction _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero
      f hH β hβ hn hw htr)

omit [DecidableRel H.Adj] in
/-- **Non-formal higher loop deformations from an integer matrix representation over a nontrivial
`ℚ`-algebra.** -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one [Nontrivial k] [Algebra ℚ k]
    (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m ℤ)
    (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0) (hβ : ∀ x, ∑ y, β y x * β x y = 0) {n : ℕ}
    (hn : 1 ≤ n) {w : Fin (n + 2) → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod = 1) :
    ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k))
      (fst_eq_snd_of_mem_support_single (fun i ↦ congrArg f (hw i)) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra_of_not_exists_hochschildDifferential_eq_obstruction _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one
      f hH β h₀ hβ hn hw htr)

/-- **Even-arity non-formality from a matrix representation with non-even trace.** A closed walk of
even length `2 r + 2` (`r ≥ 1`) in a bipartite subgraph `H` whose matrix product has non-even trace
defines a non-formal loop deformation of the zigzag algebra of `G`. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_not_even_trace
    (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m k)
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0) {r : ℕ} (hr : 1 ≤ r)
    {w : Fin (2 * r + 2) → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : ¬Even (trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod)) :
    ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k))
      (fst_eq_snd_of_mem_support_single (fun i ↦ congrArg f (hw i)) (1 : k))).IsFormal := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨F, hanti, heval⟩ := exists_bipartite_sign_dartMatrix f hH β hw
  refine not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_of_not_even hr
    (dartMatrix (f.extendByZero β))
    (sum_dartMatrix_mul_dartMatrix_symm _ (f.sum_extendByZero_mul_extendByZero β hβ))
    F hanti _ _ ?_
  rcases heval with h | h <;> rw [h]
  · exact htr
  · rwa [even_neg]

omit [DecidableRel H.Adj] in
/-- **Even-arity non-formality from an integer matrix representation when `2` is not a unit.** -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_trace_eq_one_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m ℤ)
    (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0) (hβ : ∀ x, ∑ y, β y x * β x y = 0) {r : ℕ}
    (hr : 1 ≤ r) {w : Fin (2 * r + 2) → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod = 1) :
    ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k))
      (fst_eq_snd_of_mem_support_single (fun i ↦ congrArg f (hw i)) (1 : k))).IsFormal := by
  classical
  refine not_isFormal_zigzagLoopAInfinityAlgebra_of_not_even_trace f hH
    (fun x y ↦ (Int.castRingHom k).mapMatrix (β x y))
    (sum_mapMatrix_intCast_mul_mapMatrix_intCast k β h₀ hβ) hr hw ?_
  rw [trace_list_ofFn_mapMatrix_intCast β w htr]
  exact fun he ↦ h2 (isUnit_of_dvd_one he.two_dvd)

/-- **Quartic non-formality from a matrix representation, over any nontrivial commutative ring.** A
closed walk of length four in a bipartite subgraph `H` whose matrix product has unit trace defines a
non-formal quartic loop deformation of the zigzag algebra of `G` over every nontrivial commutative
ring `k`. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_four_of_isUnit_trace [Nontrivial k]
    (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m k)
    (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0)
    {w : Fin 4 → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : IsUnit (trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod)) :
    ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k))
      (fst_eq_snd_of_mem_support_single (fun i ↦ congrArg f (hw i)) (1 : k))).IsFormal := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨F, hanti, heval⟩ := exists_bipartite_sign_dartMatrix f hH β hw
  refine not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_four
    (dartMatrix (f.extendByZero β))
    (sum_dartMatrix_mul_dartMatrix_symm _ (f.sum_extendByZero_mul_extendByZero β hβ))
    F hanti _ _ ?_
  rcases heval with h | h <;> rw [h]
  · exact htr
  · exact htr.neg

omit [DecidableRel H.Adj] in
/-- **Quartic non-formality from an integer matrix representation, over any nontrivial commutative
ring.** -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_four_of_trace_eq_one [Nontrivial k]
    (f : H.Copy G) (hH : H.IsBipartite) (β : W → W → Matrix m m ℤ)
    (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0) (hβ : ∀ x, ∑ y, β y x * β x y = 0)
    {w : Fin 4 → H.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (w t).fst (w t).snd).prod = 1) :
    ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single (fun t ↦ f.toHom.mapDart (w t)) (1 : k))
      (fst_eq_snd_of_mem_support_single (fun i ↦ congrArg f (hw i)) (1 : k))).IsFormal := by
  classical
  refine not_isFormal_zigzagLoopAInfinityAlgebra_four_of_isUnit_trace f hH
    (fun x y ↦ (Int.castRingHom k).mapMatrix (β x y))
    (sum_mapMatrix_intCast_mul_mapMatrix_intCast k β h₀ hβ) hw ?_
  rw [trace_list_ofFn_mapMatrix_intCast β w htr]
  exact isUnit_one

/-- A detected loop gives a nonzero higher Hochschild class. -/
theorem not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero
    (β : W → W → Matrix m m k) (hβ : ∀ x, ∑ y ∈ H.neighborFinset x, β y x * β x y = 0)
    (f : H.Copy G) (hH : H.IsBipartite) {n : ℕ} (hn : 1 ≤ n) {u : Fin (n + 2) → H.Dart}
    (hu : ∀ i, (u i).fst = (u (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (u t).fst (u t).snd).prod ≠ 0) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero
      f hH β hβ hn hu htr)

omit [DecidableRel H.Adj] in
/-- A detected loop gives a nonzero higher Hochschild class. -/
theorem not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_eq_one [Nontrivial k]
    (β : W → W → Matrix m m ℤ) (h₀ : ∀ x y, ¬H.Adj x y → β x y = 0)
    (h : ∀ x, ∑ y, β y x * β x y = 0) (f : H.Copy G) (hH : H.IsBipartite) {n : ℕ} (hn : 1 ≤ n)
    {u : Fin (n + 2) → H.Dart} (hu : ∀ i, (u i).fst = (u (i + 1)).snd)
    (htr : trace (List.ofFn fun t ↦ β (u t).fst (u t).snd).prod = 1) :
    ¬(𝒵).HochschildVanishesAt ⟨n + 2, by omega⟩ := by
  classical
  exact not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction
    _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_eq_one
      f hH β h₀ h hn hu htr)

end TauCeti
