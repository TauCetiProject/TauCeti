/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.SimpleGraph.Copy
public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.MatrixRepresentation

/-!
# Nonzero cyclic classes from cycles in simple graphs

Let `G` be a finite simple graph containing a copy `c` of the cycle graph `cycleGraph m` (`m ≥ 3`),
not necessarily induced. Over every nontrivial commutative ring `k`, both the signless
preprojective algebra `Π⁺(G)` and the additive preprojective algebra `Π_k(OrientedQuiver G o)` of
**every** orientation `o` of `G` contain a homogeneous element of path degree `m` which does not
lie in the commutator submodule `[Π, Π]`: its class in the cyclic quotient `Π / [Π, Π]` is
nonzero. Note that when `m` is odd `G` is not bipartite, so when `2 ≠ 0` no cornerwise unit-gauge
comparison of relators exists
(`TauCeti.DoubledQuiver.Orientation.not_exists_forall_vertexCorner_eq_smul_of_not_isBipartite`) and
the bipartite isomorphism is unavailable; nevertheless the matrix representation constructed here
factors through both quotients directly.

## The unidirectional cycle representation

Put a one-dimensional block `k` at every vertex of `G`. Along each directed step `c i → c (i + 1)`
of the `m`-cycle assign the identity `1 × 1` matrix, and assign `0` to the reverse step
`c (i + 1) → c i` as well as to every other pair of vertices via `SimpleGraph.Copy.extendByZero`.
Since `m ≥ 3`, `i + 1 + 1 ≠ i` (`TauCeti.add_one_add_one_ne_self`), so at least one factor of every
two-step backtrack `β w v * β v w` vanishes. Hence every individual backtrack acts by `0`, so both
the signless local relations `∑_{w ∼ v} β w v * β v w = 0` and the signed local preprojective
relations hold termwise for every orientation `o` of `G`. Meanwhile the closed `m`-step cycle walk
`c 0 → c 1 → ⋯ → c (m - 1) → c 0` acts as the block unit `E_{c 0, c 0}` of trace `1 ≠ 0`, which
cannot be a sum of commutators (`TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule`).

Combining this with `SimpleGraph.isAcyclic_iff_free_cycleGraph` shows that any finite simple graph
which is not acyclic has a nonzero cyclic class in some path degree `d ≥ 3` in both its signless
and oriented preprojective algebras.

## Main results

* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph`: a copy of an
  `m`-cycle (`m ≥ 3`) in `G` produces a degree-`m` element outside the commutator submodule in
  `Π⁺(G)` and in `Π_k(OrientedQuiver G o)` for every orientation `o`.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: if
  `G` is not acyclic, some graded piece of `Π⁺(G)` of degree `d ≥ 3` is not contained in the
  commutator submodule. The oriented analogue is
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic` in
  `TauCeti.RepresentationTheory.Quiver.Preprojective.Affine`.

## References

* T. Schedler, *Zeroth Hochschild homology of preprojective algebras over the integers*,
  Theorem 13.1.1, https://arxiv.org/abs/0704.3278 (arXiv v3).
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver _root_.Matrix SimpleGraph Fin.NatCast
open scoped Kronecker

universe u w

section CycleCopy

variable (k : Type w) [CommRing k]

/-- The `1 × 1` matrix assigned to a directed pair `(i, j)` of `Fin m`: `1` on the forward step
`i → i + 1` and `0` everywhere else. -/
private def cycleMatrix (m : ℕ) [NeZero m] (i j : Fin m) : Matrix Unit Unit k :=
  if j = i + 1 then 1 else 0

private theorem cycleMatrix_mul_cycleMatrix {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i j : Fin m) :
    cycleMatrix k m j i * cycleMatrix k m i j = 0 := by
  simp only [cycleMatrix]
  split_ifs with h1 h2
  · exact absurd (h2 ▸ h1.symm) (add_one_add_one_ne_self hm i)
  · exact mul_zero _
  · exact zero_mul _
  · exact zero_mul _

private theorem extendByZero_cycleMatrix_mul {V : Type u} {G : SimpleGraph V}
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) (v w : V) :
    c.extendByZero (cycleMatrix k m) w v * c.extendByZero (cycleMatrix k m) v w = 0 := by
  by_cases h : c.extendByZero (cycleMatrix k m) w v = 0
  · rw [h, zero_mul]
  -- A nonzero first factor lies on the image of an edge `j ∼ i` of the cycle.
  obtain ⟨j, i, rfl, rfl, hji, -⟩ := (c.extendByZero_ne_zero_iff _).1 h
  rw [c.extendByZero_apply_apply_of_adj _ hji, c.extendByZero_apply_apply_of_adj _ hji.symm]
  exact cycleMatrix_mul_cycleMatrix k hm i j

private theorem sum_extendByZero_cycleMatrix_mul {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) :
    ∀ v, ∑ w ∈ G.neighborFinset v,
      c.extendByZero (cycleMatrix k m) w v * c.extendByZero (cycleMatrix k m) v w = 0 := fun v =>
  c.sum_extendByZero_mul_extendByZero _ (mul_zero 0)
    (fun i => Finset.sum_eq_zero fun j _ => cycleMatrix_mul_cycleMatrix k hm i j) v

/-- The `r`-step forward walk `c 0 → c 1 → ⋯ → c r` in the doubled path algebra of `G`, written in
later-factor-first multiplication order. -/
private noncomputable def cycleWalkElem {V : Type u} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) : ℕ → pathAlgebra k (DoubledQuiver G)
  | 0 => vertexIdempotent k (vertex G (c 0))
  | r + 1 =>
      ofArrow (arrow G (c.toHom.map_adj (cycleGraph_adj_add_one hm (↑r : Fin m)))) *
        cycleWalkElem hm c r

private theorem cycleWalkElem_mem_grade {V : Type u} [Finite V] {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) (r : ℕ) :
    cycleWalkElem k hm c r ∈ grade k (DoubledQuiver G) r := by
  induction r with
  | zero => exact vertexIdempotent_mem_grade_zero _
  | succ r ih =>
      simpa only [cycleWalkElem, add_comm 1 r] using
        grade_mul_grade_le 1 r (Submodule.mul_mem_mul (ofArrow_mem_grade_one _) ih)

private theorem signlessMatrixRepresentation_cycleWalkElem {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (c : (cycleGraph m).Copy G) (r : ℕ) :
    signlessMatrixRepresentation k (c.extendByZero (cycleMatrix k m))
        (sum_extendByZero_cycleMatrix_mul k hm c)
        (signlessPreprojectiveMk k _ (cycleWalkElem k hm c r)) =
      single (c (↑r : Fin m)) (c 0) 1 ⊗ₖ 1 := by
  induction r with
  | zero =>
      simpa only [cycleWalkElem, Nat.cast_zero] using
        signlessMatrixRepresentation_vertexIdempotent
          (c.extendByZero (cycleMatrix k m)) (sum_extendByZero_cycleMatrix_mul k hm c) (c 0)
  | succ r ih =>
      have hadj : (cycleGraph m).Adj (↑r : Fin m) ((↑r : Fin m) + 1) :=
        cycleGraph_adj_add_one hm (↑r : Fin m)
      have hmat : c.extendByZero (cycleMatrix k m) (c (↑r : Fin m)) (c ((↑r : Fin m) + 1)) = 1 := by
        rw [c.extendByZero_apply_apply_of_adj _ hadj]
        simp [cycleMatrix]
      simp [cycleWalkElem, hmat, ih, ← mul_kronecker_mul]

private theorem signlessMatrixRepresentation_ofArrow_mul_reverse {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (c : (cycleGraph m).Copy G) {a b : DoubledQuiver G} (e : a ⟶ b) :
    signlessMatrixRepresentation k (c.extendByZero (cycleMatrix k m))
        (sum_extendByZero_cycleMatrix_mul k hm c)
        (signlessPreprojectiveMk k _ (ofArrow e * ofArrow (Quiver.reverse e))) = 0 := by
  obtain ⟨i, rfl⟩ := exists_eq_vertex G a
  obtain ⟨j, rfl⟩ := exists_eq_vertex G b
  have h : G.Adj i j := (nonempty_hom_iff G).1 ⟨e⟩
  have he : e = arrow G h := Subsingleton.elim _ _
  rw [he, reverse_arrow, map_mul, map_mul]
  simp [← mul_kronecker_mul, extendByZero_cycleMatrix_mul k hm c j i]

private noncomputable def cycleOrientedPathRep {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (o : Orientation G) {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (c : (cycleGraph m).Copy G) :
    pathAlgebra k (Symmetrify (OrientedQuiver G o)) →ₐ[k] Matrix (V × Unit) (V × Unit) k :=
  ((signlessMatrixRepresentation k (c.extendByZero (cycleMatrix k m))
      (sum_extendByZero_cycleMatrix_mul k hm c)).comp
    (signlessPreprojectiveMk k (DoubledQuiver G))).comp
    (orientationPathAlgebraEquiv o k).symm.toAlgHom

private theorem cycleOrientedPathRep_localPreprojectiveRelator {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (o : Orientation G) {m : ℕ}
    [NeZero m] (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) (v : OrientedQuiver G o) :
    cycleOrientedPathRep k o hm c (localPreprojectiveRelator k v) = 0 := by
  rw [localPreprojectiveRelator_eq_sum_ofArrow_mul, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hsymm_mul : (orientationPathAlgebraEquiv o k).symm
      (ofArrow b * (doubledArrowSign k b • ofArrow (Quiver.reverse b))) =
      doubledArrowSign k b •
        (ofArrow ((symmetrifyMap G o).map b) *
          ofArrow (Quiver.reverse ((symmetrifyMap G o).map b))) := by
    rw [orientationPathAlgebraEquiv_symm_apply, mul_smul_comm, map_smul, map_mul]
    simp only [mapAlgHom_ofArrow, Prefunctor.map_reverse]
  simp only [cycleOrientedPathRep, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hsymm_mul, map_smul,
    signlessMatrixRepresentation_ofArrow_mul_reverse k hm c, smul_zero]

/-- **A copy of an `m`-cycle (`m ≥ 3`) produces a nonzero signless cyclic class in degree `m`.**
Over every nontrivial commutative ring, a copy of `cycleGraph m` (`m ≥ 3`) in `G` yields an element
of path degree `m` in `Π⁺(G)` outside the commutator submodule. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph
    [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}
    [inst : ∀ i, Fintype (G.neighborSet i)] {m : ℕ} (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) m ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  have : NeZero m := ⟨by omega⟩
  have : Fintype V := Fintype.ofFinite V
  have hinst : inst = fun i => Subtype.fintype (· ∈ G.neighborSet i) := Subsingleton.elim _ _
  subst hinst
  refine ⟨signlessPreprojectiveMk k _ (cycleWalkElem k hm c m),
    signlessPreprojectiveMk_mem_grade k _ (cycleWalkElem_mem_grade k hm c m), fun hcomm => ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule
    (signlessMatrixRepresentation k (c.extendByZero (cycleMatrix k m))
      (sum_extendByZero_cycleMatrix_mul k hm c)) hcomm
  simp [signlessMatrixRepresentation_cycleWalkElem, trace_kronecker] at htr

/-- **A copy of an `m`-cycle (`m ≥ 3`) produces a nonzero preprojective cyclic class in degree `m`
for every orientation.** Over every nontrivial commutative ring and for every orientation `o` of `G`
(including odd `m` on non-bipartite graphs), a copy of `cycleGraph m` (`m ≥ 3`) in `G` yields an
element of path degree `m` in `Π_k(OrientedQuiver G o)` outside the commutator submodule. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph
    [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V} (o : Orientation G)
    {m : ℕ} (hm : 3 ≤ m) (c : (cycleGraph m).Copy G) :
    ∃ z : preprojectiveAlgebra k (OrientedQuiver G o),
      z ∈ preprojectiveGrade k (OrientedQuiver G o) m ∧
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  have : NeZero m := ⟨by omega⟩
  have : Fintype V := Fintype.ofFinite V
  let y := orientationPathAlgebraEquiv o k (cycleWalkElem k hm c m)
  have hy_grade : y ∈ grade k (Symmetrify (OrientedQuiver G o)) m :=
    (orientationPathAlgebraEquiv_mem_grade_iff o k).2 (cycleWalkElem_mem_grade k hm c m)
  let ρ := preprojectiveLiftOfForallLocalPreprojectiveRelator (cycleOrientedPathRep k o hm c)
    (cycleOrientedPathRep_localPreprojectiveRelator k o hm c)
  refine ⟨preprojectiveMk k (OrientedQuiver G o) y,
    preprojectiveMk_mem_preprojectiveGrade k _ hy_grade, fun hcomm => ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule ρ hcomm
  have hρ : ρ (preprojectiveMk k (OrientedQuiver G o) y) = single (c 0) (c 0) 1 ⊗ₖ 1 := by
    rw [preprojectiveLiftOfForallLocalPreprojectiveRelator_preprojectiveMk]
    simpa only [y, cycleOrientedPathRep, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply, Fin.natCast_self] using
      signlessMatrixRepresentation_cycleWalkElem k hm c m
  simp [hρ, trace_kronecker] at htr

private theorem exists_cycleGraph_isContained_of_not_isAcyclic {V : Type u} {G : SimpleGraph V}
    (hG : ¬ G.IsAcyclic) : ∃ m ≥ 3, cycleGraph m ⊑ G := by
  simpa only [isAcyclic_iff_free_cycleGraph, not_forall, SimpleGraph.not_free, exists_prop] using hG

/-- **Non-acyclic graphs have nonzero signless cyclic classes in degree at least three.** If a
finite simple graph `G` is not acyclic, then over every nontrivial commutative ring some element of
path degree `d ≥ 3` of `Π⁺(G)` does not lie in the commutator submodule. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] (hG : ¬ G.IsAcyclic) :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨m, hm, ⟨c⟩⟩ := exists_cycleGraph_isContained_of_not_isAcyclic hG
  exact ⟨m, hm,
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph k hm c⟩

end CycleCopy

end TauCeti
