/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.Data.Fin.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GradedOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

import Mathlib.Algebra.Group.Fin.Basic

/-!
# Positive-degree cyclic classes of non-Dynkin preprojective algebras

Over a nontrivial commutative ring `k`, the additive preprojective algebra `Π_k(OrientedQuiver G o)`
of any orientation `o` of a connected finite non-Dynkin simple graph `G` has a nonzero cyclic class
in some path degree `d ≥ 3`:

* When `G` is not acyclic, it contains a simple cycle of length `m ≥ 3` (an affine `Ã_{m-1}`
  subdiagram). Turning around those edges of the cycle which `o` directs backwards produces a
  reorientation `Reorient (OrientedQuiver G o) σ` in which the cycle is directed. Its image under
  `TauCeti.pathAlgebraToPreprojective` cannot lie in the commutator submodule because the retraction
  `TauCeti.preprojectiveToPathAlgebra` sends it back to the closed basis path in the path algebra,
  and orientation independence (`TauCeti.reorientPreprojectiveAlgebraEquiv`) transports the class
  back to `Π_k(OrientedQuiver G o)` in path degree `m`.
* When `G` is acyclic, connectivity makes `G` a non-Dynkin tree. Its signless preprojective algebra
  has a nonzero cyclic class in path degree `4`, `6`, `8` or `12` by
  `SimpleGraph.IsTree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule`, and
  bipartite sign rescaling (`SimpleGraph.Coloring.signlessPreprojectiveAlgebraEquiv`) transports it
  to `Π_k(OrientedQuiver G o)` in the same degree.

Notice that when `G` is an odd cycle and `2 ≠ 0` in `k`, no bipartite sign comparison exists
(`TauCeti.DoubledQuiver.Orientation.not_exists_forall_vertexCorner_eq_smul_of_not_isBipartite`);
reorienting into a directed cycle works directly on `Π_k(OrientedQuiver G o)` without passing
through the signless algebra.

## Main results

* `TauCeti.pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient`: any closed path in
  a quiver or in one of its reorientations yields a homogeneous element of the same degree in the
  preprojective algebra outside the commutator submodule.
* `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: a cycle of
  length `m ≥ 3` in `G` produces a nonzero cyclic class of degree `m` in every orientation of `G`.
* `SimpleGraph.IsTree.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule`: every orientation
  of a finite non-Dynkin tree has a nonzero cyclic class in path degree `4`, `6`, `8` or `12`.
* `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`:
  every orientation of a connected finite non-Dynkin simple graph has a nonzero cyclic class in some
  path degree `d ≥ 3`.

## References

* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 214
  (2007), https://arxiv.org/abs/math/0703475.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u v w

section Quiver

variable (k : Type w) [CommRing k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The image of a basis path of `Q` in `Π_k(Q)` is homogeneous of degree equal to its path
length. -/
theorem pathAlgebraToPreprojective_ofPath_mem_preprojectiveGrade (x : Quiver.TotalPath Q) :
    pathAlgebraToPreprojective k Q (ofPath x) ∈ preprojectiveGrade k Q x.2.2.length := by
  rw [pathAlgebraToPreprojective_ofPath]
  exact preprojectiveMk_mem_preprojectiveGrade k Q
    (ofPath_mem_grade_of_length (Symmetrify.of.length_mapTotalPath x))

/-- Over a nontrivial commutative ring, the image in `Π_k(Q)` of any closed basis path of `Q`
does not lie in the commutator submodule `[Π_k(Q), Π_k(Q)]`. -/
theorem pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule [Nontrivial k]
    {a : Q} (p : Path a a) :
    pathAlgebraToPreprojective k Q (ofPath ⟨a, a, p⟩) ∉
      commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  intro hp
  have hret := map_mem_commutatorSubmodule (preprojectiveToPathAlgebra k Q) hp
  rw [preprojectiveToPathAlgebra_pathAlgebraToPreprojective] at hret
  exact ofPath_notMem_commutatorSubmodule p hret

/-- Any closed path in a reorientation of `Q` produces a homogeneous element of the same path
degree in `Π_k(Q)` outside the commutator submodule over a nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient [Nontrivial k]
    (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) {a : Reorient Q σ} (p : Path a a) :
    ∃ x ∈ preprojectiveGrade k Q p.length,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  let y := pathAlgebraToPreprojective k (Reorient Q σ) (ofPath ⟨a, a, p⟩)
  refine ⟨reorientPreprojectiveAlgebraEquiv k σ y,
    (reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k σ).2
      (pathAlgebraToPreprojective_ofPath_mem_preprojectiveGrade k ⟨a, a, p⟩), fun hx => ?_⟩
  apply pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule k p
  simpa only [AlgEquiv.symm_apply_apply] using
    map_mem_commutatorSubmodule (reorientPreprojectiveAlgebraEquiv k σ).symm hx

end Quiver

section Cycle

open Fin.NatCast in
/-- Iterating a family of arrows `u r ⟶ u (r + 1)` around `Fin m` yields a closed path of length
`m` at `u 0`. -/
private theorem exists_path_length_eq_of_step {Q : Type*} [Quiver Q] {m : ℕ} [NeZero m]
    (u : Fin m → Q) (step : ∀ r : Fin m, u r ⟶ u (r + 1)) :
    ∃ p : Path (u 0) (u 0), p.length = m := by
  have walk : ∀ n : ℕ, ∃ p : Path (u 0) (u (n : Fin m)), p.length = n := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero]
      exact ⟨Path.nil, rfl⟩
    | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      have key_step : ∀ r : Fin m, r = (n : Fin m) + 1 → (u (n : Fin m) ⟶ u r) := by
        rintro _ rfl
        exact step (n : Fin m)
      exact ⟨p.cons (key_step ((n + 1 : ℕ) : Fin m) (Nat.cast_succ n)),
        by rw [Path.length_cons, hp]⟩
  obtain ⟨p, hp⟩ := walk m
  have key_end : ∀ r : Fin m, r = 0 → ∀ p : Path (u 0) (u r), p.length = m →
      ∃ q : Path (u 0) (u 0), q.length = m := by
    rintro _ rfl p hp
    exact ⟨p, hp⟩
  exact key_end (m : Fin m) (Fin.natCast_self m) p hp

variable (k : Type w) [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- A copy of a cycle graph of length `m ≥ 3` in a finite simple graph `G` yields a homogeneous
element of path degree `m` outside the commutator submodule of `Π_k(OrientedQuiver G o)` for every
orientation `o` of `G`. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy
    {m : ℕ} (hm : 3 ≤ m) (c : (SimpleGraph.cycleGraph m).Copy G) (o : Orientation G) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) m,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  have : NeZero m := ⟨by omega⟩
  let φ := (OrientedQuiver.vertexEquiv G o).symm
  let σ : ∀ ⦃i j : OrientedQuiver G o⦄, (i ⟶ j) → Bool :=
    fun i j _ => decide (∃ r : Fin m, c (r + 1) = φ i ∧ c r = φ j)
  let u (r : Fin m) : Reorient (OrientedQuiver G o) σ :=
    reorientVertex σ (OrientedQuiver.vertex G o (c r))
  have step (r : Fin m) : u r ⟶ u (r + 1) := by
    have hadj : G.Adj (c r) (c (r + 1)) :=
      c.toHom.map_adj (cycleGraph_adj_add_one hm r)
    by_cases ho : (⟨(c r, c (r + 1)), hadj⟩ : G.Dart) ∈ o
    · refine reorientKeep σ (OrientedQuiver.arrow G o hadj ho) ?_
      simp only [σ, φ, OrientedQuiver.vertexEquiv_symm_vertex, decide_eq_true_eq, not_exists,
        not_and]
      intro s hs₁ hs₂
      have hsr₁ : s + 1 = r := c.injective hs₁
      have hsr₂ : s = r + 1 := c.injective hs₂
      exact add_one_add_one_ne_self hm r (hsr₂ ▸ hsr₁)
    · have ho' : (⟨(c (r + 1), c r), hadj.symm⟩ : G.Dart) ∈ o :=
        (o.symm_mem_iff_not_mem _).2 ho
      refine reorientFlip σ (OrientedQuiver.arrow G o hadj.symm ho') ?_
      simp only [σ, φ, OrientedQuiver.vertexEquiv_symm_vertex, decide_eq_true_eq]
      exact ⟨r, rfl, rfl⟩
  obtain ⟨p, hp⟩ := exists_path_length_eq_of_step u step
  simpa only [hp] using
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient k σ p

/-- If a finite simple graph `G` is not acyclic, then over every nontrivial commutative ring and for
every orientation `o` of `G`, the preprojective algebra `Π_k(OrientedQuiver G o)` has a nonzero
cyclic class in some path degree `d ≥ 3`. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (hc : ¬ G.IsAcyclic) (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨n, hn, hc'⟩ := G.exists_isContained_affineDynkinType_A_of_not_isAcyclic hc
  rw [AffineDynkinType.graph_A] at hc'
  obtain ⟨c⟩ := hc'
  exact ⟨n + 1, by omega,
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy k (by omega) c o⟩

end Cycle

end TauCeti

namespace SimpleGraph.IsTree

open TauCeti TauCeti.DoubledQuiver

universe u w

private theorem transport_fintype_neighborSet
    {k : Type w} [CommRing k] {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (f₁ f₂ : ∀ v, Fintype (G.neighborSet v))
    (h : letI := f₁; ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    letI := f₂; ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain rfl : f₁ = f₂ := Subsingleton.elim _ _
  exact h

/-- **Non-Dynkin trees have nonzero preprojective cyclic classes in positive degree.** For every
orientation `o` of a finite tree `G` which is not isomorphic to the diagram of any valid Dynkin
type, and over every nontrivial commutative ring `k`, some element of path degree `4`, `6`, `8` or
`12` of `Π_k(OrientedQuiver G o)` does not lie in the commutator submodule. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule
    {k : Type w} [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d ∈ ({4, 6, 8, 12} : Finset ℕ), ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  let := Fintype.ofFinite V
  let fSub : ∀ v, Fintype (G.neighborSet v) := inferInstance
  obtain ⟨d, hd, hx0⟩ :=
    hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
  let fFin : ∀ v, Fintype (G.neighborSet v) := fun v => Fintype.ofFinite (G.neighborSet v)
  have hx1 := transport_fintype_neighborSet fSub fFin hx0
  let := fFin
  obtain ⟨x, hx, hxnot⟩ := hx1
  let C := hG.isAcyclic.isBipartite.coloringBool
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨d, hd, E x, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx,
    fun h => hxnot ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h

end SimpleGraph.IsTree

namespace TauCeti

open DoubledQuiver

universe u w

/-- **Connected non-Dynkin graphs have nonzero preprojective cyclic classes in degree at least
three.** If a connected finite simple graph `G` is not isomorphic to the diagram of any valid
Dynkin type, then over every nontrivial commutative ring `k` and for every orientation `o` of `G`,
some homogeneous element of path degree `d ≥ 3` in `Π_k(OrientedQuiver G o)` does not lie in the
commutator submodule. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
    (k : Type w) [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hc : G.IsAcyclic
  · have htree : G.IsTree := ⟨hG, hc⟩
    obtain ⟨d, hd, hx⟩ := htree.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule
      (k := k) hD o
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact ⟨d, hd3, hx⟩
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hc o

end TauCeti
