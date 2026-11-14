/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.Combinatorics.SimpleGraph.Copy
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
import TauCeti.Combinatorics.SimpleGraph.CycleGraph
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows
import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Nonzero cyclic classes of preprojective algebras of graphs with cycles

Let `G` be a finite simple graph containing a copy `f` of `SimpleGraph.cycleGraph m` for some
`m ≥ 3`, that is, a simple cycle of length `m` (an affine diagram `Ã_{m - 1}`). Put a
one-dimensional module `k` at every vertex of `G`, send each forward cycle arrow `f r → f (r + 1)`
of the doubled quiver to the elementary matrix `E_{f (r + 1), f r}`, and send every other doubled
arrow to zero. Because `f` is injective and `m ≥ 3`, no edge of `G` is traversed in both
directions by forward cycle steps (`(r + 1) + 1 ≠ r` in `Fin m`). Every individual backtrack
`v → w → v` therefore acts by zero.

Consequently, this single doubled-path-algebra homomorphism annihilates both:

* every signless relator `∑_{w ∼ v} b* b`, descending to
  `signlessPreprojectiveAlgebra k (DoubledQuiver G)`;
* the pullback of the additive preprojective relator `∑_a (a a* - a* a)` along
  `TauCeti.DoubledQuiver.orientationPathAlgebraEquiv`, descending to
  `preprojectiveAlgebra k (OrientedQuiver G o)` for *every* orientation `o` of `G`, including on
  odd cycles where `G` is not bipartite and the signless and additive preprojective algebras need
  not be isomorphic.

Traversing the directed cycle `r` times (`r : ℕ`) gives a closed path of length `r * m` at `f 0`
which acts by `E_{f 0, f 0}`, of matrix trace `1` (`r = 0` is the vertex idempotent at `f 0`). Over
every nontrivial commutative ring `k`, both `Π⁺(G)` and `Π_k(OrientedQuiver G o)` therefore have
homogeneous elements outside their commutator submodules in every multiple `r * m` of the cycle
length, and in particular in degree `m ≥ 3`. Since a graph fails to be acyclic precisely when it
contains a copy of `cycleGraph m` for some `m ≥ 3`, every non-acyclic finite graph has nonzero
positive-degree cyclic classes in degree at least three.

## Main results

* `TauCeti.exists_mem_signlessPreprojectiveGrade_mul_notMem_commutatorSubmodule_of_copy_cycleGraph`
  and `TauCeti.exists_mem_preprojectiveGrade_mul_notMem_commutatorSubmodule_of_copy_cycleGraph`:
  nonzero cyclic classes in every multiple `r * m` of the length of a cycle copy (`m ≥ 3`).
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_copy_cycleGraph`
  and `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_copy_cycleGraph`: the
  degree-`m` specialization.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_add_one_notMem_commutatorSubmodule` and
  `TauCeti.exists_mem_preprojectiveGrade_add_one_notMem_commutatorSubmodule`: nonzero
  degree-`(n + 1)` cyclic classes when `(AffineDynkinType.A n).graph ⊑ G` (`n ≥ 2`).
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: **every
  finite graph which is not acyclic has a nonzero cyclic class in some path degree `m ≥ 3`, both in
  its signless preprojective algebra and in the preprojective algebra of every orientation.**

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective algebra of an oriented graph.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 218
  (2008), https://arxiv.org/abs/0704.3278, for the positive-degree cyclic quotient of non-Dynkin
  preprojective algebras.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Section 3.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver _root_.Matrix PathAlgebra DoubledQuiver SimpleGraph

universe u w

/-! ### Cycle steps and directed cycle paths -/

section CycleSteps

variable {V : Type u} {G : SimpleGraph V} {m : ℕ}

/-- Whether `u → w` is a forward step `f r → f (r + 1)` along the copy `f` of `cycleGraph m`. -/
private def isCycleStep [NeZero m] (f : (cycleGraph m).Copy G) (u w : V) : Prop :=
  ∃ r : Fin m, f r = u ∧ f (r + 1) = w

private theorem not_isCycleStep_and_symm [NeZero m] (hm : 3 ≤ m) (f : (cycleGraph m).Copy G)
    (u w : V) : ¬ (isCycleStep f u w ∧ isCycleStep f w u) := by
  rintro ⟨⟨r, rfl, rfl⟩, ⟨s, hs1, hs2⟩⟩
  obtain rfl : s = r + 1 := f.injective hs1
  exact add_one_add_one_ne_self hm r (f.injective hs2)

private def cycleNode [NeZero m] : ℕ → Fin m
  | 0 => 0
  | s + 1 => cycleNode s + 1

private theorem val_cycleNode [NeZero m] (s : ℕ) :
    (cycleNode (m := m) s).val = s % m := by
  induction s with
  | zero => simp [cycleNode]
  | succ s ih =>
    rw [cycleNode, Fin.val_add, ih]
    exact (Nat.add_mod s 1 m).symm

private theorem cycleNode_mul_self [NeZero m] (r : ℕ) :
    cycleNode (m := m) (r * m) = 0 := by
  apply Fin.ext
  simp [val_cycleNode, Nat.mul_mod_left]

private def cycleStepPath [NeZero m] (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    (s : ℕ) → _root_.Quiver.Path (vertex G (f 0)) (vertex G (f (cycleNode s)))
  | 0 => .nil
  | s + 1 =>
    (cycleStepPath hm f s).cons
      (arrow G (f.toHom.map_adj (cycleGraph_adj_add_one hm (cycleNode s))))

private theorem length_cycleStepPath [NeZero m] (hm : 3 ≤ m) (f : (cycleGraph m).Copy G)
    (s : ℕ) : (cycleStepPath hm f s).length = s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [cycleStepPath, ih]

end CycleSteps

/-! ### The cycle-shift matrix representation -/

section Representation

variable {k : Type w} [CommRing k] {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {m : ℕ}

private def cycleVertex (v : DoubledQuiver G) : _root_.Matrix V V k :=
  _root_.Matrix.single ((vertexEquiv G).symm v) ((vertexEquiv G).symm v) 1

private noncomputable def cycleArrow [NeZero m] (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (_ : i ⟶ j) : _root_.Matrix V V k :=
  @ite _ (isCycleStep f ((vertexEquiv G).symm i) ((vertexEquiv G).symm j))
    (Classical.propDecidable _)
    (_root_.Matrix.single ((vertexEquiv G).symm j) ((vertexEquiv G).symm i) 1) 0

private theorem cycleVertex_mul_cycleArrow [NeZero m] (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (e : i ⟶ j) :
    cycleVertex j * cycleArrow (k := k) f e = cycleArrow f e := by
  simp only [cycleVertex, cycleArrow]
  split_ifs <;> simp

private theorem cycleArrow_mul_cycleVertex [NeZero m] (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (e : i ⟶ j) :
    cycleArrow (k := k) f e * cycleVertex i = cycleArrow f e := by
  simp only [cycleVertex, cycleArrow]
  split_ifs <;> simp

private theorem cycleArrow_mul_opposite_eq_zero [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) {i j : DoubledQuiver G} (e₁ : i ⟶ j) (e₂ : j ⟶ i) :
    cycleArrow (k := k) f e₂ * cycleArrow f e₁ = 0 := by
  simp only [cycleArrow]
  split_ifs with h1 h2
  · exact absurd ⟨h2, h1⟩ (not_isCycleStep_and_symm hm f _ _)
  all_goals simp

private theorem completeOrthogonalIdempotents_cycleVertex :
    CompleteOrthogonalIdempotents (cycleVertex (G := G) (k := k)) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨fun v w hvw => ?_, ?_⟩
  · simp [cycleVertex, single_mul_single_of_ne _ _ _ _ ((vertexEquiv G).symm.injective.ne hvw)]
  · ext a b
    rw [← (vertexEquiv G).sum_comp]
    simp only [cycleVertex, Equiv.symm_apply_apply, _root_.Matrix.sum_apply, single_apply,
      _root_.Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp only [hab, ite_false]
      exact Finset.sum_eq_zero fun c _ => by by_cases hc : c = a <;> simp_all

variable (k) in
private noncomputable def cyclePathAlgHom [NeZero m] (f : (cycleGraph m).Copy G) :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] _root_.Matrix V V k :=
  liftAlgHomOfArrows k cycleVertex completeOrthogonalIdempotents_cycleVertex
    (cycleArrow f) (cycleVertex_mul_cycleArrow f) (cycleArrow_mul_cycleVertex f)

private theorem cyclePathAlgHom_ofArrow [NeZero m] (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (e : i ⟶ j) :
    cyclePathAlgHom k f (ofArrow e) = cycleArrow f e := by
  rw [cyclePathAlgHom, ofArrow_eq_ofPath, liftAlgHomOfArrows_ofPath_toPath]

private theorem cyclePathAlgHom_backtrackElem [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) {v w : V} (h : G.Adj v w) :
    cyclePathAlgHom k f (backtrackElem G k h) = 0 := by
  rw [← ofArrow_symm_mul_ofArrow, map_mul, cyclePathAlgHom_ofArrow, cyclePathAlgHom_ofArrow]
  exact cycleArrow_mul_opposite_eq_zero hm f _ _

private theorem cyclePathAlgHom_signlessPreprojectiveRelator [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) [∀ i, Fintype (G.neighborSet i)] (x : DoubledQuiver G) :
    cyclePathAlgHom k f (signlessPreprojectiveRelator k x) = 0 := by
  obtain ⟨v, rfl⟩ := exists_eq_vertex G x
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ (instFintypeStarVertex G v),
    signlessPreprojectiveRelator_vertex, map_sum]
  exact Finset.sum_eq_zero fun w _ => cyclePathAlgHom_backtrackElem hm f w.2

variable (k) in
private noncomputable def cycleSignlessRep [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) [∀ i, Fintype (G.neighborSet i)] :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k] _root_.Matrix V V k :=
  signlessPreprojectiveLift (cyclePathAlgHom k f)
    (cyclePathAlgHom_signlessPreprojectiveRelator hm f)

private theorem cyclePathAlgHom_orientationSymm_preprojectiveRelator [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) (o : Orientation G) :
    (cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom
        (preprojectiveRelator k (OrientedQuiver G o)) = 0 := by
  have hopp {x y : Symmetrify (OrientedQuiver G o)} (b₁ : x ⟶ y) (b₂ : y ⟶ x) :
      (cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom
          (ofArrow b₂ * ofArrow b₁) = 0 := by
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_mul,
      orientationPathAlgebraEquiv_symm_apply, mapAlgHom_ofArrow, cyclePathAlgHom_ofArrow]
    exact cycleArrow_mul_opposite_eq_zero hm f _ _
  rw [preprojectiveRelator_def, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [map_sub, ← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem,
    ← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, hopp, hopp, sub_zero]

variable (k) in
private noncomputable def cyclePreprojectiveRep [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) (o : Orientation G) :
    preprojectiveAlgebra k (OrientedQuiver G o) →ₐ[k] _root_.Matrix V V k :=
  preprojectiveLift
    ((cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom)
    (cyclePathAlgHom_orientationSymm_preprojectiveRelator hm f o)

private theorem cyclePathAlgHom_cycleStepPath [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) (s : ℕ) :
    cyclePathAlgHom k f (ofPath ⟨_, _, cycleStepPath hm f s⟩) =
      _root_.Matrix.single (f (cycleNode s)) (f 0) 1 := by
  induction s with
  | zero =>
    dsimp only [cycleStepPath, cycleNode]
    simp [cyclePathAlgHom, cycleVertex]
  | succ s ih =>
    have hstep : isCycleStep f (f (cycleNode s)) (f (cycleNode s + 1)) :=
      ⟨cycleNode s, rfl, rfl⟩
    dsimp only [cycleStepPath, cycleNode]
    rw [cyclePathAlgHom, liftAlgHomOfArrows_ofPath_cons, ← cyclePathAlgHom, ih]
    simp [cycleArrow, hstep]

end Representation

/-! ### Nonzero cyclic classes -/

section CyclicClass

variable (k : Type w) [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- **A copy of `cycleGraph m` (`m ≥ 3`) produces nonzero cyclic classes in every multiple `r * m`
of `m` in the signless preprojective algebra.** -/
theorem exists_mem_signlessPreprojectiveGrade_mul_notMem_commutatorSubmodule_of_copy_cycleGraph
    [∀ i, Fintype (G.neighborSet i)] {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) (r * m),
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  let _ := Fintype.ofFinite V
  have : NeZero m := ⟨by omega⟩
  let p : Quiver.TotalPath (DoubledQuiver G) := ⟨_, _, cycleStepPath hm f (r * m)⟩
  have hp : ofPath p ∈ grade k (DoubledQuiver G) (r * m) :=
    ofPath_mem_grade_of_length (length_cycleStepPath hm f (r * m))
  refine ⟨signlessPreprojectiveMk k _ (ofPath p), signlessPreprojectiveMk_mem_grade k _ hp,
    fun hcomm => ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule (cycleSignlessRep k hm f) hcomm
  rw [cycleSignlessRep, signlessPreprojectiveLift_signlessPreprojectiveMk,
    cyclePathAlgHom_cycleStepPath hm f (r * m), cycleNode_mul_self, trace_single_eq_same] at htr
  exact one_ne_zero htr

/-- **A copy of `cycleGraph m` (`m ≥ 3`) produces a nonzero degree-`m` cyclic class in the signless
preprojective algebra.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_copy_cycleGraph
    [∀ i, Fintype (G.neighborSet i)] {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) m,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  simpa only [one_mul] using
    exists_mem_signlessPreprojectiveGrade_mul_notMem_commutatorSubmodule_of_copy_cycleGraph
      k hm f 1

/-- **A copy of `cycleGraph m` (`m ≥ 3`) produces nonzero cyclic classes in every multiple `r * m`
of `m` in the additive preprojective algebra of every orientation.** -/
theorem exists_mem_preprojectiveGrade_mul_notMem_commutatorSubmodule_of_copy_cycleGraph
    {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (o : Orientation G) (r : ℕ) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) (r * m),
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  let _ := Fintype.ofFinite V
  have : NeZero m := ⟨by omega⟩
  let p : Quiver.TotalPath (DoubledQuiver G) := ⟨_, _, cycleStepPath hm f (r * m)⟩
  let q : Quiver.TotalPath (Symmetrify (OrientedQuiver G o)) :=
    (unsymmetrifyMap G o).mapTotalPath p
  have hq : ofPath q ∈ grade k (Symmetrify (OrientedQuiver G o)) (r * m) :=
    ofPath_mem_grade_of_length
      ((Prefunctor.length_mapTotalPath (unsymmetrifyMap G o) p).trans
        (length_cycleStepPath hm f (r * m)))
  refine ⟨preprojectiveMk k (OrientedQuiver G o) (ofPath q),
    preprojectiveMk_mem_preprojectiveGrade k (OrientedQuiver G o) hq, fun hcomm => ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule (cyclePreprojectiveRep k hm f o) hcomm
  have hq_eq : ofPath (k := k) q = orientationPathAlgebraEquiv o k (ofPath p) :=
    (orientationPathAlgebraEquiv_ofPath o k p).symm
  rw [hq_eq, cyclePreprojectiveRep, preprojectiveLift_preprojectiveMk, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    cyclePathAlgHom_cycleStepPath hm f (r * m), cycleNode_mul_self, trace_single_eq_same] at htr
  exact one_ne_zero htr

/-- **A copy of `cycleGraph m` (`m ≥ 3`) produces a nonzero degree-`m` cyclic class in the additive
preprojective algebra of every orientation.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_copy_cycleGraph
    {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (o : Orientation G) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) m,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  simpa only [one_mul] using
    exists_mem_preprojectiveGrade_mul_notMem_commutatorSubmodule_of_copy_cycleGraph
      k hm f o 1

/-- **A graph containing affine `Ãₙ` (`n ≥ 2`) has a nonzero degree-`(n + 1)` cyclic class in its
signless preprojective algebra.** -/
theorem exists_mem_signlessPreprojectiveGrade_add_one_notMem_commutatorSubmodule
    [∀ i, Fintype (G.neighborSet i)] {n : ℕ} (hn : 2 ≤ n) (h : (AffineDynkinType.A n).graph ⊑ G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) (n + 1),
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  rw [AffineDynkinType.graph_A] at h
  obtain ⟨f⟩ := h
  exact exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_copy_cycleGraph
    k (by omega) f

/-- **A graph containing affine `Ãₙ` (`n ≥ 2`) has a nonzero degree-`(n + 1)` cyclic class in the
additive preprojective algebra of every orientation.** -/
theorem exists_mem_preprojectiveGrade_add_one_notMem_commutatorSubmodule
    {n : ℕ} (hn : 2 ≤ n) (h : (AffineDynkinType.A n).graph ⊑ G) (o : Orientation G) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) (n + 1),
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  rw [AffineDynkinType.graph_A] at h
  obtain ⟨f⟩ := h
  exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_copy_cycleGraph
    k (by omega) f o

/-- **Every finite non-acyclic graph has a nonzero cyclic class of path degree at least three in its
signless preprojective algebra.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    [∀ i, Fintype (G.neighborSet i)] (hc : ¬ G.IsAcyclic) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨n, hn, h⟩ := exists_isContained_affineDynkinType_A_of_not_isAcyclic hc
  exact ⟨n + 1, by omega,
    exists_mem_signlessPreprojectiveGrade_add_one_notMem_commutatorSubmodule k hn h⟩

/-- **Every finite non-acyclic graph has a nonzero cyclic class of path degree at least three in the
additive preprojective algebra of every orientation.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (hc : ¬ G.IsAcyclic) (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨n, hn, h⟩ := exists_isContained_affineDynkinType_A_of_not_isAcyclic hc
  exact ⟨n + 1, by omega,
    exists_mem_preprojectiveGrade_add_one_notMem_commutatorSubmodule k hn h o⟩

end CyclicClass

end TauCeti
