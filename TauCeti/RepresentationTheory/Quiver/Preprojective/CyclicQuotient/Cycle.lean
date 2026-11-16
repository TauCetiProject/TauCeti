/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading
import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows
import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Nonzero cyclic classes from cycles in a graph

Let `G` be a finite simple graph containing a cycle of length `m ≥ 3`, given by a copy
`f : (cycleGraph m).Copy G`. Sending each forward arrow `f i → f (i + 1)` around the cycle to the
matrix unit `E_{f (i + 1), f i}` in `Matrix V V k` and every other arrow of the doubled quiver
(including all backward arrows around the cycle and all chords) to `0` defines a representation of
the doubled path algebra in which every length-two backtrack `e' * e` vanishes: no pair of vertices
is joined in both directions by `i ↦ i + 1` on `Fin m` when `m ≥ 3`.

Consequently this single path-algebra representation annihilates both every signless preprojective
relator and (after restoring any orientation) every head and tail backtrack in the additive
preprojective relator, with no bipartiteness hypothesis or orientation case analysis. The closed
path of length `m` traversing the cycle maps to the diagonal matrix unit `E_{f 0, f 0}`, whose
trace is `1`. Over any nontrivial commutative ring, the trace vanishes on the commutator submodule,
so every finite graph that is not acyclic has a nonzero homogeneous cyclic class of degree at least
three in both its signless preprojective algebra and the preprojective algebra of every
orientation.

## Main results

* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy`:
  a copy of `cycleGraph m` (`3 ≤ m`) produces a nonzero degree-`m` cyclic class in `Π⁺(G)`.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`:
  every finite graph that is not acyclic has a nonzero cyclic class of degree `d ≥ 3` in `Π⁺(G)`.
* `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy`:
  a copy of `cycleGraph m` (`3 ≤ m`) produces a nonzero degree-`m` cyclic class in `Π(G, o)` for
  every orientation `o`.
* `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`:
  every finite graph that is not acyclic has a nonzero cyclic class of degree `d ≥ 3` in `Π(G, o)`
  for every orientation `o`.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient `A / [A, A]` and the trace
  obstruction.
* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Theorem 13.1.1,
  for cyclic classes of preprojective algebras of non-Dynkin graphs.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver SimpleGraph Matrix
open scoped Fin.NatCast

universe u w

section Path

variable {V : Type u} {G : SimpleGraph V}

/-- The path of length `r` walking forward along a cycle copy from `f 0` to `f r`. -/
private def cyclePath {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G) (hm : 3 ≤ m) :
    (r : ℕ) → Quiver.Path (vertex G (f 0)) (vertex G (f (r : Fin m)))
  | 0 => .nil
  | r + 1 =>
    (cyclePath f hm r).cons
      (arrow G (f.toHom.map_adj
        ((Nat.cast_succ (R := Fin m) r).symm ▸ cycleGraph_adj_add_one hm (r : Fin m))))

private theorem cyclePath_length {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G) (hm : 3 ≤ m)
    (r : ℕ) : (cyclePath f hm r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [cyclePath, ih]

private theorem orientationPathAlgebraEquiv_symm_ofPath_toPath {k : Type w} [CommRing k]
    [Finite V] (o : Orientation G) {x y : Symmetrify (OrientedQuiver G o)} (b : x ⟶ y) :
    (orientationPathAlgebraEquiv o k).symm (ofPath ⟨x, y, b.toPath⟩) =
      ofArrow ((symmetrifyMap G o).map b) := by
  rw [orientationPathAlgebraEquiv_symm_ofPath, Prefunctor.mapTotalPath_mk,
    Prefunctor.mapPath_toPath, ofArrow_eq_ofPath]

end Path

section Representation

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V]

/-- Diagonal matrix projection associated to a vertex of the doubled quiver. -/
private noncomputable def cycleVertex (v : DoubledQuiver G) : Matrix V V k :=
  Matrix.single ((vertexEquiv G).symm v) ((vertexEquiv G).symm v) 1

/-- Indicator scalar `1` on forward edges `(f i, f (i + 1))` of a cycle copy and `0` elsewhere. -/
private noncomputable def cycleWeight {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G) (u w : V) :
    k :=
  letI := Classical.dec
  if ∃ i : Fin m, f i = u ∧ f (i + 1) = w then 1 else 0

/-- Matrix assigned to an arrow of the doubled quiver: `E_{j, i}` on forward edges of the cycle
copy and `0` on all other arrows. -/
private noncomputable def cycleArrow {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G)
    {x y : DoubledQuiver G} (_ : x ⟶ y) : Matrix V V k :=
  Matrix.single ((vertexEquiv G).symm y) ((vertexEquiv G).symm x)
    (cycleWeight f ((vertexEquiv G).symm x) ((vertexEquiv G).symm y))

private theorem completeOrthogonalIdempotents_cycleVertex :
    CompleteOrthogonalIdempotents (cycleVertex (k := k) (G := G)) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨fun v w hvw => ?_, ?_⟩
  · simp [cycleVertex, (vertexEquiv G).symm.injective.ne hvw]
  · ext a b
    rw [← (vertexEquiv G).sum_comp]
    simp only [cycleVertex, Equiv.symm_apply_apply, Matrix.sum_apply, Matrix.single_apply,
      Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp only [hab, ite_false]
      exact Finset.sum_eq_zero fun c _ => by by_cases hc : c = a <;> simp_all

private theorem cycleVertex_mul_cycleArrow {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G)
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    cycleVertex y * cycleArrow (k := k) f e = cycleArrow f e := by
  simp [cycleVertex, cycleArrow]

private theorem cycleArrow_mul_cycleVertex {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G)
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    cycleArrow (k := k) f e * cycleVertex x = cycleArrow f e := by
  simp [cycleVertex, cycleArrow]

variable (k) in
/-- Path-algebra homomorphism supported on the forward arrows of a cycle copy. -/
private noncomputable def cyclePathAlgHom {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G) :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] Matrix V V k :=
  liftAlgHomOfArrows k cycleVertex completeOrthogonalIdempotents_cycleVertex
    (cycleArrow f) (cycleVertex_mul_cycleArrow f) (cycleArrow_mul_cycleVertex f)

private theorem cyclePathAlgHom_ofArrow {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G)
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    cyclePathAlgHom k f (ofArrow e) = cycleArrow f e := by
  rw [cyclePathAlgHom, ofArrow_eq_ofPath, liftAlgHomOfArrows_ofPath_toPath]

/-- No pair of vertices is joined in both directions by `i ↦ i + 1` on a cycle of length `≥ 3`,
so every product of opposite arrows vanishes in the cycle representation. -/
private theorem cycleArrow_mul_opposite_eq_zero {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) {x y : DoubledQuiver G} (e : x ⟶ y) (e' : y ⟶ x) :
    cycleArrow (k := k) f e' * cycleArrow f e = 0 := by
  classical
  simp only [cycleArrow, Matrix.single_mul_single_same]
  suffices cycleWeight (k := k) f ((vertexEquiv G).symm y) ((vertexEquiv G).symm x) *
      cycleWeight f ((vertexEquiv G).symm x) ((vertexEquiv G).symm y) = 0 by
    rw [this, Matrix.single_zero]
  simp only [cycleWeight]
  split_ifs with h₁ h₂
  · obtain ⟨i, hi1, hi2⟩ := h₁
    obtain ⟨j, hj1, hj2⟩ := h₂
    have hji : j = i + 1 := f.injective (hj1.trans hi2.symm)
    have hij : j + 1 = i := f.injective (hj2.trans hi1.symm)
    exact absurd (hji ▸ hij) (add_one_add_one_ne_self hm i)
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

private theorem cyclePathAlgHom_signlessPreprojectiveRelator {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) [∀ v, Fintype (G.neighborSet v)] (v : DoubledQuiver G) :
    cyclePathAlgHom k f (signlessPreprojectiveRelator k v) = 0 := by
  obtain ⟨u, rfl⟩ := exists_eq_vertex G v
  rw [signlessPreprojectiveRelator_congr k (vertex G u) _ (instFintypeStarVertex G u),
    signlessPreprojectiveRelator_vertex, map_sum]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [← ofArrow_symm_mul_ofArrow, map_mul, cyclePathAlgHom_ofArrow, cyclePathAlgHom_ofArrow]
  exact cycleArrow_mul_opposite_eq_zero hm f (arrow G w.2) (arrow G w.2.symm)

private theorem cyclePathAlgHom_comp_orientation_preprojectiveRelator {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (o : Orientation G) :
    ((cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom)
      (preprojectiveRelator k (OrientedQuiver G o)) = 0 := by
  rw [preprojectiveRelator_def, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [map_sub]
  have hhead : ((cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom)
      (headBacktrackElem k a) = 0 := by
    rw [headBacktrackElem_def, ← ofPath_mul_ofPath_of_comp, map_mul]
    change cyclePathAlgHom k f ((orientationPathAlgebraEquiv o k).symm (ofPath ⟨_, _, _⟩)) *
      cyclePathAlgHom k f ((orientationPathAlgebraEquiv o k).symm (ofPath ⟨_, _, _⟩)) = 0
    rw [orientationPathAlgebraEquiv_symm_ofPath_toPath,
      orientationPathAlgebraEquiv_symm_ofPath_toPath,
      cyclePathAlgHom_ofArrow, cyclePathAlgHom_ofArrow]
    exact cycleArrow_mul_opposite_eq_zero hm f _ _
  have htail : ((cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom)
      (tailBacktrackElem k a) = 0 := by
    rw [tailBacktrackElem_def, ← ofPath_mul_ofPath_of_comp, map_mul]
    change cyclePathAlgHom k f ((orientationPathAlgebraEquiv o k).symm (ofPath ⟨_, _, _⟩)) *
      cyclePathAlgHom k f ((orientationPathAlgebraEquiv o k).symm (ofPath ⟨_, _, _⟩)) = 0
    rw [orientationPathAlgebraEquiv_symm_ofPath_toPath,
      orientationPathAlgebraEquiv_symm_ofPath_toPath,
      cyclePathAlgHom_ofArrow, cyclePathAlgHom_ofArrow]
    exact cycleArrow_mul_opposite_eq_zero hm f _ _
  rw [hhead, htail, sub_self]

private theorem cyclePathAlgHom_cyclePath {m : ℕ} [NeZero m] (f : (cycleGraph m).Copy G)
    (hm : 3 ≤ m) (r : ℕ) :
    cyclePathAlgHom k f (ofPath ⟨_, _, cyclePath f hm r⟩) =
      Matrix.single (f (r : Fin m)) (f 0) (1 : k) := by
  induction r with
  | zero =>
    change cyclePathAlgHom k f (ofPath ⟨vertex G (f 0), vertex G (f 0), .nil⟩) =
      Matrix.single (f 0) (f 0) (1 : k)
    simp only [cyclePathAlgHom, liftAlgHomOfArrows_ofPath_nil, cycleVertex,
      vertexEquiv_symm_vertex]
  | succ r ih =>
    rw [cyclePath, ← ofArrow_mul_ofPath, map_mul, cyclePathAlgHom_ofArrow, ih]
    simp only [cycleArrow, vertexEquiv_symm_vertex, Matrix.single_mul_single_same, mul_one]
    have hweight : cycleWeight (k := k) f (f (r : Fin m)) (f ((r + 1 : ℕ) : Fin m)) = 1 := by
      classical
      simp only [cycleWeight, ite_eq_left_iff]
      intro h
      exact absurd ⟨(r : Fin m), rfl, by rw [Nat.cast_succ]⟩ h
    rw [hweight]

end Representation

section Main

variable (k : Type w) [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- **A cycle of length `m ≥ 3` yields a nonzero degree-`m` cyclic class in `Π⁺(G)`.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy
    [∀ v, Fintype (G.neighborSet v)] {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) m,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  have : NeZero m := ⟨by omega⟩
  let _ : Fintype V := Fintype.ofFinite V
  let φ : signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k] Matrix V V k :=
    signlessPreprojectiveLift (cyclePathAlgHom k f)
      (cyclePathAlgHom_signlessPreprojectiveRelator hm f)
  let p : Quiver.TotalPath (DoubledQuiver G) :=
    ⟨vertex G (f 0), vertex G (f (m : Fin m)), cyclePath f hm m⟩
  refine ⟨signlessPreprojectiveMk k _ (ofPath p),
    signlessPreprojectiveMk_mem_grade k _ (ofPath_mem_grade_of_length (cyclePath_length f hm m)),
    fun hx => ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule φ hx
  have hval : φ (signlessPreprojectiveMk k _ (ofPath p)) = Matrix.single (f 0) (f 0) (1 : k) := by
    rw [signlessPreprojectiveLift_signlessPreprojectiveMk]
    simpa [p, Fin.natCast_self] using cyclePathAlgHom_cyclePath (k := k) f hm m
  rw [hval, Matrix.trace_single_eq_same] at htr
  exact one_ne_zero htr

/-- **Every finite graph that is not acyclic has a nonzero cyclic class of degree at least three
in its signless preprojective algebra.** -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    [∀ v, Fintype (G.neighborSet v)] (hc : ¬ G.IsAcyclic) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph] at hc
  push Not at hc
  obtain ⟨m, hm, ⟨f⟩⟩ := hc
  exact ⟨m, hm,
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy k hm f⟩

/-- **A cycle of length `m ≥ 3` yields a nonzero degree-`m` cyclic class in `Π(G, o)`** for every
orientation `o` of `G`, over every nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy
    {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (o : Orientation G) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) m,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  have : NeZero m := ⟨by omega⟩
  let _ : Fintype V := Fintype.ofFinite V
  let ψ : pathAlgebra k (Symmetrify (OrientedQuiver G o)) →ₐ[k] Matrix V V k :=
    (cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom
  let φ : preprojectiveAlgebra k (OrientedQuiver G o) →ₐ[k] Matrix V V k :=
    preprojectiveLift ψ (cyclePathAlgHom_comp_orientation_preprojectiveRelator hm f o)
  let p : Quiver.TotalPath (DoubledQuiver G) :=
    ⟨vertex G (f 0), vertex G (f (m : Fin m)), cyclePath f hm m⟩
  let q : Quiver.TotalPath (Symmetrify (OrientedQuiver G o)) :=
    (unsymmetrifyMap G o).mapTotalPath p
  refine ⟨preprojectiveMk k (OrientedQuiver G o) (ofPath q),
    preprojectiveMk_mem_preprojectiveGrade k (OrientedQuiver G o)
      (ofPath_mem_grade_of_length
        (by rw [Prefunctor.length_mapTotalPath]; exact cyclePath_length f hm m)),
    fun hx => ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule φ hx
  have hval : φ (preprojectiveMk k (OrientedQuiver G o) (ofPath q)) =
      Matrix.single (f 0) (f 0) (1 : k) := by
    rw [preprojectiveLift_preprojectiveMk]
    change cyclePathAlgHom k f ((orientationPathAlgebraEquiv o k).symm (ofPath q)) = _
    rw [← orientationPathAlgebraEquiv_ofPath o k p, AlgEquiv.symm_apply_apply]
    simpa [p, Fin.natCast_self] using cyclePathAlgHom_cyclePath (k := k) f hm m
  rw [hval, Matrix.trace_single_eq_same] at htr
  exact one_ne_zero htr

/-- **Every finite graph that is not acyclic has a nonzero cyclic class of degree at least three
in the preprojective algebra of every orientation.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (hc : ¬ G.IsAcyclic) (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph] at hc
  push Not at hc
  obtain ⟨m, hm, ⟨f⟩⟩ := hc
  exact ⟨m, hm,
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy k hm f o⟩

end Main

end TauCeti
