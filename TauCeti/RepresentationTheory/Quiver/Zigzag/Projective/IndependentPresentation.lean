/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.QuadraticPresentation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Quadratic.Basis

/-!
# Independent quadratic projective presentations of zigzag simples

Choose one neighbour `c i` at each vertex of a finite graph.  In the quadratic presentation of
the simple head at `i`, use every nonreturning path `i → j → l` and only the backtrack
differences `i → j → i - i → c(i) → i`.  These map to distinct local members of the
basis `TauCeti.quadraticZigzagRelationsBasis`, so the degree-two relation term has no redundant
generators.

The induced differential has the same range as the choice-free differential indexed by all
ordered pairs of backtracks.  It is therefore exact at the neighbouring-projective term whenever
no edge is an isolated connected component.  Together with the arrow differential, this gives
the first two linear stages of the Koszul complex of a zigzag simple; no exactness assertion about
higher terms is made here.

The relations and their role in the Koszul complex follow Huerfano--Khovanov,
*A category for the adjoint representation*, Sections 3 and 6.1.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) (c : ∀ i : V, G.neighborSet i)

/-- Independent quadratic relation labels based at `i`: all nonreturning length-two paths and
one backtrack difference against the chosen neighbour for each other neighbour. -/
abbrev ZigzagIndependentQuadraticRelationIndex (i : V) :=
  (Σ j : G.neighborSet i, {l : G.neighborSet j.1 // l.1 ≠ i}) ⊕
    {j : G.neighborSet i // j ≠ c i}

/-- The endpoint of the relation path, hence the vertex of its projective summand. -/
abbrev ZigzagIndependentQuadraticRelationIndex.vertex {i : V} :
    ZigzagIndependentQuadraticRelationIndex G c i → V
  | .inl r => r.2.1.1
  | .inr _ => i

private theorem eq_of_comp_arrowPath_eq {i j j' l : V}
    {hij : G.Adj i j} {hjl : G.Adj j l} {hij' : G.Adj i j'} {hj'l : G.Adj j' l}
    (h : (arrowPath G hij).comp (arrowPath G hjl) =
      (arrowPath G hij').comp (arrowPath G hj'l)) : j = j' := by
  apply vertex_injective G
  apply _root_.Quiver.Path.obj_eq_of_cons_eq_cons
  simpa only [arrowPath_eq_toPath, _root_.Quiver.Path.comp_toPath_eq_cons] using h

/-- The member of `TauCeti.quadraticZigzagRelationsBasisIndex` represented by an independent
local relation label. -/
def zigzagIndependentQuadraticRelationBasisIndex (i : V) :
    ZigzagIndependentQuadraticRelationIndex G c i →
      quadraticZigzagRelationsBasisIndex G c
  | .inl ⟨j, l⟩ =>
      ⟨⟨vertex G i, vertex G l.1.1,
          (arrowPath G ((G.mem_neighborSet i j.1).1 j.2)).comp
            (arrowPath G ((G.mem_neighborSet j.1 l.1.1).1 l.1.2))⟩,
        by simp,
        by
          intro v h
          have hi : i = v := by
            apply vertex_injective G
            simpa using congrArg Sigma.fst h
          have hl : l.1.1 = v := by
            apply vertex_injective G
            simpa using congrArg (fun p : Quiver.TotalPath (DoubledQuiver G) => p.2.1) h
          exact l.2 (hl.trans hi.symm)⟩
  | .inr j =>
      ⟨⟨vertex G i, vertex G i,
          backtrackPath G ((G.mem_neighborSet i j.1.1).1 j.1.2)⟩,
        length_backtrackPath G _,
        by
          intro v h
          have hi : i = v := by
            apply vertex_injective G
            simpa using congrArg Sigma.fst h
          subst v
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
          exact j.2 (Subtype.ext ((backtrackPath_inj G).1 h))⟩

/-- A nonreturning local label selects its two-arrow path in the global relation basis. -/
@[simp]
theorem coe_zigzagIndependentQuadraticRelationBasisIndex_nonreturn (i : V)
    (j : G.neighborSet i) (l : {l : G.neighborSet j.1 // l.1 ≠ i}) :
    (zigzagIndependentQuadraticRelationBasisIndex G c i (.inl ⟨j, l⟩) :
      Quiver.TotalPath (DoubledQuiver G)) =
        ⟨vertex G i, vertex G l.1.1,
          (arrowPath G ((G.mem_neighborSet i j.1).1 j.2)).comp
            (arrowPath G ((G.mem_neighborSet j.1 l.1.1).1 l.1.2))⟩ :=
  by rw [zigzagIndependentQuadraticRelationBasisIndex]

/-- A returning local label selects its backtrack in the global relation basis. -/
@[simp]
theorem coe_zigzagIndependentQuadraticRelationBasisIndex_backtrack (i : V)
    (j : {j : G.neighborSet i // j ≠ c i}) :
    (zigzagIndependentQuadraticRelationBasisIndex G c i (.inr j) :
      Quiver.TotalPath (DoubledQuiver G)) =
        ⟨vertex G i, vertex G i,
          backtrackPath G ((G.mem_neighborSet i j.1.1).1 j.1.2)⟩ :=
  by rw [zigzagIndependentQuadraticRelationBasisIndex]

/-- Distinct independent local relation labels select distinct members of the global quadratic
relation basis. -/
theorem zigzagIndependentQuadraticRelationBasisIndex_injective (i : V) :
    Function.Injective (zigzagIndependentQuadraticRelationBasisIndex G c i) := by
  rintro (r | j) (r' | j') h
  · obtain ⟨⟨a, hai⟩, ⟨⟨l, hal⟩, hli⟩⟩ := r
    obtain ⟨⟨a', hai'⟩, ⟨⟨l', hal'⟩, hli'⟩⟩ := r'
    have ht := congrArg Subtype.val h
    simp only [zigzagIndependentQuadraticRelationBasisIndex] at ht
    have hl : l = l' := by
      apply vertex_injective G
      simpa using congrArg (fun p : Quiver.TotalPath (DoubledQuiver G) => p.2.1) ht
    subst l'
    have hp : (arrowPath G ((G.mem_neighborSet i a).1 hai)).comp
          (arrowPath G ((G.mem_neighborSet a l).1 hal)) =
        (arrowPath G ((G.mem_neighborSet i a').1 hai')).comp
          (arrowPath G ((G.mem_neighborSet a' l).1 hal')) := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using ht
    have ha : a = a' := eq_of_comp_arrowPath_eq G hp
    subst a'
    rfl
  · have ht := congrArg Subtype.val h
    simp only [zigzagIndependentQuadraticRelationBasisIndex] at ht
    have hl : r.2.1.1 = i := by
      apply vertex_injective G
      simpa using congrArg (fun p : Quiver.TotalPath (DoubledQuiver G) => p.2.1) ht
    exact (r.2.2 hl).elim
  · have ht := congrArg Subtype.val h
    simp only [zigzagIndependentQuadraticRelationBasisIndex] at ht
    have hl : r'.2.1.1 = i := by
      apply vertex_injective G
      simpa using congrArg (fun p : Quiver.TotalPath (DoubledQuiver G) => p.2.1) ht.symm
    exact (r'.2.2 hl).elim
  · have ht := congrArg Subtype.val h
    simp only [zigzagIndependentQuadraticRelationBasisIndex] at ht
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at ht
    have hj : j.1.1 = j'.1.1 := (backtrackPath_inj G).1 ht
    exact congrArg Sum.inr (Subtype.ext (Subtype.ext hj))

/-- The chosen local quadratic relations are linearly independent: they are a subfamily of
`TauCeti.quadraticZigzagRelationsBasis`. -/
theorem linearIndependent_zigzagIndependentQuadraticRelations
    [CommRing k] (i : V) :
    LinearIndependent k (fun r : ZigzagIndependentQuadraticRelationIndex G c i =>
      quadraticZigzagRelationsBasis k G c
        (zigzagIndependentQuadraticRelationBasisIndex G c i r)) :=
  (quadraticZigzagRelationsBasis k G c).linearIndependent.comp _
    (zigzagIndependentQuadraticRelationBasisIndex_injective G c i)

/-- The basis vector of a nonreturning local label is its two-arrow path monomial. -/
@[simp]
theorem coe_quadraticZigzagRelationsBasis_independent_nonreturn
    [CommRing k] (i : V) (j : G.neighborSet i)
    (l : {l : G.neighborSet j.1 // l.1 ≠ i}) :
    ((quadraticZigzagRelationsBasis k G c
      (zigzagIndependentQuadraticRelationBasisIndex G c i (.inl ⟨j, l⟩)) :
        quadraticZigzagRelations k G) : pathAlgebra k (DoubledQuiver G)) =
      ofPath ⟨vertex G i, vertex G l.1.1,
        (arrowPath G ((G.mem_neighborSet i j.1).1 j.2)).comp
          (arrowPath G ((G.mem_neighborSet j.1 l.1.1).1 l.1.2))⟩ := by
  apply coe_quadraticZigzagRelationsBasis_apply_of_ne
  intro h
  exact l.2 ((vertex_injective G) h.symm)

/-- The basis vector of a returning local label is its backtrack minus the chosen backtrack. -/
@[simp]
theorem coe_quadraticZigzagRelationsBasis_independent_backtrack
    [CommRing k] (i : V) (j : {j : G.neighborSet i // j ≠ c i}) :
    ((quadraticZigzagRelationsBasis k G c
      (zigzagIndependentQuadraticRelationBasisIndex G c i (.inr j)) :
        quadraticZigzagRelations k G) : pathAlgebra k (DoubledQuiver G)) =
      backtrackElem G k ((G.mem_neighborSet i j.1.1).1 j.1.2) -
        backtrackElem G k ((G.mem_neighborSet i (c i).1).1 (c i).2) := by
  rw [coe_quadraticZigzagRelationsBasis_apply_of_eq _ _ _ _ rfl,
    coe_zigzagIndependentQuadraticRelationBasisIndex_backtrack,
    vertexEquiv_symm_vertex]
  simp only [backtrackElem_eq_ofPath]

section Field

variable [Field k] [Finite V]

local notation "Z" => nonisolatedZigzagQuotient k G

/-- The direct sum of projectives indexed by an independent basis of the quadratic relations
based at `i`.  In the linear presentation its generators have degree two. -/
abbrev ZigzagIndependentQuadraticRelationProjectives (i : V) :=
  Π₀ r : ZigzagIndependentQuadraticRelationIndex G c i,
    zigzagProjective k G r.vertex

/-- The map of one independent quadratic relation into the neighbouring projectives. -/
noncomputable def zigzagProjectiveIndependentQuadraticRelationMap (i : V)
    (r : ZigzagIndependentQuadraticRelationIndex G c i) :
    zigzagProjective k G r.vertex →ₗ[Z] ZigzagNeighborProjectives k G i := by
  rcases r with r | j
  · exact zigzagProjectiveQuadraticRelationMap k G i (.inl r)
  · exact zigzagProjectiveQuadraticRelationMap k G i (.inr (j.1, c i))

/-- The independent quadratic differential, assembled from the chosen basis of relations. -/
noncomputable def zigzagProjectiveIndependentQuadraticDifferential (i : V) :
    ZigzagIndependentQuadraticRelationProjectives k G c i →ₗ[Z]
      ZigzagNeighborProjectives k G i := by
  classical
  exact DFinsupp.lsum ℕ (zigzagProjectiveIndependentQuadraticRelationMap k G c i)

/-- The independent quadratic differential on one projective summand. -/
@[simp]
theorem zigzagProjectiveIndependentQuadraticDifferential_single (i : V)
    [DecidableEq (ZigzagIndependentQuadraticRelationIndex G c i)]
    (r : ZigzagIndependentQuadraticRelationIndex G c i)
    (x : zigzagProjective k G r.vertex) :
    zigzagProjectiveIndependentQuadraticDifferential k G c i (DFinsupp.single r x) =
      zigzagProjectiveIndependentQuadraticRelationMap k G c i r x := by
  classical
  exact DFinsupp.lsum_single ℕ _ _ _

/-- A nonreturning independent relation is the corresponding nonreturning relation map. -/
@[simp]
theorem zigzagProjectiveIndependentQuadraticRelationMap_nonreturn (i : V)
    (r : Σ j : G.neighborSet i, {l : G.neighborSet j.1 // l.1 ≠ i})
    (x : zigzagProjective k G r.2.1.1) :
    zigzagProjectiveIndependentQuadraticRelationMap k G c i (.inl r) x =
      zigzagProjectiveQuadraticRelationMap k G i (.inl r) x := by
  rw [zigzagProjectiveIndependentQuadraticRelationMap]

/-- A returning independent relation compares its backtrack with the chosen backtrack. -/
@[simp]
theorem zigzagProjectiveIndependentQuadraticRelationMap_backtrack (i : V)
    (j : {j : G.neighborSet i // j ≠ c i}) (x : zigzagProjective k G i) :
    zigzagProjectiveIndependentQuadraticRelationMap k G c i (.inr j) x =
      zigzagProjectiveQuadraticRelationMap k G i (.inr (j.1, c i)) x := by
  rw [zigzagProjectiveIndependentQuadraticRelationMap]

/-- The independent quadratic differential followed by the arrow differential is zero. -/
@[simp]
theorem zigzagProjectiveArrowSum_comp_independentQuadraticDifferential (i : V) :
    zigzagProjectiveArrowSum k G i ∘ₗ
      zigzagProjectiveIndependentQuadraticDifferential k G c i = 0 := by
  classical
  apply DFinsupp.lhom_ext
  intro r x
  rw [LinearMap.comp_apply, zigzagProjectiveIndependentQuadraticDifferential_single]
  rcases r with r | j
  · rw [zigzagProjectiveIndependentQuadraticRelationMap_nonreturn]
    have h := LinearMap.congr_fun
      (zigzagProjectiveArrowSum_comp_quadraticDifferential k G i)
      (DFinsupp.single (.inl r) x)
    simpa only [LinearMap.comp_apply, zigzagProjectiveQuadraticDifferential_single,
      LinearMap.zero_apply] using h
  · rw [zigzagProjectiveIndependentQuadraticRelationMap_backtrack]
    have h := LinearMap.congr_fun
      (zigzagProjectiveArrowSum_comp_quadraticDifferential k G i)
      (DFinsupp.single (.inr (j.1, c i)) x)
    simpa only [LinearMap.comp_apply, zigzagProjectiveQuadraticDifferential_single,
      LinearMap.zero_apply] using h

private theorem range_independent_le_range_quadratic (i : V) :
    LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i) ≤
      LinearMap.range (zigzagProjectiveQuadraticDifferential k G i) := by
  classical
  rintro _ ⟨x, rfl⟩
  induction x using DFinsupp.induction with
  | h0 => simp
  | @ha r x y _ _ hy =>
      rw [map_add, zigzagProjectiveIndependentQuadraticDifferential_single]
      rcases r with r | j
      · exact (LinearMap.range (zigzagProjectiveQuadraticDifferential k G i)).add_mem
          ⟨DFinsupp.single (.inl r) x, by
            rw [zigzagProjectiveQuadraticDifferential_single,
              zigzagProjectiveIndependentQuadraticRelationMap_nonreturn]⟩ hy
      · exact (LinearMap.range (zigzagProjectiveQuadraticDifferential k G i)).add_mem
          ⟨DFinsupp.single (.inr (j.1, c i)) x, by
            rw [zigzagProjectiveQuadraticDifferential_single,
              zigzagProjectiveIndependentQuadraticRelationMap_backtrack]⟩ hy

private theorem quadraticRelationMap_mem_range_independent (i : V)
    (r : ZigzagQuadraticRelationIndex G i) (x : zigzagProjective k G r.vertex) :
    zigzagProjectiveQuadraticRelationMap k G i r x ∈
      LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i) := by
  classical
  rcases r with r | ⟨j, j'⟩
  · exact ⟨DFinsupp.single (.inl r) x, by
      rw [zigzagProjectiveIndependentQuadraticDifferential_single,
        zigzagProjectiveIndependentQuadraticRelationMap_nonreturn]⟩
  · dsimp only [ZigzagQuadraticRelationIndex.vertex] at x
    -- Each backtrack difference factors through the chosen backtrack.
    have hc : ∀ a : G.neighborSet i,
        zigzagProjectiveQuadraticRelationMap k G i (.inr (a, c i)) x ∈
          LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i) := by
      intro a
      by_cases ha : a = c i
      · subst a
        rw [zigzagProjectiveQuadraticRelationMap_backtrack, sub_self]
        exact zero_mem _
      · exact ⟨DFinsupp.single (.inr ⟨a, ha⟩) x, by
          rw [zigzagProjectiveIndependentQuadraticDifferential_single,
            zigzagProjectiveIndependentQuadraticRelationMap_backtrack]⟩
    have hsub : zigzagProjectiveQuadraticRelationMap k G i (.inr (j, j')) x =
        zigzagProjectiveQuadraticRelationMap k G i (.inr (j, c i)) x -
          zigzagProjectiveQuadraticRelationMap k G i (.inr (j', c i)) x := by
      rw [zigzagProjectiveQuadraticRelationMap_backtrack k G i j,
        zigzagProjectiveQuadraticRelationMap_backtrack k G i j,
        zigzagProjectiveQuadraticRelationMap_backtrack k G i j', sub_sub_sub_cancel_right]
    rw [hsub]
    exact sub_mem (hc j) (hc j')

private theorem range_quadratic_le_range_independent (i : V) :
    LinearMap.range (zigzagProjectiveQuadraticDifferential k G i) ≤
      LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i) := by
  classical
  rintro _ ⟨x, rfl⟩
  induction x using DFinsupp.induction with
  | h0 => simp
  | @ha r x y _ _ hy =>
      rw [map_add, zigzagProjectiveQuadraticDifferential_single]
      exact (LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i)).add_mem
        (quadraticRelationMap_mem_range_independent k G c i r x) hy

/-- The independent and redundant quadratic differentials have the same range.  Thus deleting
the redundant pairwise backtrack differences does not change the presented syzygy. -/
theorem range_zigzagProjectiveIndependentQuadraticDifferential (i : V) :
    LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i) =
      LinearMap.range (zigzagProjectiveQuadraticDifferential k G i) :=
  le_antisymm (range_independent_le_range_quadratic k G c i)
    (range_quadratic_le_range_independent k G c i)

/-- **The independent quadratic stage is exact.** Under the local branching hypothesis, its
image is the kernel of the arrow differential. -/
theorem range_zigzagProjectiveIndependentQuadraticDifferential_eq_ker (i : V)
    (hbranch : ∀ j : G.neighborSet i,
      (∃ l : G.neighborSet j.1, l.1 ≠ i) ∨ (∃ j' : G.neighborSet i, j' ≠ j)) :
    LinearMap.range (zigzagProjectiveIndependentQuadraticDifferential k G c i) =
      LinearMap.ker (zigzagProjectiveArrowSum k G i) := by
  rw [range_zigzagProjectiveIndependentQuadraticDifferential]
  exact range_zigzagProjectiveQuadraticDifferential_eq_ker k G
    (fun v => ⟨(c v).1, (G.mem_neighborSet v (c v).1).1 (c v).2⟩) i hbranch

/-- The independent quadratic differential raises every coordinate degree by one.  Shifting its
source by two and the neighbouring-projective term by one makes it degree zero. -/
theorem zigzagProjectiveIndependentQuadraticDifferential_mem_grade (i : V) {p : ℤ}
    {x : ZigzagIndependentQuadraticRelationProjectives k G c i}
    (hx : ∀ r, x r ∈ zigzagProjectiveGrade k G r.vertex p) (j : G.neighborSet i) :
    zigzagProjectiveIndependentQuadraticDifferential k G c i x j ∈
      zigzagProjectiveGrade k G j.1 (p + 1) := by
  classical
  simp only [zigzagProjectiveIndependentQuadraticDifferential, DFinsupp.lsum_apply_apply,
    DFinsupp.sumAddHom_apply, DFinsupp.sum, LinearMap.toAddMonoidHom_coe,
    DFinsupp.finsetSum_apply]
  exact Submodule.sum_mem _ fun r _ =>
    match r with
    | .inl r => zigzagProjectiveQuadraticRelationMap_mem_grade k G i (.inl r) (hx (.inl r)) j
    | .inr r => zigzagProjectiveQuadraticRelationMap_mem_grade k G i (.inr (r.1, c i))
        (hx (.inr r)) j

/-- The independent quadratic relation term is projective. -/
instance projective_zigzagIndependentQuadraticRelationProjectives (i : V) :
    Module.Projective Z (ZigzagIndependentQuadraticRelationProjectives k G c i) := by
  let : ∀ r : ZigzagIndependentQuadraticRelationIndex G c i,
      Module.Projective Z (zigzagProjective k G r.vertex) :=
    fun r => zigzagProjective_projective k G r.vertex
  infer_instance

end Field

end TauCeti
