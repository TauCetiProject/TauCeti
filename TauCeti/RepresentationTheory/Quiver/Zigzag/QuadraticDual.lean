/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.QuadraticDual
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Opposite
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# The quadratic dual of a zigzag algebra

The zigzag algebra of a finite simple graph `G` is presented on the doubled quiver by two families
of quadratic relations: the length-two paths whose endpoints differ, and the differences of two
backtracks based at one vertex. This file computes the orthogonal complement of the span of those
relators and identifies the resulting quadratic dual.

The answer is the *signless* preprojective relation. A degree-two element orthogonal to every
length-two path with distinct endpoints is supported on the backtracks, and orthogonality to the
differences of the backtracks at a vertex makes its coordinates there constant; so the orthogonal
complement is spanned by the sums

```text
s_i = ∑_{j ∼ i} (i → j → i)
```

of all backtracks at a vertex, one for each vertex, which is the relation Huerfano and Khovanov
find in the quadratic dual.

Quadratic duality presents the dual algebra on the opposite quiver, hence — through
`TauCeti.PathAlgebra.reverseOpAlgEquiv` — on the opposite of the doubled path algebra. Every
backtrack is a palindrome, so reversal carries the signless relation to itself and the quadratic
dual is presented back on the doubled quiver itself:
`TauCeti.quadraticDualQuadraticZigzagEquivSignless`.

That equivalence is a statement about the quadratic *presentation*, and holds for every finite
simple graph. The graph enters only through the identification of the presented algebra with the
zigzag algebra, `TauCeti.quadraticZigzagPresentationEquivZigzagQuotient`, which carries the
hypotheses of `TauCeti.zigzagIdeal_eq_quadraticZigzagIdeal`: connectedness and at least three
vertices. It is for such a graph, and only there, that the algebra computed here is the quadratic
dual of the zigzag algebra. The one-vertex and two-vertex graphs, whose zigzag algebras are the
dual numbers and a radical-cube-zero algebra, are not presented by their quadratic relations and
are excluded.

## Main definitions

* `TauCeti.quadraticZigzagRelations`: the `k`-span of the quadratic zigzag relators, the degree-two
  relation space of the quadratic presentation.
* `TauCeti.quadraticZigzagPresentationEquivZigzagQuotient`: for a connected graph with at least
  three vertices that relation space presents the zigzag algebra.
* `TauCeti.quadraticDualQuadraticZigzagEquivSignless`: **the quadratic dual of that presentation is
  the signless preprojective algebra of the doubled quiver**.

## Main results

* `TauCeti.twoSidedIdeal_span_quadraticZigzagRelations_eq_quadraticZigzagIdeal` and
  `TauCeti.twoSidedIdeal_span_quadraticZigzagRelations_eq_zigzagIdeal`: the relation space
  generates the quadratic zigzag ideal, which for a connected graph with at least three vertices
  is the zigzag relation ideal, so the quotient it presents is the zigzag algebra.
* `TauCeti.quadraticOrthogonal_quadraticZigzagRelations`: **the orthogonal complement of the
  quadratic zigzag relations is spanned by the signless relators**.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the quadratic dual of the zigzag algebra.
-/

public section

namespace TauCeti

open _root_.Quiver MulOpposite PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-! ### The coordinates of a signless relator -/

section Coordinates

variable [∀ v : V, Fintype (G.neighborSet v)]

/-- **The signless relator at `v` is supported on the backtracks based at `v`**: its coordinate on
any other path vanishes. -/
theorem repr_signlessPreprojectiveRelator_eq_zero (v : V)
    {x : Quiver.TotalPath (DoubledQuiver G)}
    (hx : ∀ (j : V) (h : G.Adj v j),
      x ≠ ⟨vertex G v, vertex G v, backtrackPath G h⟩) :
    (pathAlgebraBasis k (DoubledQuiver G)).repr
      (signlessPreprojectiveRelator k (vertex G v)) x = 0 := by
  rw [signlessPreprojectiveRelator_vertex, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [backtrackElem_eq_ofPath, ofPath_eq_single, pathAlgebraBasis_repr_single]
  exact Finsupp.single_eq_of_ne fun hpath =>
    hx w.1 ((G.mem_neighborSet v w).1 w.2) hpath

/-- The coordinate of the signless relator at `v` on a path which is not a loop vanishes: every
backtrack returns to its source. -/
theorem repr_signlessPreprojectiveRelator_eq_zero_of_ne (v : V)
    {x : Quiver.TotalPath (DoubledQuiver G)} (hx : x.1 ≠ x.2.1) :
    (pathAlgebraBasis k (DoubledQuiver G)).repr
      (signlessPreprojectiveRelator k (vertex G v)) x = 0 :=
  repr_signlessPreprojectiveRelator_eq_zero k G v fun _ _ hpath => hx (by rw [hpath])

/-- The coordinate of the signless relator at `v` on a path whose length is not two vanishes: every
backtrack has length two. -/
theorem repr_signlessPreprojectiveRelator_eq_zero_of_length_ne (v : V)
    {x : Quiver.TotalPath (DoubledQuiver G)} (hx : x.2.2.length ≠ 2) :
    (pathAlgebraBasis k (DoubledQuiver G)).repr
      (signlessPreprojectiveRelator k (vertex G v)) x = 0 :=
  repr_signlessPreprojectiveRelator_eq_zero k G v fun _ h hpath =>
    hx (by rw [hpath]; exact length_backtrackPath G h)

/-- The coordinate of the signless relator at `v` on a backtrack based at another vertex
vanishes. -/
theorem repr_signlessPreprojectiveRelator_backtrackPath_of_ne (v : V) {i j : V} (h : G.Adj i j)
    (hvi : v ≠ i) :
    (pathAlgebraBasis k (DoubledQuiver G)).repr
      (signlessPreprojectiveRelator k (vertex G v))
      ⟨vertex G i, vertex G i, backtrackPath G h⟩ = 0 :=
  repr_signlessPreprojectiveRelator_eq_zero k G v fun _ _ hpath =>
    hvi ((vertex_inj G).1 (congrArg Sigma.fst hpath)).symm

/-- **The coordinate of the signless relator at `v` on a backtrack based at `v` is one**: exactly
one summand of the relator is that backtrack. -/
theorem repr_signlessPreprojectiveRelator_backtrackPath_self (v : V) {j : V} (h : G.Adj v j) :
    (pathAlgebraBasis k (DoubledQuiver G)).repr
      (signlessPreprojectiveRelator k (vertex G v))
      ⟨vertex G v, vertex G v, backtrackPath G h⟩ = 1 := by
  classical
  rw [signlessPreprojectiveRelator_vertex, map_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (⟨j, (G.mem_neighborSet v j).2 h⟩ : G.neighborSet v)]
  · rw [backtrackElem_eq_ofPath, ofPath_eq_single, pathAlgebraBasis_repr_single,
      Finsupp.single_eq_same]
  · intro w _ hw
    rw [backtrackElem_eq_ofPath, ofPath_eq_single, pathAlgebraBasis_repr_single]
    refine Finsupp.single_eq_of_ne fun hpath => hw (Subtype.ext ?_)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hpath
    exact eq_of_backtrackPath_eq G hpath.symm
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The signless relator has the same coordinate on any two backtracks based at one vertex**:
this is what makes it orthogonal to the differences of those backtracks. -/
theorem repr_signlessPreprojectiveRelator_backtrackPath_congr (v : V) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    (pathAlgebraBasis k (DoubledQuiver G)).repr
        (signlessPreprojectiveRelator k (vertex G v))
        ⟨vertex G i, vertex G i, backtrackPath G h⟩ =
      (pathAlgebraBasis k (DoubledQuiver G)).repr
        (signlessPreprojectiveRelator k (vertex G v))
        ⟨vertex G i, vertex G i, backtrackPath G h'⟩ := by
  by_cases hvi : v = i
  · subst hvi
    rw [repr_signlessPreprojectiveRelator_backtrackPath_self k G v h,
      repr_signlessPreprojectiveRelator_backtrackPath_self k G v h']
  · rw [repr_signlessPreprojectiveRelator_backtrackPath_of_ne k G v h hvi,
      repr_signlessPreprojectiveRelator_backtrackPath_of_ne k G v h' hvi]

end Coordinates

/-! ### The quadratic relation space -/

/-- The **quadratic relation space of a zigzag algebra**: the `k`-span of the quadratic zigzag
relators inside the degree-two part of the path algebra of the doubled quiver. -/
noncomputable def quadraticZigzagRelations : Submodule k (pathAlgebra k (DoubledQuiver G)) :=
  Submodule.span k {x | IsQuadraticZigzagRelator k G x}

/-- The quadratic relation space is the span of the quadratic relators. -/
theorem quadraticZigzagRelations_eq_span :
    quadraticZigzagRelations k G = Submodule.span k {x | IsQuadraticZigzagRelator k G x} := by
  rw [quadraticZigzagRelations]

/-- The quadratic relators are homogeneous of degree two, so the relation space they span lies in
the degree-two part of the path algebra. -/
theorem quadraticZigzagRelations_le_grade_two :
    quadraticZigzagRelations k G ≤ grade k (DoubledQuiver G) 2 := by
  rw [quadraticZigzagRelations_eq_span, Submodule.span_le]
  rintro _ (⟨p, hp, _⟩ | ⟨p, q, hp, hq⟩)
  · exact ofPath_mem_grade_of_length hp
  · exact Submodule.sub_mem _ (ofPath_mem_grade_of_length hp) (ofPath_mem_grade_of_length hq)

variable [Finite V]

/-- The quadratic relation space generates the quadratic zigzag ideal: passing to the `k`-span
first does not change the two-sided ideal. -/
theorem twoSidedIdeal_span_quadraticZigzagRelations_eq_quadraticZigzagIdeal :
    TwoSidedIdeal.span (quadraticZigzagRelations k G : Set (pathAlgebra k (DoubledQuiver G)))
      = quadraticZigzagIdeal k G := by
  have hsub : ∀ x ∈ quadraticZigzagRelations k G, x ∈ quadraticZigzagIdeal k G := by
    intro x hx
    rw [quadraticZigzagRelations_eq_span] at hx
    have hle : Submodule.span k {y | IsQuadraticZigzagRelator k G y} ≤
        (quadraticZigzagIdeal k G).asIdeal.restrictScalars k :=
      Submodule.span_le.2 fun y hy => TwoSidedIdeal.mem_asIdeal.2
        (mem_quadraticZigzagIdeal_of_isQuadraticZigzagRelator k G hy)
    exact TwoSidedIdeal.mem_asIdeal.1 (hle hx)
  refine le_antisymm (TwoSidedIdeal.span_le.2 hsub) ?_
  rw [quadraticZigzagIdeal_eq_span]
  refine TwoSidedIdeal.span_le.2 fun x hx => TwoSidedIdeal.subset_span ?_
  rw [SetLike.mem_coe, quadraticZigzagRelations_eq_span]
  exact Submodule.subset_span hx

/-- For a connected graph with at least three vertices the quadratic relation space presents the
zigzag algebra: the two-sided ideal it generates is the zigzag relation ideal. -/
theorem twoSidedIdeal_span_quadraticZigzagRelations_eq_zigzagIdeal (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) :
    TwoSidedIdeal.span (quadraticZigzagRelations k G : Set (pathAlgebra k (DoubledQuiver G)))
      = zigzagIdeal k G := by
  rw [twoSidedIdeal_span_quadraticZigzagRelations_eq_quadraticZigzagIdeal,
    zigzagIdeal_eq_quadraticZigzagIdeal k G hconn hcard]

/-- **For a connected graph with at least three vertices the quadratic relation space presents the
zigzag algebra**: the quotient of the path algebra of the doubled quiver by the ideal it generates
is the zigzag relation quotient. This is what makes the algebra dualised below the zigzag algebra
rather than the quadratic presentation alone, and it carries the hypotheses of
`TauCeti.twoSidedIdeal_span_quadraticZigzagRelations_eq_zigzagIdeal`. -/
noncomputable def quadraticZigzagPresentationEquivZigzagQuotient (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) :
    (pathAlgebra k (DoubledQuiver G) ⧸
        (TwoSidedIdeal.span
          (quadraticZigzagRelations k G : Set (pathAlgebra k (DoubledQuiver G)))).asIdeal) ≃ₐ[k]
      nonisolatedZigzagQuotient k G :=
  Ideal.quotientEquivAlgOfEq k
    (congrArg TwoSidedIdeal.asIdeal
      (twoSidedIdeal_span_quadraticZigzagRelations_eq_zigzagIdeal k G hconn hcard))

/-- The quadratic presentation equivalence sends the class of a path-algebra element to its
class in the zigzag quotient. -/
@[simp]
theorem quadraticZigzagPresentationEquivZigzagQuotient_mk (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) (x : pathAlgebra k (DoubledQuiver G)) :
    quadraticZigzagPresentationEquivZigzagQuotient k G hconn hcard
        (Ideal.Quotient.mk
          (TwoSidedIdeal.span
            (quadraticZigzagRelations k G : Set (pathAlgebra k (DoubledQuiver G)))).asIdeal x) =
      zigzagMk k G x := by
  rw [quadraticZigzagPresentationEquivZigzagQuotient,
    Ideal.quotientEquivAlgOfEq_mk, zigzagMk_apply]

/-! ### The orthogonal complement -/

section Orthogonal

variable [∀ v : V, Fintype (G.neighborSet v)]

/-- **The quadratic dual relations of a zigzag algebra are the signless preprojective relations**:
the orthogonal complement of the quadratic zigzag relations is spanned by the sums of the
backtracks at the vertices. -/
theorem quadraticOrthogonal_quadraticZigzagRelations :
    quadraticOrthogonal k (DoubledQuiver G) (quadraticZigzagRelations k G) =
      Submodule.span k
        (Set.range fun v : DoubledQuiver G => signlessPreprojectiveRelator k v) := by
  classical
  -- Indexing the relators by the graph vertices names the same family.
  have hrange : (Set.range fun v : DoubledQuiver G => signlessPreprojectiveRelator k v) =
      Set.range fun v : V => signlessPreprojectiveRelator k (vertex G v) := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro _ ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := exists_eq_vertex G v
      exact ⟨w, signlessPreprojectiveRelator_congr k (vertex G w) _ _⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨vertex G w, signlessPreprojectiveRelator_congr k (vertex G w) _ _⟩
  rw [hrange]
  refine le_antisymm (fun f hf => ?_) ?_
  -- An orthogonal element is the combination of the relators read off its own coordinates on the
  -- backtracks.
  · rw [quadraticZigzagRelations_eq_span, mem_quadraticOrthogonal_span_iff] at hf
    obtain ⟨hdeg, horth⟩ := hf
    -- A coordinate of `f` on a length-two path which is not a loop vanishes.
    have hne : ∀ {a b : DoubledQuiver G} (p : _root_.Quiver.Path a b), p.length = 2 → a ≠ b →
        (pathAlgebraBasis k (DoubledQuiver G)).repr f ⟨a, b, p⟩ = 0 := fun p hp hab => by
      simpa only [pathPairing_apply_ofPath] using
        horth _ (IsQuadraticZigzagRelator.nonreturn p hp hab)
    -- The coordinates of `f` on the backtracks based at one vertex agree.
    have hconst : ∀ {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j'),
        (pathAlgebraBasis k (DoubledQuiver G)).repr f
            ⟨vertex G i, vertex G i, backtrackPath G h⟩ =
          (pathAlgebraBasis k (DoubledQuiver G)).repr f
            ⟨vertex G i, vertex G i, backtrackPath G h'⟩ := fun h h' => by
      simpa only [map_sub, pathPairing_apply_ofPath, sub_eq_zero] using
        horth _ (IsQuadraticZigzagRelator.equal_backtracks (backtrackPath G h)
          (backtrackPath G h') (length_backtrackPath G h) (length_backtrackPath G h'))
    let _ := Fintype.ofFinite V
    -- The common coordinate of `f` at each vertex, zero at an isolated vertex.
    set c : V → k := fun u => if h : ∃ j, G.Adj u j then
      (pathAlgebraBasis k (DoubledQuiver G)).repr f
        ⟨vertex G u, vertex G u, backtrackPath G h.choose_spec⟩ else 0 with hc
    have hcval : ∀ {u j : V} (h : G.Adj u j), c u =
        (pathAlgebraBasis k (DoubledQuiver G)).repr f
          ⟨vertex G u, vertex G u, backtrackPath G h⟩ := fun {u j} h => by
      simp only [hc]
      rw [dite_eq_left (⟨j, h⟩ : ∃ j, G.Adj u j)]
      exact hconst _ h
    have hfeq : f = ∑ v : V, c v • signlessPreprojectiveRelator k (vertex G v) := by
      refine (Module.Basis.ext_elem_iff (pathAlgebraBasis k (DoubledQuiver G))).2 fun x => ?_
      obtain ⟨a, b, p⟩ := x
      rw [map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      obtain ⟨a₀, rfl⟩ := exists_eq_vertex G a
      obtain ⟨b₀, rfl⟩ := exists_eq_vertex G b
      by_cases hlen : p.length = 2
      · by_cases hab : a₀ = b₀
        · subst hab
          obtain ⟨j, hj, rfl⟩ := exists_eq_backtrackPath G p hlen
          rw [Finset.sum_eq_single a₀,
            repr_signlessPreprojectiveRelator_backtrackPath_self k G a₀ hj, mul_one, hcval hj]
          · intro w _ hw
            rw [repr_signlessPreprojectiveRelator_backtrackPath_of_ne k G w hj hw, mul_zero]
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        · rw [hne p hlen fun h => hab ((vertex_inj G).1 h)]
          refine (Finset.sum_eq_zero fun w _ => ?_).symm
          rw [repr_signlessPreprojectiveRelator_eq_zero_of_ne k G w
            (fun h => hab ((vertex_inj G).1 h)), mul_zero]
      · rw [Finsupp.notMem_support_iff.1 fun hx => hlen (mem_grade_iff.1 hdeg _ hx)]
        refine (Finset.sum_eq_zero fun w _ => ?_).symm
        rw [repr_signlessPreprojectiveRelator_eq_zero_of_length_ne k G w hlen, mul_zero]
    rw [hfeq]
    exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self v))
  -- Conversely each relator is homogeneous of degree two and orthogonal to both families of
  -- quadratic relators.
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, quadraticZigzagRelations_eq_span, mem_quadraticOrthogonal_span_iff]
    refine ⟨signlessPreprojectiveRelator_mem_grade_two k (vertex G v), ?_⟩
    rintro _ (⟨p, hp, hab⟩ | ⟨p, q, hp, hq⟩)
    · rw [pathPairing_apply_ofPath, repr_signlessPreprojectiveRelator_eq_zero_of_ne k G v hab]
    · rename_i i
      obtain ⟨i, rfl⟩ := exists_eq_vertex G i
      obtain ⟨j, hj, rfl⟩ := exists_eq_backtrackPath G p hp
      obtain ⟨j', hj', rfl⟩ := exists_eq_backtrackPath G q hq
      rw [map_sub, pathPairing_apply_ofPath, pathPairing_apply_ofPath,
        repr_signlessPreprojectiveRelator_backtrackPath_congr k G v hj hj', sub_self]

end Orthogonal

/-! ### The quadratic dual algebra -/

section Algebra

variable [∀ v : V, Fintype (G.neighborSet v)]

/-- Every signless relator is a quadratic dual relation of the zigzag algebra. -/
theorem signlessPreprojectiveRelator_mem_quadraticOrthogonal (v : DoubledQuiver G) :
    signlessPreprojectiveRelator k v ∈
      quadraticOrthogonal k (DoubledQuiver G) (quadraticZigzagRelations k G) := by
  rw [quadraticOrthogonal_quadraticZigzagRelations]
  exact Submodule.subset_span (Set.mem_range_self v)

/-- Path reversal followed by the quotient map onto the signless preprojective algebra, read on the
opposite path algebra where the quadratic dual lives. -/
private noncomputable def signlessOfOp :
    (pathAlgebra k (DoubledQuiver G))ᵐᵒᵖ →ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  (signlessPreprojectiveMk k (DoubledQuiver G)).comp
    (reverseOpAlgEquiv k (DoubledQuiver G)).symm.toAlgHom

private theorem signlessOfOp_apply (x : (pathAlgebra k (DoubledQuiver G))ᵐᵒᵖ) :
    signlessOfOp k G x = signlessPreprojectiveMk k (DoubledQuiver G)
      ((reverseOpAlgEquiv k (DoubledQuiver G)).symm x) := (rfl)

private theorem signlessOfOp_op_eq_zero {x : pathAlgebra k (DoubledQuiver G)}
    (hx : x ∈ quadraticOrthogonal k (DoubledQuiver G) (quadraticZigzagRelations k G)) :
    signlessOfOp k G (op x) = 0 := by
  rw [quadraticOrthogonal_quadraticZigzagRelations] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [signlessOfOp_apply, ← reverseOpAlgEquiv_signlessPreprojectiveRelator k v,
      AlgEquiv.symm_apply_apply, signlessPreprojectiveMk_signlessPreprojectiveRelator]
  | zero => rw [op_zero, map_zero]
  | add y z _ _ hy hz => rw [op_add, map_add, hy, hz, add_zero]
  | smul r y _ hy => rw [op_smul, map_smul, hy, smul_zero]

/-- Path reversal followed by the quotient map onto the quadratic dual. -/
private noncomputable def quadraticDualOfPath :
    pathAlgebra k (DoubledQuiver G) →ₐ[k]
      quadraticDual k (DoubledQuiver G) (quadraticZigzagRelations k G) :=
  (quadraticDualMk k (DoubledQuiver G) (quadraticZigzagRelations k G)).comp
    (reverseOpAlgEquiv k (DoubledQuiver G)).toAlgHom

omit [∀ v : V, Fintype (G.neighborSet v)] in
private theorem quadraticDualOfPath_apply (x : pathAlgebra k (DoubledQuiver G)) :
    quadraticDualOfPath k G x =
      quadraticDualMk k (DoubledQuiver G) (quadraticZigzagRelations k G)
        (reverseOpAlgEquiv k (DoubledQuiver G) x) := (rfl)

private theorem quadraticDualOfPath_signlessPreprojectiveRelator (v : DoubledQuiver G) :
    quadraticDualOfPath k G (signlessPreprojectiveRelator k v) = 0 := by
  rw [quadraticDualOfPath_apply, reverseOpAlgEquiv_signlessPreprojectiveRelator]
  exact quadraticDualMk_op_eq_zero (signlessPreprojectiveRelator_mem_quadraticOrthogonal k G v)

/-- **The quadratic dual of the quadratic presentation of a zigzag algebra is the signless
preprojective algebra of the doubled quiver**. The quadratic dual is presented on the opposite
path algebra; path reversal carries it back to the doubled quiver, fixing every backtrack and
hence every signless relator.

The relation space dualised here presents the zigzag algebra for the graphs of
`TauCeti.quadraticZigzagPresentationEquivZigzagQuotient`, connected with at least three vertices,
and it is for those graphs that this computes the quadratic dual of the zigzag algebra itself. -/
noncomputable def quadraticDualQuadraticZigzagEquivSignless :
    quadraticDual k (DoubledQuiver G) (quadraticZigzagRelations k G) ≃ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  AlgEquiv.ofAlgHom
    (quadraticDualLift (signlessOfOp k G) fun _ hx => signlessOfOp_op_eq_zero k G hx)
    (signlessPreprojectiveLift (quadraticDualOfPath k G)
      (quadraticDualOfPath_signlessPreprojectiveRelator k G))
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k (DoubledQuiver G) y
      rw [AlgHom.comp_apply, signlessPreprojectiveLift_signlessPreprojectiveMk,
        quadraticDualOfPath_apply, quadraticDualLift_quadraticDualMk, signlessOfOp_apply,
        AlgEquiv.symm_apply_apply, AlgHom.id_apply])
    (AlgHom.ext fun y => by
      obtain ⟨z, rfl⟩ :=
        quadraticDualMk_surjective k (DoubledQuiver G) (quadraticZigzagRelations k G) y
      rw [AlgHom.comp_apply, quadraticDualLift_quadraticDualMk, signlessOfOp_apply,
        signlessPreprojectiveLift_signlessPreprojectiveMk, quadraticDualOfPath_apply,
        AlgEquiv.apply_symm_apply, AlgHom.id_apply])

/-- The identification of the quadratic dual with the signless algebra is induced by path
reversal. -/
@[simp]
theorem quadraticDualQuadraticZigzagEquivSignless_quadraticDualMk
    (x : (pathAlgebra k (DoubledQuiver G))ᵐᵒᵖ) :
    quadraticDualQuadraticZigzagEquivSignless k G
        (quadraticDualMk k (DoubledQuiver G) (quadraticZigzagRelations k G) x) =
      signlessPreprojectiveMk k (DoubledQuiver G)
        ((reverseOpAlgEquiv k (DoubledQuiver G)).symm x) := by
  rw [quadraticDualQuadraticZigzagEquivSignless, AlgEquiv.ofAlgHom_apply,
    quadraticDualLift_quadraticDualMk, signlessOfOp_apply]

/-- The inverse identification sends the class of a path-algebra element to the quadratic-dual
class obtained by path reversal. -/
@[simp]
theorem quadraticDualQuadraticZigzagEquivSignless_symm_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    (quadraticDualQuadraticZigzagEquivSignless k G).symm
        (signlessPreprojectiveMk k (DoubledQuiver G) x) =
      quadraticDualMk k (DoubledQuiver G) (quadraticZigzagRelations k G)
        (reverseOpAlgEquiv k (DoubledQuiver G) x) := by
  apply (quadraticDualQuadraticZigzagEquivSignless k G).injective
  rw [AlgEquiv.apply_symm_apply,
    quadraticDualQuadraticZigzagEquivSignless_quadraticDualMk,
    AlgEquiv.symm_apply_apply]

end Algebra

end TauCeti
