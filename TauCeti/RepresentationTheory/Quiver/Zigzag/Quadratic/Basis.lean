/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Quadratic.Dual

/-!
# An explicit basis of quadratic zigzag relations

Choose one neighbor at each vertex. The nonreturning paths of length two, together with the
backtrack differences against the chosen neighbor, form a basis of the quadratic zigzag relation
space. Unlike the family of all pairwise backtrack differences, this family is independent and
therefore provides independent degree-two generators for Koszul complexes.

The index consists of all length-two paths except the chosen backtracks. Its coordinates are
simply the ambient path coordinates on these paths. No field or finiteness assumption is needed;
the supplied neighbor choice requires every vertex to have a neighbor. The empty graph is allowed.
This concerns the quadratic relation space, including for small graphs; it does not assert that
the strict zigzag algebra has a quadratic presentation in the exceptional small cases.

The defining relations follow Huerfano--Khovanov, *A category for the adjoint representation*,
Sections 3 and 6.1, https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) (c : ∀ i : V, G.neighborSet i)

private def chosenBacktrack (i : V) : Quiver.TotalPath (DoubledQuiver G) :=
  ⟨vertex G i, vertex G i, backtrackPath G ((G.mem_neighborSet i _).1 (c i).property)⟩

/-- Length-two paths other than the chosen backtracks. Nonreturning paths index monomial
relations, and the remaining backtracks index differences against the chosen neighbor. -/
abbrev quadraticZigzagRelationsBasisIndex :=
  {p : Quiver.TotalPath (DoubledQuiver G) // p.2.2.length = 2 ∧
    ∀ i : V, p ≠ ⟨vertex G i, vertex G i,
      backtrackPath G ((G.mem_neighborSet i _).1 (c i).property)⟩}

variable [CommRing k]

private noncomputable def relationVector (p : quadraticZigzagRelationsBasisIndex G c) :
    pathAlgebra k (DoubledQuiver G) := by
  classical
  exact ofPath p.val - if p.val.1 = p.val.2.1 then
    ofPath (chosenBacktrack G c ((vertexEquiv G).symm p.val.1)) else 0

private theorem relationVector_eq [DecidableEq (DoubledQuiver G)]
    (p : quadraticZigzagRelationsBasisIndex G c) :
    relationVector k G c p = ofPath p.val - if p.val.1 = p.val.2.1 then
      ofPath (chosenBacktrack G c ((vertexEquiv G).symm p.val.1)) else 0 := by
  classical
  unfold relationVector
  split_ifs <;> rfl

private theorem relationVector_mem (p : quadraticZigzagRelationsBasisIndex G c) :
    relationVector k G c p ∈ quadraticZigzagRelations k G := by
  classical
  rw [relationVector_eq, quadraticZigzagRelations_eq_span]
  obtain ⟨⟨a, b, p⟩, hp, hchosen⟩ := p
  by_cases hab : a = b
  · subst b
    obtain ⟨i, rfl⟩ := exists_eq_vertex G a
    simp only [vertexEquiv_symm_vertex]
    exact Submodule.subset_span (IsQuadraticZigzagRelator.equal_backtracks _ _ hp (by
      simp))
  · simp only [ite_eq_right hab, sub_zero]
    exact Submodule.subset_span (IsQuadraticZigzagRelator.nonreturn p hp hab)

private noncomputable def relationCoordinates :
    pathAlgebra k (DoubledQuiver G) →ₗ[k] quadraticZigzagRelationsBasisIndex G c →₀ k :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    (pathAlgebraBasis k (DoubledQuiver G)).repr.toLinearMap

private theorem relationCoordinates_apply (f : pathAlgebra k (DoubledQuiver G))
    (p : quadraticZigzagRelationsBasisIndex G c) :
    relationCoordinates k G c f p = (pathAlgebraBasis k (DoubledQuiver G)).repr f p.val := by
  simp [relationCoordinates, Finsupp.comapDomain_apply]

private theorem relationCoordinates_vector (p : quadraticZigzagRelationsBasisIndex G c) :
    relationCoordinates k G c (relationVector k G c p) = Finsupp.single p 1 := by
  classical
  ext q
  rw [relationCoordinates_apply, relationVector_eq, map_sub, Finsupp.sub_apply]
  rw [ofPath_eq_single, pathAlgebraBasis_repr_single]
  have hpivot : (pathAlgebraBasis k (DoubledQuiver G)).repr
      (ofPath (chosenBacktrack G c ((vertexEquiv G).symm p.val.1))) q.val = 0 := by
    rw [ofPath_eq_single, pathAlgebraBasis_repr_single]
    exact Finsupp.single_eq_of_ne (q.property.2 _)
  split_ifs <;> simp_all [Finsupp.single_apply, Subtype.ext_iff]

private theorem relationVector_linearIndependent :
    LinearIndependent k (relationVector k G c) := by
  apply LinearIndependent.of_comp (relationCoordinates k G c)
  convert (Finsupp.basisSingleOne : Module.Basis (quadraticZigzagRelationsBasisIndex G c) k
    (quadraticZigzagRelationsBasisIndex G c →₀ k)).linearIndependent using 1
  funext p
  exact relationCoordinates_vector k G c p

private theorem nonreturn_mem_span {a b : DoubledQuiver G} (p : _root_.Quiver.Path a b)
    (hp : p.length = 2) (hab : a ≠ b) :
    ofPath (⟨a, b, p⟩ : Quiver.TotalPath (DoubledQuiver G)) ∈
      Submodule.span k (Set.range (relationVector k G c)) := by
  classical
  have hchosen : ∀ i : V, (⟨a, b, p⟩ : Quiver.TotalPath (DoubledQuiver G)) ≠
      chosenBacktrack G c i := by
    intro i hi
    have ha := congrArg Sigma.fst hi
    have hb := congrArg (fun x : Quiver.TotalPath (DoubledQuiver G) => x.2.1) hi
    exact hab (ha.trans hb.symm)
  let x : quadraticZigzagRelationsBasisIndex G c := ⟨⟨a, b, p⟩, hp, hchosen⟩
  have hx := Submodule.subset_span (R := k) (Set.mem_range_self (f := relationVector k G c) x)
  simpa only [relationVector_eq, x, ite_eq_right hab, sub_zero, SetLike.mem_coe] using hx

private theorem backtrack_sub_chosen_mem_span {i : V}
    (p : _root_.Quiver.Path (vertex G i) (vertex G i)) (hp : p.length = 2) :
    ofPath (⟨vertex G i, vertex G i, p⟩ : Quiver.TotalPath (DoubledQuiver G)) -
      ofPath (chosenBacktrack G c i) ∈ Submodule.span k (Set.range (relationVector k G c)) := by
  classical
  by_cases hchosen : (⟨vertex G i, vertex G i, p⟩ : Quiver.TotalPath (DoubledQuiver G)) =
      chosenBacktrack G c i
  · simp [hchosen]
  · have hall : ∀ j : V, (⟨vertex G i, vertex G i, p⟩ : Quiver.TotalPath (DoubledQuiver G)) ≠
        chosenBacktrack G c j := by
      intro j heq
      have hij : i = j := (vertex_inj G).1 (congrArg Sigma.fst heq)
      subst j
      exact hchosen heq
    let x : quadraticZigzagRelationsBasisIndex G c := ⟨⟨vertex G i, vertex G i, p⟩, hp, hall⟩
    have hx := Submodule.subset_span (R := k) (Set.mem_range_self (f := relationVector k G c) x)
    simpa only [relationVector_eq, x, ↓reduceIte, vertexEquiv_symm_vertex, SetLike.mem_coe] using hx

private theorem span_relationVector :
    Submodule.span k (Set.range (relationVector k G c)) = quadraticZigzagRelations k G := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨p, rfl⟩
    exact relationVector_mem k G c p
  · rw [quadraticZigzagRelations_eq_span, Submodule.span_le]
    rintro _ (⟨p, hp, hab⟩ | ⟨p, q, hp, hq⟩)
    · exact nonreturn_mem_span k G c p hp hab
    · rename_i a
      obtain ⟨i, rfl⟩ := exists_eq_vertex G a
      have h := Submodule.sub_mem _ (backtrack_sub_chosen_mem_span k G c p hp)
        (backtrack_sub_chosen_mem_span k G c q hq)
      simpa only [sub_sub_sub_cancel_right, SetLike.mem_coe] using h

/-- The independent quadratic zigzag relation basis: every nonreturning length-two path, and
one backtrack difference per neighbor other than the chosen neighbor. This is valid over any
commutative ring, including characteristic two. The neighbor choice is explicit data. -/
noncomputable def quadraticZigzagRelationsBasis :
    Module.Basis (quadraticZigzagRelationsBasisIndex G c) k (quadraticZigzagRelations k G) :=
  (Module.Basis.span (relationVector_linearIndependent k G c)).map
    (LinearEquiv.ofEq _ _ (span_relationVector k G c))

/-- A basis vector is its path monomial, minus the chosen backtrack if the path returns. -/
theorem coe_quadraticZigzagRelationsBasis_apply [DecidableEq (DoubledQuiver G)]
    (p : quadraticZigzagRelationsBasisIndex G c) :
    (quadraticZigzagRelationsBasis k G c p : pathAlgebra k (DoubledQuiver G)) =
      ofPath p.val - if p.val.1 = p.val.2.1 then
        backtrackElem G k ((G.mem_neighborSet ((vertexEquiv G).symm p.val.1) _).1
          (c ((vertexEquiv G).symm p.val.1)).property) else 0 := by
  classical
  rw [quadraticZigzagRelationsBasis, Module.Basis.map_apply]
  simp only [LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply,
    relationVector_eq, chosenBacktrack, backtrackElem_eq_ofPath]

/-- On a nonreturning path, the relation basis vector is the path monomial. -/
@[simp]
theorem coe_quadraticZigzagRelationsBasis_apply_of_ne
    (p : quadraticZigzagRelationsBasisIndex G c) (h : p.val.1 ≠ p.val.2.1) :
    (quadraticZigzagRelationsBasis k G c p : pathAlgebra k (DoubledQuiver G)) =
      ofPath p.val := by
  classical
  rw [coe_quadraticZigzagRelationsBasis_apply, ite_eq_right h, sub_zero]

/-- On a returning path, the relation basis vector subtracts the chosen backtrack. -/
@[simp]
theorem coe_quadraticZigzagRelationsBasis_apply_of_eq
    (p : quadraticZigzagRelationsBasisIndex G c) (h : p.val.1 = p.val.2.1) :
    (quadraticZigzagRelationsBasis k G c p : pathAlgebra k (DoubledQuiver G)) =
      ofPath p.val - backtrackElem G k
        ((G.mem_neighborSet ((vertexEquiv G).symm p.val.1) _).1
          (c ((vertexEquiv G).symm p.val.1)).property) := by
  classical
  rw [coe_quadraticZigzagRelationsBasis_apply, ite_eq_left h]

/-- Relation coordinates are the original path coordinates on all paths except the chosen
backtracks. The omitted coordinates are recovered automatically by the backtrack differences. -/
@[simp]
theorem quadraticZigzagRelationsBasis_repr (f : quadraticZigzagRelations k G)
    (p : quadraticZigzagRelationsBasisIndex G c) :
    (quadraticZigzagRelationsBasis k G c).repr f p =
      (pathAlgebraBasis k (DoubledQuiver G)).repr f.val p.val := by
  classical
  have hmap : (relationCoordinates k G c).comp (quadraticZigzagRelations k G).subtype =
      (quadraticZigzagRelationsBasis k G c).repr.toLinearMap := by
    apply (quadraticZigzagRelationsBasis k G c).ext
    intro q
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    have hq : (quadraticZigzagRelationsBasis k G c q : pathAlgebra k (DoubledQuiver G)) =
        relationVector k G c q := by
      rw [coe_quadraticZigzagRelationsBasis_apply, relationVector_eq,
        chosenBacktrack, backtrackElem_eq_ofPath]
    rw [hq, relationCoordinates_vector]
    simp
  have h := congrArg (fun m => m f p) hmap
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, relationCoordinates_apply,
    LinearEquiv.coe_coe] using h.symm

end TauCeti
