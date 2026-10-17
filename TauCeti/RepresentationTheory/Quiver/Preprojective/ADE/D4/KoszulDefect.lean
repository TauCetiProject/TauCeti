/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.SelfInjective
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.Defect

/-!
# The Koszul defect of the preprojective algebra of `D₄`

For the source--sink orientation of `D₄`, the left Koszul complex at every vertex has its
one-dimensional defect in internal degree four, in the diagonal corner at that vertex.  This is
the sharp form of the almost-Koszul property for `D₄`.

The proof combines the general one-dimensionality theorem for the defect of a finite-dimensional
preprojective algebra with the explicit degree-four socle walks in the `D₄` basis.  These walks
are nonzero by the Frobenius functional, while every arrow kills them because every path of length
five vanishes.

## Main result

* `TauCeti.finrank_preprojectiveCorner_inf_iInf_ker_D4`: the defect is one-dimensional exactly
  in degree four and at the same vertex, and vanishes in every other graded corner.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Section 4.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the Frobenius and socle input.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

attribute [local instance] d4NeighborSetFintype

private def d4SocleWalk : Fin 4 → List (Fin 4)
  | 0 => [0, 1, 2, 1, 0]
  | 1 => [1, 2, 1, 0, 1]
  | 2 => [2, 1, 3, 1, 2]
  | 3 => [3, 1, 0, 1, 3]

private theorem d4SocleWalk_isChain (v : Fin 4) :
    (d4SocleWalk v).IsChain zigzagD4Graph.Adj := by
  fin_cases v <;> decide

private theorem d4SocleWalk_ne_nil (v : Fin 4) : d4SocleWalk v ≠ [] := by
  fin_cases v <;> decide

private theorem d4SocleWalk_length (v : Fin 4) : (d4SocleWalk v).length = 5 := by
  fin_cases v <;> decide

private theorem exists_d4SoclePath (k : Type*) [CommRing k] (v : Fin 4) :
    ∃ p : _root_.Quiver.Path (vertex zigzagD4Graph v) (vertex zigzagD4Graph v),
      signlessPreprojectiveMk k _ (ofPath ⟨_, _, p⟩) =
          signlessWord k zigzagD4Graph (d4SocleWalk v) ∧
        p.length = 4 := by
  have hwalk : v :: (d4SocleWalk v).tail = d4SocleWalk v := by
    rw [← List.cons_head_tail (d4SocleWalk_ne_nil v)]
    congr 1
    fin_cases v <;> rfl
  obtain ⟨a, p, hp, hvertices⟩ := exists_ofPath_eq_signlessWord k v
    (d4SocleWalk v).tail (by
      rw [hwalk]
      exact d4SocleWalk_isChain v)
  rw [hwalk] at hp hvertices
  have hav : a = v := by
    have h := congrArg List.head? hvertices
    rw [_root_.Quiver.Path.vertices_head?] at h
    fin_cases v <;> simpa [d4SocleWalk] using h
  subst a
  refine ⟨p, hp, ?_⟩
  have h := congrArg List.length hvertices
  rw [_root_.Quiver.Path.vertices_length, List.length_map, List.length_reverse,
    d4SocleWalk_length] at h
  omega

section Field

variable (k : Type*) [Field k]

private theorem signlessWord_d4SocleWalk_ne_zero (v : Fin 4) :
    signlessWord k zigzagD4Graph (d4SocleWalk v) ≠ 0 := by
  intro hzero
  have h := congrArg (signlessPreprojectiveD4FrobeniusFunctional k) hzero
  rw [map_zero,
    signlessPreprojectiveD4FrobeniusFunctional_signlessWord k _
      (d4SocleWalk_isChain v) (d4SocleWalk_ne_nil v)] at h
  fin_cases v <;> simp [d4SocleWalk] at h

local notation "Q" => OrientedQuiver zigzagD4Graph zigzagD4Coloring.sourceSink
local notation "Π" => preprojectiveAlgebra k Q
local notation "π" => preprojectiveMk k Q

/-- Decidable equality for the vertices of the source--sink orientation of `D₄`. -/
noncomputable local instance : DecidableEq Q := Classical.decEq Q

private theorem exists_ne_zero_mem_preprojectiveCorner_D4_four (v : Q) :
    ∃ y : Π,
      y ∈ preprojectiveCorner k Q 4 (Symmetrify.of.obj v) (Symmetrify.of.obj v) ∧ y ≠ 0 ∧
        ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
          π (ofArrow (Quiver.reverse b)) * y = 0 := by
  let a : Fin 4 := (OrientedQuiver.vertexEquiv zigzagD4Graph
    zigzagD4Coloring.sourceSink).symm v
  obtain ⟨p, hp, hlength⟩ := exists_d4SoclePath k a
  let φ := unsymmetrifyMap zigzagD4Graph zigzagD4Coloring.sourceSink
  have hobj : (unsymmetrifyMap zigzagD4Graph zigzagD4Coloring.sourceSink).obj
      (vertex zigzagD4Graph a) = Symmetrify.of.obj v := by
    have hva : OrientedQuiver.vertex zigzagD4Graph zigzagD4Coloring.sourceSink a = v := by
      rw [← OrientedQuiver.vertexEquiv_apply]
      exact (OrientedQuiver.vertexEquiv zigzagD4Graph
        zigzagD4Coloring.sourceSink).apply_symm_apply v
    exact (unsymmetrifyMap_obj zigzagD4Graph zigzagD4Coloring.sourceSink a).trans
      (congrArg Symmetrify.of.obj hva)
  rw [← hobj]
  let q := φ.mapPath p
  let y : Π := π (ofPath ⟨φ.obj (vertex zigzagD4Graph a),
    φ.obj (vertex zigzagD4Graph a), q⟩)
  have hq_length : q.length = 4 := by
    simpa only [q] using (φ.length_mapPath p).trans hlength
  have horientation :
      π (orientationPathAlgebraEquiv zigzagD4Coloring.sourceSink k
        (ofPath ⟨vertex zigzagD4Graph a, vertex zigzagD4Graph a, p⟩)) = y := by
    rw [orientationPathAlgebraEquiv_ofPath, Prefunctor.mapTotalPath_mk]
  have hycorner : y ∈
      preprojectiveCorner k Q 4 (φ.obj (vertex zigzagD4Graph a))
        (φ.obj (vertex zigzagD4Graph a)) := by
    refine mem_preprojectiveCorner_iff.2 ⟨?_, ?_⟩
    · exact preprojectiveMk_mem_preprojectiveGrade k Q
        (ofPath_mem_grade_of_length hq_length)
    · dsimp only [y]
      rw [← map_mul, ← map_mul, vertexIdempotent_mul_ofPath,
        ofPath_mul_vertexIdempotent]
  have hy0 : y ≠ 0 := by
    intro hy
    apply signlessWord_d4SocleWalk_ne_zero k a
    rw [← hp]
    apply (zigzagD4SignlessEquivPreprojective k).injective
    rw [zigzagD4SignlessEquivPreprojective_mk, horientation, map_zero]
    exact hy
  refine ⟨y, hycorner, hy0, fun w b => ?_⟩
  dsimp only [y]
  rw [← map_mul, ofArrow_mul_ofPath]
  apply preprojectiveMk_D4_ofPath_eq_zero_of_five_le
  rw [_root_.Quiver.Path.length_cons, hq_length]

/-- **The `D₄` preprojective Koszul defect is the degree-four diagonal line.** At a vertex `v`,
the graded corner of elements killed by every arrow leaving `v` has dimension one for internal
degree four and source vertex `v`, and dimension zero for every other degree and source. -/
theorem finrank_preprojectiveCorner_inf_iInf_ker_D4 (v : Q) (m : ℕ) (i : Q) :
    Module.finrank k ↥(preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v) ⊓
      ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        LinearMap.ker (LinearMap.mulLeft k (π (ofArrow (Quiver.reverse b))))) =
      if m = 4 ∧ i = v then 1 else 0 := by
  obtain ⟨y, hycorner, hy0, hyarrow⟩ :=
    exists_ne_zero_mem_preprojectiveCorner_D4_four k v
  exact finrank_preprojectiveCorner_inf_iInf_ker_eq_of_mem k hycorner hy0 hyarrow m i

end Field

end TauCeti
