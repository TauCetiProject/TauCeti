/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Necklace functionals on signless preprojective algebras

Let `G` be a simple graph. A closed path of the doubled quiver `TauCeti.DoubledQuiver G` is
determined by its vertices, and up to the choice of base point by its *necklace*: the cycle
`Cycle V` of its vertices from the source, the final return to the source omitted. A weight
`W : Cycle V → k` on necklaces therefore defines a linear functional on the path algebra,
`TauCeti.DoubledQuiver.necklaceFunctional`, sending every closed path to the weight of its
necklace and every other path to zero. A product of two paths and the product in the opposite
order have rotated necklaces, so this functional takes the same value on `x * y` and on `y * x`.

By this trace property, the functional kills the signless relation ideal as soon as it kills
each product `s_v * p` of the signless relator `s_v = ∑_{w ∼ v} (v → w → v)` with a closed path
`p` at `v`. In terms of weights this is the condition that, for every closed walk at `v` read as
the list `L` of its vertices from `v` with the final return omitted,

```text
∑_{w ∼ v} W (v w L) = 0.
```

The functional then descends to the signless preprojective algebra `Π⁺(G)`, as
`TauCeti.signlessNecklaceFunctional`, and kills its commutator submodule. A closed path whose
necklace has nonzero weight therefore has nonzero class in the cyclic quotient
`Π⁺(G) / [Π⁺(G), Π⁺(G)]`, the zeroth Hochschild homology.

For a finite Dynkin graph, `Π⁺(G)` is finite-dimensional and its elements of positive path
degree are nilpotent, so they have trace zero in every finite-dimensional representation, and the
matrix representations of
`TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.MatrixRepresentation` cannot detect
cyclic classes in positive degree. Necklace weights can: in a fixed positive degree, the
weights satisfying the relations, taken up to their values on necklaces that are not closed walks
of the graph (which the functional never sees), correspond to the dual of that piece of the cyclic
quotient, and a weight is checked on finitely many closed walks.

## Main definitions

* `TauCeti.DoubledQuiver.necklaceFunctional`: the linear functional on the path algebra of the
  doubled quiver attached to a weight on necklaces.
* `TauCeti.IsSignlessNecklaceWeight`: the signless necklace relations on a weight.
* `TauCeti.signlessNecklaceFunctional`: its descent to the signless preprojective algebra, for a
  weight satisfying the signless necklace relations.

## Main results

* `TauCeti.DoubledQuiver.necklaceFunctional_mul_comm`: the necklace functional is a trace.
* `TauCeti.DoubledQuiver.necklaceFunctional_eq_zero_of_mem_signlessPreprojectiveIdeal`: under
  the signless necklace relations it kills the signless relation ideal.
* `TauCeti.commutatorSubmodule_le_ker_signlessNecklaceFunctional`: the descended functional
  kills the commutator submodule.
* `TauCeti.signlessPreprojectiveMk_ofPath_notMem_commutatorSubmodule`: a closed path whose
  necklace has nonzero weight is not a sum of commutators in `Π⁺(G)`.
* `TauCeti.signlessNecklaceFunctional_signlessWord`: the value on the class of a closed walk of a
  graph on `Fin n`, given by its list of vertices.

## Implementation notes

The descent of the necklace functional through the relation ideal, by induction on the
two-sided span and the trace property, follows the construction of the `D₄` Frobenius functional
`TauCeti.signlessPreprojectiveD4FrobeniusFunctional`.

## References

* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3, for the
  signless relation.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V)

namespace DoubledQuiver

/-! ### Vertices of closed paths of a doubled quiver -/

/-- The vertices of a closed path at `v` of a doubled quiver, the final return to `v` omitted,
form a closed walk of the graph at `v`. -/
private theorem isChain_append_dropLast_vertices {v : V} (p : Path (vertex G v) (vertex G v)) :
    (p.vertices.dropLast.map (vertexEquiv G).symm ++ [v]).IsChain G.Adj := by
  have h := isChain_map_vertices G p
  rwa [← Path.dropLast_append_end_eq, List.map_append, List.map_singleton,
    vertexEquiv_symm_vertex] at h

/-- The vertices of a closed path at `v` of a doubled quiver, the final return omitted, start at
`v` unless the path is trivial. -/
private theorem head?_dropLast_vertices {v : V} (p : Path (vertex G v) (vertex G v)) :
    ∀ a ∈ (p.vertices.dropLast.map (vertexEquiv G).symm).head?, a = v := by
  intro a ha
  rw [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have h := p.vertices_head?
  rw [← Path.dropLast_append_end_eq, List.head?_append, hb, Option.some_or] at h
  rw [Option.some.inj h, vertexEquiv_symm_vertex]

/-! ### The necklace functional on the path algebra -/

section PathAlgebra

variable [CommSemiring k]

open Classical in
/-- The **necklace functional** of a weight `W` on necklaces of vertices: the linear functional
on the path algebra of the doubled quiver sending a closed path to the weight of its necklace,
the cycle of its vertices with the final return omitted, and every other path to zero. -/
noncomputable def necklaceFunctional (W : Cycle V → k) : pathAlgebra k (DoubledQuiver G) →ₗ[k] k :=
  liftLinear k fun x => if x.1 = x.2.1 then
    W ((x.2.2.vertices.dropLast.map (vertexEquiv G).symm : List V) : Cycle V) else 0

variable {k G} (W : Cycle V → k)

/-- The necklace functional on a closed path is the weight of its necklace. -/
@[simp]
theorem necklaceFunctional_ofPath (a : DoubledQuiver G) (p : Path a a) :
    necklaceFunctional k G W (ofPath ⟨a, a, p⟩) =
      W ((p.vertices.dropLast.map (vertexEquiv G).symm : List V) : Cycle V) := by
  rw [necklaceFunctional, liftLinear_ofPath, ite_eq_left rfl]

/-- The necklace functional vanishes on a path which is not closed. -/
@[simp]
theorem necklaceFunctional_ofPath_of_ne {a b : DoubledQuiver G} (p : Path a b) (h : a ≠ b) :
    necklaceFunctional k G W (ofPath ⟨a, b, p⟩) = 0 := by
  rw [necklaceFunctional, liftLinear_ofPath, ite_eq_right h]

private theorem necklaceFunctional_ofPath_mul_ofPath (x y : Quiver.TotalPath (DoubledQuiver G)) :
    necklaceFunctional k G W (ofPath x * ofPath y) =
      necklaceFunctional k G W (ofPath y * ofPath x) := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases hda : d = a
  · subst d
    by_cases hbc : b = c
    · subst c
      rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp, necklaceFunctional_ofPath,
        necklaceFunctional_ofPath, Path.vertices_comp, Path.vertices_comp,
        List.dropLast_append_of_ne_nil q.vertices_ne_nil,
        List.dropLast_append_of_ne_nil p.vertices_ne_nil, List.map_append, List.map_append]
      exact congrArg W (Cycle.coe_eq_coe.mpr List.isRotated_append)
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_not_composable hbc,
        necklaceFunctional_ofPath_of_ne W _ (Ne.symm hbc), map_zero]
  · rw [ofPath_mul_ofPath_of_not_composable hda, map_zero]
    by_cases hbc : b = c
    · subst c
      rw [ofPath_mul_ofPath_of_comp, necklaceFunctional_ofPath_of_ne W _ (Ne.symm hda)]
    · rw [ofPath_mul_ofPath_of_not_composable hbc, map_zero]

/-- **The necklace functional is a trace**: it takes the same value on `x * y` and on `y * x`,
since the necklaces of the two products of paths are rotations of each other. -/
theorem necklaceFunctional_mul_comm (x y : pathAlgebra k (DoubledQuiver G)) :
    necklaceFunctional k G W (x * y) = necklaceFunctional k G W (y * x) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']
  | single p a =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [add_mul, mul_add, map_add, hy, hy']
    | single q b =>
      simp only [single_eq_smul_ofPath, smul_mul_assoc, mul_smul_comm, map_smul,
        necklaceFunctional_ofPath_mul_ofPath, smul_smul, mul_comm]

end PathAlgebra

end DoubledQuiver

/-! ### Descent to the signless preprojective algebra -/

section Signless

variable [CommRing k] [∀ v, Fintype (G.neighborSet v)] {k G} (W : Cycle V → k)

variable (G) in
/-- The **signless necklace relations** for a weight `W` on necklaces: for every closed walk at
`v`, read as the list `L` of its vertices from `v` with the final return to `v` omitted, the
weights of the necklaces `v w L` over the neighbours `w` of `v` sum to zero. These say that the
necklace functional kills the product of the signless relator at `v` with every closed path at
`v`. -/
def IsSignlessNecklaceWeight : Prop :=
  ∀ (v : V) (L : List V), (L ++ [v]).IsChain G.Adj → (∀ a ∈ L.head?, a = v) →
    ∑ w : G.neighborSet v, W ((v :: (w : V) :: L : List V) : Cycle V) = 0

variable (G) in
/-- The signless necklace relations, by their defining condition on closed walks. -/
theorem isSignlessNecklaceWeight_iff : IsSignlessNecklaceWeight G W ↔
    ∀ (v : V) (L : List V), (L ++ [v]).IsChain G.Adj → (∀ a ∈ L.head?, a = v) →
      ∑ w : G.neighborSet v, W ((v :: (w : V) :: L : List V) : Cycle V) = 0 :=
  Iff.rfl

variable {W}

private theorem necklaceFunctional_relator_mul_ofPath (hW : IsSignlessNecklaceWeight G W) (v : V)
    (x : Quiver.TotalPath (DoubledQuiver G)) :
    necklaceFunctional k G W (signlessPreprojectiveRelator k (vertex G v) * ofPath x) = 0 := by
  rw [signlessPreprojectiveRelator_vertex, Finset.sum_mul, map_sum]
  obtain ⟨a, b, p⟩ := x
  by_cases hb : b = vertex G v
  swap
  · exact Finset.sum_eq_zero fun w _ => by
      rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_not_composable hb, map_zero]
  subst b
  by_cases ha : a = vertex G v
  swap
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_comp,
      necklaceFunctional_ofPath_of_ne W _ ha]
  subst a
  -- The product with the backtrack along `w` is the closed path `p` followed by the backtrack,
  -- whose necklace is a rotation of `v w L`.
  have hrot (w : G.neighborSet v) :
      necklaceFunctional k G W (backtrackElem G k ((G.mem_neighborSet v w).1 w.2) *
          ofPath ⟨vertex G v, vertex G v, p⟩) =
        W ((v :: (w : V) :: p.vertices.dropLast.map (vertexEquiv G).symm : List V) :
          Cycle V) := by
    rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_comp, necklaceFunctional_ofPath,
      Path.vertices_comp, backtrackPath_eq_comp, Path.vertices_comp, arrowPath_eq_toPath,
      arrowPath_eq_toPath, Path.vertices_toPath, Path.vertices_toPath]
    simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.cons_append,
      List.nil_append, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _), List.map_append,
      List.map_cons, List.map_nil, vertexEquiv_symm_vertex]
    exact congrArg W (Cycle.coe_eq_coe.mpr (List.isRotated_append (l' := [v, (w : V)])))
  simp_rw [hrot]
  exact (isSignlessNecklaceWeight_iff G W).mp hW v _ (isChain_append_dropLast_vertices G p)
    (head?_dropLast_vertices G p)

variable [Finite V]

/-- **The necklace functional kills the signless relation ideal** when its weight satisfies the
signless necklace relations. -/
theorem DoubledQuiver.necklaceFunctional_eq_zero_of_mem_signlessPreprojectiveIdeal
    (hW : IsSignlessNecklaceWeight G W) {x : pathAlgebra k (DoubledQuiver G)}
    (hx : x ∈ signlessPreprojectiveIdeal k (DoubledQuiver G)) :
    necklaceFunctional k G W x = 0 := by
  rw [signlessPreprojectiveIdeal_eq_span] at hx
  suffices h : ∀ a b, necklaceFunctional k G W (a * x * b) = 0 by simpa using h 1 1
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := exists_eq_vertex G u
    intro a b
    dsimp only
    -- Rotate the relator to the front, then expand the remaining factor in the path basis.
    rw [mul_assoc, necklaceFunctional_mul_comm, mul_assoc,
      signlessPreprojectiveRelator_congr k _ _ (instFintypeStarVertex G v)]
    induction b * a using induction_linear with
    | zero => simp
    | add y z hy hz => rw [mul_add, map_add, hy, hz, add_zero]
    | single p c =>
      rw [single_eq_smul_ofPath, mul_smul_comm, map_smul,
        necklaceFunctional_relator_mul_ofPath hW, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => intro a b; rw [mul_add, add_mul, map_add, hx, hy, add_zero]
  | neg x _ hx => intro a b; rw [mul_neg, neg_mul, map_neg, hx, neg_zero]
  | left_absorb c x _ hx => intro a b; simpa only [mul_assoc] using hx (a * c) b
  | right_absorb c x _ hx => intro a b; simpa only [mul_assoc] using hx a (c * b)

variable (k G W) in
/-- The **signless necklace functional**: for a weight `W` on necklaces satisfying the signless
necklace relations, the necklace functional descends to the signless preprojective algebra. It
sends the class of a closed path to the weight of its necklace, and kills commutators. -/
noncomputable def signlessNecklaceFunctional (hW : IsSignlessNecklaceWeight G W) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₗ[k] k :=
  (signlessPreprojectiveMk k _).toLinearMap.liftOfSurjective
    (signlessPreprojectiveMk_surjective k _)
    ⟨necklaceFunctional k G W, fun _ hx => LinearMap.mem_ker.mpr
      (necklaceFunctional_eq_zero_of_mem_signlessPreprojectiveIdeal hW
        ((signlessPreprojectiveMk_eq_zero_iff k _).mp (LinearMap.mem_ker.mp hx)))⟩

variable (hW : IsSignlessNecklaceWeight G W)

/-- The signless necklace functional on the class of an element of the path algebra is the
necklace functional of that element. -/
@[simp]
theorem signlessNecklaceFunctional_signlessPreprojectiveMk (x : pathAlgebra k (DoubledQuiver G)) :
    signlessNecklaceFunctional k G W hW (signlessPreprojectiveMk k _ x) =
      necklaceFunctional k G W x :=
  LinearMap.equivOfSurjective_apply _ _

/-- **The signless necklace functional is a trace.** -/
theorem signlessNecklaceFunctional_mul_comm
    (x y : signlessPreprojectiveAlgebra k (DoubledQuiver G)) :
    signlessNecklaceFunctional k G W hW (x * y) = signlessNecklaceFunctional k G W hW (y * x) := by
  obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k _ x
  obtain ⟨y, rfl⟩ := signlessPreprojectiveMk_surjective k _ y
  simp only [← map_mul, signlessNecklaceFunctional_signlessPreprojectiveMk,
    necklaceFunctional_mul_comm]

/-- **The signless necklace functional kills the commutator submodule.** -/
theorem commutatorSubmodule_le_ker_signlessNecklaceFunctional :
    commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ≤
      LinearMap.ker (signlessNecklaceFunctional k G W hW) :=
  (commutatorSubmodule_le_ker_iff _).2 (signlessNecklaceFunctional_mul_comm hW)

/-- **A closed path whose necklace has nonzero weight is not a sum of commutators** in the
signless preprojective algebra, for a weight satisfying the signless necklace relations: its
class in the cyclic quotient is nonzero. -/
theorem signlessPreprojectiveMk_ofPath_notMem_commutatorSubmodule
    (hW : IsSignlessNecklaceWeight G W) {a : DoubledQuiver G} (p : Path a a)
    (hp : W ((p.vertices.dropLast.map (vertexEquiv G).symm : List V) : Cycle V) ≠ 0) :
    signlessPreprojectiveMk k _ (ofPath ⟨a, a, p⟩) ∉
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  intro h
  have h₀ := LinearMap.mem_ker.mp (commutatorSubmodule_le_ker_signlessNecklaceFunctional hW h)
  rw [signlessNecklaceFunctional_signlessPreprojectiveMk, necklaceFunctional_ofPath] at h₀
  exact hp h₀

end Signless

/-! ### Closed walks of a graph on `Fin n` -/

section Fin

variable {k} [CommRing k] {n : ℕ} {G : SimpleGraph (Fin n)} [∀ i, Fintype (G.neighborSet i)]
  {W : Cycle (Fin n) → k} (hW : IsSignlessNecklaceWeight G W)

/-- The signless necklace functional on the class `TauCeti.signlessWord` of a closed walk
`i :: r`, listed latest vertex first and returning to `i`, is the weight of the necklace of the
reversed list `r`: the walk visits the vertices of `r` in reverse order after leaving `i`. -/
theorem signlessNecklaceFunctional_signlessWord (i : Fin n) (r : List (Fin n))
    (hw : (i :: r).IsChain G.Adj) (hi : (i :: r).getLast (List.cons_ne_nil i r) = i) :
    signlessNecklaceFunctional k G W hW (signlessWord k G (i :: r)) =
      W (r.reverse : Cycle (Fin n)) := by
  obtain ⟨a, p, hp, hv⟩ := exists_ofPath_eq_signlessWord k i r hw
  -- The earliest vertex of the walk is its last listed vertex, which is `i`.
  have ha : a = i := by
    have hh := p.vertices_head?
    rw [hv, List.head?_map, List.head?_reverse, List.getLast?_eq_getLast_of_ne_nil
      (List.cons_ne_nil i r), hi] at hh
    exact (vertex_injective G (Option.some.inj hh)).symm
  subst a
  rw [← hp, signlessNecklaceFunctional_signlessPreprojectiveMk, necklaceFunctional_ofPath, hv,
    List.reverse_cons, List.map_append, List.map_singleton, List.dropLast_concat, List.map_map]
  simp [Function.comp_def]

end Fin

end TauCeti
