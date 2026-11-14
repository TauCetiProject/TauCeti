/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.SimpleGraph.Paths
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Connected

/-!
# Cyclic classes of preprojective algebras from closed trails and cycles

Let `G` be a finite simple graph and `p` a closed trail in `G` at a vertex `u`. Because `p` visits
every edge of `G` at most once, it never traverses both a dart and its reverse
(`SimpleGraph.Walk.IsTrail.symm_notMem_darts`). Sending each vertex `v` to the matrix unit `E_vv`
and each arrow `i → j` of the doubled quiver to `E_ji` when `(i, j)` is a dart of `p`, and to `0`
otherwise, therefore defines an algebra homomorphism from the doubled path algebra to `Matrix V V k`
in which every length-two backtrack `i → j → i` acts as zero.

Consequently, this indicator representation factors simultaneously through the signless
preprojective algebra `Π⁺(G)` and, after identifying the doubled quiver with the symmetrification of
any orientation `o` of `G`, through the additive preprojective algebra `Π_k(OrientedQuiver G o)`
(including when `G` has odd cycles and is not bipartite). Along `p` itself, the doubled-quiver path
acts by `E_uu`, whose trace is `1`. Over every nontrivial commutative ring, a closed trail of length
`d` therefore yields a nonzero cyclic class in path degree `d` in both `Π⁺(G)` and
`Π_k(OrientedQuiver G o)`.

In particular, every finite simple graph which is not acyclic contains a cycle of length at least
three, hence has a nonzero cyclic class in some path degree `d ≥ 3` over every nontrivial
commutative ring, in both its signless preprojective algebra and the preprojective algebra of every
orientation.

## Main results

* `TauCeti.signlessPreprojectiveMk_walkToPath_notMem_commutatorSubmodule_of_isTrail`: the class of a
  closed trail in `Π⁺(G)` lies outside the commutator submodule over any nontrivial commutative
  ring.
* `TauCeti.exists_mem_preprojectiveGrade_length_notMem_commutatorSubmodule_of_isTrail`: every closed
  trail gives a homogeneous element of its length in `Π_k(OrientedQuiver G o)` outside the
  commutator submodule.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: **every
  finite non-acyclic graph has a nonzero cyclic class of path degree at least three** in both
  `Π⁺(G)` and `Π_k(OrientedQuiver G o)`.

## References

* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 229
  (2012), https://arxiv.org/abs/0704.3278, for cyclic classes attached to cycles in extended `A`
  quivers.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for trace functionals vanishing on commutators.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u w

section Representation

variable (k : Type w) [CommRing k] {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {u₀ v₀ : V} (p : G.Walk u₀ v₀)

private def trailVertex (v : DoubledQuiver G) : Matrix V V k :=
  Matrix.single ((vertexEquiv G).symm v) ((vertexEquiv G).symm v) 1

open scoped Classical in
private noncomputable def trailArrow {i j : DoubledQuiver G} (e : i ⟶ j) : Matrix V V k :=
  if (⟨((vertexEquiv G).symm i, (vertexEquiv G).symm j), e.down⟩ : G.Dart) ∈ p.darts then
    Matrix.single ((vertexEquiv G).symm j) ((vertexEquiv G).symm i) 1
  else 0

private theorem completeOrthogonalIdempotents_trailVertex :
    CompleteOrthogonalIdempotents (trailVertex k (G := G)) := by
  unfold trailVertex
  simpa only [Function.comp_def, Matrix.diagonalRingHom_apply, Matrix.diagonal_single] using
    (CompleteOrthogonalIdempotents.equiv (vertexEquiv G).symm).mpr
      ((CompleteOrthogonalIdempotents.single (fun _ : V => k)).map (Matrix.diagonalRingHom V k))

private theorem trailVertex_mul_trailArrow {i j : DoubledQuiver G} (e : i ⟶ j) :
    trailVertex k j * trailArrow k p e = trailArrow k p e := by
  classical
  simp only [trailVertex, trailArrow]
  split_ifs <;> simp

private theorem trailArrow_mul_trailVertex {i j : DoubledQuiver G} (e : i ⟶ j) :
    trailArrow k p e * trailVertex k i = trailArrow k p e := by
  classical
  simp only [trailVertex, trailArrow]
  split_ifs <;> simp

private noncomputable def trailPathAlgHom :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] Matrix V V k :=
  liftAlgHomOfArrows k (trailVertex k) (completeOrthogonalIdempotents_trailVertex k)
    (trailArrow k p) (trailVertex_mul_trailArrow k p) (trailArrow_mul_trailVertex k p)

private theorem trailPathAlgHom_ofArrow {i j : DoubledQuiver G} (e : i ⟶ j) :
    trailPathAlgHom k p (ofArrow e) = trailArrow k p e := by
  rw [trailPathAlgHom, ofArrow_eq_ofPath, liftAlgHomOfArrows_ofPath_toPath]

private theorem trailPathAlgHom_ofArrow_mul_reverse (hp : p.IsTrail)
    {i j : DoubledQuiver G} (e : i ⟶ j) :
    trailPathAlgHom k p (ofArrow e) * trailPathAlgHom k p (ofArrow (Quiver.reverse e)) = 0 := by
  classical
  rw [trailPathAlgHom_ofArrow, trailPathAlgHom_ofArrow]
  simp only [trailArrow]
  set d : G.Dart := ⟨((vertexEquiv G).symm i, (vertexEquiv G).symm j), e.down⟩
  have hrev : (⟨((vertexEquiv G).symm j, (vertexEquiv G).symm i),
      (Quiver.reverse e).down⟩ : G.Dart) = d.symm := by
    ext <;> rfl
  rw [hrev]
  by_cases hd : d ∈ p.darts
  · rw [ite_eq_left hd, ite_eq_right (hp.symm_notMem_darts hd), mul_zero]
  · rw [ite_eq_right hd, zero_mul]

private theorem trailPathAlgHom_walkToPath {a b : V} (q : G.Walk a b)
    (hq : ∀ d ∈ q.darts, d ∈ p.darts) :
    trailPathAlgHom k p (ofPath ⟨vertex G a, vertex G b, walkToPath G q⟩) =
      Matrix.single b a 1 := by
  classical
  induction q with
  | nil =>
      rw [walkToPath_nil, ← vertexIdempotent_eq_ofPath, trailPathAlgHom,
        liftAlgHomOfArrows_vertexIdempotent, trailVertex, vertexEquiv_symm_vertex]
  | @cons a c b h q ih =>
      rw [walkToPath_cons, ← ofPath_mul_ofPath_of_comp, ← ofArrow_eq_ofPath, map_mul,
        ih fun d hd => hq d (List.mem_cons_of_mem _ hd), trailPathAlgHom_ofArrow]
      have hd : (⟨(a, c), h⟩ : G.Dart) ∈ p.darts := hq _ List.mem_cons_self
      simp only [trailArrow, vertexEquiv_symm_vertex, hd, ↓reduceIte,
        Matrix.single_mul_single_same, mul_one]

private noncomputable def signlessTrailRepresentation
    [∀ i, Fintype (G.neighborSet i)] (hp : p.IsTrail) :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k] Matrix V V k :=
  signlessPreprojectiveLift (trailPathAlgHom k p) fun v => by
    rw [signlessPreprojectiveRelator_def, map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← ofPath_mul_ofPath_of_comp, ← ofArrow_eq_ofPath, ← ofArrow_eq_ofPath, map_mul]
    simpa only [Quiver.reverse_reverse] using
      trailPathAlgHom_ofArrow_mul_reverse k p hp (Quiver.reverse x.2)

private noncomputable def preprojectiveTrailRepresentation
    (o : Orientation G) (hp : p.IsTrail) :
    preprojectiveAlgebra k (OrientedQuiver G o) →ₐ[k] Matrix V V k :=
  preprojectiveLiftOfForallLocalPreprojectiveRelator
    ((trailPathAlgHom k p).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom) fun v => by
      rw [localPreprojectiveRelator_eq_sum_ofArrow_mul, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_eq_zero fun b _ => ?_
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_mul, map_smul,
        mul_smul_comm, orientationPathAlgebraEquiv_symm_apply, mapAlgHom_ofArrow,
        Prefunctor.map_reverse]
      rw [trailPathAlgHom_ofArrow_mul_reverse k p hp, smul_zero]

end Representation

section TrailAndCycle

variable (k : Type w) [CommRing k] [Nontrivial k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- **The path class of a closed trail in `Π⁺(G)` is not a sum of commutators** over any nontrivial
commutative ring. -/
theorem signlessPreprojectiveMk_walkToPath_notMem_commutatorSubmodule_of_isTrail
    [∀ i, Fintype (G.neighborSet i)] {u : V} {p : G.Walk u u} (hp : p.IsTrail) :
    signlessPreprojectiveMk k (DoubledQuiver G)
      (ofPath ⟨vertex G u, vertex G u, walkToPath G p⟩) ∉
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  let := Fintype.ofFinite V
  intro hcomm
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule
    (signlessTrailRepresentation k p hp) hcomm
  rw [signlessTrailRepresentation, signlessPreprojectiveLift_signlessPreprojectiveMk,
    trailPathAlgHom_walkToPath k p p (fun _ hd => hd), Matrix.trace_single_eq_same] at htr
  exact one_ne_zero htr

/-- **Every closed trail of length `d` gives a degree-`d` element of `Π_k(OrientedQuiver G o)`
outside the commutator submodule**, for any orientation `o` of `G` and any nontrivial commutative
ring `k`. -/
theorem exists_mem_preprojectiveGrade_length_notMem_commutatorSubmodule_of_isTrail
    (o : Orientation G) {u : V} {p : G.Walk u u} (hp : p.IsTrail) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) p.length,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  let := Fintype.ofFinite V
  let w : pathAlgebra k (DoubledQuiver G) := ofPath ⟨vertex G u, vertex G u, walkToPath G p⟩
  refine ⟨preprojectiveMk k (OrientedQuiver G o) (orientationPathAlgebraEquiv o k w),
    preprojectiveMk_mem_preprojectiveGrade k _ ((orientationPathAlgebraEquiv_mem_grade_iff o k).mpr
      (ofPath_mem_grade_of_length (length_walkToPath G p))), ?_⟩
  · intro hcomm
    have htr := trace_map_eq_zero_of_mem_commutatorSubmodule
      (preprojectiveTrailRepresentation k p o hp) hcomm
    rw [preprojectiveTrailRepresentation,
      preprojectiveLiftOfForallLocalPreprojectiveRelator_preprojectiveMk,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
      trailPathAlgHom_walkToPath k p p (fun _ hd => hd), Matrix.trace_single_eq_same] at htr
    exact one_ne_zero htr

/-- **Every finite non-acyclic graph has a nonzero cyclic class of path degree at least three in its
signless preprojective algebra**, over every nontrivial commutative ring. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    [∀ i, Fintype (G.neighborSet i)] (hc : ¬ G.IsAcyclic) :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨u, p, hp⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp hc
  refine ⟨p.length, hp.three_le_length,
    signlessPreprojectiveMk k _ (ofPath ⟨vertex G u, vertex G u, walkToPath G p⟩),
    signlessPreprojectiveMk_mem_grade k _ (ofPath_mem_grade_of_length (length_walkToPath G p)),
    signlessPreprojectiveMk_walkToPath_notMem_commutatorSubmodule_of_isTrail k hp.isTrail⟩

/-- **Every orientation of a finite non-acyclic graph has a nonzero cyclic class of path degree at
least three in its preprojective algebra**, over every nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (hc : ¬ G.IsAcyclic) (o : Orientation G) :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨u, p, hp⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp hc
  exact ⟨p.length, hp.three_le_length,
    exists_mem_preprojectiveGrade_length_notMem_commutatorSubmodule_of_isTrail k o hp.isTrail⟩

end TrailAndCycle

end TauCeti
