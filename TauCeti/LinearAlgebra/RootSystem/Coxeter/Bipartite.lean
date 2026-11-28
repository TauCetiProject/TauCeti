/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

/-!
# The two-colouring of the Dynkin diagram of a Weyl group

The Coxeter matrix of a base `b` of a finite crystallographic root pairing has entry `2` at a pair
of simple roots exactly when they are orthogonal, that is, when their Cartan entries vanish. Its
Coxeter graph is therefore the Dynkin diagram of `b` with edge multiplicities forgotten
(`RootPairing.graph_coxeterMatrixOfBase`). For a root system this diagram is a forest, because the
Cartan matrix is of finite type, so it admits a two-colouring by `Bool`; for an irreducible
reduced root system it is a tree, so the two-colouring is unique up to exchanging the colours.

Consequently the bipartite Coxeter element `CoxeterSystem.bipartiteCoxeterElement` of the Coxeter
system `TauCeti.weylCoxeterSystem` of the Weyl group is available for every colouring of the
Dynkin diagram, and for an irreducible reduced root system the bipartite Coxeter elements of the
two colourings are mutually inverse and conjugate
(`CoxeterSystem.isConj_bipartiteCoxeterElement` with
`RootPairing.preconnected_graph_coxeterMatrixOfBase`).

## Main results

* `RootPairing.graph_coxeterMatrixOfBase`: the Coxeter graph of a base is its Dynkin diagram.
* `RootPairing.isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType`,
  `RootPairing.nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType`,
  `RootPairing.isAcyclic_graph_coxeterMatrixOfBase`, and
  `RootPairing.nonempty_coloring_graph_coxeterMatrixOfBase`: when the Cartan matrix is of finite
  type (in particular, for a root system), the Coxeter graph is a forest and has a two-colouring.
* `RootPairing.preconnected_graph_coxeterMatrixOfBase`: for an irreducible reduced root pairing it
  is connected.
* `RootPairing.Base.cartanMatrix_eq_zero_of_color_eq`: distinct simple roots of the same colour
  in a two-colouring of the Coxeter graph have vanishing Cartan entry.
* `RootPairing.colorClassProd_smul`: the product of the simple reflections of one colour subtracts
  from a vector its components along the simple roots of that colour.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Ch. VI, §4.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  (b : P.Base)

/-- **The Coxeter graph of a base is its Dynkin diagram**: two distinct simple roots are joined
exactly when both of their Cartan entries are nonzero. -/
theorem graph_coxeterMatrixOfBase :
    (coxeterMatrixOfBase P b).graph = diagramGraph b.cartanMatrix := by
  ext i j
  simp only [CoxeterMatrix.graph_adj, diagramGraph_adj, ne_eq, coxeterMatrixOfBase_eq_two_iff,
    ← cartanMatrix_mul_cartanMatrix_eq_zero_iff_isOrthogonal, mul_eq_zero, not_or]

/-- **The Coxeter graph of a base with finite-type Cartan matrix is a forest.** -/
theorem isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType (hft : IsFiniteType b.cartanMatrix) :
    (coxeterMatrixOfBase P b).graph.IsAcyclic :=
  graph_coxeterMatrixOfBase P b ▸ hft.isAcyclic_diagramGraph

/-- **The Coxeter graph of a base with finite-type Cartan matrix has a two-colouring**: its simple
roots can be coloured by `Bool` so that simple roots of the same colour are orthogonal. -/
theorem nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType
    (hft : IsFiniteType b.cartanMatrix) :
    Nonempty ((coxeterMatrixOfBase P b).graph.Coloring Bool) :=
  Nonempty.map ((coxeterMatrixOfBase P b).graph.recolorOfEquiv finTwoEquiv)
    (isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b hft).isBipartite

/-- **The Coxeter graph of a base of a root system is a forest.** -/
theorem isAcyclic_graph_coxeterMatrixOfBase [P.IsRootSystem] :
    (coxeterMatrixOfBase P b).graph.IsAcyclic :=
  isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b (isFiniteType_cartanMatrix b)

/-- **The Dynkin diagram of a root system has a two-colouring**: its simple roots can be coloured
by `Bool` so that simple roots of the same colour are orthogonal. -/
theorem nonempty_coloring_graph_coxeterMatrixOfBase [P.IsRootSystem] :
    Nonempty ((coxeterMatrixOfBase P b).graph.Coloring Bool) :=
  nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType P b (isFiniteType_cartanMatrix b)

/-- **The Coxeter graph of a base of an irreducible reduced root pairing is connected**, so its
two-colourings agree up to exchanging the colours. -/
theorem preconnected_graph_coxeterMatrixOfBase [P.IsReduced] [P.IsIrreducible] :
    (coxeterMatrixOfBase P b).graph.Preconnected :=
  graph_coxeterMatrixOfBase P b ▸ preconnected_diagramGraph_cartanMatrix b

/-- Distinct simple roots of the same colour in a two-colouring of the Coxeter graph are
orthogonal. -/
theorem Base.cartanMatrix_eq_zero_of_color_eq {P : RootPairing ι R M N} [P.IsCrystallographic]
    (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {p q : b.support}
    (hpq : p ≠ q) (hc : col p = col q) : b.cartanMatrix p q = 0 :=
  by_contra fun hne ↦ col.valid ((graph_coxeterMatrixOfBase P b).symm ▸ (diagramGraph_adj ..).mpr
    ⟨hpq, hne, fun hqp ↦ hne (b.cartanMatrix_apply_eq_zero_iff_symm.mpr hqp)⟩) hc

/-! ### The action of a colour class -/

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] in
/-- A product of pairwise orthogonal simple reflections subtracts from `m` its components along
their simple roots. -/
theorem noncommProd_ofIdx_smul (s : Finset b.support) (f : b.support → P.weylGroup)
    (hf : ∀ i, f i = weylGroup.ofIdx P (i : ι))
    (hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P.pairing i j = 0) (comm) (m : M) :
    s.noncommProd f comm • m = m - ∑ j ∈ s, P.coroot' j m • P.root j := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, mul_smul,
      ih (fun i hi j hj ↦ hs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)), hf,
      weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply, Finset.sum_insert ha]
    have h0 : P.coroot' a (∑ j ∈ s, P.coroot' j m • P.root j) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [map_smul, root_coroot'_eq_pairing, hs j (Finset.mem_insert_of_mem hj) a
        (Finset.mem_insert_self a s) (by rintro rfl; exact ha hj), smul_zero]
    rw [map_sub, h0, sub_zero]
    abel

/-- Distinct simple roots of the same colour are orthogonal. -/
theorem pairingIn_eq_zero_of_color_eq (c : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {i j : b.support} (hij : i ≠ j) (h : c i = c j) : P.pairingIn ℤ i j = 0 :=
  (b.cartanMatrixIn_def ℤ i j).symm ▸ b.cartanMatrix_eq_zero_of_color_eq c hij h

/-- The product of the simple reflections of colour `x` subtracts from `m` its components along
the simple roots of colour `x`. -/
theorem colorClassProd_smul [P.IsReduced] (c : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (x : Bool) (m : M) :
    (weylCoxeterSystem P b).colorClassProd c x • m =
      m - ∑ j, (if c j = x then P.coroot' j m else 0) • P.root j := by
  classical
  rw [CoxeterSystem.colorClassProd_def,
    noncommProd_ofIdx_smul P b _ _ (weylCoxeterSystem_simple P b)]
  · simp_rw [Finset.sum_filter, ite_smul, zero_smul]
  · intro i hi j hj hij
    rw [← P.algebraMap_pairingIn ℤ, pairingIn_eq_zero_of_color_eq P b c hij
      ((Finset.mem_filter.1 hi).2.trans (Finset.mem_filter.1 hj).2.symm), map_zero]

end RootPairing
