/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.FixedNode
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
import TauCeti.Combinatorics.SimpleGraph.Acyclic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# Orthogonality of simple orbits of a based automorphism

Let `σ` be a based automorphism of an irreducible finite reduced crystallographic root system with
base `b`, meaning that `σ` permutes the simple roots. Stembridge's construction of the folded root
system of `σ` requires the simple roots in each `σ`-orbit to be pairwise orthogonal. This file
shows that this condition fails in exactly one family: either every orbit of simple roots is
orthogonal, or the root system has type `A₂ₙ` with `n ≥ 1` and `σ` reverses the chain of its
Bourbaki-numbered simple roots, whose middle pair is then a nonorthogonal orbit.

The Dynkin diagram of `b` is a tree on which `σ` acts by graph automorphisms. If `σ` fixes a simple
root, it preserves the distance to it in the tree, while two adjacent vertices of a tree lie at
different distances from it; so no two simple roots in one orbit are adjacent, that is,
nonorthogonal. By the classification, every symmetry of a numbered Dynkin diagram fixes a node
except the reversal of `A₂ₙ` (`TauCeti.DynkinType.exists_apply_eq_self_of_mem_diagramSymmetry`,
`TauCeti.DynkinType.mem_diagramSymmetry_A_iff`).

No simple-lacing hypothesis is needed: for a nonsimply-laced root system `σ` is the identity
(`RootPairing.Base.eq_one_of_forall_mem_support_of_not_isSimplyLaced`), and its orbits are
singletons.

## Main results

* `RootPairing.Base.pairing_eq_zero_of_mem_orbitIndices`: if a based automorphism fixes a simple
  root, then any two distinct simple roots in one of its orbits are orthogonal.
* `RootPairing.Base.simpleOrbit_pairing_eq_zero_or_typeA_even`: the orbits of simple roots of a
  based automorphism are orthogonal, or the root system has type `A₂ₙ` and the automorphism reverses
  a simultaneous numbering of its simple roots.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, condition (1).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §4 and plates I–IX.
-/

public section

namespace RootPairing.Base

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

variable [Finite ι] [IsDomain R] [CharZero R] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]

/-- **A based automorphism fixing a simple root has orthogonal simple orbits.** Its powers act on
the Dynkin diagram, a tree, by automorphisms fixing that root, and such an automorphism moves no
vertex to a neighbour. -/
theorem pairing_eq_zero_of_mem_orbitIndices (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {v : ι} (hv : v ∈ b.support)
    (hσv : σ.indexEquiv v = v) {i j : ι} (hi : i ∈ b.support) (hj : j ∈ P.orbitIndices σ i)
    (hij : i ≠ j) : P.pairing i j = 0 := by
  have : Nonempty ι := ⟨v⟩
  obtain ⟨k, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
  set φ := Equiv.Perm.subtypePermOfFintype σ.indexEquiv hσ
  have hφ : φ ^ k ∈ matrixSymmetryGroup b.cartanMatrix :=
    pow_mem (b.subtypePerm_mem_matrixSymmetryGroup σ _) k
  have hφv : (φ ^ k) ⟨v, hv⟩ = ⟨v, hv⟩ := by
    ext
    simp [φ, Equiv.Perm.subtypePerm_pow, Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσv]
  have hφi : ((φ ^ k) ⟨i, hi⟩ : ι) = (σ.indexEquiv ^ k) i := by
    simp [φ, Equiv.Perm.subtypePerm_pow]
  have hnadj := (isTree_diagramGraph_cartanMatrix b).not_adj_apply_of_apply_eq_self
    ⟨φ ^ k, diagramGraph_adj_apply_iff (congrFun₂ (mem_matrixSymmetryGroup_iff.mp hφ))⟩ hφv ⟨i, hi⟩
  simp only [RelIso.coe_fn_mk, diagramGraph_adj, not_and, not_not] at hnadj
  rw [← hφi]
  refine (b.cartanMatrix_apply_eq_zero_iff_pairing (i := ⟨i, hi⟩)).mp ?_
  by_contra h
  exact h (b.cartanMatrix_apply_eq_zero_iff_symm.mpr
    (hnadj (fun he ↦ hij (hφi ▸ congrArg Subtype.val he)) h))

/-- **The simple orbits of a based automorphism are orthogonal, except for the reversal of
`A₂ₙ`.** Let `σ` be an automorphism of an irreducible finite reduced crystallographic root system
over a characteristic-zero domain, mapping the simple roots of a base `b` to simple roots. Then
either any two distinct simple roots in one `σ`-orbit are orthogonal, or there is `n ≥ 1` and a
numbering of the simple roots identifying the Cartan matrix of `b` with that of `A₂ₙ`, along which
`σ` reverses the chain. In the second case the two middle simple roots form the only nonorthogonal
orbit (`TauCeti.diagramGraph_A_adj_graphPermA_iff`). -/
theorem simpleOrbit_pairing_eq_zero_or_typeA_even (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) :
    (∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) ∨
      ∃ n, 0 < n ∧ ∃ e : b.support ≃ Fin (2 * n),
        (∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        ∀ i : b.support, e ⟨σ.indexEquiv i, hσ i i.2⟩ = (e i).rev := by
  cases isEmpty_or_nonempty ι
  · exact Or.inl fun i ↦ isEmptyElim i
  set φ := Equiv.Perm.subtypePermOfFintype σ.indexEquiv hσ
  -- It suffices to find a fixed simple root outside the exceptional case.
  suffices h : (∃ v, φ v = v) ∨ ∃ n, 0 < n ∧ ∃ e : b.support ≃ Fin (2 * n),
      (∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
      ∀ i : b.support, e (φ i) = (e i).rev by
    rcases h with ⟨v, hv⟩ | ⟨n, hn, e, he, hrev⟩
    · refine Or.inl fun i hi j hj hij ↦ pairing_eq_zero_of_mem_orbitIndices b hσ v.2 ?_ hi hj hij
      simpa [φ] using congrArg Subtype.val hv
    · exact Or.inr ⟨n, hn, e, he, hrev⟩
  -- Transport `φ` along a numbering of the simple roots to a symmetry of the numbered diagram.
  obtain ⟨t, ⟨ht, hb⟩, -⟩ := existsUnique_dynkinType b
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp hb
  have hρ : e.symm.trans (φ.trans e) ∈ t.diagramSymmetry :=
    DynkinType.mem_diagramSymmetry_of_mem_matrixSymmetryGroup he
      (b.subtypePerm_mem_matrixSymmetryGroup σ _)
  have hfix {x : Fin t.rank} (hx : e.symm.trans (φ.trans e) x = x) : ∃ v, φ v = v :=
    ⟨e.symm x, e.injective (by simpa using hx)⟩
  by_cases hA : ∃ n, t = DynkinType.A (2 * n)
  swap
  · obtain ⟨x, hx⟩ := DynkinType.exists_apply_eq_self_of_mem_diagramSymmetry ht
      (fun n h ↦ hA ⟨n, h⟩) hρ
    exact Or.inl (hfix hx)
  obtain ⟨n, rfl⟩ := hA
  have hn : 0 < n := by have := DynkinType.valid_A.mp ht; omega
  rcases DynkinType.mem_diagramSymmetry_A_iff.mp hρ with h1 | hrev
  · exact Or.inl (hfix (x := ⟨0, by simp only [DynkinType.rank_A]; omega⟩)
      (by rw [h1]; exact Equiv.Perm.one_apply _))
  have hrev' (i : b.support) : e (φ i) = graphPermA _ (e i) := by
    have h := congrArg (· (e i)) hrev
    have h' : (φ.trans e) (e.symm (e i)) = e (φ i) := by
      rw [e.symm_apply_apply, Equiv.trans_apply]
    exact h'.symm.trans h
  exact Or.inr ⟨n, hn, e, he, fun i ↦ (hrev' i).trans (graphPermA_apply _ _)⟩

end RootPairing.Base
