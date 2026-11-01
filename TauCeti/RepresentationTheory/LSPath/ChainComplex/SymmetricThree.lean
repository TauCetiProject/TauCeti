/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.Bruhat
public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Pure
import Mathlib.Tactic.FinCases

/-!
# The four-tetrahedron Bruhat-chain complex for `S₃`

The order complex of Bruhat order on the six actual permutations of three letters has four
maximal tetrahedra: `{1, s, st, sts}`, `{1, s, ts, sts}`, `{1, t, st, sts}`, and
`{1, t, ts, sts}`. This file constructs that complex, characterizes all its faces, and
identifies its maximal faces and their intersections. Changing either middle vertex glues two
tetrahedra along a triangle; changing both leaves the common edge `{1, sts}`.

This is a complex of possible chains of path directions. Its simplex points allow arbitrary
nonnegative real barycentric coordinates; they are not the finite set of LS paths of a fixed
shape, whose rational breaks must also satisfy the chain integrality conditions.

References: Björner–Brenti, *Combinatorics of Coxeter Groups*, §2.2; Littelmann,
*Paths and root operators in representation theory*, Ann. of Math. 142 (1995), §4.
-/

public section

namespace TauCeti

open Finset

/-- The order complex of Bruhat order on the symmetric group on three letters. -/
noncomputable def symmetricThreeBruhatComplex : AbstractSimplicialComplex (Equiv.Perm (Fin 3)) :=
  letI := (permCoxeterSystem 3).bruhatPartialOrder
  AbstractSimplicialComplex.orderComplex (Equiv.Perm (Fin 3))

/-- A face is a nonempty set containing at most one permutation of each Coxeter length. -/
@[simp]
theorem mem_symmetricThreeBruhatComplex_iff {σ : Finset (Equiv.Perm (Fin 3))} :
    σ ∈ symmetricThreeBruhatComplex ↔
      σ.Nonempty ∧ Set.InjOn (permCoxeterSystem 3).length (↑σ : Set (Equiv.Perm (Fin 3))) := by
  classical
  let : PartialOrder (Equiv.Perm (Fin 3)) := (permCoxeterSystem 3).bruhatPartialOrder
  rw [symmetricThreeBruhatComplex, AbstractSimplicialComplex.mem_orderComplex_iff']
  simp only [CoxeterSystem.bruhatPartialOrder_le, Equiv.Perm.bruhatLE_three_iff]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun u hu v hv he ↦ ?_⟩
    rcases h u hu v hv with (heq | hlt) | (heq | hlt)
    · exact heq
    · omega
    · exact heq.symm
    · omega
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun u hu v hv ↦ ?_⟩
    rcases lt_trichotomy ((permCoxeterSystem 3).length u)
      ((permCoxeterSystem 3).length v) with hlt | he | hlt
    · exact Or.inl (Or.inr hlt)
    · exact Or.inl (Or.inl (h hu hv he))
    · exact Or.inr (Or.inr hlt)

/-- A maximal chain chooses one of `s, t` and one of `st, ts`, together with both endpoints. -/
def symmetricThreeBruhatTetrahedron (a b : Fin 2) : Finset (Equiv.Perm (Fin 3)) :=
  {symmetricThreeVertex 0, symmetricThreeVertex (![1, 2] a),
    symmetricThreeVertex (![3, 4] b), symmetricThreeVertex 5}

/-- The vertices of one of the four Bruhat tetrahedra. -/
theorem symmetricThreeBruhatTetrahedron_def (a b : Fin 2) :
    symmetricThreeBruhatTetrahedron a b =
      {symmetricThreeVertex 0, symmetricThreeVertex (![1, 2] a),
        symmetricThreeVertex (![3, 4] b), symmetricThreeVertex 5} := (rfl)

/-- Each maximal Bruhat chain has four distinct vertices. -/
@[simp]
theorem card_symmetricThreeBruhatTetrahedron (a b : Fin 2) :
    (symmetricThreeBruhatTetrahedron a b).card = 4 := by
  fin_cases a <;> fin_cases b <;>
    rw [symmetricThreeBruhatTetrahedron_def] <;> simp only [symmetricThreeVertex_def] <;> decide

/-- Each displayed maximal chain is a face of the Bruhat-chain complex. -/
@[simp↓]
theorem symmetricThreeBruhatTetrahedron_mem (a b : Fin 2) :
    symmetricThreeBruhatTetrahedron a b ∈ symmetricThreeBruhatComplex := by
  classical
  rw [mem_symmetricThreeBruhatComplex_iff]
  refine ⟨card_pos.mp (by simp), ?_⟩
  intro u hu v hv he
  simp only [Finset.mem_coe] at hu hv
  simp only [symmetricThreeBruhatTetrahedron_def, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
      simp only [length_symmetricThreeVertex] at he <;>
        fin_cases a <;> fin_cases b <;> simp_all

private theorem face_subset_tetrahedron {σ : Finset (Equiv.Perm (Fin 3))}
    (hσ : σ ∈ symmetricThreeBruhatComplex) :
    ∃ a b, σ ⊆ symmetricThreeBruhatTetrahedron a b := by
  classical
  obtain ⟨_, hinj⟩ := mem_symmetricThreeBruhatComplex_iff.mp hσ
  have h12 : ¬(symmetricThreeVertex 1 ∈ σ ∧ symmetricThreeVertex 2 ∈ σ) := by
    rintro ⟨h1, h2⟩
    have he := hinj h1 h2 (by simp only [length_symmetricThreeVertex]; decide)
    exact (by decide : (1 : Fin 6) ≠ 2) (bijective_symmetricThreeVertex.injective he)
  have h34 : ¬(symmetricThreeVertex 3 ∈ σ ∧ symmetricThreeVertex 4 ∈ σ) := by
    rintro ⟨h3, h4⟩
    have he := hinj h3 h4 (by simp only [length_symmetricThreeVertex]; decide)
    exact (by decide : (3 : Fin 6) ≠ 4) (bijective_symmetricThreeVertex.injective he)
  by_cases h1 : symmetricThreeVertex 1 ∈ σ <;>
    by_cases h3 : symmetricThreeVertex 3 ∈ σ
  · refine ⟨0, 0, fun u hu ↦ ?_⟩
    obtain ⟨i, rfl⟩ := bijective_symmetricThreeVertex.surjective u
    fin_cases i <;> simp_all [symmetricThreeBruhatTetrahedron_def]
  · refine ⟨0, 1, fun u hu ↦ ?_⟩
    obtain ⟨i, rfl⟩ := bijective_symmetricThreeVertex.surjective u
    fin_cases i <;> simp_all [symmetricThreeBruhatTetrahedron_def]
  · refine ⟨1, 0, fun u hu ↦ ?_⟩
    obtain ⟨i, rfl⟩ := bijective_symmetricThreeVertex.surjective u
    fin_cases i <;> simp_all [symmetricThreeBruhatTetrahedron_def]
  · refine ⟨1, 1, fun u hu ↦ ?_⟩
    obtain ⟨i, rfl⟩ := bijective_symmetricThreeVertex.surjective u
    fin_cases i <;> simp_all [symmetricThreeBruhatTetrahedron_def]

/-- The Bruhat-chain complex consists exactly of the nonempty faces of the four tetrahedra. -/
theorem mem_symmetricThreeBruhatComplex_iff_subset {σ : Finset (Equiv.Perm (Fin 3))} :
    σ ∈ symmetricThreeBruhatComplex ↔
      σ.Nonempty ∧ ∃ a b, σ ⊆ symmetricThreeBruhatTetrahedron a b := by
  constructor
  · intro hσ
    exact ⟨(mem_symmetricThreeBruhatComplex_iff.mp hσ).1, face_subset_tetrahedron hσ⟩
  · rintro ⟨hne, a, b, hsub⟩
    exact (symmetricThreeBruhatComplex.isRelLowerSet_faces
      (symmetricThreeBruhatTetrahedron_mem a b)).2 hsub hne

/-- Every Bruhat-chain face extends to one of the four tetrahedra. -/
theorem isPure_symmetricThreeBruhatComplex :
    PreAbstractSimplicialComplex.IsPure
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex 3 := by
  rw [PreAbstractSimplicialComplex.isPure_iff]
  intro σ hσ
  obtain ⟨a, b, hsub⟩ := face_subset_tetrahedron hσ
  exact ⟨_, symmetricThreeBruhatTetrahedron_mem a b, hsub, card_symmetricThreeBruhatTetrahedron a b⟩

/-- The maximal faces are precisely the four displayed tetrahedra. -/
theorem maximal_symmetricThreeBruhatComplex_iff {σ : Finset (Equiv.Perm (Fin 3))} :
    Maximal (· ∈ symmetricThreeBruhatComplex) σ ↔
      ∃ a b, σ = symmetricThreeBruhatTetrahedron a b := by
  constructor
  · intro hσ
    obtain ⟨a, b, hsub⟩ := face_subset_tetrahedron hσ.prop
    exact ⟨a, b, le_antisymm hsub (hσ.2 (symmetricThreeBruhatTetrahedron_mem a b) hsub)⟩
  · rintro ⟨a, b, rfl⟩
    refine ⟨symmetricThreeBruhatTetrahedron_mem a b, fun τ hτ hsub ↦ ?_⟩
    have hcard := isPure_symmetricThreeBruhatComplex.card_le hτ
    exact (Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)).symm.le

/-- Distinct choices of the two middle vertices give distinct maximal tetrahedra. -/
theorem symmetricThreeBruhatTetrahedron_injective :
    Function.Injective (fun ab : Fin 2 × Fin 2 ↦ symmetricThreeBruhatTetrahedron ab.1 ab.2) := by
  intro ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [symmetricThreeBruhatTetrahedron_def, symmetricThreeVertex_def] <;> decide

/-- Two tetrahedra share both endpoints and exactly those middle vertices on which their
choices agree. Thus one changed choice gives a triangular intersection and two give an edge. -/
theorem symmetricThreeBruhatTetrahedron_inter (a b c d : Fin 2) :
    symmetricThreeBruhatTetrahedron a b ∩ symmetricThreeBruhatTetrahedron c d =
      {symmetricThreeVertex 0, symmetricThreeVertex 5} ∪
        (if a = c then {symmetricThreeVertex (![1, 2] a)} else ∅) ∪
        (if b = d then {symmetricThreeVertex (![3, 4] b)} else ∅) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [symmetricThreeBruhatTetrahedron_def, symmetricThreeVertex_def] <;> decide

end TauCeti
