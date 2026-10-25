/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.PotentialIso

/-!
# Potential isomorphism of countably generated structures

A back-and-forth system between countably generated structures yields an isomorphism, and
indeed every member of the system extends to one. The countable case therefore identifies
potential isomorphism with isomorphism. No relational-language or countability-of-symbols
hypothesis is needed.

The proof adapts `FirstOrder.Language.equiv_between_cg` in
`Mathlib/ModelTheory/PartialEquiv.lean`, by Aaron Anderson, Gabin Kolly, and David Wärn.
Instead of requiring all finitely generated partial equivalences to extend, we apply
`Order.sequenceOfCofinals` to the subtype of a single back-and-forth system. Mathlib's
`DirectLimit.partialEquivLimit` then assembles the resulting increasing chain.
This is the countable back-and-forth argument underlying Carol Karp,
*Finite-quantifier equivalence* (1965).
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- Between countably generated structures, every member of a back-and-forth system of finitely
generated partial equivalences extends to an isomorphism. -/
theorem exists_le_equiv_of_cg {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g) {g : L.FGEquiv M N} (hg : g ∈ S)
    (hM : Structure.CG L M) (hN : Structure.CG L N) :
    ∃ e : M ≃[L] N, g.1 ≤ e.toEmbedding.toPartialEquiv := by
  classical
  obtain ⟨X, hX, hXgen⟩ := Structure.cg_iff.mp hM
  obtain ⟨Y, hY, hYgen⟩ := Structure.cg_iff.mp hN
  have : Countable X := hX.to_subtype
  have : Countable Y := hY.to_subtype
  let : Encodable X := Encodable.ofCountable X
  let : Encodable Y := Encodable.ofCountable Y
  -- Cofinality is relative to S: no extension may leave the chosen system.
  let D : X ⊕ Y → Order.Cofinal S := fun p => p.elim
    (fun x => {
      carrier := {f | x.1 ∈ f.1.1.dom}
      isCofinal := fun f => by
        obtain ⟨k, hk, hx, hfk⟩ := hforth f.1 f.2 x.1
        exact ⟨⟨k, hk⟩, hx, hfk⟩ })
    (fun y => {
      carrier := {f | y.1 ∈ f.1.1.cod}
      isCofinal := fun f => by
        obtain ⟨k, hk, hy, hfk⟩ := hback f.1 f.2 y.1
        exact ⟨⟨k, hk⟩, hy, hfk⟩ })
  let C : ℕ →o M ≃ₚ[L] N :=
    ⟨fun n => (Order.sequenceOfCofinals (⟨g, hg⟩ : S) D n).1.1,
      fun _ _ hij => Order.sequenceOfCofinals.monotone (⟨g, hg⟩ : S) D hij⟩
  let F := DirectLimit.partialEquivLimit C
  have hXdom : X ⊆ F.dom := by
    intro x hx
    have hxmem := Order.sequenceOfCofinals.encode_mem (⟨g, hg⟩ : S) D
      (Sum.inl (⟨x, hx⟩ : X))
    exact PartialEquiv.dom_le_dom (DirectLimit.le_partialEquivLimit C
      (Encodable.encode (Sum.inl (⟨x, hx⟩ : X) : X ⊕ Y) + 1)) hxmem
  have hYcod : Y ⊆ F.cod := by
    intro y hy
    have hymem := Order.sequenceOfCofinals.encode_mem (⟨g, hg⟩ : S) D
      (Sum.inr (⟨y, hy⟩ : Y))
    exact PartialEquiv.cod_le_cod (DirectLimit.le_partialEquivLimit C
      (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y) : X ⊕ Y) + 1)) hymem
  have hdom : F.dom = ⊤ := by
    rwa [← top_le_iff, ← hXgen, Substructure.closure_le]
  have hcod : F.cod = ⊤ := by
    rwa [← top_le_iff, ← hYgen, Substructure.closure_le]
  refine ⟨PartialEquiv.toEquivOfEqTop hdom hcod, ?_⟩
  convert! DirectLimit.le_partialEquivLimit C 0
  rw [PartialEquiv.toEquivOfEqTop_toEmbedding]
  exact Embedding.toPartialEquiv_toEmbedding hdom

/-- Potentially isomorphic countably generated structures are isomorphic. Countable generation
suffices even when function symbols generate uncountably many elements. -/
theorem PotentialIso.nonempty_equiv_of_cg (h : PotentialIso (L := L) M N)
    (hM : Structure.CG L M) (hN : Structure.CG L N) : Nonempty (M ≃[L] N) :=
  let ⟨_, ⟨_, hg⟩, hforth, hback⟩ := potentialIso_def.mp h
  ⟨(exists_le_equiv_of_cg hforth hback hg hM hN).choose⟩

/-- For countable structures, potential isomorphism is equivalent to isomorphism.
This includes empty structures and languages with function or nullary relation symbols. -/
theorem countable_potentialIso_iff_iso [Countable M] [Countable N] :
    PotentialIso (L := L) M N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => h.nonempty_equiv_of_cg Structure.cg_of_countable Structure.cg_of_countable,
    fun ⟨e⟩ => e.potentialIso⟩

end TauCeti
