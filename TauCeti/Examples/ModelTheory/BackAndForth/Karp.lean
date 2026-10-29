/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.BackAndForth.Karp
import TauCeti.ModelTheory.Order
import Mathlib.ModelTheory.Order

/-!
# Regression examples for infinitary equivalence

These downstream examples use the public API. The forward direction of Karp's theorem holds at a
carrier in a higher universe than both structures, and agreement at `ℕ` transports to every
encodable carrier. Contrapositively, `(ℕ, ≤)` and `(ℤ, ≤)` are not potentially isomorphic: the
sentence asserting a least element holds in the first and fails in the second.

The converse holds at any common carrier, not only `M ⊕ N`: for countable structures the carrier
`ℕ` gives Karp's theorem for `L_{ω₁ω}`, and for empty structures the empty carrier suffices. On
countable structures, agreement at `ℕ` is isomorphism, so pure sets of different finite sizes are
separated. Two empty structures that differ on a nullary relation are separated by that relation,
at every carrier in every universe.
-/

universe u

namespace TauCeti

open FirstOrder FirstOrder.Language

-- An isomorphism gives agreement on sentences branching over a carrier in any universe.
example {L : Language} [L.IsRelational] {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) (κ : Type u) : InfEquivAt (L := L) κ M N :=
  e.potentialIso.infEquivAt κ

-- Agreement at `ℕ` transports to every encodable carrier.
example {L : Language} {M N : Type*} [L.Structure M] [L.Structure N] (κ : Type*) [Encodable κ]
    (h : InfEquivAt (L := L) ℕ M N) : InfEquivAt (L := L) κ M N :=
  h.of_reindex (IndexCoding.ofEncodable κ)

-- `(ℕ, ≤)` has a least element and `(ℤ, ≤)` does not, so they are not potentially isomorphic.
example :
    letI := Language.orderStructure ℕ
    letI := Language.orderStructure ℤ
    ¬ PotentialIso (L := Language.order) ℕ ℤ := by
  let _ := Language.orderStructure ℕ
  let _ := Language.orderStructure ℤ
  intro h
  -- `∃ x, ∀ y, x ≤ y`, with `x` and `y` the bound variables `0` and `1`.
  let φ : Language.order.SentenceInf Unit :=
    (BoundedFormulaInf.rel leSymb ![Term.var (Sum.inr 0), Term.var (Sum.inr 1)]).all.ex
  have hφ : (∃ x : ℕ, ∀ y : ℕ, x ≤ y) ↔ ∃ x : ℤ, ∀ y : ℤ, x ≤ y := by
    simpa [φ, Fin.snoc] using infEquivAt_iff.1 (h.infEquivAt Unit) φ
  obtain ⟨x, hx⟩ := hφ.1 ⟨0, Nat.zero_le⟩
  have := hx (x - 1)
  omega

-- For countable structures, the carrier `ℕ` gives Karp's theorem for `L_{ω₁ω}`.
example {L : Language} [L.IsRelational] {M N : Type*} [L.Structure M] [L.Structure N]
    [Encodable M] [Encodable N] : PotentialIso (L := L) M N ↔ InfEquivAt (L := L) ℕ M N :=
  karp_theorem_at (IndexCoding.ofEncodable M) (IndexCoding.ofEncodable N)

-- Empty structures are coded into the empty carrier, at which every conjunction is empty, and
-- agreement there already gives a potential isomorphism.
example {L : Language} [L.IsRelational] {M N : Type*} [L.Structure M] [L.Structure N]
    [IsEmpty M] [IsEmpty N] (h : InfEquivAt (L := L) Empty M N) : PotentialIso (L := L) M N :=
  h.potentialIso (IndexCoding.ofEquiv (Equiv.equivEmpty M))
    (IndexCoding.ofEquiv (Equiv.equivEmpty N))

-- Two empty structures that differ on a nullary relation disagree on the sentence consisting of
-- that relation, at every carrier in every universe.
example (κ : Type u) :
    let L : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
    let _ : L.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
    let _ : L.Structure (ULift.{0} Empty) := ⟨fun f => Empty.elim f, fun _ _ => False⟩
    ¬ InfEquivAt (L := L) κ Empty (ULift.{0} Empty) := by
  intro L _ _ h
  have := infEquivAt_iff_forall_realize.1 h (.rel (⟨rfl⟩ : L.Relations 0) Fin.elim0)
  simp only [BoundedFormulaInf.realize_rel] at this
  exact this.1 trivial

-- Hence the same structures are not fully infinitarily equivalent, nor potentially isomorphic.
example :
    let L : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
    let _ : L.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
    let _ : L.Structure (ULift.{0} Empty) := ⟨fun f => Empty.elim f, fun _ _ => False⟩
    ¬ InfEquivW (L := L) Empty (ULift.{0} Empty) := by
  intro L _ _ h
  have := infEquivAt_iff_forall_realize.1 (infEquivW_iff.1 h Empty)
    (.rel (⟨rfl⟩ : L.Relations 0) Fin.elim0)
  simp only [BoundedFormulaInf.realize_rel] at this
  exact this.1 trivial

-- Countable structures agreeing on the `L_{ω₁ω}` sentences are isomorphic.
example {L : Language} [L.IsRelational] {M N : Type*} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (h : InfEquivAt (L := L) ℕ M N) : Nonempty (M ≃[L] N) :=
  countable_infEquivAt_nat_iff_iso.1 h

-- Pure sets of sizes `2` and `3` are not isomorphic, so some `L_{ω₁ω}` sentence separates them.
example [Language.empty.Structure (Fin 2)] [Language.empty.Structure (Fin 3)] :
    ¬ InfEquivAt (L := Language.empty) ℕ (Fin 2) (Fin 3) := by
  rw [countable_infEquivAt_nat_iff_iso]
  rintro ⟨e⟩
  simpa using Fintype.card_congr e.toEquiv

end TauCeti
