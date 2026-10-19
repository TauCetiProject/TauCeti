/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.BackAndForth.Karp
import Mathlib.ModelTheory.Order

/-!
# Regression examples for infinitary equivalence

These downstream examples use the public API. The forward direction of Karp's theorem holds at a
carrier in a higher universe than both structures, and agreement at `ℕ` transports to every
encodable carrier. Contrapositively, `(ℕ, ≤)` and `(ℤ, ≤)` are not potentially isomorphic: the
sentence asserting a least element holds in the first and fails in the second.
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
  have : Language.order.OrderedStructure ℕ := ⟨fun _ => Iff.rfl⟩
  have : Language.order.OrderedStructure ℤ := ⟨fun _ => Iff.rfl⟩
  have hφ : (∃ x : ℕ, ∀ y : ℕ, x ≤ y) ↔ ∃ x : ℤ, ∀ y : ℤ, x ≤ y := by
    simpa [φ, Fin.snoc] using infEquivAt_iff.1 (h.infEquivAt Unit) φ
  obtain ⟨x, hx⟩ := hφ.1 ⟨0, Nat.zero_le⟩
  have := hx (x - 1)
  omega

end TauCeti
