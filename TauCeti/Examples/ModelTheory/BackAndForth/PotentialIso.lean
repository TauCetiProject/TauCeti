/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.BackAndForth.Presentation
import Mathlib.ModelTheory.Order

/-!
# Regression examples for potential isomorphism

These downstream examples use the public API to check that potential isomorphism composes, and
that potential isomorphism does not require every finitely generated partial equivalence to extend,
as Mathlib's global extension property `Language.IsExtensionPair` does: `(ℕ, ≤)` is isomorphic to
itself, yet the one-point partial isomorphism `1 ↦ 0` extends to no partial isomorphism defined at
`0`.
-/

namespace TauCeti

open FirstOrder FirstOrder.Language

-- Transitivity composes the potential isomorphisms given by an isomorphism and its inverse, in
-- any language.
example {L : Language} {M N : Type*} [L.Structure M] [L.Structure N] (e : M ≃[L] N) :
    PotentialIso (L := L) M M :=
  e.potentialIso.trans e.potentialIso.symm

-- `(ℕ, ≤)` is potentially isomorphic to itself, but not every partial isomorphism extends: the
-- extension of `1 ↦ 0` to `0` would have to send `0` below `0`.
example :
    letI := Language.orderStructure ℕ
    PotentialIso (L := Language.order) ℕ ℕ ∧ ¬ Language.order.IsExtensionPair ℕ ℕ := by
  let _ := Language.orderStructure ℕ
  refine ⟨(Language.Equiv.refl _ ℕ).potentialIso, fun hext => ?_⟩
  have h : SameAtomicType (L := Language.order) (fun _ : Fin 1 => (1 : ℕ)) (fun _ => 0) := by
    rw [sameAtomicType_iff]
    refine ⟨fun _ _ => by simp, fun r v => ?_⟩
    cases r
    exact iff_of_true (le_refl 1) (le_refl 0)
  obtain ⟨f, a, ha, hb, -⟩ := h.exists_fgEquiv
  obtain ⟨g, h0, hfg⟩ := hext f 0
  -- `g` extends `f`, so it sends `a 0 = 1` to `0`, and must send `0` below `0`.
  have h1 : (a 0 : ℕ) ∈ g.1.dom := PartialEquiv.dom_le_dom hfg (a 0).2
  have hg1 : (g.1.toEquiv ⟨a 0, h1⟩ : ℕ) = 0 :=
    (PartialEquiv.toEquiv_apply_of_le hfg (a 0).2).trans (by simpa using hb 0)
  have hle : (g.1.toEquiv ⟨0, h0⟩ : ℕ) ≤ g.1.toEquiv ⟨a 0, h1⟩ :=
    (g.1.toEquiv.map_rel (leSymb (L := Language.order)) ![⟨0, h0⟩, ⟨a 0, h1⟩]).2 (Nat.zero_le _)
  rw [hg1, Nat.le_zero] at hle
  have h01 := congrArg Subtype.val (g.1.toEquiv.injective (Subtype.ext (hle.trans hg1.symm)))
  simp [ha 0] at h01

end TauCeti
