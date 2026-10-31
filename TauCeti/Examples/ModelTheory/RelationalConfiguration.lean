/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.Structure
import TauCeti.ModelTheory.RelationalConfiguration.Topology
import Mathlib.ModelTheory.Order

/-!
# Spaces of structures on finite, infinite and empty carriers

The order on `ℕ` survives encoding and decoding, and its atom `0 ≤ 1` gives a clopen cylinder.
The finite and infinite coding spaces have the advertised standard Borel structures. Empty
carriers still retain nullary relations, and transport to a different universe preserves
infinitary sentences.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- The order structure, rather than just its carrier, is recovered.
example : (@ofStructure Language.order ℕ (orderStructure ℕ)).toStructure = orderStructure ℕ := by
  simp

example :
    IsClopen {c : RelationalConfiguration Language.order ℕ |
      c.eval (atom (leSymb : Language.order.Relations 2) ![0, 1]) = true} :=
  isClopen_setOf_eval _ _

example {L : Language} [∀ n, Countable (L.Relations n)] (n : ℕ) :
    StandardBorelSpace (RelationalConfiguration L (Fin n)) := inferInstance

example {L : Language} [∀ n, Countable (L.Relations n)] :
    StandardBorelSpace (RelationalConfiguration L ℕ × RelationalConfiguration L ℕ) := inferInstance

-- The empty carrier imposes no constraint on the truth value of a nullary symbol.
example {L : Language} [L.IsRelational] (R : L.Relations 0) (b : Bool) :
    @Structure.RelMap L Empty (mk (fun _ => b)).toStructure 0 R Fin.elim0 ↔ b = true := by
  simp

example {L : Language} [L.IsRelational] {M : Type*} [L.Structure M] (φ : L.Sentenceω) :
    @SentenceInf.Realize L ℕ φ (ULift M)
      ((Equiv.ulift : ULift M ≃ M).symm.encodeVia (L := L)).toStructure ↔
        SentenceInf.Realize φ M :=
  Equiv.realize_encodeVia _ _
