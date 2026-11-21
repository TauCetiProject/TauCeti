/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.Structure
import TauCeti.ModelTheory.RelationalConfiguration.Topology
import TauCeti.ModelTheory.RelationalConfiguration.Coding
import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.Infinitary.Infinite
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Graph

/-!
# Spaces of structures on finite, infinite and empty carriers

The order on `ℕ` survives encoding and decoding, and its atom `0 ≤ 1` gives a clopen cylinder.
The finite and infinite coding spaces have the advertised standard Borel structures. Empty
carriers still retain nullary relations, and transport to a different universe preserves
infinitary sentences. The query code reads each atom at its own index, pads with `false`, and
in a language without relation symbols is constantly `false`.
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

-- No configuration on a finite carrier models the infinitude sentence, and every one on `ℕ` does.
example {L : Language} [L.IsRelational] (n : ℕ) :
    (modelsOf L.infiniteSentence : Set (RelationalConfiguration L (Fin n))) = ∅ :=
  modelsOf_infiniteSentence_of_finite

example {L : Language} [L.IsRelational] :
    (modelsOf L.infiniteSentence : Set (RelationalConfiguration L ℕ)) = Set.univ :=
  modelsOf_infiniteSentence_of_infinite

-- Model classes of `L_{ω₁ω}` sentences on countable carriers are standard Borel spaces.
example {L : Language} [L.IsRelational] [∀ n, Countable (L.Relations n)] (φ : L.Sentenceω) :
    StandardBorelSpace (modelsOf φ : Set (RelationalConfiguration L ℕ)) := inferInstance

-- The query code reads the atom `0 ≤ 1` at its index under `Encodable.ofCountable`.
example (c : RelationalConfiguration Language.order ℕ) :
    let a := atom (leSymb : Language.order.Relations 2) ![0, 1]
    queryCode c (@Encodable.encode _ (Encodable.ofCountable _) a) = c.eval a :=
  queryCode_encode c _

-- With no relation symbols there are no atoms, so the query code is all padding.
example (c : RelationalConfiguration Language.empty ℕ) (n : ℕ) : queryCode c n = false := by
  have : IsEmpty (Atom Language.empty ℕ) := ⟨fun ⟨_, R, _⟩ => R.elim⟩
  refine queryCode_of_decode_eq_none c ?_
  cases h : @Encodable.decode (Atom Language.empty ℕ) (Encodable.ofCountable _) n with
  | none => rfl
  | some a => exact isEmptyElim a

-- The coding space of graphs on `ℕ` has continuum many points.
example : Cardinal.mk (RelationalConfiguration Language.graph ℕ) = Cardinal.continuum :=
  mk_eq_continuum _ _ two_ne_zero Language.adj
