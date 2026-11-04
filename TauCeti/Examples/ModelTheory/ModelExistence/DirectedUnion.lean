/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.ModelExistence.DirectedUnion

/-!
# Regression examples: directed unions and omitting types

These examples exercise directed unions of fragment-elementary substructures and type omission
from a downstream module, through public statements only:

* the chain form applies to chains of substructures indexed by `ℕ`;
* the empty partial type of `0`-tuples is never omitted: the empty tuple realizes all of its
  members vacuously, even in the empty structure;
* the partial type `{⊥}` is omitted by every structure.
-/

universe u v w

open FirstOrder FirstOrder.Language

-- An `ℕ`-indexed chain of `A`-elementary substructures has an `A`-elementary union.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Fragment L}
    {S : ℕ → L.Substructure M} (hmono : Monotone S) (hS : ∀ i, AElementary A (S i).subtype) :
    AElementary A (⨆ i, S i).subtype :=
  aElementary_iSup_of_monotone hmono hS

-- No structure omits the empty partial type of `0`-tuples.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] :
    ¬ OmitsType M (∅ : Set (L.BoundedFormulaω Empty 0)) := by
  rw [omitsType_iff]
  exact fun h => by simpa using h default

-- Every structure omits the partial type `{⊥}`.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] {n : ℕ} :
    OmitsType M ({⊥} : Set (L.BoundedFormulaω Empty n)) :=
  omitsType_iff.2 fun _ => ⟨⊥, rfl, by simp [BoundedFormulaInf.realize_bot]⟩
