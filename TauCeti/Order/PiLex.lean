/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex

/-!
# Lexicographic products and coordinatewise maps

This module provides `TauCeti.strictMono_toLex_comp`, lifting a family of coordinatewise strictly
monotone maps to a strictly monotone map on `Lex (∀ i, β i)`.

## Main results

* `TauCeti.strictMono_toLex_comp`: coordinatewise strictly monotone maps induce a strictly monotone
  map between lexicographic products.
-/

public section

namespace TauCeti

/-- A family of coordinatewise strictly monotone maps induces a strictly monotone map on the
lexicographic product. -/
theorem strictMono_toLex_comp {ι : Type*} {β γ : ι → Type*} [LinearOrder ι]
    [∀ i, PartialOrder (β i)] [∀ i, PartialOrder (γ i)]
    {f : ∀ i, β i → γ i} (hf : ∀ i, StrictMono (f i)) :
    StrictMono fun x : Lex (∀ i, β i) ↦ toLex fun i ↦ f i (ofLex x i) :=
  fun _ _ ⟨i, hi, hlt⟩ ↦ ⟨i, fun j hj ↦ congrArg (f j) (hi j hj), hf i hlt⟩

end TauCeti
