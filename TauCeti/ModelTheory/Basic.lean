/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic

/-!
# Basic facts about first-order languages

Additions to Mathlib's `Mathlib.ModelTheory.Basic`.

## Main results

* `FirstOrder.Language.countable_functions_of_countable_sigma`,
  `FirstOrder.Language.countable_relations_of_countable_sigma`: a language with countably many
  function or relation symbols in total has countably many of each arity.
-/

public section

namespace FirstOrder

namespace Language

variable {L : Language}

/-- A language with countably many function symbols has countably many of each arity. -/
instance countable_functions_of_countable_sigma [Countable (Σ n, L.Functions n)] (n : ℕ) :
    Countable (L.Functions n) :=
  (sigma_mk_injective (i := n)).countable

/-- A language with countably many relation symbols has countably many of each arity. -/
instance countable_relations_of_countable_sigma [Countable (Σ n, L.Relations n)] (n : ℕ) :
    Countable (L.Relations n) :=
  (sigma_mk_injective (i := n)).countable

end Language

end FirstOrder
