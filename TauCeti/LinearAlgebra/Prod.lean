/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Prod

/-!
# Factorwise comparison of submodule products

Mathlib's `Mathlib/LinearAlgebra/Prod.lean` compares a submodule product against another
submodule only through the map/projection API (`Submodule.le_prod_iff`, `Submodule.prod_le_iff`).
This file records the purely factorwise order characterisation of two products, which follows
from that API by rewriting the projections of a product back to its factors.

## Main declarations

* `TauCeti.Submodule.prod_le_prod_iff`: products of submodules compare factorwise.
-/

public section

namespace TauCeti

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- A product of submodules is contained in another product of submodules exactly when each
factor is contained in the corresponding factor. A general order lemma that could move to
Mathlib's `Mathlib/LinearAlgebra/Prod.lean`. -/
lemma prod_le_prod_iff {p p' : Submodule R M} {q q' : Submodule R N} :
    p.prod q ≤ p'.prod q' ↔ p ≤ p' ∧ q ≤ q' := by
  rw [Submodule.le_prod_iff, Submodule.prod_map_fst, Submodule.prod_map_snd]

end Submodule

end TauCeti
