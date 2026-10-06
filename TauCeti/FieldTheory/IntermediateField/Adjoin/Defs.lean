/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# The generator of a simple intermediate field as a root

For an element `α` of an extension `E / F`, the generator `IntermediateField.AdjoinSimple.gen F α`
of `F⟮α⟯` is a root of a polynomial `p` over `F`, viewed over `F⟮α⟯`, exactly when `α` is a root
of `p`. This is the form in which a root of `p` is removed from `p` over the field it generates.

## Main results

* `IntermediateField.AdjoinSimple.isRoot_map_gen_iff`: the generator of `F⟮α⟯` is a root of `p`
  mapped to `F⟮α⟯` if and only if `α` is a root of `p`.
-/

public section

namespace TauCeti

open Polynomial IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The generator of `F⟮α⟯` is a root of `p` mapped to `F⟮α⟯` if and only if `α` is a root
of `p`. -/
theorem _root_.IntermediateField.AdjoinSimple.isRoot_map_gen_iff (α : E) {p : F[X]} :
    (p.map (algebraMap F F⟮α⟯)).IsRoot (AdjoinSimple.gen F α) ↔ aeval α p = 0 := by
  rw [IsRoot.def, eval_map_algebraMap, ← ZeroMemClass.coe_eq_zero, AdjoinSimple.coe_aeval_gen_apply]

end TauCeti
