/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root system that need no further theory.

## Main results

* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.finite_weight_of_isRootSystem`: the weight module of a finite root system is finitely
  generated.
* `RootPairing.reflection_reflection_of_pairing_eq_zero`: reflecting in `i` then `j` when
  `P.pairing i j = 0` subtracts both coroot projections independently.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- On a finite root system, the weight module is finitely generated because it is spanned by the
finite set of roots. -/
theorem finite_weight_of_isRootSystem (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem] :
    Module.Finite R M :=
  Module.finite_def.mpr
    (IsRootSystem.span_root_eq_top (P := P) ▸ Submodule.fg_span (Set.finite_range P.root))

/-- Reflecting in `i` and then in `j` when `P.pairing i j = 0` subtracts the `i`-th and
`j`-th coroot projections independently. -/
theorem reflection_reflection_of_pairing_eq_zero (P : RootPairing ι R M N) {i j : ι}
    (h0 : P.pairing i j = 0) (y : M) :
    P.reflection j (P.reflection i y) =
      y - P.coroot' i y • P.root i - P.coroot' j y • P.root j := by
  rw [reflection_apply, reflection_apply, map_sub, map_smul, root_coroot'_eq_pairing, h0,
    smul_eq_mul, mul_zero, sub_zero]

end RootPairing
