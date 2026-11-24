/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit

import TauCeti.FieldTheory.AbelRuffini
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Separable

/-!
# Dummit's criterion for quintics solvable by radicals

In characteristic zero, the roots of a monic irreducible quintic are expressible by radicals
exactly when its Galois group is solvable
(`TauCeti.isSolvable_gal_iff_forall_rootSet_mem_solvableByRad`). By Dummit's criterion in group
form, `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec_of_five_ne_zero`, this
happens exactly when its `F₂₀` resolvent sextic has a root in the base field. When it does, the
sextic is a linear factor times an irreducible quintic
(`TauCeti.exists_irreducible_eq_X_sub_C_mul_of_isRoot_specialize_quinticF20Spec`).

## Main results

* `TauCeti.forall_rootSet_mem_solvableByRad_iff_exists_isRoot_specialize_quinticF20Spec`:
  **Dummit's criterion, radical form**: in characteristic zero, the roots of a monic irreducible
  quintic are expressible by radicals exactly when its sextic has a root in the base field.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), Theorem 1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] {f : F[X]}

/-- **Dummit's criterion, radical form** (Dummit, Theorem 1). In characteristic zero, the roots
of a monic irreducible quintic in an algebraic closure are all expressible by radicals exactly
when its `F₂₀` resolvent sextic has a root in the base field. -/
theorem forall_rootSet_mem_solvableByRad_iff_exists_isRoot_specialize_quinticF20Spec [CharZero F]
    (hf : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (∀ x ∈ f.rootSet (AlgebraicClosure F), x ∈ solvableByRad F (AlgebraicClosure F)) ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  rw [← isSolvable_gal_iff_forall_rootSet_mem_solvableByRad]
  exact isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec_of_five_ne_zero (by norm_num)
    hf hirr hdeg

end TauCeti
