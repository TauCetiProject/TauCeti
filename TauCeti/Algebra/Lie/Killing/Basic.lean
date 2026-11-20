/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# The Killing property as nondegeneracy of the Killing form

`LieAlgebra.IsKilling R L` is stated as the vanishing of the Killing orthogonal complement of the
whole algebra. Mathlib turns that into nondegeneracy of the Killing form in
`LieAlgebra.IsKilling.killingForm_nondegenerate`; this file supplies the converse and packages the
two as an equivalence, saying that `LieAlgebra.IsKilling` is exactly nondegeneracy of the Killing
form. That is the form in which the property is recognised when it is produced by a computation
with the form itself, as under base change.

Nondegeneracy of the Killing form also forces `L` to be finite over the base ring: on a module with
no finite basis every trace vanishes, so the Killing form would be zero, and a zero form is
nondegenerate only on the zero module (`TauCeti.finite_of_isKilling`). Results about Killing Lie
algebras, such as Whitehead's lemmas, therefore need no separate finiteness hypothesis.

## Main declarations

* `TauCeti.isKilling_iff_ker_killingForm_eq_bot`: a Lie algebra is Killing exactly when its
  Killing form has trivial kernel.
* `TauCeti.isKilling_of_killingForm_nondegenerate`: a Lie algebra whose Killing form is
  nondegenerate is Killing.
* `TauCeti.isKilling_iff_killingForm_nondegenerate`: `LieAlgebra.IsKilling` is exactly
  nondegeneracy of the Killing form.
* `TauCeti.finite_of_isKilling`: a Lie algebra with nondegenerate Killing form is finite over the
  base ring.
* `TauCeti.exists_killingForm_lie_ne_zero`: on a nontrivial Killing Lie algebra the Killing form
  does not vanish on all brackets.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.1, for the Killing
  form and Cartan's criterion.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra is Killing exactly when its Killing form has trivial kernel. -/
theorem isKilling_iff_ker_killingForm_eq_bot :
    IsKilling R L ↔ LinearMap.ker (killingForm R L) = ⊥ :=
  ⟨fun _ ↦ IsKilling.ker_killingForm_eq_bot R L, fun h ↦
    ⟨(LieSubmodule.toSubmodule_eq_bot _).mp <| (LieIdeal.coe_killingCompl_top R L).trans h⟩⟩

/-- A Lie algebra whose Killing form is nondegenerate is Killing.

This is the converse of `LieAlgebra.IsKilling.killingForm_nondegenerate`, and the two together say
that `LieAlgebra.IsKilling` is exactly nondegeneracy of the Killing form. -/
theorem isKilling_of_killingForm_nondegenerate (h : (killingForm R L).Nondegenerate) :
    IsKilling R L :=
  (isKilling_iff_ker_killingForm_eq_bot R L).mpr h.ker_eq_bot

/-- A Lie algebra is Killing exactly when its Killing form is nondegenerate. -/
theorem isKilling_iff_killingForm_nondegenerate :
    IsKilling R L ↔ (killingForm R L).Nondegenerate :=
  ⟨fun _ ↦ IsKilling.killingForm_nondegenerate R L, isKilling_of_killingForm_nondegenerate R L⟩

variable {R L}

/-- A Lie algebra with nondegenerate Killing form is finite over the base ring. -/
theorem finite_of_isKilling [IsKilling R L] : Module.Finite R L := by
  by_contra hnf
  -- Without a finite basis every trace vanishes, so the Killing form is zero, and a zero form is
  -- nondegenerate only on the zero module.
  have h0 (x y : L) : killingForm R L x y = 0 := by
    simp [LieModule.traceForm_apply_apply, LinearMap.trace_eq_zero_of_not_finite hnf]
  have : Subsingleton L := subsingleton_of_forall_eq 0 fun x ↦
    (IsKilling.killingForm_nondegenerate R L).1 x (h0 x)
  exact hnf inferInstance

/-- On a nontrivial Lie algebra with nondegenerate Killing form, the Killing form does not vanish
on all brackets. -/
theorem exists_killingForm_lie_ne_zero [Nontrivial L] [IsKilling R L] :
    ∃ x y z : L, killingForm R L ⁅x, y⁆ z ≠ 0 := by
  by_contra! h
  -- The nondegenerate Killing form detects every bracket, so `L` is abelian; then the Killing form
  -- vanishes, and a zero form is nondegenerate only on the zero module.
  have hnd := IsKilling.killingForm_nondegenerate R L
  have : IsLieAbelian L := ⟨fun x y ↦ hnd.1 _ (h x y)⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  exact hx <| hnd.1 x fun y ↦ by simp [traceForm_eq_zero_of_isTrivial]

end TauCeti
