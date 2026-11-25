/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.TraceForm

/-!
# The Killing property as nondegeneracy of the Killing form

`LieAlgebra.IsKilling R L` is stated as the vanishing of the Killing orthogonal complement of the
whole algebra. Mathlib turns that into nondegeneracy of the Killing form in
`LieAlgebra.IsKilling.killingForm_nondegenerate`; this file supplies the converse and packages the
two as an equivalence, saying that `LieAlgebra.IsKilling` is exactly nondegeneracy of the Killing
form. That is the form in which the property is recognised when it is produced by a computation
with the form itself, as under base change.

Nondegeneracy of the Killing form also forces `L` to be finite and free over the base ring: by
`TauCeti.exists_basis_of_traceForm_ne_zero`, a representation with a nonzero trace form has a
finite basis, and a nondegenerate form on a nontrivial module is nonzero. Results about Killing Lie
algebras, such as Whitehead's lemmas, therefore need no separate finiteness hypothesis. A related
vanishing argument shows that an abelian Killing Lie algebra is trivial, over any commutative ring:
its Killing form is zero, and a zero form is nondegenerate only on the zero module.

## Main declarations

* `TauCeti.isKilling_iff_killingForm_nondegenerate`: `LieAlgebra.IsKilling` is exactly
  nondegeneracy of the Killing form.
* `TauCeti.subsingleton_of_isKilling_of_isLieAbelian`: an abelian Killing Lie algebra is trivial.
* `TauCeti.free_of_isKilling`, `TauCeti.finite_of_isKilling`: a Lie algebra with nondegenerate
  Killing form is free and finite over the base ring.
* `TauCeti.exists_killingForm_lie_ne_zero`: on a nontrivial Killing Lie algebra the Killing form
  does not vanish on all brackets.
* `LieIdeal.lie_eq_zero_of_disjoint`, `LieIdeal.killingForm_eq_zero_of_disjoint`: the bracket and
  the Killing form vanish between Lie ideals with trivial intersection.
* `LieIdeal.killingForm_apply_apply_coe`: on a Lie ideal of a finite free Lie algebra over a
  principal ideal domain, the Killing form of the ambient algebra restricts to that of the ideal.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.1, for the Killing
  form and Cartan's criterion.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra is Killing exactly when its Killing form is nondegenerate.

The forward direction is `LieAlgebra.IsKilling.killingForm_nondegenerate`. For the condition that
the Killing form has trivial kernel, combine this with
`LinearMap.IsRefl.nondegenerate_iff_separatingLeft` and
`LinearMap.separatingLeft_iff_ker_eq_bot`. -/
theorem isKilling_iff_killingForm_nondegenerate :
    IsKilling R L ↔ (killingForm R L).Nondegenerate :=
  ⟨fun _ ↦ IsKilling.killingForm_nondegenerate R L, fun h ↦
    ⟨(LieSubmodule.toSubmodule_eq_bot _).mp <|
      (LieIdeal.coe_killingCompl_top R L).trans h.ker_eq_bot⟩⟩

/-- An abelian Killing Lie algebra is trivial: its Killing form vanishes, and a zero form is
nondegenerate only on the zero module. -/
theorem subsingleton_of_isKilling_of_isLieAbelian [IsKilling R L] [IsLieAbelian L] :
    Subsingleton L := by
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  exact (IsKilling.killingForm_nondegenerate R L).ne_zero (traceForm_eq_zero_of_isTrivial R L L)

variable {R L}

/-- A Killing Lie algebra has a finite basis over the base ring. -/
private theorem exists_basis_of_isKilling [IsKilling R L] :
    ∃ s : Finset L, Nonempty (Module.Basis s R L) := by
  cases subsingleton_or_nontrivial L
  · exact ⟨∅, ⟨.empty _⟩⟩
  · exact exists_basis_of_traceForm_ne_zero (IsKilling.killingForm_nondegenerate R L).ne_zero

/-- A Lie algebra with nondegenerate Killing form is free over the base ring. -/
theorem free_of_isKilling [IsKilling R L] : Module.Free R L :=
  have ⟨_, ⟨b⟩⟩ := exists_basis_of_isKilling (R := R) (L := L)
  .of_basis b

/-- A Lie algebra with nondegenerate Killing form is finite over the base ring. -/
theorem finite_of_isKilling [IsKilling R L] : Module.Finite R L :=
  have ⟨_, ⟨b⟩⟩ := exists_basis_of_isKilling (R := R) (L := L)
  .of_basis b

/-- On a nontrivial Lie algebra with nondegenerate Killing form, the Killing form does not vanish
on all brackets. -/
theorem exists_killingForm_lie_ne_zero [Nontrivial L] [IsKilling R L] :
    ∃ x y z : L, killingForm R L ⁅x, y⁆ z ≠ 0 := by
  by_contra! h
  -- The nondegenerate Killing form detects every bracket, so `L` is abelian, hence trivial.
  have : IsLieAbelian L := ⟨fun x y ↦ (IsKilling.killingForm_nondegenerate R L).1 _ (h x y)⟩
  exact not_subsingleton L (subsingleton_of_isKilling_of_isLieAbelian R L)

end TauCeti

namespace LieIdeal

open LieAlgebra LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The bracket of elements of two Lie ideals with trivial intersection vanishes. -/
theorem lie_eq_zero_of_disjoint {I J : LieIdeal R L} (h : Disjoint I J) {x y : L} (hx : x ∈ I)
    (hy : y ∈ J) : ⁅x, y⁆ = 0 :=
  (LieSubmodule.mem_bot _).mp <| h.le_bot <|
    (LieSubmodule.mem_inf _ _ _).mpr ⟨lie_mem_left R L I x y hx, lie_mem_right R L J x y hy⟩

/-- The Killing form vanishes between two Lie ideals with trivial intersection. -/
theorem killingForm_eq_zero_of_disjoint {I J : LieIdeal R L} (h : Disjoint I J) {x y : L}
    (hx : x ∈ I) (hy : y ∈ J) : killingForm R L x y = 0 := by
  have : toEnd R L L x ∘ₗ toEnd R L L y = 0 := by
    ext z
    exact lie_eq_zero_of_disjoint h hx (lie_mem_left R L J y z hy)
  rw [killingForm, traceForm_apply_apply, this, map_zero]

/-- On a Lie ideal of a finite free Lie algebra over a principal ideal domain, the Killing form of
the ambient algebra restricts to the Killing form of the ideal: the pointwise form of Mathlib's
`LieIdeal.killingForm_eq`. -/
theorem killingForm_apply_apply_coe [Module.Free R L] [Module.Finite R L] [IsDomain R]
    [IsPrincipalIdealRing R] (I : LieIdeal R L) (x y : I) :
    killingForm R L x y = killingForm R I x y :=
  (LinearMap.congr_fun₂ (killingForm_eq (I := I)) x y).symm

end LieIdeal
