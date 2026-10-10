/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.CategoryTheory.Monoidal.Grp.Subobject
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The closed-subgroup criterion

A closed subscheme of a group scheme is a subgroup scheme exactly when the identity,
multiplication of its two copies, and inversion factor through it. Scheme-theoretic
factorization is expressed by inclusion of ideal sheaves in the kernels of these maps.
Thus the criterion detects the equations on nonreduced bases, not merely stability of
geometric points.

`grpObjOfClosedImmersion` constructs the group law from these three conditions, and
`exists_grpObj_iff_ker_le` proves the converse. The compatible group structure is unique,
and is commutative if the ambient group scheme is commutative. The resulting inclusion
can be used with `ClosedSubgroupScheme.mk`.

The criterion applies to arbitrary closed subschemes, in particular to the finite locally
free divisors used to define Drinfeld structures. No Cartier, flatness, finiteness, or
smoothness assumption is needed for the group axioms themselves.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
* Mathlib's `AlgebraicGeometry.IsClosedImmersion.lift` supplies the factorization of the
  three scheme morphisms through the closed immersion.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

variable {S : Scheme.{u}} {H G : Over S} [GrpObj G]

/-- Construct the group structure on a closed subscheme whose ideal vanishes on the identity,
multiplication and inversion maps. -/
@[instance_reducible]
noncomputable def grpObjOfClosedImmersion (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) : GrpObj H := by
  have : Mono i := Over.mono_of_mono_left i
  exact grpObjOfMono i
    (closedImmersionOverLift i η[G] he)
    (closedImmersionOverLift i ((i ⊗ₘ i) ≫ μ[G]) hm)
    (closedImmersionOverLift i (i ≫ ι[G]) hj)
    (by simp) (by simp) (by simp)

/-- The identity of the induced group scheme is the lift of the ambient identity. -/
@[simp]
theorem grpObjOfClosedImmersion_one (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) :
    (grpObjOfClosedImmersion i he hm hj).one = closedImmersionOverLift i η[G] he := by
  simp

/-- The multiplication of the induced group scheme is the lift of the ambient multiplication. -/
@[simp]
theorem grpObjOfClosedImmersion_mul (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) :
    (grpObjOfClosedImmersion i he hm hj).mul =
      closedImmersionOverLift i ((i ⊗ₘ i) ≫ μ[G]) hm := by
  simp

/-- The inversion of the induced group scheme is the lift of the ambient inversion. -/
@[simp]
theorem grpObjOfClosedImmersion_inv (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) :
    (grpObjOfClosedImmersion i he hm hj).inv =
      closedImmersionOverLift i (i ≫ ι[G]) hj := by
  simp

/-- The inclusion of the group scheme constructed by the closed-subgroup criterion is a
homomorphism. -/
theorem isMonHom_grpObjOfClosedImmersion (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) :
    letI := grpObjOfClosedImmersion i he hm hj
    IsMonHom i := by
  let := grpObjOfClosedImmersion i he hm hj
  exact ⟨by simp, by simp⟩

/-- **The closed-subgroup criterion.** A closed subscheme carries a compatible group structure
if and only if its defining ideal vanishes on identity, multiplication and inversion. -/
theorem exists_grpObj_iff_ker_le (i : H ⟶ G) [IsClosedImmersion i.left] :
    (∃ h : GrpObj H, letI := h; IsMonHom i) ↔
      i.left.ker ≤ η[G].left.ker ∧
      i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker ∧
      i.left.ker ≤ (i ≫ ι[G]).left.ker := by
  constructor
  · rintro ⟨h, hi⟩
    let := h
    let := hi
    refine ⟨?_, ?_, ?_⟩
    · rw [← IsMonHom.one_hom i]
      exact η[H].left.le_ker_comp i.left
    · rw [← IsMonHom.mul_hom i]
      exact μ[H].left.le_ker_comp i.left
    · rw [← GrpObj.inv_hom i]
      exact ι[H].left.le_ker_comp i.left
  · rintro ⟨he, hm, hj⟩
    exact ⟨grpObjOfClosedImmersion i he hm hj,
      isMonHom_grpObjOfClosedImmersion i he hm hj⟩

/-- The compatible group structure supplied by the closed-subgroup criterion is unique. -/
theorem eq_grpObjOfClosedImmersion (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) (h : GrpObj H)
    (hi : @IsMonHom _ _ _ H G h.toMonObj inferInstance i) :
    h = grpObjOfClosedImmersion i he hm hj := by
  have : Mono i := Over.mono_of_mono_left i
  exact grpObj_eq_of_mono i _ _ hi (isMonHom_grpObjOfClosedImmersion i he hm hj)

/-- The subgroup of a commutative group scheme constructed by the criterion is commutative. -/
theorem isCommMonObj_grpObjOfClosedImmersion [IsCommMonObj G]
    (i : H ⟶ G) [IsClosedImmersion i.left]
    (he : i.left.ker ≤ η[G].left.ker)
    (hm : i.left.ker ≤ ((i ⊗ₘ i) ≫ μ[G]).left.ker)
    (hj : i.left.ker ≤ (i ≫ ι[G]).left.ker) :
    letI := grpObjOfClosedImmersion i he hm hj
    IsCommMonObj H := by
  let := grpObjOfClosedImmersion i he hm hj
  have : Mono i := Over.mono_of_mono_left i
  have := isMonHom_grpObjOfClosedImmersion i he hm hj
  exact isCommMonObj_of_mono i

end TauCeti.GroupScheme
