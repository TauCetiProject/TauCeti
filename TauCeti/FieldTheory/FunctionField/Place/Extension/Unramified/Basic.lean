/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Equiv

/-!
# Unramified places

A place `P'` of `F' / k'` lying over the place `P = P' ∩ F` of `F / k` is **unramified** over `F`
when `e(P' ∣ P) = 1` and the residue extension `F'_{P'} / F_P` is separable.

Stichtenoth (Definition 3.1.5) calls `P' ∣ P` unramified as soon as `e(P' ∣ P) = 1`, since his
constant field is perfect and residue extensions are then separable. Over an imperfect residue
field the separability condition is not automatic, and it is needed for unramifiedness to pass to
composita and Galois closures (Stichtenoth, Corollary 3.9.3); see
`TauCeti.Place.forall_isUnramified_sup_iff`.

## Main definitions

* `TauCeti.Place.IsUnramified`: a place with ramification index one and separable residue
  extension.

## Main results

* `TauCeti.Place.isUnramified_equivOfRingEquiv_iff`: unramifiedness is invariant under an
  isomorphism of the upstairs field over the base field.
* `TauCeti.Place.forall_isUnramified_iff_of_algEquiv`: so is the property that every place above
  a given place of the base field is unramified.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.1.5.
-/

public section

namespace TauCeti.Place

universe u u' v v'

section Defs

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

variable (k F) in
/-- A place `P'` of `F' / k'` is **unramified** over `F` when its ramification index over the
place `P = P' ∩ F` below it is one and its residue extension `F'_{P'} / F_P` is separable.

Stichtenoth (Definition 3.1.5) only asks for `e(P' ∣ P) = 1`; the two notions agree when the
residue field of `P` is perfect, for instance when the constant field is perfect. The definition
needs only an integral extension `F' / F`; for a finite separable one it agrees with Mathlib's
`Algebra.IsUnramifiedAt` for the local model at the centre of `P'`, by
`TauCeti.Place.isUnramified_iff_isUnramifiedAt`. -/
@[mk_iff]
structure IsUnramified (P' : Place k' F') : Prop where
  /-- The ramification index of an unramified place is `1`. -/
  ramificationIdx_eq_one : ramificationIdx F P' = 1
  /-- The residue extension of an unramified place is separable. -/
  isSeparable_residueField :
    Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField

end Defs

section Equiv

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']
variable [Algebra.IsIntegral F L] [Algebra.IsIntegral F L']

/-- **Unramifiedness is invariant under an isomorphism of the upstairs field** over the base
field. -/
@[simp]
theorem isUnramified_equivOfRingEquiv_iff (e : L ≃ₐ[F] L') (Q : Place k L) :
    IsUnramified k F (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv (fun c ↦ by
      simp [IsScalarTower.algebraMap_apply k F L,
        IsScalarTower.algebraMap_apply k F L']) Q) ↔ IsUnramified k F Q := by
  rw [isUnramified_iff, isUnramified_iff, ramificationIdx_equivOfRingEquiv,
    isSeparable_residueField_equivOfRingEquiv_iff]

/-- Whether every place above a place `P` of `F` is unramified depends only on the extension up
to isomorphism over `F`. -/
theorem forall_isUnramified_iff_of_algEquiv (P : Place k F) (e : L ≃ₐ[F] L') :
    (∀ Q : Place k L, Q.restrict k F = P → IsUnramified k F Q) ↔
      ∀ Q : Place k L', Q.restrict k F = P → IsUnramified k F Q := by
  let t := equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv (fun c ↦ by
    simp [IsScalarTower.algebraMap_apply k F L, IsScalarTower.algebraMap_apply k F L'])
  rw [← t.forall_congr_right]
  simp only [t, restrict_equivOfRingEquiv, isUnramified_equivOfRingEquiv_iff]

end Equiv

end TauCeti.Place
