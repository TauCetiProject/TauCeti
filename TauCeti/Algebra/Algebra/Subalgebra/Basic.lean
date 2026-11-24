/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Subalgebras over different base rings and restrictions to ranges

Mathlib's `Subalgebra.equivOfEq` identifies two equal subalgebras of an algebra `A` over one and
the same base ring `R`. Two subalgebras of `A` over *different* base rings cannot be equal, since
they live in different types, but they can still have the same underlying set, and then they are
the same subsemiring of `A`. This file records the resulting ring isomorphism, which is
`RingEquiv.subsemiringCongr` on the underlying subsemirings, together with the fact that it is
compatible with the two inclusions into `A`.

It also provides the generic range-restriction maps `AlgHom.rangeMap` and `AlgEquiv.rangeMap`,
restricting `φ : B →ₐ[R] B'` (respectively `e : B ≃ₐ[R] B'`) from `α.range` onto `(φ.comp α).range`
(respectively `((e : B →ₐ[R] B').comp α).range`) for any `α : H →ₐ[R] B`.

## Main results

* `Subalgebra.ringEquivOfSetEq`: the ring isomorphism between two subalgebras of `A`, over possibly
  different base rings, with the same underlying set.
* `Subalgebra.coe_ringEquivOfSetEq_apply` and `Subalgebra.coe_ringEquivOfSetEq_symm_apply`: the
  isomorphism and its inverse commute with the inclusions into `A`.
* `AlgHom.rangeMap`, `AlgHom.coe_rangeMap_apply`, `AlgHom.rangeMap_surjective`: surjective
  restriction `α.range →ₐ[R] (φ.comp α).range` of an algebra homomorphism `φ : B →ₐ[R] B'`.
* `AlgEquiv.rangeMap`, `AlgEquiv.coe_rangeMap_apply`, `AlgEquiv.coe_rangeMap_symm_apply`:
  restriction `α.range ≃ₐ[R] ((e : B →ₐ[R] B').comp α).range` of an algebra equivalence
  `e : B ≃ₐ[R] B'`.
-/

public section

namespace Subalgebra

variable {R₁ R₂ A : Type*} [CommSemiring R₁] [CommSemiring R₂] [Semiring A] [Algebra R₁ A]
  [Algebra R₂ A]

/-- Two subalgebras of `A`, over possibly different base rings, with the same underlying set are
isomorphic as rings: the identity of `A` restricted to that set. This is the counterpart of
`Subalgebra.equivOfEq` for subalgebras over different base rings, and is
`RingEquiv.subsemiringCongr` on the underlying subsemirings. -/
def ringEquivOfSetEq (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A) (h : (S₁ : Set A) = S₂) :
    S₁ ≃+* S₂ :=
  RingEquiv.subsemiringCongr (s := S₁.toSubsemiring) (t := S₂.toSubsemiring) (SetLike.ext' h)

@[simp]
theorem coe_ringEquivOfSetEq_apply (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) = S₂) (a : S₁) : (ringEquivOfSetEq S₁ S₂ h a : A) = a :=
  (rfl)

@[simp]
theorem coe_ringEquivOfSetEq_symm_apply (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) = S₂) (b : S₂) : ((ringEquivOfSetEq S₁ S₂ h).symm b : A) = b :=
  (rfl)

end Subalgebra

namespace AlgHom

variable {R H B B' : Type*} [CommSemiring R] [Semiring H] [Semiring B] [Semiring B']
  [Algebra R H] [Algebra R B] [Algebra R B']

/-- Restricting `φ : B →ₐ[R] B'` to the range of `α : H →ₐ[R] B` gives a surjective `R`-algebra
homomorphism `α.range →ₐ[R] (φ.comp α).range`. -/
def rangeMap (φ : B →ₐ[R] B') (α : H →ₐ[R] B) : α.range →ₐ[R] (φ.comp α).range :=
  (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α φ).symm).toAlgHom.comp (φ.subalgebraMap α.range)

/-- Applying `φ.rangeMap α` acts by `φ` on underlying elements. -/
@[simp]
theorem coe_rangeMap_apply (φ : B →ₐ[R] B') (α : H →ₐ[R] B) (x : α.range) :
    (φ.rangeMap α x : B') = φ x.1 := by
  simp [rangeMap]

/-- `φ.rangeMap α` is surjective onto `(φ.comp α).range`. -/
theorem rangeMap_surjective (φ : B →ₐ[R] B') (α : H →ₐ[R] B) :
    Function.Surjective (φ.rangeMap α) :=
  (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α φ).symm).surjective.comp
    (φ.subalgebraMap_surjective α.range)

end AlgHom

namespace AlgEquiv

variable {R H B B' : Type*} [CommSemiring R] [Semiring H] [Semiring B] [Semiring B']
  [Algebra R H] [Algebra R B] [Algebra R B']

/-- Restricting an algebra equivalence `e : B ≃ₐ[R] B'` to the range of `α : H →ₐ[R] B` gives
an `R`-algebra equivalence `α.range ≃ₐ[R] ((e : B →ₐ[R] B').comp α).range`. -/
def rangeMap (e : B ≃ₐ[R] B') (α : H →ₐ[R] B) :
    α.range ≃ₐ[R] ((e : B →ₐ[R] B').comp α).range :=
  (e.subalgebraMap α.range).trans
    (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α (e : B →ₐ[R] B')).symm)

/-- Applying `e.rangeMap α` acts by `e` on underlying elements. -/
@[simp]
theorem coe_rangeMap_apply (e : B ≃ₐ[R] B') (α : H →ₐ[R] B) (x : α.range) :
    (e.rangeMap α x : B') = e x.1 := by
  simp [rangeMap]

/-- Applying `(e.rangeMap α).symm` acts by `e.symm` on underlying elements. -/
@[simp]
theorem coe_rangeMap_symm_apply (e : B ≃ₐ[R] B') (α : H →ₐ[R] B)
    (y : ((e : B →ₐ[R] B').comp α).range) :
    ((e.rangeMap α).symm y : B) = e.symm y.1 := by
  apply e.injective
  rw [e.apply_symm_apply, ← coe_rangeMap_apply]
  exact congrArg Subtype.val ((e.rangeMap α).apply_symm_apply y)

end AlgEquiv
