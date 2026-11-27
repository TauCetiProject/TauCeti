/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import TauCeti.Algebra.Module.Equiv.Basic

/-!
# Subalgebras over different base rings, restrictions to ranges, and division by natural numbers

Mathlib's `Subalgebra.equivOfEq` identifies two equal subalgebras of an algebra `A` over one and
the same base ring `R`. Two subalgebras of `A` over *different* base rings cannot be equal, since
they live in different types, but they can still have the same underlying set, and then they are
the same subsemiring of `A`. This file records the resulting ring isomorphism, which is
`RingEquiv.subsemiringCongr` on the underlying subsemirings, together with the fact that it is
compatible with the two inclusions into `A`.

It also provides the generic range-restriction maps `AlgHom.rangeMap` and `AlgEquiv.rangeMap`,
restricting `φ : B →ₐ[R] B'` (respectively `e : B ≃ₐ[R] B'`) from `α.range` onto `(φ.comp α).range`
(respectively `((e : B →ₐ[R] B').comp α).range`) for any `α : H →ₐ[R] B`.

Transporting the ambient algebra by an algebra equivalence is semilinear over the induced
equivalence of a subalgebra with its image.

A subalgebra over `K` is also closed under division by a natural number `m` that is a unit in `K`:
it contains `m * t` exactly when it contains `t`.

## Main results

* `Subalgebra.equivMapSemilinear`: ambient semilinear transport over the equivalence of a
  subalgebra with its image.

* `Subalgebra.ringEquivOfSetEq`: the ring isomorphism between two subalgebras of `A`, over possibly
  different base rings, with the same underlying set.
* `Subalgebra.coe_ringEquivOfSetEq_apply` and `Subalgebra.coe_ringEquivOfSetEq_symm_apply`: the
  isomorphism and its inverse commute with the inclusions into `A`.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
* `AlgHom.rangeMap`, `AlgHom.coe_rangeMap_apply`, `AlgHom.rangeMap_surjective`: surjective
  restriction `α.range →ₐ[R] (φ.comp α).range` of an algebra homomorphism `φ : B →ₐ[R] B'`.
* `AlgEquiv.rangeMap`, `AlgEquiv.coe_rangeMap_apply`, `AlgEquiv.coe_rangeMap_symm_apply`:
  restriction `α.range ≃ₐ[R] ((e : B →ₐ[R] B').comp α).range` of an algebra equivalence
  `e : B ≃ₐ[R] B'`.
-/

public section

namespace Subalgebra

section Transport

variable {R D E : Type*} [CommSemiring R] [Semiring D] [Semiring E]
  [Algebra R D] [Algebra R E]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Transport the ambient algebra semilinearly over the induced equivalence of subalgebras. -/
def equivMapSemilinear (O : Subalgebra R D) (f : D ≃ₐ[R] E) :
    D ≃ₛₗ[((f.subalgebraMap O).toRingEquiv : O →+* O.map f.toAlgHom)] E :=
  { f.toEquiv with
    map_add' := f.map_add
    map_smul' := fun b x => by
      -- Expose the algebra-equivalence projection so its image-coercion equation applies.
      change f (b • x) = (f.subalgebraMap O b) • f x
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [AlgEquiv.subalgebraMap_apply_coe] }

/-- The ambient semilinear transport acts by the original algebra equivalence. -/
@[simp↓]
theorem equivMapSemilinear_apply (O : Subalgebra R D) (f : D ≃ₐ[R] E) (x : D) :
    O.equivMapSemilinear f x = f x := by rfl

/-- The inverse ambient semilinear transport acts by the inverse algebra equivalence. -/
@[simp↓]
theorem equivMapSemilinear_symm_apply (O : Subalgebra R D) (f : D ≃ₐ[R] E) (y : E) :
    (O.equivMapSemilinear f).symm y = f.symm y := by rfl

/-- Pointwise ambient transport over the induced equivalence of a subalgebra with its image. -/
def equivMapPiSemilinear (O : Subalgebra R D) (f : D ≃ₐ[R] E) (ι : Type*) :=
  LinearEquiv.piCongrRightₛₗ (fun _ : ι => O.equivMapSemilinear f)

/-- Pointwise ambient transport applies the algebra equivalence at each coordinate. -/
@[simp↓]
theorem equivMapPiSemilinear_apply (O : Subalgebra R D) (f : D ≃ₐ[R] E)
    {ι : Type*} (x : ι → D) (i : ι) : O.equivMapPiSemilinear f ι x i = f (x i) := by
  simp only [equivMapPiSemilinear, LinearEquiv.piCongrRightₛₗ_apply, equivMapSemilinear_apply]

/-- Inverse pointwise ambient transport applies the inverse algebra equivalence. -/
@[simp↓]
theorem equivMapPiSemilinear_symm_apply (O : Subalgebra R D) (f : D ≃ₐ[R] E)
    {ι : Type*} (x : ι → E) (i : ι) :
    (O.equivMapPiSemilinear f ι).symm x i = f.symm (x i) := by
  simp only [equivMapPiSemilinear, LinearEquiv.piCongrRightₛₗ_symm_apply,
    equivMapSemilinear_symm_apply]

end Transport

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

/-- A subalgebra over `K` contains `m * t` exactly when it contains `t`, provided the natural
number `m` is invertible in `K`. -/
theorem natCast_mul_mem_iff {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    (T : Subalgebra K L) {m : ℕ} (hm : IsUnit (m : K)) {t : L} : (m : L) * t ∈ T ↔ t ∈ T := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem_iff_of_isUnit (Subalgebra.toSubmodule T) hm

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
    (φ.rangeMap α x : B') = φ x.val := by
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
    (e.rangeMap α x : B') = e x.val := by
  simp [rangeMap]

/-- Applying `(e.rangeMap α).symm` acts by `e.symm` on underlying elements. -/
@[simp]
theorem coe_rangeMap_symm_apply (e : B ≃ₐ[R] B') (α : H →ₐ[R] B)
    (y : ((e : B →ₐ[R] B').comp α).range) :
    ((e.rangeMap α).symm y : B) = e.symm y.val := by
  apply e.injective
  rw [e.apply_symm_apply, ← coe_rangeMap_apply]
  exact congrArg Subtype.val ((e.rangeMap α).apply_symm_apply y)

end AlgEquiv
