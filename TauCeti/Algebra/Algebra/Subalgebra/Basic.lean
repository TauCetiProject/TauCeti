/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Subalgebras over different base rings, and division by natural numbers

Mathlib's `Subalgebra.equivOfEq` identifies two equal subalgebras of an algebra `A` over one and
the same base ring `R`. Two subalgebras of `A` over *different* base rings cannot be equal, since
they live in different types, but they can still have the same underlying set, and then they are
the same subsemiring of `A`. This file records the resulting ring isomorphism, which is
`RingEquiv.subsemiringCongr` on the underlying subsemirings, together with the fact that it is
compatible with the two inclusions into `A`.

A subalgebra over `K` is also closed under division by a natural number `m` that is a unit in `K`:
it contains `m * t` exactly when it contains `t`.

## Main results

* `Subalgebra.ringEquivOfSetEq`: the ring isomorphism between two subalgebras of `A`, over possibly
  different base rings, with the same underlying set.
* `Subalgebra.coe_ringEquivOfSetEq_apply` and `Subalgebra.coe_ringEquivOfSetEq_symm_apply`: the
  isomorphism and its inverse commute with the inclusions into `A`.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
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

/-- A subalgebra over `K` contains `m * t` exactly when it contains `t`, provided the natural
number `m` is invertible in `K`. -/
theorem natCast_mul_mem_iff {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    (T : Subalgebra K L) {m : ℕ} (hm : IsUnit (m : K)) {t : L} : (m : L) * t ∈ T ↔ t ∈ T := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem_iff_of_isUnit (Subalgebra.toSubmodule T) hm

end Subalgebra
