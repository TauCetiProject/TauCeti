/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Subalgebras over different base rings with the same underlying set

Mathlib's `Subalgebra.equivOfEq` identifies two equal subalgebras of an algebra `A` over one and
the same base ring `R`. Two subalgebras of `A` over *different* base rings cannot be equal, since
they live in different types, but they can still have the same underlying set, and then they are
the same subring of `A`. This file records the resulting ring isomorphism, which is
`RingEquiv.subringCongr` on the underlying subrings, together with the fact that it is compatible
with the two inclusions into `A`.

## Main results

* `Subalgebra.ringEquivOfSetEq`: the ring isomorphism between two subalgebras of `A`, over possibly
  different base rings, with the same underlying set.
* `Subalgebra.coe_ringEquivOfSetEq_apply` and `Subalgebra.coe_ringEquivOfSetEq_symm_apply`: the
  isomorphism and its inverse commute with the inclusions into `A`.
-/

public section

namespace Subalgebra

variable {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [Ring A] [Algebra R₁ A] [Algebra R₂ A]

/-- Two subalgebras of `A`, over possibly different base rings, with the same underlying set are
isomorphic as rings: the identity of `A` restricted to that set. This is the counterpart of
`Subalgebra.equivOfEq` for subalgebras over different base rings, and is `RingEquiv.subringCongr`
on the underlying subrings. -/
def ringEquivOfSetEq (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A) (h : (S₁ : Set A) = S₂) :
    S₁ ≃+* S₂ :=
  RingEquiv.subringCongr (s := S₁.toSubring) (t := S₂.toSubring) (SetLike.ext' h)

@[simp]
theorem coe_ringEquivOfSetEq_apply (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) = S₂) (a : S₁) : (ringEquivOfSetEq S₁ S₂ h a : A) = a :=
  (rfl)

@[simp]
theorem coe_ringEquivOfSetEq_symm_apply (S₁ : Subalgebra R₁ A) (S₂ : Subalgebra R₂ A)
    (h : (S₁ : Set A) = S₂) (b : S₂) : ((ringEquivOfSetEq S₁ S₂ h).symm b : A) = b :=
  (rfl)

end Subalgebra
