/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Data.Finset.NoncommProd

/-!
# One-point families in `Multiplicative (ι → M)`

Mathlib's `MulEquiv.funMultiplicative ι M : Multiplicative (ι → M) ≃* (ι → Multiplicative M)`
regroups a multiplicatively written family of additive elements as a family of multiplicative
elements. It sends the additive one-point family `Pi.single i r` to the multiplicative one-point
family `Pi.mulSingle i (ofAdd r)`. Transporting `MonoidHom.pi_ext` along it, a monoid homomorphism
out of `Multiplicative (ι → M)`, into any monoid, is determined by its values on the one-point
families `ofAdd (Pi.single i r)`.

## Main results

* `MulEquiv.funMultiplicative_ofAdd_single`: the image of an additive one-point family.
* `MonoidHom.ext_ofAdd_single`: homomorphisms out of `Multiplicative (ι → M)` agreeing on
  one-point families are equal.
-/

public section

open Multiplicative (ofAdd toAdd)

variable {ι M : Type*} [DecidableEq ι] [AddMonoid M]

/-- `MulEquiv.funMultiplicative` sends the additive one-point family `Pi.single i r` to the
multiplicative one-point family `Pi.mulSingle i (ofAdd r)`. -/
theorem MulEquiv.funMultiplicative_ofAdd_single (i : ι) (r : M) :
    MulEquiv.funMultiplicative ι M (ofAdd (Pi.single i r)) = Pi.mulSingle i (ofAdd r) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h]

/-- Monoid homomorphisms out of `Multiplicative (ι → M)` agree when they agree on every one-point
family `ofAdd (Pi.single i r)`. The target need not be commutative. -/
theorem MonoidHom.ext_ofAdd_single [Finite ι] {N : Type*} [Monoid N]
    {f g : Multiplicative (ι → M) →* N}
    (h : ∀ i r, f (ofAdd (Pi.single i r)) = g (ofAdd (Pi.single i r))) : f = g := by
  refine (MonoidHom.cancel_right (f := (MulEquiv.funMultiplicative ι M).symm.toMonoidHom)
    (MulEquiv.funMultiplicative ι M).symm.surjective).mp <|
    MonoidHom.pi_ext fun i r ↦ ?_
  obtain ⟨r, rfl⟩ := ofAdd.surjective r
  simpa [← MulEquiv.funMultiplicative_ofAdd_single] using h i r
