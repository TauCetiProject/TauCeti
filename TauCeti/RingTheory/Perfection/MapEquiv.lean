/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfection

/-!
# Perfection of a ring isomorphism

A ring isomorphism `e : R ≃+* S` of semirings of characteristic `p` induces a ring isomorphism
`Perfection R p ≃+* Perfection S p`, acting on coordinates by `e`, with inverse induced by
`e.symm`. It upgrades Mathlib's `Perfection.map` to ring isomorphisms.

## Main definitions

* `Perfection.mapEquiv`: the ring isomorphism of perfections induced by a ring isomorphism.
-/

public section

namespace Perfection

variable (p : ℕ) [Fact p.Prime] {R S : Type*} [CommSemiring R] [CharP R p] [CommSemiring S]
  [CharP S p]

/-- The ring isomorphism `Perfection R p ≃+* Perfection S p` induced by a ring isomorphism
`e : R ≃+* S`, acting on coordinates by `e`. -/
def mapEquiv (e : R ≃+* S) : Perfection R p ≃+* Perfection S p where
  __ := map p (e : R →+* S)
  invFun := map p (e.symm : S →+* R)
  left_inv x := ext fun n ↦ by simp
  right_inv y := ext fun n ↦ by simp

variable {p}

@[simp]
theorem mapEquiv_apply (e : R ≃+* S) (x : Perfection R p) :
    mapEquiv p e x = map p (e : R →+* S) x :=
  (rfl)

@[simp]
theorem mapEquiv_symm (e : R ≃+* S) : (mapEquiv p e).symm = mapEquiv p e.symm :=
  (rfl)

theorem coeff_mapEquiv (e : R ≃+* S) (x : Perfection R p) (n : ℕ) :
    coeff S p n (mapEquiv p e x) = e (coeff R p n x) :=
  coeff_map p _ x n

end Perfection
