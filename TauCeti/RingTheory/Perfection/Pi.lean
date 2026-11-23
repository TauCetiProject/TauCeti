/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Pi
public import Mathlib.RingTheory.Perfection

/-!
# Perfections of products

Perfections are computed coordinatewise: for a nonempty family of commutative semirings `R i` of
characteristic `p`, the perfections of the projections give a ring isomorphism
`Perfection (∀ i, R i) p ≃+* ∀ i, Perfection (R i) p`, under which the `n`-th coordinate of a
family is the family of `n`-th coordinates. The family is assumed nonempty so that the product
has characteristic `p` (`Pi.instCharP`).

## Main definitions

* `Perfection.piEquiv`: `Perfection (∀ i, R i) p ≃+* ∀ i, Perfection (R i) p`.

## Main results

* `Perfection.coeff_piEquiv_apply`, `Perfection.coeff_piEquiv_symm`: coordinates under
  `Perfection.piEquiv`.
-/

public section

variable {ι : Type*} [Nonempty ι]

namespace Perfection

variable (p : ℕ) [Fact p.Prime] {R : ι → Type*} [∀ i, CommSemiring (R i)] [∀ i, CharP (R i) p]

/-- **Perfections commute with products**: `Perfection (∀ i, R i) p ≃+* ∀ i, Perfection (R i) p`,
by the perfections of the projections; coordinates are taken coordinatewise. -/
def piEquiv : Perfection (∀ i, R i) p ≃+* ∀ i, Perfection (R i) p where
  __ := RingHom.pi fun i ↦ map p (Pi.evalRingHom R i)
  invFun y := ⟨fun n i ↦ coeff (R i) p n (y i), fun n ↦ funext fun i ↦ by
    rw [Pi.pow_apply, coeff_pow_p']⟩
  left_inv x := ext fun n ↦ funext fun i ↦ by simp [coeff_mk]
  right_inv y := funext fun i ↦ ext fun n ↦ by
    refine (coeff_map p (Pi.evalRingHom R i) _ n).trans ?_
    simp [coeff_mk]

variable {p}

@[simp]
theorem piEquiv_apply (x : Perfection (∀ i, R i) p) (i : ι) :
    piEquiv p x i = map p (Pi.evalRingHom R i) x :=
  (rfl)

theorem coeff_piEquiv_apply (x : Perfection (∀ i, R i) p) (i : ι) (n : ℕ) :
    coeff (R i) p n (piEquiv p x i) = coeff _ p n x i := by
  rw [piEquiv_apply, coeff_map, Pi.evalRingHom_apply]

@[simp]
theorem coeff_piEquiv_symm (y : ∀ i, Perfection (R i) p) (n : ℕ) :
    coeff _ p n ((piEquiv p).symm y) = fun i ↦ coeff (R i) p n (y i) :=
  funext fun i ↦ by rw [← coeff_piEquiv_apply, RingEquiv.apply_symm_apply]

end Perfection
