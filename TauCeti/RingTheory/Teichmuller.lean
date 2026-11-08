/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Teichmuller

/-!
# Coordinates of the inverse of reduction on perfection

The inverse of `Perfection.quotientMulEquiv` commutes with shifting compatible root sequences.
Its `n`-th coordinate is therefore the Teichmüller map applied after `n` shifts. These formulas
extend Mathlib's zeroth-coordinate formula `Perfection.coeff_zero_symm_quotientMulEquiv`.
-/

public section

namespace Perfection

variable {p : ℕ} {R : Type*} [CommRing R] [Fact p.Prime] {I : Ideal R}
  [CharP (R ⧸ I) p] [IsAdicComplete I R]

/-- The inverse of reduction on perfection commutes with shifting the root sequence. -/
theorem semiconj_symm_quotientMulEquiv_pthRootMonoidHom :
    Function.Semiconj (quotientMulEquiv p I).symm
      (pthRootMonoidHom (R ⧸ I) p) (pthRootMonoidHom R p) := by
  intro y
  apply (quotientMulEquiv p I).injective
  have hfwd (z : Perfection R p) :
      quotientMulEquiv p I (pthRootMonoidHom R p z) =
        pthRootMonoidHom (R ⧸ I) p (quotientMulEquiv p I z) := by
    apply Perfection.ext
    intro n
    simp only [coeff_quotientMulEquiv, coeffMonoidHom_pthRootMonoidHom,
      pthRootMonoidHom_eq_pthRoot, coe_pthRoot_eq_symm_frobeniusEquiv,
      coeff_symm_frobeniusEquiv]
  rw [hfwd, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The `n`-th coordinate of inverse reduction is Teichmüller after `n` shifts. -/
@[simp]
theorem coeffMonoidHom_symm_quotientMulEquiv (x : Perfection (R ⧸ I) p) (n : ℕ) :
    coeffMonoidHom R p n ((quotientMulEquiv p I).symm x) =
      teichmuller₀ p I ((pthRootMonoidHom (R ⧸ I) p)^[n] x) := by
  have hc := coeffMonoidHom_iterate_symm_powMulEquiv
    ((quotientMulEquiv p I).symm x) 0 n
  rw [Nat.zero_add, ← coe_pthRootMonoidHom_eq_powMulEquiv_symm,
    ← semiconj_symm_quotientMulEquiv_pthRootMonoidHom.iterate_right n x,
    coeff_zero_symm_quotientMulEquiv] at hc
  exact hc.symm

end Perfection
