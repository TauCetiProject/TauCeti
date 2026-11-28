/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basis
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Counting Bessel coordinates of symmetric-power type

In the Poincaré construction for a theta lift, each distinguished infinite place contributes
coordinates from a degree-`a` symmetric power of the standard module. The other places have
weight zero and contribute just one coordinate each. This gives a bound on the total number
of coordinates in the product of the local systems, for use in the unfolded second moment.

The theta-lift specialization is `New.Data.card_besselCoord_le_pow` in
`grh/src/New/Spanning/Unfolding/FillingAdmissible.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead1/grh
-/

public section

open scoped TensorProduct

namespace TauCeti.ThetaLift

variable {R : Type*} [CommSemiring R] [StrongRankCondition R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {I : ι → Type*} [∀ v, Fintype (I v)] {k a : ℕ} {S : Finset ι}

/-- The number of global coordinates is the product of the local dimensions. If the local
spaces have symmetric-power degree `a` on `S` and degree zero elsewhere, only the places in
`S` contribute a factor to this product. -/
theorem card_besselCoord_eq (e : ∀ v, (I v → R) ≃ₗ[R]
    Sym[R]^(if v ∈ S then a else 0)(Fin k → R)) :
    Fintype.card (∀ v, I v) = (k.multichoose a) ^ S.card := by
  have hdim (v : ι) : Fintype.card (I v) = if v ∈ S then k.multichoose a else 1 := by
    have h := (e v).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, SymmetricPower.finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    by_cases hv : v ∈ S <;> simpa [hv, Nat.multichoose_zero_right] using h
  simp only [Fintype.card_pi, hdim, Fintype.prod_ite_mem, Finset.prod_const]

/-- At degree `a` with `a + 1 ≤ b²`, the number of coordinates is at most
`b ^ (2 * (k - 1) * #S)`, where `k` is the source rank and `S` is the set of distinguished
places. For the weight `a = x * b`, the degree bound follows from `x < b`. -/
theorem card_besselCoord_le_pow (e : ∀ v, (I v → R) ≃ₗ[R]
    Sym[R]^(if v ∈ S then a else 0)(Fin k → R)) {b : ℕ} (ha : a + 1 ≤ b ^ 2) :
    Fintype.card (∀ v, I v) ≤ b ^ (2 * (k - 1) * S.card) := by
  rw [card_besselCoord_eq e, pow_mul, pow_mul]
  refine Nat.pow_le_pow_left ?_ _
  have h : k.multichoose a ≤ (a + 1) ^ (k - 1) := by
    cases k with
    | zero => cases a <;> simp
    | succ j =>
      rw [Nat.multichoose_eq, Nat.succ_add_sub_one, Nat.add_comm j a, Nat.choose_symm_add]
      exact Nat.choose_add_le_add_one_pow a j
  exact h.trans (Nat.pow_le_pow_left ha _)

end TauCeti.ThetaLift
