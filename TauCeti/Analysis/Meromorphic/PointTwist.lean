/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Germ
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The local quotient of a point twist

For every integer `n`, the coefficient of `(z-a)^n` identifies the quotient of meromorphic
germs of order at least `n` by those of order at least `n+1` with `ℂ`. It is computed as the
residue after multiplication by `(z-a)^(-n-1)`. This avoids choosing the value of a
meromorphic representative at its centre.

For divisor sheaves, take `n = -D(P)-1`: this is the local quotient in the point-twist sequence
`0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0`. The results here concern germs in a coordinate; they do not
assert exactness or any cohomology statement for that sheaf sequence.

## Main declarations

* `TauCeti.meromorphicGerms.coeff`: coefficient extraction on an order-filtration step.
* `TauCeti.meromorphicGerms.ker_coeff`: its kernel is the next step.
* `TauCeti.meromorphicGerms.orderGEQuotientEquiv`: the quotient is one-dimensional, with
  inverse represented by coordinate monomials.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1 and 16.
-/

public noncomputable section

namespace TauCeti.meromorphicGerms

variable {a : ℂ}

/-- The coefficient of `(z-a)^n`, read as the residue of `(z-a)^(-n-1) φ`. -/
def coeff (a : ℂ) (n : ℤ) : orderGE a n →ₗ[ℂ] ℂ :=
  (residue a).comp ((LinearMap.mulLeft ℂ (coordinate a ^ (-n - 1))).comp (orderGE a n).subtype)

/-- Coefficient extraction is the residue after the indicated coordinate shift. -/
theorem coeff_apply (n : ℤ) (φ : orderGE a n) :
    coeff a n φ = residue a (coordinate a ^ (-n - 1) * φ.1) := (rfl)

/-- The coefficient vanishes exactly when the order increases by at least one. -/
@[simp]
theorem coeff_eq_zero_iff (n : ℤ) (φ : orderGE a n) :
    coeff a n φ = 0 ↔ φ.1 ∈ orderGE a (n + 1) := by
  have hbound : coordinate a ^ (-n - 1) * φ.1 ∈ orderGE a (-1) := by
    have h := (coordinate_zpow_mul_mem_orderGE_iff φ.1 (-n - 1) n).mpr φ.2
    have hexp : -n - 1 + n = -1 := by omega
    rwa [hexp] at h
  rw [coeff_apply, residue_eq_zero_iff_of_mem_orderGE_neg_one _ hbound,
    mem_orderGE, order_mul, order_coordinate_zpow, mem_orderGE, WithTop.coe_zero]
  cases h : order φ.1 with
  | top => simp
  | coe j =>
    have hint : 0 ≤ -n - 1 + j ↔ n + 1 ≤ j := by omega
    simpa only [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] using hint

/-- Coefficient extraction recovers the scalar of a coordinate monomial. -/
@[simp]
theorem coeff_monomial (n : ℤ) (c : ℂ) : coeff a n (monomial a n c) = c := by
  have hexp : -n - 1 + n = -1 := by omega
  rw [coeff_apply, coe_monomial, mul_smul_comm, map_smul,
    ← zpow_add₀ (coordinate_ne_zero a), hexp, zpow_neg_one, residue_coordinate_inv,
    smul_eq_mul, mul_one]

/-- Every scalar occurs as a coefficient at every integer order bound. -/
theorem coeff_surjective (a : ℂ) (n : ℤ) : Function.Surjective (coeff a n) :=
  fun c ↦ ⟨monomial a n c, coeff_monomial n c⟩

/-- The kernel is the next filtration step, viewed inside the current step. -/
theorem ker_coeff (a : ℂ) (n : ℤ) :
    LinearMap.ker (coeff a n) = (orderGE a (n + 1)).comap (orderGE a n).subtype := by
  ext φ
  exact coeff_eq_zero_iff n φ

/-- **The local point-twist quotient.** Consecutive order bounds on meromorphic germs differ by
one complex parameter, the coefficient of `(z-a)^n`. -/
def orderGEQuotientEquiv (a : ℂ) (n : ℤ) :
    (orderGE a n ⧸ (orderGE a (n + 1)).comap (orderGE a n).subtype) ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ (ker_coeff a n).symm).trans
    ((coeff a n).quotKerEquivOfSurjective (coeff_surjective a n))

@[simp]
theorem orderGEQuotientEquiv_apply_mk (n : ℤ) (φ : orderGE a n) :
    orderGEQuotientEquiv a n (Submodule.Quotient.mk φ) = coeff a n φ := by
  simp [orderGEQuotientEquiv]

/-- The inverse sends a scalar to the class of its coordinate monomial. -/
@[simp]
theorem orderGEQuotientEquiv_symm_apply (n : ℤ) (c : ℂ) :
    (orderGEQuotientEquiv a n).symm c = Submodule.Quotient.mk (monomial a n c) := by
  apply (orderGEQuotientEquiv a n).injective
  simp

end TauCeti.meromorphicGerms
