/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Germ
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Residue duality for the order filtration of meromorphic germs

In the coordinate `z - a`, the pairing of meromorphic function germs with coefficients of
meromorphic differentials is `(φ, ψ) ↦ Res_a(φ ψ dz)`. Its annihilator of the lattice of germs
of order at least `n` is exactly the lattice of order at least `-n`. In particular the
holomorphic lattice is its own annihilator. The sign comes from the fact that residue reads
order `-1`, whereas a product of nonnegative order has zero residue.

Consequently residue descends to a nondegenerate pairing between the order windows
`orderGE a n / orderGE a m` and `orderGE a (-m) / orderGE a (-n)`. The quotients below use
comaps to regard the denominator as a submodule of the numerator. For `n ≤ m` these are the
usual quotients of nested lattices. For example, principal parts with poles of order at
most `N` pair with holomorphic differential coefficients modulo those vanishing to order `N`.
These are the local annihilator and nondegeneracy statements used in residue duality for
divisor sheaves; no global cohomological duality is asserted here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, GTM 81, §17 (residue duality).
-/

public noncomputable section

namespace TauCeti.meromorphicGerms

variable {a : ℂ}

/-- The residue pairing of a meromorphic function germ and a meromorphic differential
coefficient, in the coordinate `z - a`. -/
def residuePairing (a : ℂ) : LinearMap.BilinForm ℂ (meromorphicGerms ℂ a) :=
  (LinearMap.mul ℂ (meromorphicGerms ℂ a)).compr₂ (residue a)

/-- The pairing is the residue of the product, not the residue of `φ dψ`. -/
@[simp]
theorem residuePairing_apply (φ ψ : meromorphicGerms ℂ a) :
    residuePairing a φ ψ = residue a (φ * ψ) :=
  (rfl)

/-- Multiplication of differential coefficients makes the residue pairing symmetric. -/
theorem residuePairing_isSymm (a : ℂ) : (residuePairing a).IsSymm :=
  ⟨fun φ ψ ↦ congrArg (residue a) (mul_comm φ ψ)⟩

/-- A product of germs whose orders have nonnegative sum has zero residue. -/
theorem residue_mul_eq_zero_of_mem_orderGE {φ ψ : meromorphicGerms ℂ a} {n m : ℤ}
    (hφ : φ ∈ orderGE a n) (hψ : ψ ∈ orderGE a m) (hnm : 0 ≤ n + m) :
    residue a (φ * ψ) = 0 := by
  have hprod : φ * ψ ∈ orderGE a 0 := by
    rw [mem_orderGE, order_mul]
    exact (WithTop.coe_le_coe.mpr hnm).trans
      (by simpa only [WithTop.coe_add] using
        add_le_add ((mem_orderGE _ _).1 hφ) ((mem_orderGE _ _).1 hψ))
  exact (residue_eq_zero_iff_of_mem_orderGE_neg_one _
    (orderGE_antitone a (by omega) hprod)).2 hprod

/-- **The annihilator of an order lattice.** A germ pairs to zero with every germ of order
at least `n` exactly when its own order is at least `-n`. -/
theorem forall_residue_mul_eq_zero_iff (φ : meromorphicGerms ℂ a) (n : ℤ) :
    (∀ ψ ∈ orderGE a n, residue a (ψ * φ) = 0) ↔ φ ∈ orderGE a (-n) := by
  refine ⟨fun h ↦ ?_, fun hφ ψ hψ ↦
    residue_mul_eq_zero_of_mem_orderGE hψ hφ (by omega)⟩
  by_contra hφ
  cases ho : order φ with
  | top => simp [mem_orderGE, ho] at hφ
  | coe j =>
    have hj : j < -n := by simpa only [mem_orderGE, ho, WithTop.coe_le_coe, not_le] using hφ
    let ψ := coordinate a ^ (-j - 1)
    have hψ : ψ ∈ orderGE a n := by
      simp only [mem_orderGE, ψ, order_coordinate_zpow, WithTop.coe_le_coe]
      omega
    have hord : order (ψ * φ) = (-1 : ℤ) := by
      rw [order_mul, ho, order_coordinate_zpow, ← WithTop.coe_add]
      congr 1
      omega
    have hrem := (residue_eq_zero_iff_of_mem_orderGE_neg_one (ψ * φ)
      (by simp [mem_orderGE, hord])).1 (h ψ hψ)
    have hbad : (0 : ℤ) ≤ -1 := by
      exact_mod_cast (mem_orderGE _ _).1 hrem |>.trans_eq hord
    omega

/-- The orthogonal complement is computed using Mathlib's bilinear-form orthogonal. -/
@[simp]
theorem orthogonal_residuePairing_orderGE (a : ℂ) (n : ℤ) :
    (residuePairing a).orthogonal (orderGE a n) = orderGE a (-n) := by
  ext φ
  exact LinearMap.BilinForm.mem_orthogonal_iff.trans
    (forall_residue_mul_eq_zero_iff φ n)

/-- **Nondegeneracy on all meromorphic germs.** A nonzero germ can be tested against its
inverse times the reciprocal coordinate; their product has residue one. -/
theorem residuePairing_nondegenerate (a : ℂ) : (residuePairing a).Nondegenerate := by
  have hleft : (residuePairing a).SeparatingLeft := by
    intro φ hφ
    by_contra hne
    have h := hφ (φ⁻¹ * (coordinate a)⁻¹)
    simp [hne] at h
  exact ⟨hleft, fun φ hφ ↦ hleft φ fun ψ ↦ by
    simpa only [residuePairing_apply, mul_comm] using hφ ψ⟩

/-! ## Pairing quotient windows -/

/-- The quotient of two order bounds, with the denominator viewed in the numerator.
For `n ≤ m` it consists of the coefficients of orders `n, …, m - 1`. -/
abbrev OrderWindow (a : ℂ) (n m : ℤ) :=
  orderGE a n ⧸ (orderGE a m).comap (orderGE a n).subtype

private def residuePairingRestrict (a : ℂ) (n m : ℤ) :
    orderGE a n →ₗ[ℂ] orderGE a (-m) →ₗ[ℂ] ℂ :=
  (residuePairing a).compl₁₂ (orderGE a n).subtype (orderGE a (-m)).subtype

/-- Residue pairs an order window with the complementary window of differential
coefficients. Changing either representative by its denominator does not change the residue. -/
def orderWindowResiduePairing (a : ℂ) (n m : ℤ) :
    OrderWindow a n m →ₗ[ℂ] OrderWindow a (-m) (-n) →ₗ[ℂ] ℂ :=
  (residuePairingRestrict a n m).liftQ₂ _ _
    (fun φ hφ ↦ LinearMap.ext fun ψ ↦
      residue_mul_eq_zero_of_mem_orderGE hφ ψ.2 (by omega))
    (fun ψ hψ ↦ LinearMap.ext fun φ ↦
      residue_mul_eq_zero_of_mem_orderGE φ.2 hψ (by omega))

/-- On representatives, the quotient pairing is the residue of their product. -/
@[simp]
theorem orderWindowResiduePairing_mk (n m : ℤ) (φ : orderGE a n) (ψ : orderGE a (-m)) :
    orderWindowResiduePairing a n m (Submodule.Quotient.mk φ) (Submodule.Quotient.mk ψ) =
      residue a (φ.1 * ψ.1) :=
  (rfl)

/-- **Nondegeneracy of the quotient residue pairing.** Both radicals vanish, without any
restriction on the signs of the order bounds. -/
theorem orderWindowResiduePairing_nondegenerate (a : ℂ) (n m : ℤ) :
    (orderWindowResiduePairing a n m).Nondegenerate := by
  constructor
  · intro φ hφ
    induction φ using Submodule.Quotient.induction_on with
    | _ φ =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have h := (forall_residue_mul_eq_zero_iff φ.1 (-m)).1 fun ψ hψ ↦ by
        simpa only [orderWindowResiduePairing_mk, mul_comm] using
          hφ (Submodule.Quotient.mk (⟨ψ, hψ⟩ : orderGE a (-m)))
      simpa only [Submodule.mem_comap, Submodule.subtype_apply, neg_neg] using h
  · intro ψ hψ
    induction ψ using Submodule.Quotient.induction_on with
    | _ ψ =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (forall_residue_mul_eq_zero_iff ψ.1 n).1 fun φ hφ ↦ by
        simpa only [LinearMap.flip_apply, orderWindowResiduePairing_mk] using
          hψ (Submodule.Quotient.mk (⟨φ, hφ⟩ : orderGE a n))

end TauCeti.meromorphicGerms
