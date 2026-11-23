/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.LinearAlgebra.BilinearForm.Flip

/-!
# Central exponents for a bilinear twist

Opposite powers of a unit define an exponent subgroup before any torus algebra is built.
The subgroup is the kernel of the skew part when the unit has infinite order. For an
alternating integral form it is the radical when the parameter square has infinite order.

## Reference

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Proposition 11.2.
-/

public section

namespace Units

variable {R L : Type*} [Monoid R] [AddCommGroup L]

/-- The exponents for which the opposite powers of a scalar unit agree against every test
exponent. When a based quantum torus exists, these are exactly its central monomials. -/
def quantumTorusCentralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) : AddSubgroup L :=
  ⨅ b : L, (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ.flip b).toAddMonoidHom).eqLocus
    (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ b).toAddMonoidHom)

/-- Membership in the central exponent subgroup is equality of opposite powers. -/
@[simp]
theorem mem_quantumTorusCentralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ (Λ a b) = u ^ (Λ b a) := by
  rw [quantumTorusCentralExponents, AddSubgroup.mem_iInf]
  constructor
  · intro h b
    have hb := AddMonoidHom.mem_eqLocusM.mp (h b)
    simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditiveRight,
      Function.comp_apply, LinearMap.toAddMonoidHom_coe, zpowersHom_apply] at hb
    have hf : (Λ.flip b) a = Λ a b := LinearMap.flip_apply Λ a b
    rw [hf] at hb
    exact Additive.ofMul.injective hb
  · intro h b
    apply AddMonoidHom.mem_eqLocusM.mpr
    simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditiveRight,
      Function.comp_apply, LinearMap.toAddMonoidHom_coe, zpowersHom_apply]
    have hf : (Λ.flip b) a = Λ a b := LinearMap.flip_apply Λ a b
    rw [hf]
    exact congrArg Additive.ofMul (h b)

/-- The skew part of any bilinear form detects central exponents, including at finite order. -/
theorem mem_quantumTorusCentralExponents_iff (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ ((Λ - Λ.flip) a b) = 1 := by
  rw [mem_quantumTorusCentralExponents]
  apply forall_congr'
  intro b
  have hf : (Λ.flip a) b = Λ b a := LinearMap.flip_apply Λ b a
  simp only [LinearMap.sub_apply]
  rw [hf, zpow_sub, _root_.mul_inv_eq_one]

/-- An infinite-order parameter makes the central exponent subgroup the kernel of the skew part. -/
theorem quantumTorusCentralExponents_eq_ker (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (hu : ¬ IsOfFinOrder u) :
    u.quantumTorusCentralExponents Λ = (LinearMap.ker (Λ - Λ.flip)).toAddSubgroup := by
  ext a
  rw [mem_quantumTorusCentralExponents_iff, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  constructor
  · intro h
    ext b
    exact (injective_zpow_iff_not_isOfFinOrder.mpr hu)
      ((h b).trans (zpow_zero u).symm)
  · intro h b
    rw [LinearMap.congr_fun h b]
    exact zpow_zero u

end Units

namespace LinearMap.BilinForm.IsAlt

variable {R L : Type*} [Monoid R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- For an alternating form, central exponents are detected by the commutation factors.
The parameter may have finite order. -/
theorem mem_quantumTorusCentralExponents_iff (hΛ : Λ.IsAlt) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ (2 * Λ a b) = 1 := by
  simp only [Units.mem_quantumTorusCentralExponents_iff, sub_flip_apply_eq_two_mul hΛ]

/-- For an alternating form and a parameter whose square has infinite order, the central
exponent subgroup is the radical of the form. -/
theorem quantumTorusCentralExponents_eq_ker (hΛ : Λ.IsAlt) (hu : ¬ IsOfFinOrder (u ^ 2)) :
    u.quantumTorusCentralExponents Λ = (LinearMap.ker Λ).toAddSubgroup := by
  rw [Units.quantumTorusCentralExponents_eq_ker u Λ (fun h ↦ hu h.pow)]
  ext a
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  constructor
  · intro h
    ext b
    have h' := LinearMap.congr_fun h b
    simp only [sub_flip_apply_eq_two_mul hΛ, LinearMap.zero_apply] at h' ⊢
    omega
  · intro h
    ext b
    simp only [sub_flip_apply_eq_two_mul hΛ, LinearMap.congr_fun h b, LinearMap.zero_apply,
      mul_zero]

end LinearMap.BilinForm.IsAlt
