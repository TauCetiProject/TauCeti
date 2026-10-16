/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.NumberTheory.QuadraticOrder.Basic
public import TauCeti.NumberTheory.QuadraticOrder.Product
public import TauCeti.Algebra.QuadraticAlgebra.Split
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Square-discriminant quadratic orders

For a nonzero integer `s`, the canonical order of discriminant `s²` is isomorphic to
`{(x, y) : ℤ × ℤ | s ∣ x - y}`. The isomorphism agrees with the rational splitting
at the two roots `s` and `-s`, so it identifies the actual embedded orders.

This transfers the congruence product order's unit count to the canonical order.
At discriminant one the order is the full integer product, with four units.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section
open QuadraticAlgebra
namespace TauCeti.QuadraticOrder

private theorem two_mul_sq_sub_ediv_two (s : ℤ) :
    2 * ((s ^ 2 - s) / 2) = s ^ 2 - s := by
  have h : (2 : ℤ) ∣ s ^ 2 - s := by
    simpa only [mul_sub, mul_one, ← pow_two] using (Int.even_mul_pred_self s).two_dvd
  exact Int.mul_ediv_cancel' h

private noncomputable def integralEquivProductModel (s : ℤ) :
    QuadraticAlgebra ℤ ((s ^ 2 - (s ^ 2) ^ 2) / 4) (s ^ 2) ≃ₐ[ℤ]
      QuadraticAlgebra ℤ 0 s :=
  QuadraticAlgebra.changeGeneratorEquiv 0 s 1 ((s ^ 2 - s) / 2)
    (by
      have hd := parameter_discr (s ^ 2) (by rw [Int.sq_emod_four]; omega)
      rw [QuadraticAlgebra.discr_def] at hd
      have hq := two_mul_sq_sub_ediv_two s
      simp only [Units.val_one, one_pow, mul_zero, one_mul, zero_sub]
      nlinarith [sq_nonneg (s ^ 2 - 2 * ((s ^ 2 - s) / 2) - s)])
    (by simp only [Units.val_one, one_mul]; have hq := two_mul_sq_sub_ediv_two s; omega)

private theorem integralEquivProductModel_apply (s : ℤ)
    (z : QuadraticAlgebra ℤ ((s ^ 2 - (s ^ 2) ^ 2) / 4) (s ^ 2)) :
    integralEquivProductModel s z = ⟨z.re + ((s ^ 2 - s) / 2) * z.im, z.im⟩ := by
  ext <;> simp [integralEquivProductModel, mul_comm]

/-- The canonical order of nonzero square discriminant is the integer congruence product order. -/
noncomputable def equivProductOfSq (s : ℤ) (hs : s ≠ 0) :
    toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega) ≃ₐ[ℤ] productSubalgebra s :=
  (equivToSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega)).symm.trans
    ((integralEquivProductModel s).trans (equivProductSubalgebra s hs))

/-- The rational quadratic algebra of a nonzero integer square splits at its two roots. -/
noncomputable def algEquivProdOfIntSq (s : ℤ) (hs : s ≠ 0) :
    QuadraticAlgebra ℚ ((s ^ 2 : ℤ) : ℚ) 0 ≃ₐ[ℚ] ℚ × ℚ := by
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)
  exact TauCeti.QuadraticAlgebra.algEquivProdOfSq (Units.mk0 (s : ℚ) (by exact_mod_cast hs))
    (by simp)

/-- The rational splitting evaluates at the opposite integer roots. -/
@[simp] theorem algEquivProdOfIntSq_apply (s : ℤ) (hs : s ≠ 0)
    (z : QuadraticAlgebra ℚ ((s ^ 2 : ℤ) : ℚ) 0) :
    algEquivProdOfIntSq s hs z = (z.re + s * z.im, z.re - s * z.im) := by
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)
  unfold algEquivProdOfIntSq
  exact _root_.QuadraticAlgebra.algEquivProdOfSq_apply _ _ _

private theorem coe_shift (s : ℤ) :
    (((s ^ 2 - s) / 2 : ℤ) : ℚ) = ((s : ℚ) ^ 2 - s) / 2 := by
  have h : (2 : ℚ) * (((s ^ 2 - s) / 2 : ℤ) : ℚ) = (s : ℚ) ^ 2 - s := by
    exact_mod_cast two_mul_sq_sub_ediv_two s
  linarith

/-- The order isomorphism evaluates the shifted integral generator in both coordinates. -/
@[simp] theorem coe_equivProductOfSq_apply (s : ℤ) (hs : s ≠ 0)
    (z : QuadraticAlgebra ℤ ((s ^ 2 - (s ^ 2) ^ 2) / 4) (s ^ 2)) :
    (equivProductOfSq s hs
      (equivToSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega) z) : ℤ × ℤ) =
      (z.re + (((s ^ 2 - s) / 2) + s) * z.im, z.re + ((s ^ 2 - s) / 2) * z.im) := by
  simp [equivProductOfSq, AlgEquiv.trans_apply, integralEquivProductModel_apply]
  ring

/-- The order isomorphism agrees with the rational splitting on its embedded elements. -/
theorem equivProductOfSq_commutes (s : ℤ) (hs : s ≠ 0)
    (z : toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega)) :
    algEquivProdOfIntSq s hs (z : QuadraticAlgebra ℚ ((s ^ 2 : ℤ) : ℚ) 0) =
      (((equivProductOfSq s hs z : ℤ × ℤ).1 : ℚ),
        ((equivProductOfSq s hs z : ℤ × ℤ).2 : ℚ)) := by
  obtain ⟨w, rfl⟩ := (equivToSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega)).surjective z
  rw [coe_equivToSubalgebra_apply, lift_apply, coe_equivProductOfSq_apply]
  ext <;> simp [Algebra.smul_def, coe_shift]
  all_goals ring

/-- The rational splitting identifies the embedded canonical order with the embedded congruence
product order. -/
theorem map_toSubalgebra_of_sq (s : ℤ) (hs : s ≠ 0) :
    (toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega)).map
      ((algEquivProdOfIntSq s hs).toAlgHom.restrictScalars ℤ) =
      (productSubalgebra s).map
        (AlgHom.prodMap (Algebra.ofId ℤ ℚ) (Algebra.ofId ℤ ℚ)) := by
  ext y
  rw [Subalgebra.mem_map, Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z : toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega) := ⟨x, hx⟩
    refine ⟨(equivProductOfSq s hs z : ℤ × ℤ),
      (equivProductOfSq s hs z).property, ?_⟩
    exact (equivProductOfSq_commutes s hs z).symm
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz⟩ := (equivProductOfSq s hs).surjective ⟨v, hv⟩
    refine ⟨z, z.property, ?_⟩
    have hvz : (equivProductOfSq s hs z : ℤ × ℤ) = v := congrArg Subtype.val hz
    rw [← hvz]
    exact equivProductOfSq_commutes s hs z

/-- The unit group of the square-discriminant order has cardinality four when `s ∣ 2`,
and two otherwise. -/
theorem card_units_toSubalgebra_sq (s : ℤ) (hs : s ≠ 0) :
    Nat.card (Units (toSubalgebra (s ^ 2) (by rw [Int.sq_emod_four]; omega))) =
      if s ∣ 2 then 4 else 2 := by
  rw [Nat.card_congr (Units.mapEquiv (equivProductOfSq s hs).toRingEquiv.toMulEquiv).toEquiv]
  exact card_units_productSubalgebra s

/-- At discriminant one the canonical order is the full integer product. -/
noncomputable def equivProdOfOne : toSubalgebra 1 (by decide) ≃ₐ[ℤ] ℤ × ℤ :=
  (equivProductOfSq 1 (by decide)).trans
    ((Subalgebra.equivOfEq _ _ productSubalgebra_one).trans (Subalgebra.topEquiv))

/-- The rational coordinates of the discriminant-one order equivalence evaluate at both roots. -/
@[simp↓] theorem coe_equivProdOfOne_apply (z : toSubalgebra 1 (by decide)) :
    (((equivProdOfOne z).1 : ℚ), ((equivProdOfOne z).2 : ℚ)) =
      ((z : QuadraticAlgebra ℚ ((1 : ℤ) : ℚ) 0).re +
        (z : QuadraticAlgebra ℚ ((1 : ℤ) : ℚ) 0).im,
       (z : QuadraticAlgebra ℚ ((1 : ℤ) : ℚ) 0).re -
        (z : QuadraticAlgebra ℚ ((1 : ℤ) : ℚ) 0).im) := by
  have h := equivProductOfSq_commutes 1 (by decide)
  simp only [algEquivProdOfIntSq_apply, Int.cast_one, one_mul] at h
  exact (h z).symm

/-- The discriminant-one order has four units. -/
theorem card_units_toSubalgebra_one :
    Nat.card (Units (toSubalgebra 1 (by decide))) = 4 := by
  simpa using card_units_toSubalgebra_sq 1 (by decide)

end TauCeti.QuadraticOrder
