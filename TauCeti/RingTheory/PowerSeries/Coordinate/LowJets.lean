/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Jet
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Coefficients of formal coordinate jets

`FormalCoordinate.Jet.oneEquivUnits` identifies first jets with coefficient units.
`FormalCoordinate.Jet.coeffEquiv` classifies jets of any positive order by their coefficients.
`FormalCoordinate.Jet.twoEquiv` records the linear and quadratic coefficients of a second jet.
`FormalCoordinate.Jet.twoEquiv_mul` gives the product `(a, b) * (c, d) = (ac, ad + bc²)`,
composing the first coordinate after the second. `FormalCoordinate.Jet.twoEquiv_symm_apply`
recovers a jet from its coefficient pair, and
`FormalCoordinate.Jet.isMulCommutative_two_iff_subsingleton_units` shows that the second-jet group
is commutative exactly when `1` is the only unit of the coefficient ring.
-/

public section

open PowerSeries

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R]

namespace Jet

/-- A second jet is specified by a unit linear coefficient and a quadratic coefficient. -/
noncomputable def twoEquiv : Jet R 2 ≃ Rˣ × R :=
  (coeffEquiv 1).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) R))

-- The simp projections leave whole equivalence applications available for cancellation.
/-- The coordinates of a second jet are its first jet read as a unit and its degree-two
coefficient. -/
theorem twoEquiv_apply (x : Jet R 2) :
    twoEquiv x = (oneEquivUnits (truncate (by decide : 1 ≤ 2) x), x.coeff (Fin.last 2)) := by
  have h : (twoEquiv : Jet R 2 ≃ Rˣ × R) =
      (coeffEquiv 1).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) R)) := rfl
  rw [h, Equiv.trans_apply, coeffEquiv_apply]
  exact Prod.ext rfl (congrArg x.coeff (Fin.ext rfl))

/-- The unit coordinate is the first jet read as a unit. -/
@[simp]
theorem twoEquiv_fst (x : Jet R 2) :
    (twoEquiv x).1 = oneEquivUnits (truncate (by decide : 1 ≤ 2) x) :=
  congrArg Prod.fst (twoEquiv_apply x)

/-- The scalar coordinate is the degree-two coefficient. -/
@[simp]
theorem twoEquiv_snd (x : Jet R 2) : (twoEquiv x).2 = x.coeff (Fin.last 2) :=
  congrArg Prod.snd (twoEquiv_apply x)

/-- Recover a second jet from its linear and quadratic coefficients by scaling a strict
coordinate with just one nonlinear term. -/
theorem twoEquiv_symm_apply (a : Rˣ) (b : R) :
    twoEquiv.symm (a, b) =
      jet 2 (homothety a * ofStrictCoeffs (Pi.single 1 ((↑a⁻¹ : R) * b))) := by
  apply twoEquiv.injective
  rw [Equiv.apply_symm_apply, twoEquiv_apply]
  refine Prod.ext ?_ ?_
  · -- Only the homothety contributes to the linear coefficient.
    rw [truncate_jet, oneEquivUnits_jet, map_mul, linearCoeff_homothety,
      MonoidHom.mem_ker.mp (ofStrictCoeffs_mem_ker_linearCoeff _), mul_one]
  · -- `ofStrictCoeffs` sets the quadratic coefficient before scaling by the homothety.
    have h₂ : PowerSeries.coeff 2
        (ofStrictCoeffs (Pi.single 1 ((↑a⁻¹ : R) * b))).toPowerSeries = (↑a⁻¹ : R) * b :=
      (coeff_succ_ofStrictCoeffs _ 1).trans (Pi.single_eq_same 1 _)
    simp only [coeff_jet, Fin.val_last, toPowerSeries_homothety_mul, coeff_smul, smul_eq_mul,
      h₂, Units.mul_inv_cancel_left]

/-- The linear and quadratic coordinates of the composite `x ∘ y` of second jets. -/
theorem twoEquiv_mul (x y : Jet R 2) :
    twoEquiv (x * y) = ((twoEquiv x).1 * (twoEquiv y).1,
      ((twoEquiv x).1 : R) * (twoEquiv y).2 + (twoEquiv x).2 * ((twoEquiv y).1 : R) ^ 2) := by
  refine Prod.ext (by simp only [twoEquiv_apply, map_mul]) ?_
  obtain ⟨φ, rfl⟩ := jet_surjective 2 x
  obtain ⟨ψ, rfl⟩ := jet_surjective 2 y
  -- In `coeff_subst_eq_sum_range`, the square contributes only its leading term,
  -- computed by `coeff_pow_mul_of_le_order`.
  have hsq : PowerSeries.coeff 2 (ψ.toPowerSeries ^ 2) =
      PowerSeries.coeff 1 ψ.toPowerSeries ^ 2 :=
    coeff_pow_mul_of_le_order (n := 1)
      (one_le_order_iff_constCoeff_eq_zero.mpr ψ.constantCoeff_toPowerSeries) 2
  rw [← map_mul]
  simp only [twoEquiv_apply, truncate_jet, oneEquivUnits_jet, coeff_jet, Fin.val_last,
    val_linearCoeff, toPowerSeries_mul]
  rw [coeff_subst_eq_sum_range _ ψ.constantCoeff_toPowerSeries]
  simp [Finset.sum_range_succ, hsq, smul_eq_mul]

/-- The second-jet group is commutative exactly when the coefficient ring has only the unit
`1`. -/
theorem isMulCommutative_two_iff_subsingleton_units :
    IsMulCommutative (Jet R 2) ↔ Subsingleton Rˣ := by
  rw [isMulCommutative_iff]
  constructor
  · intro h
    refine ⟨fun a b ↦ ?_⟩
    have eq_one (u : Rˣ) : u = 1 := by
      let x := (twoEquiv (R := R)).symm (u, 0)
      let y := (twoEquiv (R := R)).symm (1, 1)
      have hx : twoEquiv x = (u, 0) := Equiv.apply_symm_apply _ _
      have hy : twoEquiv y = (1, 1) := Equiv.apply_symm_apply _ _
      have heq := congrArg (fun z ↦ (twoEquiv z).2) (h x y)
      have hu : (u : R) = (u : R) ^ 2 := by
        simpa only [twoEquiv_mul, hx, hy, Units.val_one, mul_one, zero_mul, add_zero,
          mul_zero, one_mul, zero_add] using heq
      have hu' : u * 1 = u * u := Units.ext (by simpa only [Units.val_mul, Units.val_one, mul_one,
        pow_two] using hu)
      exact (mul_left_cancel hu').symm
    rw [eq_one a, eq_one b]
  · intro h x y
    apply twoEquiv.injective
    refine Prod.ext (h.elim _ _) ?_
    have hx : (twoEquiv x).1 = 1 := h.elim _ _
    have hy : (twoEquiv y).1 = 1 := h.elim _ _
    simp only [twoEquiv_mul, hx, hy, Units.val_one, one_pow, one_mul, mul_one, add_comm]

end Jet

end TauCeti.FormalCoordinate
