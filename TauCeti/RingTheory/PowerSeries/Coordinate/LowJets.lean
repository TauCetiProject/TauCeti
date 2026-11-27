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
# Linear and quadratic jets of formal coordinates

`FormalCoordinate.Jet.oneEquivUnits` identifies first jets with coefficient units.
`FormalCoordinate.Jet.twoEquiv` records the linear and quadratic coefficients of a second jet.
`FormalCoordinate.Jet.twoEquiv_mul` computes their composition.
`FormalCoordinate.Jet.isMulCommutative_two_iff_subsingleton_units` characterizes commutativity.
The product formula computes composition directly from the linear and quadratic coefficients,
using `PowerSeries.coeff_subst_eq_sum_range`. The inverse of the first-jet equivalence composes
`FormalCoordinate.homothety` with `FormalCoordinate.jet 1`.
-/

public section

open PowerSeries

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R]

/-- A coordinate and its linear homothety have the same first jet. -/
theorem jet_one_homothety_linearCoeff (φ : FormalCoordinate R) :
    jet 1 (homothety φ.linearCoeff) = jet 1 φ := by
  apply jet_eq_jet_iff_coeff.mpr
  intro i hi
  interval_cases i
  · simp only [coeff_zero_eq_constantCoeff, constantCoeff_toPowerSeries]
  · simp only [← val_linearCoeff, linearCoeff_homothety]

namespace Jet

/-- A first jet is determined by its unit linear coefficient. -/
noncomputable def oneEquivUnits : Jet R 1 ≃* Rˣ :=
  (MulEquiv.ofBijective ((jet 1).comp homothety) (by
    constructor
    · intro a b hab
      have h : PowerSeries.coeff 1 (homothety a).toPowerSeries =
          PowerSeries.coeff 1 (homothety b).toPowerSeries := jet_eq_jet_iff_coeff.mp hab 1 le_rfl
      apply Units.ext
      simpa only [← val_linearCoeff, linearCoeff_homothety] using h
    · intro x
      obtain ⟨φ, rfl⟩ := jet_surjective 1 x
      exact ⟨φ.linearCoeff, jet_one_homothety_linearCoeff φ⟩)).symm

/-- The inverse sends a unit to the first jet of its homothety. -/
@[simp]
theorem oneEquivUnits_symm_apply (u : Rˣ) : oneEquivUnits.symm u = jet 1 (homothety u) :=
  (rfl)

/-- The first jet of a coordinate corresponds to its linear coefficient. -/
@[simp]
theorem oneEquivUnits_jet (φ : FormalCoordinate R) : oneEquivUnits (jet 1 φ) = φ.linearCoeff := by
  apply oneEquivUnits.symm.injective
  rw [MulEquiv.symm_apply_apply, oneEquivUnits_symm_apply]
  exact (jet_one_homothety_linearCoeff φ).symm

private theorem two_coeff_injective :
    Function.Injective fun x : Jet R 2 ↦
      (oneEquivUnits (truncate (by decide : 1 ≤ 2) x), x.coeff (Fin.last 2)) := by
  intro x y h
  obtain ⟨φ, rfl⟩ := jet_surjective 2 x
  obtain ⟨ψ, rfl⟩ := jet_surjective 2 y
  apply jet_eq_jet_iff_coeff.mpr
  intro i hi
  interval_cases i
  · simp only [coeff_zero_eq_constantCoeff, constantCoeff_toPowerSeries]
  · simpa only [truncate_jet, oneEquivUnits_jet, val_linearCoeff] using
      congrArg (fun p : Rˣ × R ↦ (p.1 : R)) h
  · simpa only [coeff_jet, Fin.val_last] using congrArg Prod.snd h

private theorem two_coeff_rightInverse :
    Function.RightInverse
      (fun p : Rˣ × R ↦ jet 2 (homothety p.1 *
        ofStrictCoeffs (Pi.single 1 ((↑p.1⁻¹ : R) * p.2))))
      (fun x ↦ (oneEquivUnits (truncate (by decide : 1 ≤ 2) x), x.coeff (Fin.last 2))) := by
  rintro ⟨a, b⟩
  have h₂ : PowerSeries.coeff 2
      (ofStrictCoeffs (Pi.single 1 ((↑a⁻¹ : R) * b))).toPowerSeries = (↑a⁻¹ : R) * b := by
    simpa only [Pi.single_eq_same, PNat.one_coe, Nat.reduceAdd] using
      coeff_succ_ofStrictCoeffs (Pi.single 1 ((↑a⁻¹ : R) * b)) 1
  refine Prod.ext (Units.ext ?_) ?_
  · simp only [truncate_jet, oneEquivUnits_jet, val_linearCoeff, toPowerSeries_homothety_mul,
      coeff_smul, coeff_one_ofStrictCoeffs, smul_eq_mul, mul_one]
  · simp only [coeff_jet, Fin.val_last, toPowerSeries_homothety_mul, coeff_smul, h₂, smul_eq_mul,
      ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- A second jet is specified by a unit linear coefficient and a quadratic coefficient. -/
noncomputable def twoEquiv : Jet R 2 ≃ Rˣ × R :=
  ⟨_, _, fun _ ↦ two_coeff_injective (two_coeff_rightInverse _), two_coeff_rightInverse⟩

/-- The coordinates of a second jet are its first jet read as a unit and its degree-two
coefficient. -/
@[simp]
theorem twoEquiv_apply (x : Jet R 2) :
    twoEquiv x = (oneEquivUnits (truncate (by decide : 1 ≤ 2) x), x.coeff (Fin.last 2)) :=
  (rfl)

/-- Recover a second jet from its linear and quadratic coefficients by scaling a strict
coordinate with just one nonlinear term. -/
@[simp]
theorem twoEquiv_symm_apply (a : Rˣ) (b : R) :
    twoEquiv.symm (a, b) =
      jet 2 (homothety a * ofStrictCoeffs (Pi.single 1 ((↑a⁻¹ : R) * b))) :=
  (rfl)

/-- The linear and quadratic coordinates of the composite `x ∘ y` of second jets. -/
theorem twoEquiv_mul (x y : Jet R 2) :
    twoEquiv (x * y) = ((twoEquiv x).1 * (twoEquiv y).1,
      ((twoEquiv x).1 : R) * (twoEquiv y).2 + (twoEquiv x).2 * ((twoEquiv y).1 : R) ^ 2) := by
  refine Prod.ext (by simp only [twoEquiv_apply, map_mul]) ?_
  obtain ⟨φ, rfl⟩ := jet_surjective 2 x
  obtain ⟨ψ, rfl⟩ := jet_surjective 2 y
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
