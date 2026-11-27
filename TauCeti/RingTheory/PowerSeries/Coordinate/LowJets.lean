/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Jet
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Linear and quadratic jets of formal coordinates

`FormalCoordinate.Jet.oneEquivUnits` identifies first jets with coefficient units.
`FormalCoordinate.Jet.twoEquiv` records the linear and quadratic coefficients of a second jet.
`FormalCoordinate.Jet.twoEquiv_mul` computes their composition.
`FormalCoordinate.Jet.isMulCommutative_two_iff_subsingleton_units` characterizes commutativity.
The proofs use `FormalCoordinate.jet_eq_jet_iff_coeff` and
`PowerSeries.coeff_subst_eq_sum_range`.
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

private theorem two_coeff_bijective :
    Function.Bijective fun x : Jet R 2 ↦
      (oneEquivUnits (truncate (by decide : 1 ≤ 2) x), x.coeff (Fin.last 2)) := by
  constructor
  · intro x y h
    obtain ⟨φ, rfl⟩ := jet_surjective 2 x
    obtain ⟨ψ, rfl⟩ := jet_surjective 2 y
    have h₁ : φ.linearCoeff = ψ.linearCoeff := by
      simpa only [truncate_jet, oneEquivUnits_jet] using congrArg Prod.fst h
    have h₂ : PowerSeries.coeff 2 φ.toPowerSeries =
        PowerSeries.coeff 2 ψ.toPowerSeries := by
      simpa only [coeff_jet, Fin.val_last] using congrArg Prod.snd h
    apply jet_eq_jet_iff_coeff.mpr
    intro i hi
    interval_cases i
    · simp only [coeff_zero_eq_constantCoeff, constantCoeff_toPowerSeries]
    · simpa only [← val_linearCoeff] using congrArg Units.val h₁
    · exact h₂
  · rintro ⟨a, b⟩
    let p : R⟦X⟧ := monomial 1 (a : R) + monomial 2 b
    have h₁ : IsUnit (PowerSeries.coeff 1 p) := by
      simpa only [p, map_add, coeff_monomial_same, coeff_monomial, Nat.reduceEqDiff, ite_false,
        add_zero] using a.isUnit
    refine ⟨jet 2 (p.toFormalCoordinate h₁), Prod.ext (Units.ext ?_) ?_⟩
    · simp [p, coeff_monomial]
    · simp [p, coeff_monomial]

/-- A second jet is specified by a unit linear coefficient and a quadratic coefficient. -/
noncomputable def twoEquiv : Jet R 2 ≃ Rˣ × R :=
  Equiv.ofBijective _ two_coeff_bijective

/-- The coordinates of a second jet are its first jet read as a unit and its degree-two
coefficient. -/
@[simp]
theorem twoEquiv_apply (x : Jet R 2) :
    twoEquiv x = (oneEquivUnits (truncate (by decide : 1 ≤ 2) x), x.coeff (Fin.last 2)) :=
  (rfl)

/-- The linear and quadratic coordinates of the composite `x ∘ y` of second jets. -/
theorem twoEquiv_mul (x y : Jet R 2) :
    twoEquiv (x * y) = ((twoEquiv x).1 * (twoEquiv y).1,
      ((twoEquiv x).1 : R) * (twoEquiv y).2 + (twoEquiv x).2 * ((twoEquiv y).1 : R) ^ 2) := by
  refine Prod.ext (by simp only [twoEquiv_apply, map_mul]) ?_
  obtain ⟨φ, rfl⟩ := jet_surjective 2 x
  obtain ⟨ψ, rfl⟩ := jet_surjective 2 y
  have hsq : PowerSeries.coeff 2 (ψ.toPowerSeries ^ 2) =
      PowerSeries.coeff 1 ψ.toPowerSeries ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ_succ']
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_cons, Finset.map_singleton,
      Finset.sum_singleton, coeff_zero_eq_constantCoeff, constantCoeff_toPowerSeries, zero_mul,
      mul_zero, zero_add, pow_two]
    rfl
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
    apply Prod.ext
    · exact h.elim _ _
    · have hx : (twoEquiv x).1 = 1 := h.elim _ _
      have hy : (twoEquiv y).1 = 1 := h.elim _ _
      simp only [twoEquiv_mul, hx, hy, Units.val_one, one_pow, one_mul, mul_one, add_comm]

end Jet

end TauCeti.FormalCoordinate
