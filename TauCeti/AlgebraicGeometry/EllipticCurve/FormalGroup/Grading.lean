/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Grading
public import TauCeti.RingTheory.FormalGroup.Rescale.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Graded

/-!
# Scaling and homological homogeneity of Weierstrass formal groups

A pure Weierstrass scaling `scaling R u = (u, 0, 0, 0)` acts on the Weierstrass formal
neighbourhood by rescaling the formal parameter by `u⁻¹`:
* its formal coordinate transition from `scaling R u • W` to `W` is the homothety `z ↦ u⁻¹ z`
  (`WeierstrassCurve.VariableChange.formalCoordinate_scaling`);
* the formal group law of `scaling R u • W` is `(formalGroup W).rescale ↑u⁻¹`
  (`WeierstrassCurve.formalGroup_scaling_smul`);
* the `w`-expansion, invariant-differential denominator and normalised invariant differential
  transform by `u³ w_W(u⁻¹ z)`, `G_W(u⁻¹ z)` and `P_W(u⁻¹ z)`
  (`WeierstrassCurve.formalW_scaling_smul`,
  `WeierstrassCurve.formalInvariantDifferentialDenom_scaling_smul`,
  `WeierstrassCurve.invariantDifferential_formalGroup_scaling_smul`);
* conjugating a strict Weierstrass change by `scaling R u` conjugates the induced strict formal
  parameter transition by `homothety u`
  (`WeierstrassCurve.VariableChange.inv_formalCoordinate_heisenbergHom_heisenbergAction`).

Evaluating these scaling identities at the Laurent degree unit `T (-2)` over
`A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `A[r, s, t]` immediately yields the homological and weighted
homogeneity of the universal Weierstrass formal group law, its `[k]`-series, `formalW`, the
invariant differential, and the universal strict formal coordinate transition
`Strict.formalCoordinate`, without coefficientwise induction or division by integers.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.Strict.formalCoordinate`: the universal strict formal
  coordinate over `A[r, s, t]` carrying `formalGroup (WeierstrassCurve.map Universal.curve C)` to
  `formalGroup (WeierstrassCurve.map Universal.curve Strict.rightUnit)`.

## Main results

* `WeierstrassCurve.formalGroup_scaling_smul`, `WeierstrassCurve.formalW_scaling_smul`,
  `WeierstrassCurve.formalInvariantDifferentialDenom_scaling_smul`,
  `WeierstrassCurve.invariantDifferential_formalGroup_scaling_smul`: pure-scaling formulas on the
  formal neighbourhood over any commutative ring.
* `WeierstrassCurve.Universal.coeff_formalGroup_mem_baseGrading`,
  `WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_formalGroup`: the coefficient of
  `X^(d 0) Y^(d 1)` in the universal Weierstrass formal group has modular weight `d.degree - 1`
  and homological degree `2 * (d.degree - 1)`.
* `WeierstrassCurve.Universal.coeff_nsmulSeries_formalGroup_mem_baseGrading`,
  `WeierstrassCurve.Universal.coeff_formalW_mem_baseGrading`,
  `WeierstrassCurve.Universal.coeff_formalInvariantDifferentialDenom_mem_baseGrading`,
  `WeierstrassCurve.Universal.coeff_invariantDifferential_formalGroup_mem_baseGrading`:
  homological and weighted homogeneity of `[k]`, `formalW`, `G(z)` and `P(z)`.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.formalCoordinate_mem_gradedSubgroup`: the universal
  strict formal coordinate transition lies in `FormalCoordinate.gradedSubgroup arrowGrading 2`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section

noncomputable section

open TauCeti.GradedAlgebra

/-! ### Pure scalings on the Weierstrass formal neighbourhood -/

namespace WeierstrassCurve.VariableChange

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The transition denominator of a pure scaling `(u, 0, 0, 0)` is the constant `u³`. -/
theorem formalDenom_scaling (u : Rˣ) (W : WeierstrassCurve R) :
    (scaling R u).formalDenom W = PowerSeries.C (u : R) ^ 3 := by
  simp [formalDenom_def]

/-- A pure scaling `(u, 0, 0, 0)` induces the formal homothety `z ↦ u⁻¹ z`. -/
theorem formalCoordinate_scaling (u : Rˣ) (W : WeierstrassCurve R) :
    (scaling R u).formalCoordinate W = TauCeti.FormalCoordinate.homothety u⁻¹ := by
  apply TauCeti.FormalCoordinate.ext
  have hinv : invOfUnit ((scaling R u).formalDenom W) ((scaling R u).u ^ 3) =
      PowerSeries.C (↑u⁻¹ : R) ^ 3 := by
    apply ((scaling R u).isUnit_formalDenom W).mul_left_cancel
    rw [mul_invOfUnit _ _ ((scaling R u).constantCoeff_formalDenom W), formalDenom_scaling,
      ← map_pow, ← map_pow, ← _root_.map_mul, ← mul_pow, Units.mul_inv, one_pow, _root_.map_one]
  rw [formalCoordinate_toPowerSeries, hinv, TauCeti.FormalCoordinate.toPowerSeries_homothety,
    PowerSeries.smul_eq_C_mul]
  simp only [scaling_apply, map_zero, zero_mul, add_zero, ← map_pow]
  calc
    PowerSeries.C ((u : R) ^ 2) * X * PowerSeries.C ((↑u⁻¹ : R) ^ 3) =
        PowerSeries.C ((u : R) ^ 2 * (↑u⁻¹ : R) ^ 2 * ↑u⁻¹) * X := by
      simp only [_root_.map_mul, map_pow]
      ring
    _ = PowerSeries.C (↑u⁻¹ : R) * X := by
      rw [← mul_pow, Units.mul_inv, one_pow, one_mul]

/-- Conjugating a strict Weierstrass change by `scaling R u` conjugates the induced formal
coordinate transition by `homothety u`. -/
theorem formalCoordinate_heisenbergHom_heisenbergAction (u : Rˣ) (a : TauCeti.HeisenbergGroup R)
    (W : WeierstrassCurve R) :
    (heisenbergHom R (heisenbergAction R u a)).formalCoordinate (scaling R u • W) =
      TauCeti.FormalCoordinate.homothety u * (heisenbergHom R a).formalCoordinate W *
        TauCeti.FormalCoordinate.homothety u⁻¹ := by
  have hact := heisenbergHom_action R u a
  rw [hact, formalCoordinate_mul, ← _root_.map_inv, formalCoordinate_scaling, inv_inv,
    _root_.map_inv, inv_smul_smul, formalCoordinate_mul, formalCoordinate_scaling, mul_assoc]

/-- Conjugating a strict Weierstrass change by `scaling R u` conjugates the inverse formal
coordinate transition (from `W` to the transformed curve) by `homothety u`. -/
theorem inv_formalCoordinate_heisenbergHom_heisenbergAction (u : Rˣ) (a : TauCeti.HeisenbergGroup R)
    (W : WeierstrassCurve R) :
    ((heisenbergHom R (heisenbergAction R u a)).formalCoordinate (scaling R u • W))⁻¹ =
      TauCeti.FormalCoordinate.homothety u * ((heisenbergHom R a).formalCoordinate W)⁻¹ *
        TauCeti.FormalCoordinate.homothety u⁻¹ := by
  rw [formalCoordinate_heisenbergHom_heisenbergAction]
  simp [mul_inv_rev, mul_assoc]

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R]

/-- **Pure scaling of the formal group law**: scaling `W` by `(u, 0, 0, 0)` rescales its formal
group law by `u⁻¹`. -/
theorem formalGroup_scaling_smul (u : Rˣ) (W : WeierstrassCurve R) :
    formalGroup (VariableChange.scaling R u • W) = (formalGroup W).rescale (↑u⁻¹ : R) := by
  rw [VariableChange.formalGroup_smul, VariableChange.formalCoordinate_scaling, ← _root_.map_inv,
    inv_inv, FormalGroup.homothety_smul]

/-- **Pure scaling of the normalised invariant differential**: scaling `W` by `(u, 0, 0, 0)`
rescales `P_W(z)` to `P_W(u⁻¹ z)`. -/
theorem invariantDifferential_formalGroup_scaling_smul (u : Rˣ) (W : WeierstrassCurve R) :
    (formalGroup (VariableChange.scaling R u • W)).invariantDifferential =
      PowerSeries.rescale (↑u⁻¹ : R) (formalGroup W).invariantDifferential := by
  rw [formalGroup_scaling_smul, FormalGroup.invariantDifferential_rescale]

/-- **Pure scaling of the invariant-differential denominator**: scaling `W` by `(u, 0, 0, 0)`
rescales `G_W(z)` to `G_W(u⁻¹ z)`. -/
theorem formalInvariantDifferentialDenom_scaling_smul (u : Rˣ) (W : WeierstrassCurve R) :
    (VariableChange.scaling R u • W).formalInvariantDifferentialDenom =
      PowerSeries.rescale (↑u⁻¹ : R) W.formalInvariantDifferentialDenom := by
  have h := (VariableChange.scaling R u).subst_formalCoordinate_formalInvariantDifferentialDenom W
  rw [VariableChange.formalCoordinate_scaling, TauCeti.FormalCoordinate.toPowerSeries_homothety,
    ← PowerSeries.rescale_eq_subst] at h
  have hd : d⁄dX ((↑u⁻¹ : R) • (PowerSeries.X : PowerSeries R)) = PowerSeries.C (↑u⁻¹ : R) := by
    simp [PowerSeries.smul_eq_C_mul]
  have hu : PowerSeries.C ((VariableChange.scaling R u).u : R) * PowerSeries.C (↑u⁻¹ : R) = 1 := by
    rw [VariableChange.scaling_apply, ← map_mul, Units.mul_inv, map_one]
  rw [hd, hu, one_mul] at h
  exact h.symm

/-- **Pure scaling of the `w`-expansion**: scaling `W` by `(u, 0, 0, 0)` transforms `w_W(z)` to
`u³ w_W(u⁻¹ z)`. -/
theorem formalW_scaling_smul (u : Rˣ) (W : WeierstrassCurve R) :
    formalW (VariableChange.scaling R u • W) =
      (u : R) ^ 3 • PowerSeries.rescale (↑u⁻¹ : R) (formalW W) := by
  have h := congrArg (· * (VariableChange.scaling R u).formalDenom W)
    ((VariableChange.scaling R u).subst_formalCoordinate_formalW W)
  rw [mul_assoc, invOfUnit_mul _ _ ((VariableChange.scaling R u).constantCoeff_formalDenom W),
    mul_one, VariableChange.formalCoordinate_scaling,
    TauCeti.FormalCoordinate.toPowerSeries_homothety, ← PowerSeries.rescale_eq_subst,
    VariableChange.formalDenom_scaling, mul_comm, ← map_pow, ← PowerSeries.smul_eq_C_mul] at h
  exact h.symm

/-! ### Homogeneity of the universal Weierstrass formal group and formal expansions -/

namespace Universal

open TauCeti.WeierstrassHopfAlgebroid

private def degreeUnit : (LaurentPolynomial (MvPolynomial Coeff ℤ))ˣ :=
  (unitOfInvertible (LaurentPolynomial.T (2 : ℤ)))⁻¹

private theorem val_degreeUnit :
    (degreeUnit : LaurentPolynomial (MvPolynomial Coeff ℤ)) = LaurentPolynomial.T (-2) := by
  simp [degreeUnit, val_inv_unitOfInvertible]

private theorem val_inv_degreeUnit :
    (↑degreeUnit⁻¹ : LaurentPolynomial (MvPolynomial Coeff ℤ)) = LaurentPolynomial.T 2 := by
  simp [degreeUnit]

/-- Applying the homological grading homomorphism `a ↦ ∑ₙ aₙ Tⁿ` to `Universal.curve` over
`LaurentPolynomial A` is the pure scaling by `T (-2)`. -/
private theorem map_toLaurent_toPolynomial_curve :
    WeierstrassCurve.map Universal.curve
        (Polynomial.toLaurent.comp (toPolynomial Strict.baseGrading)) =
      VariableChange.scaling _ degreeUnit •
        WeierstrassCurve.map Universal.curve LaurentPolynomial.C := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, curve_a₁, curve_a₂, curve_a₃, curve_a₄,
      curve_a₆, RingHom.comp_apply, toPolynomial_of_mem (Strict.X_mem_baseGrading _),
      Polynomial.toLaurent_C_mul_T, VariableChange.scaling_apply, variableChange_a₁,
      variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
      val_inv_degreeUnit, LaurentPolynomial.T_pow, mul_zero, zero_mul, add_zero, sub_zero,
      zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), coefficientWeight_A₁,
      coefficientWeight_A₂, coefficientWeight_A₃, coefficientWeight_A₄, coefficientWeight_A₆,
      mul_comm] <;>
    rfl

/-- **Homological homogeneity of the universal Weierstrass formal group law**: the coefficient of
`X^(d 0) Y^(d 1)` lies in `Strict.baseGrading (2 * (d.degree - 1))`. -/
theorem coeff_formalGroup_mem_baseGrading (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries ∈
      Strict.baseGrading (2 * (d.degree - 1)) := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have hexp : ((d.degree - 1 : ℕ) * 2 : ℤ) = (2 * (d.degree - 1) : ℕ) := by
    push_cast
    ring
  have h := congrArg (fun W ↦ MvPowerSeries.coeff d (formalGroup W).toPowerSeries)
    map_toLaurent_toPolynomial_curve
  rw [map_formalGroup, formalGroup_scaling_smul, map_formalGroup, FormalGroup.map_toPowerSeries,
    FormalGroup.coeff_rescale, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map,
    RingHom.comp_apply, MvPowerSeries.coeff_map, val_inv_degreeUnit, LaurentPolynomial.T_pow,
    mul_comm (LaurentPolynomial.T _), hexp, ← Polynomial.toLaurent_C_mul_T] at h
  exact h

/-- **Weighted homogeneity of the universal Weierstrass formal group law**: the coefficient of
`X^(d 0) Y^(d 1)` is weighted homogeneous of modular weight `d.degree - 1` in `a₁, a₂, a₃, a₄, a₆`.
-/
theorem isWeightedHomogeneous_coeff_formalGroup (d : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries).IsWeightedHomogeneous
      coefficientWeight (d.degree - 1) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalGroup_mem_baseGrading d)

/-- The coefficient of `X^m` in `[k]` on the universal Weierstrass formal group has homological
degree `2 * (m - 1)`. -/
theorem coeff_nsmulSeries_formalGroup_mem_baseGrading (k m : ℕ) :
    PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k) ∈
      Strict.baseGrading (2 * (m - 1)) :=
  FormalGroup.coeff_nsmulSeries_mem (formalGroup Universal.curve) coeff_formalGroup_mem_baseGrading
    k m

/-- The coefficient of `X^m` in `[k]` on the universal Weierstrass formal group has modular weight
`m - 1`. -/
theorem isWeightedHomogeneous_coeff_nsmulSeries_formalGroup (k m : ℕ) :
    (PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k)).IsWeightedHomogeneous
      coefficientWeight (m - 1) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_nsmulSeries_formalGroup_mem_baseGrading k m)

/-- The coefficient of `z^n` in the universal `w`-expansion `formalW Universal.curve` has
homological degree `2 * (n - 3)`. -/
theorem coeff_formalW_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n (formalW Universal.curve) ∈ Strict.baseGrading (2 * (n - 3)) := by
  rcases n with _ | _ | _ | n
  · simp [coeff_formalW, zero_mem]
  · simp [coeff_formalW, zero_mem]
  · simp [coeff_formalW, zero_mem]
  · change PowerSeries.coeff (n + 3) (formalW Universal.curve) ∈ Strict.baseGrading (2 * n)
    apply toPolynomial_eq_monomial_iff.mp
    apply Polynomial.toLaurent_injective
    have hexp : ((3 : ℕ) * (-2 : ℤ) + (n + 3 : ℕ) * 2 : ℤ) = (2 * n : ℕ) := by
      push_cast
      ring
    have h := congrArg (PowerSeries.coeff (n + 3))
      (congrArg formalW map_toLaurent_toPolynomial_curve)
    rw [map_formalW, formalW_scaling_smul, map_formalW, PowerSeries.coeff_map, RingHom.comp_apply,
      PowerSeries.coeff_smul, PowerSeries.coeff_rescale, PowerSeries.coeff_map, val_degreeUnit,
      val_inv_degreeUnit, smul_eq_mul, LaurentPolynomial.T_pow, LaurentPolynomial.T_pow,
      ← mul_assoc, ← LaurentPolynomial.T_add, mul_comm (LaurentPolynomial.T _), hexp,
      ← Polynomial.toLaurent_C_mul_T] at h
    exact h

/-- The coefficient of `z^n` in `formalW Universal.curve` is weighted homogeneous of modular weight
`n - 3`. -/
theorem isWeightedHomogeneous_coeff_formalW (n : ℕ) :
    (PowerSeries.coeff n (formalW Universal.curve)).IsWeightedHomogeneous
      coefficientWeight (n - 3) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalW_mem_baseGrading n)

/-- The coefficient of `z^n` in `Universal.curve.formalInvariantDifferentialDenom` has homological
degree `2 * n`. -/
theorem coeff_formalInvariantDifferentialDenom_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom ∈
      Strict.baseGrading (2 * n) := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have hexp : ((n : ℤ) * 2 : ℤ) = (2 * n : ℕ) := by
    push_cast
    ring
  have h := congrArg (PowerSeries.coeff n)
    (congrArg formalInvariantDifferentialDenom map_toLaurent_toPolynomial_curve)
  rw [map_formalInvariantDifferentialDenom, formalInvariantDifferentialDenom_scaling_smul,
    map_formalInvariantDifferentialDenom, PowerSeries.coeff_map, RingHom.comp_apply,
    PowerSeries.coeff_rescale, PowerSeries.coeff_map, val_inv_degreeUnit, LaurentPolynomial.T_pow,
    mul_comm (LaurentPolynomial.T _), hexp, ← Polynomial.toLaurent_C_mul_T] at h
  exact h

/-- The coefficient of `z^n` in `Universal.curve.formalInvariantDifferentialDenom` is weighted
homogeneous of modular weight `n`. -/
theorem isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom (n : ℕ) :
    (PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom).IsWeightedHomogeneous
      coefficientWeight n :=
  Strict.mem_baseGrading_two_mul_iff.mp
    (coeff_formalInvariantDifferentialDenom_mem_baseGrading n)

/-- The coefficient of `z^n` in `(formalGroup Universal.curve).invariantDifferential` has
homological degree `2 * n`. -/
theorem coeff_invariantDifferential_formalGroup_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n (formalGroup Universal.curve).invariantDifferential ∈
      Strict.baseGrading (2 * n) := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have hexp : ((n : ℤ) * 2 : ℤ) = (2 * n : ℕ) := by
    push_cast
    ring
  have h := congrArg (PowerSeries.coeff n)
    (congrArg (fun W ↦ (formalGroup W).invariantDifferential) map_toLaurent_toPolynomial_curve)
  rw [invariantDifferential_formalGroup_scaling_smul, map_formalGroup,
    ← FormalGroup.map_invariantDifferential, map_formalGroup,
    ← FormalGroup.map_invariantDifferential, PowerSeries.coeff_map, RingHom.comp_apply,
    PowerSeries.coeff_rescale, PowerSeries.coeff_map, val_inv_degreeUnit, LaurentPolynomial.T_pow,
    mul_comm (LaurentPolynomial.T _), hexp, ← Polynomial.toLaurent_C_mul_T] at h
  exact h

/-- The coefficient of `z^n` in `(formalGroup Universal.curve).invariantDifferential` is weighted
homogeneous of modular weight `n`. -/
theorem isWeightedHomogeneous_coeff_invariantDifferential_formalGroup (n : ℕ) :
    (PowerSeries.coeff n
      (formalGroup Universal.curve).invariantDifferential).IsWeightedHomogeneous
        coefficientWeight n :=
  Strict.mem_baseGrading_two_mul_iff.mp
    (coeff_invariantDifferential_formalGroup_mem_baseGrading n)

end Universal

end WeierstrassCurve

/-! ### The universal strict formal coordinate transition over `A[r, s, t]` -/

namespace TauCeti.WeierstrassHopfAlgebroid.Strict

open MvPolynomial _root_.WeierstrassCurve _root_.WeierstrassCurve.VariableChange
open TauCeti.WeierstrassChange.StrictChangeRing

/-- The universal strict formal coordinate transition over `A[r, s, t]`, carrying
`formalGroup (WeierstrassCurve.map Universal.curve C)` to
`formalGroup (WeierstrassCurve.map Universal.curve rightUnit)`. -/
def formalCoordinate : TauCeti.FormalCoordinate ArrowRing :=
  ((universalChange (MvPolynomial Coeff ℤ)).formalCoordinate
    (WeierstrassCurve.map Universal.curve C))⁻¹

theorem formalCoordinate_def :
    formalCoordinate =
      ((universalChange (MvPolynomial Coeff ℤ)).formalCoordinate
        (WeierstrassCurve.map Universal.curve C))⁻¹ :=
  (rfl)

/-- Equivalently, `Strict.formalCoordinate` is the transition induced by `(universalChange A)⁻¹`
on the target curve `(1, r, s, t) • W`. -/
theorem formalCoordinate_eq_inv_formalCoordinate :
    formalCoordinate =
      (universalChange (MvPolynomial Coeff ℤ))⁻¹.formalCoordinate
        (WeierstrassCurve.map Universal.curve rightUnit) := by
  rw [map_rightUnit, formalCoordinate_inv]
  rfl

/-- `Strict.formalCoordinate` has linear coefficient `1`. -/
@[simp]
theorem linearCoeff_formalCoordinate :
    TauCeti.FormalCoordinate.linearCoeff formalCoordinate = 1 := by
  simp [formalCoordinate]

/-- `Strict.formalCoordinate` is a strict formal coordinate. -/
theorem formalCoordinate_mem_ker_linearCoeff :
    formalCoordinate ∈ (TauCeti.FormalCoordinate.linearCoeff (R := ArrowRing)).ker :=
  MonoidHom.mem_ker.mpr linearCoeff_formalCoordinate

/-- `Strict.formalCoordinate` transports the source formal group law over `A[r, s, t]` to the
target formal group law classified by `Strict.rightUnit`. -/
theorem formalCoordinate_smul_formalGroup :
    formalCoordinate • formalGroup (WeierstrassCurve.map Universal.curve C) =
      formalGroup (WeierstrassCurve.map Universal.curve rightUnit) := by
  rw [map_rightUnit, formalGroup_smul]
  rfl

/-- Specializing `Strict.formalCoordinate` along the map classifying `(W, a)` gives the strict
formal transition `((heisenbergHom R a).formalCoordinate W)⁻¹` from `formalGroup W` to
`formalGroup (heisenbergHom R a • W)`. -/
@[simp]
theorem map_lift_formalCoordinate {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (a : TauCeti.HeisenbergGroup R) :
    formalCoordinate.map (lift (W.specialize, a)) =
      ((heisenbergHom R a).formalCoordinate W)⁻¹ := by
  rw [formalCoordinate, _root_.map_inv, ← map_formalCoordinate, map_lift_universalChange,
    WeierstrassCurve.map_map, lift_comp_C]
  congr 2
  exact WeierstrassCurve.map_specialize W

@[simp]
theorem coeff_one_formalCoordinate :
    PowerSeries.coeff 1 formalCoordinate.toPowerSeries = 1 := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_one_formalCoordinate]
  simp [inv_def]

/-- The quadratic coefficient `b₁` of `Strict.formalCoordinate` is `-s`. -/
@[simp]
theorem coeff_two_formalCoordinate :
    PowerSeries.coeff 2 formalCoordinate.toPowerSeries = -(X 1 : ArrowRing) := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_two_formalCoordinate]
  simp [inv_def]

/-- The cubic coefficient `b₂` of `Strict.formalCoordinate` is `s² - r`. -/
@[simp]
theorem coeff_three_formalCoordinate :
    PowerSeries.coeff 3 formalCoordinate.toPowerSeries = X 1 ^ 2 - (X 0 : ArrowRing) := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_three_formalCoordinate]
  simp [inv_def]
  ring

/-- The quartic coefficient `b₃` of `Strict.formalCoordinate` is `-t - s³ + 2 r s - a₁ r`. -/
@[simp]
theorem coeff_four_formalCoordinate :
    PowerSeries.coeff 4 formalCoordinate.toPowerSeries =
      -X 2 - X 1 ^ 3 + 2 * X 0 * X 1 - C (X .A₁) * (X 0 : ArrowRing) := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_four_formalCoordinate]
  simp [inv_def, variableChange_a₁]
  ring

/-- **Homological homogeneity of the universal strict Weierstrass formal coordinate**: the
coefficient of `z^n` in `Strict.formalCoordinate` lies in `Strict.arrowGrading (2 * (n - 1))`. -/
theorem formalCoordinate_mem_gradedSubgroup :
    formalCoordinate ∈ TauCeti.FormalCoordinate.gradedSubgroup arrowGrading 2 := by
  rw [TauCeti.FormalCoordinate.mem_gradedSubgroup,
    ← TauCeti.FormalCoordinate.map_toLaurent_eq_conjugate_iff]
  let ω : ArrowRing →+* LaurentPolynomial ArrowRing :=
    Polynomial.toLaurent.comp (toPolynomial arrowGrading)
  let u : (LaurentPolynomial ArrowRing)ˣ := (unitOfInvertible (LaurentPolynomial.T ↑(2 : ℕ)))⁻¹
  have hu : (↑u⁻¹ : LaurentPolynomial ArrowRing) = LaurentPolynomial.T 2 := by simp [u]
  have hW : WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C) ω =
      scaling _ u •
        WeierstrassCurve.map (WeierstrassCurve.map Universal.curve C) LaurentPolynomial.C := by
    have hX (i : Coeff) : (C (X i) : ArrowRing) ∈ arrowGrading (2 * coefficientWeight i) :=
      C_mem_arrowGrading (X_mem_baseGrading i)
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
      simp only [ω, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, Universal.curve_a₁, Universal.curve_a₂,
        Universal.curve_a₃, Universal.curve_a₄, Universal.curve_a₆, RingHom.comp_apply,
        toPolynomial_of_mem (hX _), Polynomial.toLaurent_C_mul_T, scaling_apply, variableChange_a₁,
        variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, hu,
        LaurentPolynomial.T_pow, mul_zero, zero_mul, add_zero, sub_zero,
        zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), coefficientWeight_A₁,
        coefficientWeight_A₂, coefficientWeight_A₃, coefficientWeight_A₄, coefficientWeight_A₆,
        mul_comm] <;>
      rfl
  have ha : HeisenbergGroup.map ω (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      heisenbergAction _ u
        (HeisenbergGroup.map LaurentPolynomial.C (universalHeisenberg (MvPolynomial Coeff ℤ))) := by
    have hr := toPolynomial_of_mem (X_mem_arrowGrading 0)
    have hs := toPolynomial_of_mem (X_mem_arrowGrading 1)
    have ht := toPolynomial_of_mem (X_mem_arrowGrading 2)
    ext <;>
      simp only [ω, HeisenbergGroup.map_apply, universalHeisenberg_x, universalHeisenberg_y,
        universalHeisenberg_z, heisenbergAction_apply, RingHom.comp_apply, hr, hs, ht,
        strictCoordDegree_zero, strictCoordDegree_one, strictCoordDegree_two,
        Polynomial.toLaurent_C_mul_T, hu, LaurentPolynomial.T_pow, mul_comm] <;>
      rfl
  have hC : (universalChange (MvPolynomial Coeff ℤ)).map ω =
      heisenbergHom _ (heisenbergAction _ u
        (HeisenbergGroup.map LaurentPolynomial.C
          (universalHeisenberg (MvPolynomial Coeff ℤ)))) := by
    rw [universalChange_eq_heisenbergHom, map_heisenbergHom, ha]
  rw [formalCoordinate, _root_.map_inv, ← map_formalCoordinate, hC, hW,
    inv_formalCoordinate_heisenbergHom_heisenbergAction, ← map_heisenbergHom,
    ← universalChange_eq_heisenbergHom, map_formalCoordinate, ← _root_.map_inv]
  simp only [u, inv_inv]

/-- For every `i : ℕ+`, the coefficient of `z^(i + 1)` in `Strict.formalCoordinate` lies in
`Strict.arrowGrading (2 * i)`. -/
theorem coeff_succ_formalCoordinate_mem_arrowGrading (i : ℕ+) :
    PowerSeries.coeff (i + 1) formalCoordinate.toPowerSeries ∈ arrowGrading (2 * (i : ℕ)) := by
  simpa using (TauCeti.FormalCoordinate.mem_gradedSubgroup arrowGrading 2 formalCoordinate).mp
    formalCoordinate_mem_gradedSubgroup (i + 1)

end TauCeti.WeierstrassHopfAlgebroid.Strict
