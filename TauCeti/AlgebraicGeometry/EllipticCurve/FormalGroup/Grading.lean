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
neighbourhood by rescaling the formal parameter by `u⁻¹` (`formalCoordinate_scaling`,
`formalGroup_scaling_smul`, `formalW_scaling_smul`, `formalInvariantDifferentialDenom_scaling_smul`,
`invariantDifferential_formalGroup_scaling_smul`). Evaluating these scaling identities at the
Laurent degree unit `T (-2)` yields homological and weighted homogeneity of the universal
Weierstrass formal group law, `[k]`-series, `formalW`, the invariant differential, and the
universal strict formal coordinate transition `Strict.formalCoordinate`.

## Main definitions and results

* `WeierstrassCurve.formalGroup_scaling_smul`, `formalW_scaling_smul`,
  `formalInvariantDifferentialDenom_scaling_smul`, `invariantDifferential_formalGroup_scaling_smul`.
* `WeierstrassCurve.Universal.coeff_formalGroup_mem_baseGrading`,
  `coeff_nsmulSeries_formalGroup_mem_baseGrading`, `coeff_formalW_mem_baseGrading`,
  `coeff_formalInvariantDifferentialDenom_mem_baseGrading`,
  `coeff_invariantDifferential_formalGroup_mem_baseGrading` (and weighted-homogeneous forms).
* `TauCeti.WeierstrassHopfAlgebroid.Strict.formalCoordinate` and
  `formalCoordinate_mem_gradedSubgroup`.

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
    (scaling R u).formalDenom W = PowerSeries.C (u : R) ^ 3 := by simp [formalDenom_def]

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
  have hmul : PowerSeries.C ((u : R) ^ 2) * X * PowerSeries.C ((↑u⁻¹ : R) ^ 3) =
      PowerSeries.C ((u : R) ^ 2 * (↑u⁻¹ : R) ^ 2 * ↑u⁻¹) * X := by
    simp only [_root_.map_mul, map_pow]; ring
  rw [hmul, ← mul_pow, Units.mul_inv, one_pow, one_mul]

/-- Conjugating a strict Weierstrass change by `scaling R u` conjugates the induced formal
coordinate transition by `homothety u`. -/
theorem formalCoordinate_heisenbergHom_heisenbergAction (u : Rˣ) (a : TauCeti.HeisenbergGroup R)
    (W : WeierstrassCurve R) :
    (heisenbergHom R (heisenbergAction R u a)).formalCoordinate (scaling R u • W) =
      TauCeti.FormalCoordinate.homothety u * (heisenbergHom R a).formalCoordinate W *
        TauCeti.FormalCoordinate.homothety u⁻¹ := by
  rw [heisenbergHom_action R u a, formalCoordinate_mul, ← _root_.map_inv, formalCoordinate_scaling,
    inv_inv, _root_.map_inv, inv_smul_smul, formalCoordinate_mul, formalCoordinate_scaling,
    mul_assoc]

/-- Conjugating a strict Weierstrass change by `scaling R u` conjugates the inverse formal
coordinate transition by `homothety u`. -/
theorem inv_formalCoordinate_heisenbergHom_heisenbergAction (u : Rˣ) (a : TauCeti.HeisenbergGroup R)
    (W : WeierstrassCurve R) :
    ((heisenbergHom R (heisenbergAction R u a)).formalCoordinate (scaling R u • W))⁻¹ =
      TauCeti.FormalCoordinate.homothety u * ((heisenbergHom R a).formalCoordinate W)⁻¹ *
        TauCeti.FormalCoordinate.homothety u⁻¹ := by
  rw [formalCoordinate_heisenbergHom_heisenbergAction]; simp [mul_inv_rev, mul_assoc]

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

/-- **Pure scaling of the normalised invariant differential**: `P_{u • W}(z) = P_W(u⁻¹ z)`. -/
theorem invariantDifferential_formalGroup_scaling_smul (u : Rˣ) (W : WeierstrassCurve R) :
    (formalGroup (VariableChange.scaling R u • W)).invariantDifferential =
      PowerSeries.rescale (↑u⁻¹ : R) (formalGroup W).invariantDifferential := by
  rw [formalGroup_scaling_smul, FormalGroup.invariantDifferential_rescale]

/-- **Pure scaling of the invariant-differential denominator**: `G_{u • W}(z) = G_W(u⁻¹ z)`. -/
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

/-- **Pure scaling of the `w`-expansion**: `w_{u • W}(z) = u³ w_W(u⁻¹ z)`. -/
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

private theorem map_toLaurent_toPolynomial_eq_scaling {B : Type*} [CommRing B]
    (𝒜 : ℕ → Submodule ℤ B) [GradedAlgebra 𝒜]
    (f : MvPolynomial Coeff ℤ →+* B) (hf : ∀ i, f (.X i) ∈ 𝒜 (2 * coefficientWeight i)) :
    WeierstrassCurve.map (WeierstrassCurve.map Universal.curve f)
        (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
      VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T ↑(2 : ℕ) : LaurentPolynomial B))⁻¹ •
        WeierstrassCurve.map (WeierstrassCurve.map Universal.curve f) LaurentPolynomial.C := by
  let u : (LaurentPolynomial B)ˣ := (unitOfInvertible (LaurentPolynomial.T ↑(2 : ℕ)))⁻¹
  have hu : (↑u⁻¹ : LaurentPolynomial B) = LaurentPolynomial.T 2 := by simp [u]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [u, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, Universal.curve_a₁, Universal.curve_a₂,
      Universal.curve_a₃, Universal.curve_a₄, Universal.curve_a₆, RingHom.comp_apply,
      toPolynomial_of_mem (hf _), Polynomial.toLaurent_C_mul_T, VariableChange.scaling_apply,
      variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
      hu, LaurentPolynomial.T_pow, mul_zero, zero_mul, add_zero, sub_zero,
      zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), coefficientWeight_A₁,
      coefficientWeight_A₂, coefficientWeight_A₃, coefficientWeight_A₄, coefficientWeight_A₆,
      mul_comm] <;>
    rfl

/-! ### Homogeneity of the universal Weierstrass formal group and formal expansions -/

namespace Universal

open TauCeti.WeierstrassHopfAlgebroid

private abbrev degreeUnit : (LaurentPolynomial (MvPolynomial Coeff ℤ))ˣ :=
  (unitOfInvertible (LaurentPolynomial.T ↑(2 : ℕ)))⁻¹

private theorem val_degreeUnit :
    (degreeUnit : LaurentPolynomial (MvPolynomial Coeff ℤ)) = LaurentPolynomial.T (-2) := by
  simp [degreeUnit, val_inv_unitOfInvertible]

private theorem val_inv_degreeUnit :
    (↑degreeUnit⁻¹ : LaurentPolynomial (MvPolynomial Coeff ℤ)) = LaurentPolynomial.T 2 := by
  simp [degreeUnit]

private theorem map_toLaurent_toPolynomial_curve :
    WeierstrassCurve.map Universal.curve
        (Polynomial.toLaurent.comp (toPolynomial Strict.baseGrading)) =
      VariableChange.scaling _ degreeUnit •
        WeierstrassCurve.map Universal.curve LaurentPolynomial.C := by
  simpa [degreeUnit] using map_toLaurent_toPolynomial_eq_scaling Strict.baseGrading
    (RingHom.id _) Strict.X_mem_baseGrading

private theorem coeff_mem_baseGrading_of_rescale (P : PowerSeries (MvPolynomial Coeff ℤ))
    (hP : PowerSeries.map (Polynomial.toLaurent.comp (toPolynomial Strict.baseGrading)) P =
      PowerSeries.rescale (↑degreeUnit⁻¹) (PowerSeries.map LaurentPolynomial.C P)) (n : ℕ) :
    PowerSeries.coeff n P ∈ Strict.baseGrading (2 * n) := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have hexp : ((n : ℤ) * 2 : ℤ) = (2 * n : ℕ) := by push_cast; ring
  have h := congrArg (PowerSeries.coeff n) hP
  rwa [PowerSeries.coeff_map, RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
    val_inv_degreeUnit, LaurentPolynomial.T_pow, mul_comm (LaurentPolynomial.T _), hexp,
    ← Polynomial.toLaurent_C_mul_T] at h

/-- **Homological homogeneity of the universal Weierstrass formal group law**. -/
theorem coeff_formalGroup_mem_baseGrading (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries ∈
      Strict.baseGrading (2 * (d.degree - 1)) := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have hexp : ((d.degree - 1 : ℕ) * 2 : ℤ) = (2 * (d.degree - 1) : ℕ) := by push_cast; ring
  have h := congrArg (fun W ↦ MvPowerSeries.coeff d (formalGroup W).toPowerSeries)
    map_toLaurent_toPolynomial_curve
  rwa [map_formalGroup, formalGroup_scaling_smul, map_formalGroup, FormalGroup.map_toPowerSeries,
    FormalGroup.coeff_rescale, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map,
    RingHom.comp_apply, MvPowerSeries.coeff_map, val_inv_degreeUnit, LaurentPolynomial.T_pow,
    mul_comm (LaurentPolynomial.T _), hexp, ← Polynomial.toLaurent_C_mul_T] at h

/-- **Weighted homogeneity of the universal Weierstrass formal group law**. -/
theorem isWeightedHomogeneous_coeff_formalGroup (d : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries).IsWeightedHomogeneous
      coefficientWeight (d.degree - 1) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalGroup_mem_baseGrading d)

theorem coeff_nsmulSeries_formalGroup_mem_baseGrading (k m : ℕ) :
    PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k) ∈
      Strict.baseGrading (2 * (m - 1)) :=
  FormalGroup.coeff_nsmulSeries_mem (formalGroup Universal.curve) coeff_formalGroup_mem_baseGrading
    k m

theorem isWeightedHomogeneous_coeff_nsmulSeries_formalGroup (k m : ℕ) :
    (PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k)).IsWeightedHomogeneous
      coefficientWeight (m - 1) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_nsmulSeries_formalGroup_mem_baseGrading k m)

theorem coeff_formalW_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n (formalW Universal.curve) ∈ Strict.baseGrading (2 * (n - 3)) := by
  rcases n with _ | _ | _ | n
  · simp [coeff_formalW, zero_mem]
  · simp [coeff_formalW, zero_mem]
  · simp [coeff_formalW, zero_mem]
  · change PowerSeries.coeff (n + 3) (formalW Universal.curve) ∈ Strict.baseGrading (2 * n)
    apply toPolynomial_eq_monomial_iff.mp
    apply Polynomial.toLaurent_injective
    have hexp : ((3 : ℕ) * (-2 : ℤ) + (n + 3 : ℕ) * 2 : ℤ) = (2 * n : ℕ) := by push_cast; ring
    have h := congrArg (PowerSeries.coeff (n + 3) ∘ formalW) map_toLaurent_toPolynomial_curve
    rwa [Function.comp_apply, Function.comp_apply, map_formalW, formalW_scaling_smul, map_formalW,
      PowerSeries.coeff_map, RingHom.comp_apply, PowerSeries.coeff_smul, PowerSeries.coeff_rescale,
      PowerSeries.coeff_map, val_degreeUnit, val_inv_degreeUnit, smul_eq_mul,
      LaurentPolynomial.T_pow, LaurentPolynomial.T_pow, ← mul_assoc, ← LaurentPolynomial.T_add,
      mul_comm (LaurentPolynomial.T _), hexp, ← Polynomial.toLaurent_C_mul_T] at h

theorem isWeightedHomogeneous_coeff_formalW (n : ℕ) :
    (PowerSeries.coeff n (formalW Universal.curve)).IsWeightedHomogeneous
      coefficientWeight (n - 3) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalW_mem_baseGrading n)

theorem coeff_formalInvariantDifferentialDenom_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom ∈
      Strict.baseGrading (2 * n) :=
  coeff_mem_baseGrading_of_rescale _ (by
    have h := congrArg formalInvariantDifferentialDenom map_toLaurent_toPolynomial_curve
    rwa [map_formalInvariantDifferentialDenom, formalInvariantDifferentialDenom_scaling_smul,
      map_formalInvariantDifferentialDenom] at h) n

theorem isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom (n : ℕ) :
    (PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom).IsWeightedHomogeneous
      coefficientWeight n :=
  Strict.mem_baseGrading_two_mul_iff.mp
    (coeff_formalInvariantDifferentialDenom_mem_baseGrading n)

theorem coeff_invariantDifferential_formalGroup_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n (formalGroup Universal.curve).invariantDifferential ∈
      Strict.baseGrading (2 * n) :=
  coeff_mem_baseGrading_of_rescale _ (by
    have h := congrArg (fun W ↦ (formalGroup W).invariantDifferential)
      map_toLaurent_toPolynomial_curve
    rwa [invariantDifferential_formalGroup_scaling_smul, map_formalGroup,
      ← FormalGroup.map_invariantDifferential, map_formalGroup,
      ← FormalGroup.map_invariantDifferential] at h) n

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
        (WeierstrassCurve.map Universal.curve C))⁻¹ := (rfl)

theorem formalCoordinate_eq_inv_formalCoordinate :
    formalCoordinate =
      (universalChange (MvPolynomial Coeff ℤ))⁻¹.formalCoordinate
        (WeierstrassCurve.map Universal.curve rightUnit) := by
  rw [map_rightUnit, formalCoordinate_inv]; rfl

@[simp] theorem linearCoeff_formalCoordinate :
    TauCeti.FormalCoordinate.linearCoeff formalCoordinate = 1 := by simp [formalCoordinate]

theorem formalCoordinate_mem_ker_linearCoeff :
    formalCoordinate ∈ (TauCeti.FormalCoordinate.linearCoeff (R := ArrowRing)).ker :=
  MonoidHom.mem_ker.mpr linearCoeff_formalCoordinate

theorem formalCoordinate_smul_formalGroup :
    formalCoordinate • formalGroup (WeierstrassCurve.map Universal.curve C) =
      formalGroup (WeierstrassCurve.map Universal.curve rightUnit) := by
  rw [map_rightUnit, formalGroup_smul]; rfl

@[simp] theorem map_lift_formalCoordinate {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (a : TauCeti.HeisenbergGroup R) :
    formalCoordinate.map (lift (W.specialize, a)) =
      ((heisenbergHom R a).formalCoordinate W)⁻¹ := by
  rw [formalCoordinate, _root_.map_inv, ← map_formalCoordinate, map_lift_universalChange,
    WeierstrassCurve.map_map, lift_comp_C]
  congr 2; exact WeierstrassCurve.map_specialize W

@[simp] theorem coeff_one_formalCoordinate :
    PowerSeries.coeff 1 formalCoordinate.toPowerSeries = 1 := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_one_formalCoordinate]
  simp [inv_def]

@[simp] theorem coeff_two_formalCoordinate :
    PowerSeries.coeff 2 formalCoordinate.toPowerSeries = -(X 1 : ArrowRing) := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_two_formalCoordinate]
  simp [inv_def]

@[simp] theorem coeff_three_formalCoordinate :
    PowerSeries.coeff 3 formalCoordinate.toPowerSeries = X 1 ^ 2 - (X 0 : ArrowRing) := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_three_formalCoordinate]
  simp [inv_def]; ring

@[simp] theorem coeff_four_formalCoordinate :
    PowerSeries.coeff 4 formalCoordinate.toPowerSeries =
      -X 2 - X 1 ^ 3 + 2 * X 0 * X 1 - C (X .A₁) * (X 0 : ArrowRing) := by
  rw [formalCoordinate_eq_inv_formalCoordinate, VariableChange.coeff_four_formalCoordinate]
  simp [inv_def, variableChange_a₁]; ring

/-- **Homological homogeneity of the universal strict Weierstrass formal coordinate**. -/
theorem formalCoordinate_mem_gradedSubgroup :
    formalCoordinate ∈ TauCeti.FormalCoordinate.gradedSubgroup arrowGrading 2 := by
  rw [TauCeti.FormalCoordinate.mem_gradedSubgroup,
    ← TauCeti.FormalCoordinate.map_toLaurent_eq_conjugate_iff]
  let ω : ArrowRing →+* LaurentPolynomial ArrowRing :=
    Polynomial.toLaurent.comp (toPolynomial arrowGrading)
  let u : (LaurentPolynomial ArrowRing)ˣ := (unitOfInvertible (LaurentPolynomial.T ↑(2 : ℕ)))⁻¹
  have hu : (↑u⁻¹ : LaurentPolynomial ArrowRing) = LaurentPolynomial.T 2 := by simp [u]
  have hW := WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling arrowGrading C
    fun i ↦ C_mem_arrowGrading (X_mem_baseGrading i)
  have hC : (universalChange (MvPolynomial Coeff ℤ)).map ω =
      heisenbergHom _ (heisenbergAction _ u
        (HeisenbergGroup.map LaurentPolynomial.C
          (universalHeisenberg (MvPolynomial Coeff ℤ)))) := by
    rw [universalChange_eq_heisenbergHom, map_heisenbergHom]
    congr 1
    ext <;>
      simp only [ω, HeisenbergGroup.map_apply, universalHeisenberg_x, universalHeisenberg_y,
        universalHeisenberg_z, heisenbergAction_apply, RingHom.comp_apply,
        toPolynomial_of_mem (X_mem_arrowGrading _), strictCoordDegree_zero, strictCoordDegree_one,
        strictCoordDegree_two, Polynomial.toLaurent_C_mul_T, hu, LaurentPolynomial.T_pow,
        mul_comm] <;>
      rfl
  rw [formalCoordinate, _root_.map_inv, ← map_formalCoordinate, hC, hW,
    inv_formalCoordinate_heisenbergHom_heisenbergAction, ← map_heisenbergHom,
    ← universalChange_eq_heisenbergHom, map_formalCoordinate, ← _root_.map_inv]
  simp only [u, inv_inv]

theorem coeff_succ_formalCoordinate_mem_arrowGrading (i : ℕ+) :
    PowerSeries.coeff (i + 1) formalCoordinate.toPowerSeries ∈ arrowGrading (2 * (i : ℕ)) := by
  simpa using (TauCeti.FormalCoordinate.mem_gradedSubgroup arrowGrading 2 formalCoordinate).mp
    formalCoordinate_mem_gradedSubgroup (i + 1)

end TauCeti.WeierstrassHopfAlgebroid.Strict
