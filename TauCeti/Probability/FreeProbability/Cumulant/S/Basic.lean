/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.SubstInv
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The formal S-series

For a normalized function `φ : A → R` on a monoid and an element `a` with unit mean, put
`Ψ(z) = M(z) - 1`. Its formal S-series is

`S(z) = (1 + z) Ψ⁻¹(z) / z`,

where the inverse is for substitution and division by `z` removes its zero constant
coefficient. The moment–cumulant equation identifies this series with `C₀⁻¹(z) / z`, where
`C₀(z) = C(z) - 1 = z R(z)`, so `z S(z)` is a two-sided compositional inverse of `C₀`, which
characterizes `S`. In particular its constant coefficient is the inverse mean and
it is a unit power series. These are formal identities over a commutative ring; they assert
no analytic convergence. The identity and scalar laws `S_1(z) = 1`, `S_{c a}(z) = c⁻¹ S_a(z)`, and
`S_{c · 1}(z) = c⁻¹` are `TauCeti.sSeries_one`, `TauCeti.sSeries_smul`, and
`TauCeti.sSeries_algebraMap`; the multiplicativity `S_{ab} = S_a S_b` for free `a` and `b` is
`TauCeti.IsFreelyIndependent.sSeries_mul`.

At the level of power series, every `f : R⟦X⟧` with unit linear coefficient `coeff 1 f` determines
a formal coordinate `f.toFormalCoordinate hf = f - C (constantCoeff f)` and hence a unit formal
S-series `f.boxedSSeries hf = (f - f(0))⁻¹ / X` (`PowerSeries.boxedSSeriesUnit`,
`PowerSeries.boxedSSeries`). For a normalised functional `φ`, `TauCeti.sSeries φ a ha` is the
boxed S-series of `freeCumulantSeries φ a` (`TauCeti.sSeries_eq_boxedSSeries_freeCumulantSeries`),
and without normalisation `TauCeti.sSeries φ a ha = (1 + X) * (momentSeries φ a).boxedSSeries _`
(`TauCeti.sSeries_eq_one_add_X_mul_boxedSSeries_momentSeries`), from which `TauCeti.sSeries_smul`
follows by `PowerSeries.boxedSSeries_rescale`.

The definition also makes sense without normalization, following the convention for
`momentSeries`; the scalar law `TauCeti.sSeries_smul` holds without normalization, while the
interpretation as the inverse of `Ψ` and the cumulant comparison use `φ 1 = 1`. Requiring a unit
mean is the ring-valued form of the nonzero-mean condition over a field.

## Main definitions

* `PowerSeries.boxedSSeriesUnit`, `PowerSeries.boxedSSeries`: the formal S-series `(f - f(0))⁻¹ / X`
  of `f` (with `(f - f(0))⁻¹` the compositional inverse of `f - C (constantCoeff f)`), as a unit of
  `R⟦X⟧` and as a power series.
* `TauCeti.sSeries`: the formal S-series `(1 + X) (M_a - 1)⁻¹ / X` of an element `a` with unit
  mean.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 16–18.
* The formal construction uses Mathlib's `PowerSeries.substInvOfIsUnit` and its substitution
  inverse laws, and `PowerSeries.eq_X_mul_shift_add_const` to remove a factor of `X`.
-/

public section

namespace PowerSeries

open TauCeti

section SeriesSSeries

variable {R : Type*} [CommRing R]

/-- The formal S-series `(f - f(0))⁻¹ / X` of a power series `f` with unit linear coefficient,
where `(f - f(0))⁻¹` denotes the compositional inverse of `f - C (constantCoeff f)`, packaged as a
unit of `R⟦X⟧`. -/
noncomputable def boxedSSeriesUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) : R⟦X⟧ˣ :=
  (f.toFormalCoordinate hf)⁻¹.unitsEquiv

theorem boxedSSeriesUnit_def (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    f.boxedSSeriesUnit hf = (f.toFormalCoordinate hf)⁻¹.unitsEquiv := (rfl)

/-- The formal S-series `(f - f(0))⁻¹ / X` of a power series `f` with unit linear coefficient,
where `(f - f(0))⁻¹` denotes the compositional inverse of `f - C (constantCoeff f)`. For a
normalised functional `φ`, the boxed S-series of `freeCumulantSeries φ a` coincides with
`TauCeti.sSeries φ a ha`. -/
noncomputable def boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) : R⟦X⟧ :=
  (f.boxedSSeriesUnit hf : R⟦X⟧)

@[simp]
theorem val_boxedSSeriesUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (f.boxedSSeriesUnit hf : R⟦X⟧) = f.boxedSSeries hf := (rfl)

/-- Multiplying `f.boxedSSeries hf` by `X` recovers the compositional inverse of
`f - C (constantCoeff f)`. -/
theorem X_mul_boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    X * f.boxedSSeries hf =
      (f - C (constantCoeff f)).substInvOfIsUnit (by simpa [coeff_C] using hf) := by
  rw [boxedSSeries, boxedSSeriesUnit, FormalCoordinate.X_mul_val_unitsEquiv,
    FormalCoordinate.toPowerSeries_inv]
  exact substInvOfIsUnit_congr (toPowerSeries_toFormalCoordinate f hf) _ _

/-- The boxed S-series as the coefficient shift of the compositional inverse of
`f - C (constantCoeff f)`. -/
theorem boxedSSeries_eq_shift_substInvOfIsUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    f.boxedSSeries hf = mk fun n =>
      coeff (n + 1) ((f - C (constantCoeff f)).substInvOfIsUnit (by simpa [coeff_C] using hf)) := by
  ext n; rw [coeff_mk, ← X_mul_boxedSSeries, coeff_succ_X_mul]

/-- The constant coefficient of `f.boxedSSeriesUnit hf` as a unit of `R` is `(coeff 1 f)⁻¹`. -/
@[simp]
theorem units_map_constantCoeff_boxedSSeriesUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    Units.map ↑(constantCoeff (R := R)) (f.boxedSSeriesUnit hf) = hf.unit⁻¹ := by
  rw [boxedSSeriesUnit, FormalCoordinate.units_map_constantCoeff_unitsEquiv, map_inv,
    linearCoeff_toFormalCoordinate]

/-- The constant coefficient of `f.boxedSSeries hf` is the inverse of `coeff 1 f`. -/
@[simp]
theorem constantCoeff_boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    constantCoeff (f.boxedSSeries hf) = Ring.inverse (coeff 1 f) := by
  have h := congrArg Units.val (units_map_constantCoeff_boxedSSeriesUnit f hf)
  rw [Units.coe_map] at h; simpa [Ring.inverse_of_isUnit hf] using h

/-- `f.boxedSSeries hf` is a unit of `R⟦X⟧`. -/
@[simp]
theorem isUnit_boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) : IsUnit (f.boxedSSeries hf) :=
  (f.boxedSSeriesUnit hf).isUnit

/-- The right compositional inverse equation `(f - f(0))(X * S_f) = X`. -/
@[simp]
theorem sub_C_constantCoeff_subst_X_mul_boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (f - C (constantCoeff f)).subst (X * f.boxedSSeries hf) = X := by
  have h := (f.toFormalCoordinate hf).toPowerSeries_mul_inv
  rwa [FormalCoordinate.toPowerSeries_mul, toPowerSeries_toFormalCoordinate,
    ← FormalCoordinate.X_mul_val_unitsEquiv, ← boxedSSeriesUnit_def, val_boxedSSeriesUnit] at h

/-- The left compositional inverse equation `(X * S_f)(f - f(0)) = X`. -/
@[simp]
theorem X_mul_boxedSSeries_subst_sub_C_constantCoeff (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (X * f.boxedSSeries hf).subst (f - C (constantCoeff f)) = X := by
  have h := (f.toFormalCoordinate hf).toPowerSeries_inv_mul
  rwa [FormalCoordinate.toPowerSeries_mul, toPowerSeries_toFormalCoordinate,
    ← FormalCoordinate.X_mul_val_unitsEquiv, ← boxedSSeriesUnit_def, val_boxedSSeriesUnit] at h

/-- `f.boxedSSeries hf` is uniquely determined by `(f - f(0))(X * S) = X`. -/
theorem eq_boxedSSeries_of_subst_X_mul_eq {f : R⟦X⟧} (hf : IsUnit (coeff 1 f)) {S : R⟦X⟧}
    (hS : (f - C (constantCoeff f)).subst (X * S) = X) : S = f.boxedSSeries hf :=
  X_mul_injective <| ((f - C (constantCoeff f)).eq_substInvOfIsUnit_of_subst_eq_X (by simp)
    (by simpa [coeff_C] using hf) (.of_constantCoeff_zero' (by simp)) hS).trans
    (X_mul_boxedSSeries f hf).symm

/-- Characterisation of `f.boxedSSeries hf` by the right compositional inverse equation. -/
theorem eq_boxedSSeries_iff {f : R⟦X⟧} (hf : IsUnit (coeff 1 f)) {S : R⟦X⟧} :
    S = f.boxedSSeries hf ↔ (f - C (constantCoeff f)).subst (X * S) = X :=
  ⟨by rintro rfl; exact sub_C_constantCoeff_subst_X_mul_boxedSSeries f hf,
    eq_boxedSSeries_of_subst_X_mul_eq hf⟩

/-- `boxedSSeriesUnit` depends only on the positive-degree coefficients of `f`. -/
theorem boxedSSeriesUnit_congr {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g))
    (h : ∀ k, k ≠ 0 → coeff k f = coeff k g) : f.boxedSSeriesUnit hf = g.boxedSSeriesUnit hg :=
  congrArg (fun φ => φ⁻¹.unitsEquiv) (toFormalCoordinate_congr hf hg h)

/-- Adding a constant series on the left leaves `boxedSSeriesUnit` unchanged. -/
@[simp]
theorem boxedSSeriesUnit_C_add (c : R) (f : R⟦X⟧) (hf : IsUnit (coeff 1 (C c + f))) :
    (C c + f).boxedSSeriesUnit hf = f.boxedSSeriesUnit (by simpa [coeff_C] using hf) := by
  simp_rw [boxedSSeriesUnit_def, toFormalCoordinate_C_add]

/-- Adding a constant series on the right leaves `boxedSSeriesUnit` unchanged. -/
@[simp]
theorem boxedSSeriesUnit_add_C (f : R⟦X⟧) (c : R) (hf : IsUnit (coeff 1 (f + C c))) :
    (f + C c).boxedSSeriesUnit hf = f.boxedSSeriesUnit (by simpa [coeff_C] using hf) := by
  simp_rw [boxedSSeriesUnit_def, toFormalCoordinate_add_C]

/-- Subtracting a constant series leaves `boxedSSeriesUnit` unchanged. -/
@[simp]
theorem boxedSSeriesUnit_sub_C (f : R⟦X⟧) (c : R) (hf : IsUnit (coeff 1 (f - C c))) :
    (f - C c).boxedSSeriesUnit hf = f.boxedSSeriesUnit (by simpa [coeff_C] using hf) := by
  simp_rw [boxedSSeriesUnit_def, toFormalCoordinate_sub_C]

/-- `boxedSSeries` depends only on the positive-degree coefficients of `f`. -/
theorem boxedSSeries_congr {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g))
    (h : ∀ k, k ≠ 0 → coeff k f = coeff k g) : f.boxedSSeries hf = g.boxedSSeries hg :=
  congrArg Units.val (boxedSSeriesUnit_congr hf hg h)

/-- Adding a constant series on the left leaves `boxedSSeries` unchanged. -/
@[simp]
theorem boxedSSeries_C_add (c : R) (f : R⟦X⟧) (hf : IsUnit (coeff 1 (C c + f))) :
    (C c + f).boxedSSeries hf = f.boxedSSeries (by simpa [coeff_C] using hf) :=
  congrArg Units.val (boxedSSeriesUnit_C_add c f hf)

/-- Adding a constant series on the right leaves `boxedSSeries` unchanged. -/
@[simp]
theorem boxedSSeries_add_C (f : R⟦X⟧) (c : R) (hf : IsUnit (coeff 1 (f + C c))) :
    (f + C c).boxedSSeries hf = f.boxedSSeries (by simpa [coeff_C] using hf) :=
  congrArg Units.val (boxedSSeriesUnit_add_C f c hf)

/-- Subtracting a constant series leaves `boxedSSeries` unchanged. -/
@[simp]
theorem boxedSSeries_sub_C (f : R⟦X⟧) (c : R) (hf : IsUnit (coeff 1 (f - C c))) :
    (f - C c).boxedSSeries hf = f.boxedSSeries (by simpa [coeff_C] using hf) :=
  congrArg Units.val (boxedSSeriesUnit_sub_C f c hf)

/-- Base change commutes with `boxedSSeriesUnit`. -/
@[simp]
theorem map_boxedSSeriesUnit {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf : IsUnit (coeff 1 f)) :
    Units.map ↑(map α) (f.boxedSSeriesUnit hf) =
      (map α f).boxedSSeriesUnit (by simpa using hf.map α) := by
  simp_rw [boxedSSeriesUnit_def, FormalCoordinate.map_unitsEquiv, map_inv, map_toFormalCoordinate]

/-- Base change commutes with `boxedSSeries`. -/
@[simp]
theorem map_boxedSSeries {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf : IsUnit (coeff 1 f)) :
    map α (f.boxedSSeries hf) = (map α f).boxedSSeries (by simpa using hf.map α) :=
  congrArg Units.val (map_boxedSSeriesUnit α f hf)

/-- Rescaling `f` by a unit `c` multiplies `f.boxedSSeriesUnit` by `C c⁻¹`. -/
theorem boxedSSeriesUnit_rescale {c : R} (hc : IsUnit c) (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (rescale c f).boxedSSeriesUnit (by simpa [coeff_rescale] using hc.mul hf) =
      Units.map ↑(C (R := R)) hc.unit⁻¹ * f.boxedSSeriesUnit hf := by
  simp_rw [boxedSSeriesUnit_def, toFormalCoordinate_rescale hc f hf, mul_inv_rev, ← map_inv,
    FormalCoordinate.unitsEquiv_homothety_mul]

/-- Rescaling `f` by a unit `c` scales `f.boxedSSeries` by `c⁻¹`. -/
theorem boxedSSeries_rescale {c : R} (hc : IsUnit c) (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (rescale c f).boxedSSeries (by simpa [coeff_rescale] using hc.mul hf) =
      Ring.inverse c • f.boxedSSeries hf := by
  simpa [Algebra.smul_def, Ring.inverse_of_isUnit hc] using
    congrArg Units.val (boxedSSeriesUnit_rescale hc f hf)

@[simp]
theorem boxedSSeries_one_add_X : (1 + X : R⟦X⟧).boxedSSeries (by simp) = 1 :=
  (eq_boxedSSeries_of_subst_X_mul_eq _ (by simp)).symm

@[simp]
theorem boxedSSeriesUnit_one_add_X : (1 + X : R⟦X⟧).boxedSSeriesUnit (by simp) = 1 :=
  Units.ext boxedSSeries_one_add_X

@[simp]
theorem boxedSSeries_X : (X : R⟦X⟧).boxedSSeries (by simp) = 1 :=
  (eq_boxedSSeries_of_subst_X_mul_eq _ (by simp)).symm

@[simp]
theorem boxedSSeriesUnit_X : (X : R⟦X⟧).boxedSSeriesUnit (by simp) = 1 :=
  Units.ext boxedSSeries_X

/-- The boxed S-series of `c X` for a unit scalar `c` is the constant series `c⁻¹`. -/
theorem boxedSSeries_C_mul_X {c : R} (hc : IsUnit c) :
    (C c * X).boxedSSeries (by simpa [coeff_C_mul] using hc) = C (Ring.inverse c) := by
  refine (boxedSSeries_congr _ (by simpa [coeff_rescale] using hc)
    fun k _ => congrArg (coeff k) (rescale_X c).symm).trans ?_
  rw [boxedSSeries_rescale hc X (by simp), boxedSSeries_X, Algebra.smul_def, mul_one, algebraMap_eq]

end SeriesSSeries

end PowerSeries

open PowerSeries

namespace TauCeti

variable {R A : Type*} [CommRing R]

section Monoid

variable [Monoid A] (φ : A → R) (a : A)

/-- A unit mean gives a unit linear coefficient of the reduced moment series `Ψ = M - 1`. -/
theorem isUnit_coeff_one_momentSeries_sub_one (ha : IsUnit (φ a)) :
    IsUnit (coeff 1 (momentSeries φ a - 1)) := by
  simpa using ha

/-- A unit mean gives a unit linear coefficient of `C₀ = C - 1`. -/
theorem isUnit_coeff_one_freeCumulantSeries_sub_one (ha : IsUnit (φ a)) :
    IsUnit (coeff 1 (freeCumulantSeries φ a - 1)) := by
  simpa [coeff_one_freeCumulantSeries] using ha

/-- The formal S-series `(1 + X) Ψ⁻¹ / X` of an element with unit mean. For its usual
interpretation as an inverse-transform expression, the functional must satisfy `φ 1 = 1`.
The factor `X` is removed by shifting the coefficients of the compositional inverse. -/
noncomputable def sSeries (ha : IsUnit (φ a)) : R⟦X⟧ :=
  (1 + X) * mk (fun n => coeff (n + 1)
    ((momentSeries φ a - 1).substInvOfIsUnit (isUnit_coeff_one_momentSeries_sub_one φ a ha)))

/-- The defining expression for the formal S-series, with division by `X` written as a
coefficient shift. -/
theorem sSeries_def (ha : IsUnit (φ a)) :
    sSeries φ a ha = (1 + X) * mk (fun n => coeff (n + 1)
      ((momentSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_momentSeries_sub_one φ a ha))) := (rfl)

/-- Multiplication by `X` restores the compositional inverse in the definition of `S`. -/
theorem X_mul_sSeries (ha : IsUnit (φ a)) :
    X * sSeries φ a ha = (1 + X) * (momentSeries φ a - 1).substInvOfIsUnit
      (isUnit_coeff_one_momentSeries_sub_one φ a ha) := by
  rw [sSeries_def, ← mul_assoc, mul_comm X (1 + X), mul_assoc]
  congr 1
  simpa using (eq_X_mul_shift_add_const ((momentSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_momentSeries_sub_one φ a ha))).symm

/-- The constant coefficient of the S-series is the inverse of the mean. -/
@[simp]
theorem constantCoeff_sSeries (ha : IsUnit (φ a)) :
    constantCoeff (sSeries φ a ha) = Ring.inverse (φ a) := by
  simp [sSeries_def, coeff_one_substInvOfIsUnit, ← Ring.inverse_of_isUnit]

/-- The S-series of an element with unit mean is a unit of the power series ring. -/
theorem isUnit_sSeries (ha : IsUnit (φ a)) : IsUnit (sSeries φ a ha) :=
  isUnit_iff_constantCoeff.mpr (constantCoeff_sSeries φ a ha ▸ ha.ringInverse)

variable {φ}

/-- The cumulant expression for the S-series: `X S = C₀⁻¹`, where `C₀ = C - 1`. -/
theorem X_mul_sSeries_eq_substInvOfIsUnit (hφ : φ 1 = 1) (ha : IsUnit (φ a)) :
    X * sSeries φ a ha = (freeCumulantSeries φ a - 1).substInvOfIsUnit
      (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha) := by
  let I := (momentSeries φ a - 1).substInvOfIsUnit (isUnit_coeff_one_momentSeries_sub_one φ a ha)
  have hI : HasSubst I := .substInvOfIsUnit _ _
  have hM : HasSubst (X * momentSeries φ a) := .of_constantCoeff_zero' (by simp)
  have hMI : (momentSeries φ a).subst I = 1 + X := by
    have h := (momentSeries φ a - 1).subst_substInvOfIsUnit_right
      (by simp [hφ]) (isUnit_coeff_one_momentSeries_sub_one φ a ha)
    rw [subst_sub hI, subst_one] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hcomp : (X * momentSeries φ a).subst I = (1 + X) * I := by
    rw [subst_mul hI, subst_X hI, hMI, mul_comm]
  rw [X_mul_sSeries]
  apply (freeCumulantSeries φ a - 1).eq_substInvOfIsUnit_of_subst_eq_X (by simp) _
    (.of_constantCoeff_zero' (by simp))
  rw [← hcomp, ← subst_comp_subst_apply hM hI, subst_sub hM, subst_one,
    freeCumulantSeries_subst_X_mul_momentSeries a hφ, subst_substInvOfIsUnit_right _ (by simp [hφ])]

/-- The formal S-series agrees with `C₀⁻¹ / X`, with division expressed by a coefficient
shift. This identifies the moment and cumulant definitions of the S-transform. -/
theorem sSeries_eq_shift_substInvOfIsUnit (hφ : φ 1 = 1) (ha : IsUnit (φ a)) :
    sSeries φ a ha = mk (fun n => coeff (n + 1)
      ((freeCumulantSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha))) := by
  apply X_mul_injective; dsimp only
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ ha]
  simpa using eq_X_mul_shift_add_const ((freeCumulantSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha))

/-- A series is the S-series if multiplying it by `X` gives a right compositional inverse
of `C₀ = C - 1`. -/
theorem eq_sSeries_of_subst_X_mul_eq (hφ : φ 1 = 1) (ha : IsUnit (φ a)) {S : R⟦X⟧}
    (hS : (freeCumulantSeries φ a - 1).subst (X * S) = X) : S = sSeries φ a ha :=
  X_mul_injective <| ((freeCumulantSeries φ a - 1).eq_substInvOfIsUnit_of_subst_eq_X
    (by simp) (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha)
    (.of_constantCoeff_zero' (by simp)) hS).trans (X_mul_sSeries_eq_substInvOfIsUnit a hφ ha).symm

/-- The right inverse equation `(C - 1)(X * S) = X`. -/
@[simp]
theorem freeCumulantSeries_sub_one_subst_X_mul_sSeries (hφ : φ 1 = 1) (ha : IsUnit (φ a)) :
    (freeCumulantSeries φ a - 1).subst (X * sSeries φ a ha) = X := by
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ ha, subst_substInvOfIsUnit_right _ (by simp)]

/-- The left inverse equation `(X * S)(C - 1) = X`. -/
@[simp]
theorem X_mul_sSeries_subst_freeCumulantSeries_sub_one (hφ : φ 1 = 1) (ha : IsUnit (φ a)) :
    (X * sSeries φ a ha).subst (freeCumulantSeries φ a - 1) = X := by
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ ha, subst_substInvOfIsUnit_left _ (by simp)]

/-- The S-series is characterized by the right inverse equation for `C - 1`. -/
theorem eq_sSeries_iff (hφ : φ 1 = 1) (ha : IsUnit (φ a)) {S : R⟦X⟧} :
    S = sSeries φ a ha ↔ (freeCumulantSeries φ a - 1).subst (X * S) = X :=
  ⟨by rintro rfl; exact freeCumulantSeries_sub_one_subst_X_mul_sSeries a hφ ha,
    eq_sSeries_of_subst_X_mul_eq a hφ ha⟩

/-- Equal moment series give equal S-series, even when the underlying monoids differ. -/
theorem sSeries_congr {B : Type*} [Monoid B] {ψ : B → R} {b : B}
    (ha : IsUnit (φ a)) (hb : IsUnit (ψ b))
    (h : momentSeries φ a = momentSeries ψ b) : sSeries φ a ha = sSeries ψ b hb := by
  rw [sSeries_def, sSeries_def]; congr 1; ext n; simp only [coeff_mk]; congr 2
  exact congrArg (· - 1) h

end Monoid

section MonoidBridge

variable [Monoid A]

/-- For a normalised functional `φ`, the formal S-series `sSeries φ a ha` is the boxed S-series of
the free cumulant series `freeCumulantSeries φ a`. -/
theorem sSeries_eq_boxedSSeries_freeCumulantSeries {φ : A → R} (hφ : φ 1 = 1) (a : A)
    (ha : IsUnit (φ a)) :
    sSeries φ a ha =
      (freeCumulantSeries φ a).boxedSSeries (by rwa [coeff_one_freeCumulantSeries]) :=
  (eq_sSeries_of_subst_X_mul_eq a hφ ha <| by
    simpa [constantCoeff_freeCumulantSeries] using
      sub_C_constantCoeff_subst_X_mul_boxedSSeries (freeCumulantSeries φ a)
        (by rwa [coeff_one_freeCumulantSeries])).symm

/-- The formal S-series `sSeries φ a ha` equals `(1 + X)` times the boxed S-series of
`momentSeries φ a`; for a normalised functional `φ`, this reflects `C_a = M_a ⊠ μ` and
`S_μ = 1 + X`. -/
theorem sSeries_eq_one_add_X_mul_boxedSSeries_momentSeries {φ : A → R} (a : A) (ha : IsUnit (φ a)) :
    sSeries φ a ha = (1 + X) * (momentSeries φ a).boxedSSeries (by simpa using ha) := by
  rw [sSeries_def, boxedSSeries_eq_shift_substInvOfIsUnit]
  congr 1; ext n; simp only [coeff_mk]; congr 1
  exact substInvOfIsUnit_eq_of_coeff_eq _ _ fun k hk => by simp [coeff_C, hk]

/-- The formal S-series of the identity element `1` for a normalised `φ` is `1`. -/
@[simp]
theorem sSeries_one {φ : A → R} (hφ : φ 1 = 1) (h1 : IsUnit (φ 1)) :
    sSeries φ (1 : A) h1 = 1 :=
  (eq_sSeries_of_subst_X_mul_eq (1 : A) hφ h1 (by rw [freeCumulantSeries_one hφ]; simp)).symm

end MonoidBridge

section Algebra

variable [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- Rescaling a variable `a` of unit mean by a unit scalar `c` scales its formal S-series by the
inverse of `c`: `S_{c a}(z) = c⁻¹ S_a(z)`. -/
theorem sSeries_smul {a : A} (ha : IsUnit (φ a)) {c : R} (hc : IsUnit c) :
    sSeries φ (c • a) (by simpa [smul_eq_mul] using hc.mul ha) =
      Ring.inverse c • sSeries φ a ha := by
  rw [sSeries_eq_one_add_X_mul_boxedSSeries_momentSeries,
    sSeries_eq_one_add_X_mul_boxedSSeries_momentSeries,
    boxedSSeries_congr _ (by simpa [coeff_rescale] using hc.mul ha)
      (fun k _ => congrArg (coeff k) (momentSeries_smul φ c a)),
    boxedSSeries_rescale hc, mul_smul_comm]

/-- A scalar variable of unit value has the constant S-series given by its inverse. -/
@[simp]
theorem sSeries_algebraMap (hφ : φ 1 = 1) (c : R) (hc : IsUnit c) :
    sSeries φ (algebraMap R A c) (by simpa [Algebra.algebraMap_eq_smul_one, hφ] using hc) =
      C (Ring.inverse c) := by
  refine (sSeries_congr _ _ _ (congrArg (momentSeries φ) (Algebra.algebraMap_eq_smul_one c))).trans
    ((sSeries_smul (hφ ▸ isUnit_one) hc).trans ?_)
  rw [sSeries_one hφ, Algebra.smul_def, mul_one, algebraMap_eq]

end Algebra

end TauCeti
