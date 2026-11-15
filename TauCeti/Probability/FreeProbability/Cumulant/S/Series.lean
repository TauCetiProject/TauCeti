/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.BoxedConvolution.Associative
public import TauCeti.Probability.FreeProbability.Cumulant.S.Free
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import TauCeti.RingTheory.PowerSeries.Geometric
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The formal S-series of a power series and boxed convolution

Over a commutative ring `R`, every formal power series `f : R⟦X⟧` with unit linear coefficient
`coeff 1 f` determines a formal coordinate `f.toFormalCoordinate hf = f - C (constantCoeff f)` and
hence a unit formal S-series

`f.boxedSSeries hf = (f - f(0))⁻¹ / X`,

packaged as `f.boxedSSeriesUnit hf : R⟦X⟧ˣ` via `FormalCoordinate.unitsEquiv`. For a normalised
linear functional `φ` and an element `a` of unit mean, the S-series `TauCeti.sSeries φ a ha` is the
boxed S-series of `C_a` (`TauCeti.sSeries_eq_boxedSSeries_freeCumulantSeries`).

Combining universal algebraic realisation (`TauCeti.exists_freeProduct_freeCumulantSeries_eq`) with
multiplicativity of the S-series for two free elements
(`TauCeti.IsFreelyIndependentElements.sSeries_mul`) shows that `PowerSeries.boxedSSeries` converts
scalar boxed convolution into Cauchy multiplication:
`(f.boxedConvolution g).boxedSSeries _ = f.boxedSSeries hf * g.boxedSSeries hg` for arbitrary
constant coefficients. Together with the explicit inverse map `u ↦ 1 + (X u)⁻¹`
(`PowerSeries.ofBoxedSSeriesUnit`), this evaluates `PowerSeries.boxedSSeries` on the zeta series
`∑_{n ≥ 0} Xⁿ` (`∑_{n ≥ 0} (-X)ⁿ`) and the Möbius series `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) Xⁿ`
(`1 + X`), recovering `sSeries φ a ha = (1 + X) * (momentSeries φ a).boxedSSeries _`.

## Main definitions

* `PowerSeries.toFormalCoordinate`: the formal coordinate `f - C (constantCoeff f)` attached to a
  series `f` with unit linear coefficient.
* `PowerSeries.boxedSSeriesUnit`, `PowerSeries.boxedSSeries`: the formal S-series `(f - f(0))⁻¹ / X`
  of `f`, as a unit of `R⟦X⟧` and as a power series.
* `PowerSeries.ofBoxedSSeriesUnit`: the inverse construction `u ↦ 1 + (X u)⁻¹` producing a
  normalised series with prescribed boxed S-series unit `u : R⟦X⟧ˣ`.

## Main results

* `PowerSeries.boxedSSeries_boxedConvolution`, `PowerSeries.boxedSSeriesUnit_boxedConvolution`:
  `boxedSSeries` turns boxed convolution into Cauchy multiplication.
* `PowerSeries.ofBoxedSSeriesUnit_mul`: `ofBoxedSSeriesUnit` turns Cauchy multiplication in `R⟦X⟧ˣ`
  into boxed convolution.
* `PowerSeries.boxedSSeries_mk_one`, `PowerSeries.boxedSSeries_mobius`: boxed S-series of the zeta
  and Möbius series.
* `TauCeti.sSeries_eq_boxedSSeries_freeCumulantSeries`,
  `TauCeti.sSeries_eq_one_add_X_mul_boxedSSeries_momentSeries`: expressions of `sSeries φ a ha` via
  the boxed S-series of `freeCumulantSeries φ a` and `momentSeries φ a`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 17 and 18.
* A. Nica, R. Speicher, *A "Fourier transform" for multiplicative functions on non-crossing
  partitions*, J. Algebraic Combin. 6 (1997), 141–160.
-/

public section

open TauCeti

namespace PowerSeries

section SeriesSSeries

variable {R : Type*} [CommRing R]

/-- Subtracts the constant term of a power series `f` with unit linear coefficient to form the
formal coordinate `f - C (constantCoeff f)`. -/
noncomputable def toFormalCoordinate (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    FormalCoordinate R where
  toPowerSeries := f - C (constantCoeff f)
  constantCoeff_toPowerSeries := by simp
  isUnit_coeff_one := by simpa [coeff_C] using hf

@[simp]
theorem toPowerSeries_toFormalCoordinate (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (f.toFormalCoordinate hf).toPowerSeries = f - C (constantCoeff f) := (rfl)

@[simp]
theorem linearCoeff_toFormalCoordinate (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (f.toFormalCoordinate hf).linearCoeff = hf.unit :=
  Units.ext <| by simp

/-- `toFormalCoordinate` depends only on the positive-degree coefficients of `f`. -/
theorem toFormalCoordinate_congr {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g))
    (h : ∀ k, k ≠ 0 → coeff k f = coeff k g) :
    f.toFormalCoordinate hf = g.toFormalCoordinate hg :=
  FormalCoordinate.ext <| PowerSeries.ext fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [coeff_zero_eq_constantCoeff_apply]
    · simp [coeff_C, hn, h n hn]

/-- Base change of `toFormalCoordinate` along a ring homomorphism `α : R →+* S`. -/
theorem map_toFormalCoordinate {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf : IsUnit (coeff 1 f)) :
    FormalCoordinate.map α (f.toFormalCoordinate hf) =
      (map α f).toFormalCoordinate (by simpa using hf.map α) :=
  FormalCoordinate.ext <| PowerSeries.ext fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [← coeff_zero_eq_constantCoeff_apply (map α f), coeff_map]
    · simp [coeff_C, hn]

/-- Rescaling `f` by a unit `c` right-multiplies `f.toFormalCoordinate` by `homothety c`. -/
theorem toFormalCoordinate_rescale {c : R} (hc : IsUnit c) (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (rescale c f).toFormalCoordinate (by simpa [coeff_rescale] using hc.mul hf) =
      f.toFormalCoordinate hf * FormalCoordinate.homothety hc.unit :=
  FormalCoordinate.ext <| PowerSeries.ext fun n => by
    rw [FormalCoordinate.toPowerSeries_mul_homothety]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [← coeff_zero_eq_constantCoeff_apply (rescale _ _), coeff_rescale]
    · simp [coeff_rescale, coeff_C, hn]

/-- The formal S-series `(f - f(0))⁻¹ / X` of a power series `f` with unit linear coefficient,
packaged as a unit of `R⟦X⟧`. -/
noncomputable def boxedSSeriesUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) : R⟦X⟧ˣ :=
  (f.toFormalCoordinate hf)⁻¹.unitsEquiv

theorem boxedSSeriesUnit_def (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    f.boxedSSeriesUnit hf = (f.toFormalCoordinate hf)⁻¹.unitsEquiv := (rfl)

/-- The formal S-series `(f - f(0))⁻¹ / X` of a power series `f` with unit linear coefficient.
For a normalised free cumulant series `C_a`, this coincides with `TauCeti.sSeries φ a ha`. -/
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
  rfl

/-- The boxed S-series as the coefficient shift of `(f - C (constantCoeff f))⁻¹`. -/
theorem boxedSSeries_eq_shift_substInvOfIsUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    f.boxedSSeries hf = mk fun n =>
      coeff (n + 1) ((f - C (constantCoeff f)).substInvOfIsUnit (by simpa [coeff_C] using hf)) := by
  rw [boxedSSeries, boxedSSeriesUnit, FormalCoordinate.val_unitsEquiv,
    FormalCoordinate.toPowerSeries_inv]
  rfl

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
  rw [Units.coe_map] at h
  simpa [Ring.inverse_of_isUnit hf] using h

/-- `f.boxedSSeries hf` is a unit of `R⟦X⟧`. -/
theorem isUnit_boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    IsUnit (f.boxedSSeries hf) :=
  (f.boxedSSeriesUnit hf).isUnit

/-- The right compositional inverse equation `(f - f(0))(X * S_f) = X`. -/
@[simp]
theorem sub_C_constantCoeff_subst_X_mul_boxedSSeries (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (f - C (constantCoeff f)).subst (X * f.boxedSSeries hf) = X := by
  have h := (f.toFormalCoordinate hf).toPowerSeries_mul_inv
  rw [FormalCoordinate.toPowerSeries_mul, toPowerSeries_toFormalCoordinate,
    ← FormalCoordinate.X_mul_val_unitsEquiv] at h
  exact h

/-- The left compositional inverse equation `(X * S_f)(f - f(0)) = X`. -/
@[simp]
theorem X_mul_boxedSSeries_subst_sub_C_constantCoeff (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (X * f.boxedSSeries hf).subst (f - C (constantCoeff f)) = X := by
  have h := (f.toFormalCoordinate hf).toPowerSeries_inv_mul
  rw [FormalCoordinate.toPowerSeries_mul, toPowerSeries_toFormalCoordinate,
    ← FormalCoordinate.X_mul_val_unitsEquiv] at h
  exact h

/-- `f.boxedSSeries hf` is uniquely determined by `(f - f(0))(X * S) = X`. -/
theorem eq_boxedSSeries_of_subst_X_mul_eq {f : R⟦X⟧} (hf : IsUnit (coeff 1 f)) {S : R⟦X⟧}
    (hS : (f - C (constantCoeff f)).subst (X * S) = X) :
    S = f.boxedSSeries hf := by
  apply X_mul_injective
  exact ((f - C (constantCoeff f)).eq_substInvOfIsUnit_of_subst_eq_X (by simp)
    (by simpa [coeff_C] using hf) (.of_constantCoeff_zero' (by simp)) hS).trans
    (X_mul_boxedSSeries f hf).symm

/-- Characterisation of `f.boxedSSeries hf` by the right compositional inverse equation. -/
theorem eq_boxedSSeries_iff {f : R⟦X⟧} (hf : IsUnit (coeff 1 f)) {S : R⟦X⟧} :
    S = f.boxedSSeries hf ↔ (f - C (constantCoeff f)).subst (X * S) = X :=
  ⟨by rintro rfl; exact sub_C_constantCoeff_subst_X_mul_boxedSSeries f hf,
    eq_boxedSSeries_of_subst_X_mul_eq hf⟩

/-- `boxedSSeriesUnit` depends only on the positive-degree coefficients of `f`. -/
theorem boxedSSeriesUnit_congr {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g))
    (h : ∀ k, k ≠ 0 → coeff k f = coeff k g) :
    f.boxedSSeriesUnit hf = g.boxedSSeriesUnit hg :=
  congrArg (fun φ => φ⁻¹.unitsEquiv) (toFormalCoordinate_congr hf hg h)

/-- `boxedSSeries` depends only on the positive-degree coefficients of `f`. -/
theorem boxedSSeries_congr {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g))
    (h : ∀ k, k ≠ 0 → coeff k f = coeff k g) :
    f.boxedSSeries hf = g.boxedSSeries hg :=
  congrArg Units.val (boxedSSeriesUnit_congr hf hg h)

/-- Base change commutes with `boxedSSeriesUnit`. -/
theorem map_boxedSSeriesUnit {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf : IsUnit (coeff 1 f)) :
    Units.map ↑(map α) (f.boxedSSeriesUnit hf) =
      (map α f).boxedSSeriesUnit (by simpa using hf.map α) := by
  rw [boxedSSeriesUnit, FormalCoordinate.map_unitsEquiv, map_inv, map_toFormalCoordinate]
  rfl

/-- Base change commutes with `boxedSSeries`. -/
theorem map_boxedSSeries {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf : IsUnit (coeff 1 f)) :
    map α (f.boxedSSeries hf) = (map α f).boxedSSeries (by simpa using hf.map α) :=
  congrArg Units.val (map_boxedSSeriesUnit α f hf)

/-- Rescaling `f` by a unit `c` multiplies `f.boxedSSeriesUnit` by `C c⁻¹`. -/
theorem boxedSSeriesUnit_rescale {c : R} (hc : IsUnit c) (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (rescale c f).boxedSSeriesUnit (by simpa [coeff_rescale] using hc.mul hf) =
      Units.map ↑(C (R := R)) hc.unit⁻¹ * f.boxedSSeriesUnit hf := by
  rw [boxedSSeriesUnit, toFormalCoordinate_rescale hc f hf, mul_inv_rev, ← map_inv,
    FormalCoordinate.unitsEquiv_homothety_mul]
  rfl

/-- Rescaling `f` by a unit `c` scales `f.boxedSSeries` by `c⁻¹`. -/
theorem boxedSSeries_rescale {c : R} (hc : IsUnit c) (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    (rescale c f).boxedSSeries (by simpa [coeff_rescale] using hc.mul hf) =
      Ring.inverse c • f.boxedSSeries hf := by
  have h := congrArg Units.val (boxedSSeriesUnit_rescale hc f hf)
  simpa [Algebra.smul_def, Ring.inverse_of_isUnit hc] using h

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
  have hrc : rescale c (X : R⟦X⟧) = C c * X := by
    ext (_ | _ | n) <;> simp
  refine (boxedSSeries_congr _ (by simpa [coeff_rescale] using hc)
    fun k _ => congrArg (coeff k) hrc.symm).trans ?_
  rw [boxedSSeries_rescale hc X (by simp), boxedSSeries_X, Algebra.smul_def, mul_one,
    algebraMap_eq]

end SeriesSSeries

end PowerSeries

namespace TauCeti

open PowerSeries

section MonoidBridge

variable {R A : Type*} [CommRing R] [Monoid A]

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

end MonoidBridge

end TauCeti

namespace PowerSeries

open TauCeti

section Multiplicativity

variable {R : Type*} [CommRing R]

private theorem boxedSSeries_boxedConvolution_of_constantCoeff_eq_one {f g : R⟦X⟧}
    (hf₀ : constantCoeff f = 1) (hg₀ : constantCoeff g = 1)
    (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedSSeries (by rw [coeff_one_boxedConvolution]; exact hf.mul hg) =
      f.boxedSSeries hf * g.boxedSSeries hg := by
  let F : Fin 2 → R⟦X⟧ := ![f, g]
  obtain ⟨φ, hφ, hfree, hseries⟩ := exists_freeProduct_freeCumulantSeries_eq F (by
    intro i
    fin_cases i <;> assumption)
  set a : Fin 2 → _ :=
    fun i => LinearAlgebra.FreeProduct.ι R (fun _ : Fin 2 => Polynomial R) i Polynomial.X
  have hfC : freeCumulantSeries φ (a 0) = f := hseries 0
  have hgC : freeCumulantSeries φ (a 1) = g := hseries 1
  have ha₀ : IsUnit (φ (a 0)) := by
    rwa [← coeff_one_freeCumulantSeries φ (a 0), hfC]
  have ha₁ : IsUnit (φ (a 1)) := by
    rwa [← coeff_one_freeCumulantSeries φ (a 1), hgC]
  have hfgC : freeCumulantSeries φ (a 0 * a 1) = f.boxedConvolution g := by
    rw [hfree.freeCumulantSeries_mul hφ (i := 0) (j := 1) (by decide), hfC, hgC]
  have hmul := hfree.sSeries_mul hφ (i := 0) (j := 1) (by decide) ha₀ ha₁
  rw [sSeries_eq_boxedSSeries_freeCumulantSeries hφ, sSeries_eq_boxedSSeries_freeCumulantSeries hφ,
    sSeries_eq_boxedSSeries_freeCumulantSeries hφ] at hmul
  refine (boxedSSeries_congr _ _ fun k _ => congrArg (coeff k) hfgC.symm).trans
    (hmul.trans (congrArg₂ (· * ·)
      (boxedSSeries_congr _ hf fun k _ => congrArg (coeff k) hfC)
      (boxedSSeries_congr _ hg fun k _ => congrArg (coeff k) hgC)))

/-- *Multiplicativity of the formal S-series under boxed convolution*: for any two series `f` and
`g` over a commutative ring `R` whose linear coefficients are units (with arbitrary constant
coefficients), the boxed S-series of `f.boxedConvolution g` is the Cauchy product of the boxed
S-series of `f` and of `g`. -/
theorem boxedSSeries_boxedConvolution {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f))
    (hg : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedSSeries (by rw [coeff_one_boxedConvolution]; exact hf.mul hg) =
      f.boxedSSeries hf * g.boxedSSeries hg := by
  let N (s : R⟦X⟧) : R⟦X⟧ := s + C (1 - constantCoeff s)
  have hN₀ (s : R⟦X⟧) : constantCoeff (N s) = 1 := by simp [N]
  have hN (s : R⟦X⟧) (k : ℕ) (hk : k ≠ 0) : coeff k s = coeff k (N s) := by simp [N, coeff_C, hk]
  have hfN : IsUnit (coeff 1 (N f)) := hN f 1 one_ne_zero ▸ hf
  have hgN : IsUnit (coeff 1 (N g)) := hN g 1 one_ne_zero ▸ hg
  refine (boxedSSeries_congr _
    (by rw [coeff_one_boxedConvolution]; exact hfN.mul hgN)
    fun k hk => coeff_boxedConvolution_congr hk (hN f) (hN g)).trans ?_
  rw [boxedSSeries_boxedConvolution_of_constantCoeff_eq_one (hN₀ f) (hN₀ g) hfN hgN]
  exact congrArg₂ (· * ·) (boxedSSeries_congr hfN hf fun k hk => (hN f k hk).symm)
    (boxedSSeries_congr hgN hg fun k hk => (hN g k hk).symm)

/-- `boxedSSeriesUnit` converts boxed convolution into multiplication in `R⟦X⟧ˣ`. -/
theorem boxedSSeriesUnit_boxedConvolution {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f))
    (hg : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedSSeriesUnit (by rw [coeff_one_boxedConvolution]; exact hf.mul hg) =
      f.boxedSSeriesUnit hf * g.boxedSSeriesUnit hg :=
  Units.ext (boxedSSeries_boxedConvolution hf hg)

/-- The boxed S-series of the zeta series `∑_{n ≥ 0} Xⁿ` is `(1 + X)⁻¹ = ∑_{n ≥ 0} (-X)ⁿ`. -/
theorem boxedSSeries_mk_one :
    (mk 1 : R⟦X⟧).boxedSSeries (by simp) = mk fun n => (-1 : R) ^ n := by
  set S : R⟦X⟧ := mk fun n => (-1 : R) ^ n
  have hS : (1 + X) * S = 1 := by
    simpa [S, mul_comm] using powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (-1 : R)
  have h1S : 1 - X * S = S := (eq_sub_of_add_eq (by simpa [add_mul] using hS)).symm
  have hmk : (1 - X) * (mk 1 - 1 : R⟦X⟧) = X := by
    ext (_ | _ | n) <;> simp [sub_mul, mul_sub, coeff_succ_X_mul, coeff_one]
  have hw : HasSubst (X * S) := .of_constantCoeff_zero' (by simp)
  have h1X : (1 - X : R⟦X⟧).subst (X * S) = S := by
    rw [subst_sub hw, subst_one, subst_X hw, h1S]
  have hsub := congrArg (subst (X * S)) hmk
  rw [subst_mul hw, h1X, subst_X hw] at hsub
  refine (eq_boxedSSeries_of_subst_X_mul_eq _ ?_).symm
  calc
    (mk 1 - C (constantCoeff (mk 1 : R⟦X⟧))).subst (X * S) =
        ((1 + X) * S) * (mk 1 - 1 : R⟦X⟧).subst (X * S) := by simp [hS]
    _ = (1 + X) * (S * (mk 1 - 1 : R⟦X⟧).subst (X * S)) := mul_assoc _ _ _
    _ = (1 + X) * (X * S) := by rw [hsub]
    _ = X * ((1 + X) * S) := mul_left_comm _ _ _
    _ = X := by rw [hS, mul_one]

/-- The boxed S-series of the Möbius series `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) Xⁿ` is `1 + X`. -/
theorem boxedSSeries_mobius :
    (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)).boxedSSeries (by simp) = 1 + X := by
  set M := (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)).boxedSSeries (by simp)
  have hS : (1 + X) * (mk fun n => (-1 : R) ^ n) = 1 := by
    simpa [mul_comm] using powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (-1 : R)
  have hconv : (mk fun n => (-1 : R) ^ n) * M = 1 := by
    have h := (boxedSSeries_congr
      (f := (mk 1 : R⟦X⟧).boxedConvolution (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)))
      (by simp) (by simp) fun k _ =>
        congrArg (coeff k) boxedConvolution_mk_one_mobius).trans boxedSSeries_one_add_X
    rwa [boxedSSeries_boxedConvolution (by simp) (by simp), boxedSSeries_mk_one] at h
  calc
    M = ((1 + X) * mk fun n => (-1 : R) ^ n) * M := by rw [hS, one_mul]
    _ = (1 + X) * ((mk fun n => (-1 : R) ^ n) * M) := mul_assoc _ _ _
    _ = 1 + X := by rw [hconv, mul_one]

/-- Constructs the unique normalised power series `1 + (X u)⁻¹` whose boxed S-series unit is a
given `u : R⟦X⟧ˣ`. -/
noncomputable def ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) : R⟦X⟧ :=
  1 + (FormalCoordinate.unitsEquiv.symm u)⁻¹.toPowerSeries

theorem ofBoxedSSeriesUnit_def (u : R⟦X⟧ˣ) :
    ofBoxedSSeriesUnit u = 1 + (FormalCoordinate.unitsEquiv.symm u)⁻¹.toPowerSeries := (rfl)

@[simp]
theorem constantCoeff_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    constantCoeff (ofBoxedSSeriesUnit u) = 1 := by
  simp [ofBoxedSSeriesUnit]

@[simp]
theorem coeff_one_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    coeff 1 (ofBoxedSSeriesUnit u) = Ring.inverse (constantCoeff (u : R⟦X⟧)) := by
  have hval := congrArg Units.val
    (map_inv FormalCoordinate.linearCoeff (FormalCoordinate.unitsEquiv.symm u))
  simp only [FormalCoordinate.val_linearCoeff, FormalCoordinate.linearCoeff_unitsEquiv_symm] at hval
  rw [ofBoxedSSeriesUnit, map_add, coeff_one, ite_eq_right one_ne_zero, zero_add, hval]
  exact (Ring.inverse_unit (Units.map (constantCoeff (R := R) : R⟦X⟧ →* R) u)).symm

/-- The linear coefficient of `ofBoxedSSeriesUnit u` is a unit. -/
theorem isUnit_coeff_one_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    IsUnit (coeff 1 (ofBoxedSSeriesUnit u)) := by
  simp [ofBoxedSSeriesUnit, coeff_one]

theorem toFormalCoordinate_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    (ofBoxedSSeriesUnit u).toFormalCoordinate (isUnit_coeff_one_ofBoxedSSeriesUnit u) =
      (FormalCoordinate.unitsEquiv.symm u)⁻¹ :=
  FormalCoordinate.ext <| by simp [ofBoxedSSeriesUnit]

@[simp]
theorem boxedSSeriesUnit_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    (ofBoxedSSeriesUnit u).boxedSSeriesUnit (isUnit_coeff_one_ofBoxedSSeriesUnit u) = u := by
  rw [boxedSSeriesUnit, toFormalCoordinate_ofBoxedSSeriesUnit, inv_inv, Equiv.apply_symm_apply]

@[simp]
theorem boxedSSeries_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    (ofBoxedSSeriesUnit u).boxedSSeries (isUnit_coeff_one_ofBoxedSSeriesUnit u) = (u : R⟦X⟧) :=
  congrArg Units.val (boxedSSeriesUnit_ofBoxedSSeriesUnit u)

/-- `ofBoxedSSeriesUnit` recovers the positive-degree part of `f` shifted by constant term `1`. -/
theorem ofBoxedSSeriesUnit_boxedSSeriesUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf) = 1 + (f - C (constantCoeff f)) := by
  rw [ofBoxedSSeriesUnit, boxedSSeriesUnit, Equiv.symm_apply_apply, inv_inv,
    toPowerSeries_toFormalCoordinate]

/-- On normalised series (`constantCoeff f = 1`), `ofBoxedSSeriesUnit` is a left inverse to
`boxedSSeriesUnit`. -/
theorem ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one {f : R⟦X⟧}
    (hf₀ : constantCoeff f = 1) (hf₁ : IsUnit (coeff 1 f)) :
    ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁) = f := by
  rw [ofBoxedSSeriesUnit_boxedSSeriesUnit, hf₀, map_one, add_sub_cancel]

/-- Two series with equal boxed S-series agree on all positive-degree coefficients. -/
theorem coeff_eq_of_boxedSSeries_eq {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g))
    (h : f.boxedSSeries hf = g.boxedSSeries hg) {n : ℕ} (hn : n ≠ 0) :
    coeff n f = coeff n g := by
  have hu := congrArg (fun u => coeff n (ofBoxedSSeriesUnit u)) (Units.ext h)
  simpa [ofBoxedSSeriesUnit_boxedSSeriesUnit, coeff_one, coeff_C, hn] using hu

/-- Two series with equal constant coefficients and equal boxed S-series are equal. -/
theorem eq_of_constantCoeff_eq_of_boxedSSeries_eq {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f))
    (hg : IsUnit (coeff 1 g)) (h₀ : constantCoeff f = constantCoeff g)
    (hS : f.boxedSSeries hf = g.boxedSSeries hg) : f = g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using h₀
  · exact coeff_eq_of_boxedSSeries_eq hf hg hS hn

@[simp]
theorem ofBoxedSSeriesUnit_one : ofBoxedSSeriesUnit (1 : R⟦X⟧ˣ) = 1 + X := by
  rw [← boxedSSeriesUnit_one_add_X,
    ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one (by simp)]

/-- `ofBoxedSSeriesUnit` turns Cauchy multiplication in `R⟦X⟧ˣ` into boxed convolution. -/
theorem ofBoxedSSeriesUnit_mul (u v : R⟦X⟧ˣ) :
    ofBoxedSSeriesUnit (u * v) =
      (ofBoxedSSeriesUnit u).boxedConvolution (ofBoxedSSeriesUnit v) :=
  eq_of_constantCoeff_eq_of_boxedSSeries_eq (isUnit_coeff_one_ofBoxedSSeriesUnit (u * v))
    (by
      rw [coeff_one_boxedConvolution]
      exact (isUnit_coeff_one_ofBoxedSSeriesUnit u).mul (isUnit_coeff_one_ofBoxedSSeriesUnit v))
    (by simp)
    (by
      rw [boxedSSeries_ofBoxedSSeriesUnit,
        boxedSSeries_boxedConvolution (isUnit_coeff_one_ofBoxedSSeriesUnit u)
          (isUnit_coeff_one_ofBoxedSSeriesUnit v),
        boxedSSeries_ofBoxedSSeriesUnit, boxedSSeries_ofBoxedSSeriesUnit, Units.val_mul])

end Multiplicativity

end PowerSeries

namespace TauCeti

open PowerSeries

/-- For a normalised functional `φ`, the formal S-series `sSeries φ a ha` equals `(1 + X)` times
the boxed S-series of `momentSeries φ a`, reflecting `C_a = M_a ⊠ μ` and `S_μ = 1 + X`. -/
theorem sSeries_eq_one_add_X_mul_boxedSSeries_momentSeries {R A : Type*} [CommRing R] [Monoid A]
    {φ : A → R} (hφ : φ 1 = 1) (a : A) (ha : IsUnit (φ a)) :
    sSeries φ a ha = (1 + X) * (momentSeries φ a).boxedSSeries (by simpa using ha) := by
  rw [sSeries_eq_boxedSSeries_freeCumulantSeries hφ a ha]
  have h := boxedConvolution_momentSeries_mobius a hφ
  refine (boxedSSeries_congr _ (by simpa [coeff_one_boxedConvolution] using ha)
    fun k _ => congrArg (coeff k) h.symm).trans ?_
  rw [boxedSSeries_boxedConvolution (by simpa using ha) (by simp), boxedSSeries_mobius, mul_comm]

end TauCeti
