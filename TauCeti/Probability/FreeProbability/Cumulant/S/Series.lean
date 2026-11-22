/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.BoxedConvolution.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.S.Free
import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.Probability.FreeProbability.Cumulant.Realization
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Multiplicativity and inversion of the boxed S-series

Combining universal algebraic realisation (`TauCeti.exists_freeProduct_freeCumulantSeries_eq`)
with multiplicativity of the S-series for two free elements
(`TauCeti.IsFreelyIndependentElements.sSeries_mul`) shows that `PowerSeries.boxedSSeries` (defined
in `TauCeti.Probability.FreeProbability.Cumulant.S.Basic`) converts scalar boxed convolution into
Cauchy multiplication:
`(f.boxedConvolution g).boxedSSeries _ = f.boxedSSeries hf * g.boxedSSeries hg` for arbitrary
constant coefficients. Together with the compositional-inverse characterisation
(`PowerSeries.eq_boxedSSeries_of_subst_X_mul_eq`), multiplicativity evaluates
`PowerSeries.boxedSSeries` on the zeta series `∑_{n ≥ 0} Xⁿ` (`∑_{n ≥ 0} (-X)ⁿ`) and the Möbius
series `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) Xⁿ` (`1 + X`).

Separately, the explicit inverse construction `PowerSeries.ofBoxedSSeriesUnit`, sending
`u : R⟦X⟧ˣ` to the normalised series `1 + (X u)⁻¹` (where `(X u)⁻¹` denotes the compositional
inverse of `X u`), inverts `PowerSeries.boxedSSeriesUnit` on normalised series and converts
Cauchy multiplication in `R⟦X⟧ˣ` into boxed convolution (`PowerSeries.ofBoxedSSeriesUnit_mul`).

## Main definitions

* `PowerSeries.ofBoxedSSeriesUnit`: the inverse construction `u ↦ 1 + (X u)⁻¹` (with `(X u)⁻¹` the
  compositional inverse of `X u`) producing a normalised series with prescribed boxed S-series unit
  `u : R⟦X⟧ˣ`.

## Main results

* `PowerSeries.boxedSSeries_boxedConvolution`, `PowerSeries.boxedSSeriesUnit_boxedConvolution`:
  `boxedSSeries` turns boxed convolution into Cauchy multiplication.
* `PowerSeries.ofBoxedSSeriesUnit_mul`: `ofBoxedSSeriesUnit` turns Cauchy multiplication in `R⟦X⟧ˣ`
  into boxed convolution.
* `PowerSeries.boxedSSeries_mk_one`, `PowerSeries.boxedSSeries_mobius`: boxed S-series of the zeta
  and Möbius series.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 17 and 18.
* A. Nica, R. Speicher, *A "Fourier transform" for multiplicative functions on non-crossing
  partitions*, J. Algebraic Combin. 6 (1997), 141–160.
-/

public section

namespace PowerSeries

open TauCeti

section Multiplicativity

variable {R : Type*} [CommRing R]

private theorem boxedSSeries_boxedConvolution_of_constantCoeff_eq_one {f g : R⟦X⟧}
    (hf₀ : constantCoeff f = 1) (hg₀ : constantCoeff g = 1)
    (hf : IsUnit (coeff 1 f)) (hg : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedSSeries (by rw [coeff_one_boxedConvolution]; exact hf.mul hg) =
      f.boxedSSeries hf * g.boxedSSeries hg := by
  obtain ⟨φ, hφ, hfree, hseries⟩ := exists_freeProduct_freeCumulantSeries_eq ![f, g]
    fun i => by fin_cases i <;> assumption
  set a : Fin 2 → _ :=
    fun i => LinearAlgebra.FreeProduct.ι R (fun _ : Fin 2 => Polynomial R) i Polynomial.X
  have hfC : freeCumulantSeries φ (a 0) = f := hseries 0
  have hgC : freeCumulantSeries φ (a 1) = g := hseries 1
  have hmul := hfree.sSeries_mul hφ (i := 0) (j := 1) (by decide)
    (by rwa [← coeff_one_freeCumulantSeries φ (a 0), hfC])
    (by rwa [← coeff_one_freeCumulantSeries φ (a 1), hgC])
  simp only [sSeries_eq_boxedSSeries_freeCumulantSeries hφ] at hmul
  refine (boxedSSeries_congr _ _ fun k _ => congrArg (coeff k) (show
    freeCumulantSeries φ (a 0 * a 1) = f.boxedConvolution g by
      rw [hfree.freeCumulantSeries_mul hφ (i := 0) (j := 1) (by decide), hfC, hgC]).symm).trans
    (hmul.trans (congrArg₂ (· * ·) (boxedSSeries_congr _ hf fun k _ => congrArg (coeff k) hfC)
      (boxedSSeries_congr _ hg fun k _ => congrArg (coeff k) hgC)))

/-- *Multiplicativity of the formal S-series under boxed convolution*: for any two series `f` and
`g` over a commutative ring `R` whose linear coefficients are units (with arbitrary constant
coefficients), the boxed S-series of `f.boxedConvolution g` is the Cauchy product of the boxed
S-series of `f` and of `g`. -/
theorem boxedSSeries_boxedConvolution {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f))
    (hg : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedSSeries (by rw [coeff_one_boxedConvolution]; exact hf.mul hg) =
      f.boxedSSeries hf * g.boxedSSeries hg := by
  obtain ⟨f', hf₀, hf'⟩ := exists_constantCoeff_eq_one_coeff_eq f
  obtain ⟨g', hg₀, hg'⟩ := exists_constantCoeff_eq_one_coeff_eq g
  have hfN : IsUnit (coeff 1 f') := hf' 1 one_ne_zero ▸ hf
  have hgN : IsUnit (coeff 1 g') := hg' 1 one_ne_zero ▸ hg
  refine (boxedSSeries_congr _ (by rw [coeff_one_boxedConvolution]; exact hfN.mul hgN)
    fun k hk => coeff_boxedConvolution_congr hk hf' hg').trans ?_
  rw [boxedSSeries_boxedConvolution_of_constantCoeff_eq_one hf₀ hg₀ hfN hgN]
  exact congrArg₂ (· * ·) (boxedSSeries_congr _ hf fun k hk => (hf' k hk).symm)
    (boxedSSeries_congr _ hg fun k hk => (hg' k hk).symm)

/-- `boxedSSeriesUnit` converts boxed convolution into multiplication in `R⟦X⟧ˣ`. -/
theorem boxedSSeriesUnit_boxedConvolution {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f))
    (hg : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedSSeriesUnit (by rw [coeff_one_boxedConvolution]; exact hf.mul hg) =
      f.boxedSSeriesUnit hf * g.boxedSSeriesUnit hg :=
  Units.ext (by simp [boxedSSeries_boxedConvolution hf hg])

/-- The boxed S-series of the zeta series `∑_{n ≥ 0} Xⁿ` is the Cauchy inverse
`(1 + X)⁻¹ = ∑_{n ≥ 0} (-X)ⁿ`. -/
theorem boxedSSeries_mk_one :
    (mk 1 : R⟦X⟧).boxedSSeries (by simp) = mk fun n => (-1 : R) ^ n := by
  set S : R⟦X⟧ := mk fun n => (-1 : R) ^ n
  have hS : (1 + X) * S = 1 := mul_comm S (1 + X) ▸ mk_neg_one_pow_mul_one_add_eq_one R
  have hw : HasSubst (X * S) := .of_constantCoeff_zero' (by simp)
  have hsub := congrArg (subst (X * S))
    (show (1 - X) * (mk 1 - 1 : R⟦X⟧) = X by
      rw [mul_sub, mul_one, mul_comm, mk_one_mul_one_sub_eq_one, sub_sub_cancel])
  rw [subst_mul hw, subst_sub hw, subst_one, subst_X hw,
    (eq_sub_of_add_eq (by simpa [add_mul] using hS)).symm] at hsub
  refine (eq_boxedSSeries_of_subst_X_mul_eq _ ?_).symm
  calc (mk 1 - C (constantCoeff (mk 1 : R⟦X⟧))).subst (X * S)
      = ((1 + X) * S) * (mk 1 - 1 : R⟦X⟧).subst (X * S) := by simp [hS]
    _ = (1 + X) * (X * S) := by rw [mul_assoc, hsub]
    _ = X := by rw [mul_left_comm, hS, mul_one]

/-- The boxed S-series of the Möbius series `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) Xⁿ` is `1 + X`. -/
theorem boxedSSeries_mobius :
    (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)).boxedSSeries (by simp) = 1 + X := by
  have hS : (1 + X) * (mk fun n => (-1 : R) ^ n) = 1 := by
    rw [mul_comm]; exact mk_neg_one_pow_mul_one_add_eq_one R
  have hconv := (boxedSSeries_congr
    (f := (mk 1 : R⟦X⟧).boxedConvolution (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)))
    (by simp) (by simp) fun k _ =>
      congrArg (coeff k) boxedConvolution_mk_one_mobius).trans boxedSSeries_one_add_X
  rw [boxedSSeries_boxedConvolution (by simp) (by simp), boxedSSeries_mk_one] at hconv
  exact (left_inv_eq_right_inv hS hconv).symm

/-- Constructs the unique normalised power series `1 + (X u)⁻¹`, where `(X u)⁻¹` denotes the
compositional inverse of `X u`, whose boxed S-series unit is a given `u : R⟦X⟧ˣ`. -/
noncomputable def ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) : R⟦X⟧ :=
  1 + (FormalCoordinate.unitsEquiv.symm u)⁻¹.toPowerSeries

theorem ofBoxedSSeriesUnit_def (u : R⟦X⟧ˣ) :
    ofBoxedSSeriesUnit u = 1 + (FormalCoordinate.unitsEquiv.symm u)⁻¹.toPowerSeries := (rfl)

@[simp]
theorem constantCoeff_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    constantCoeff (ofBoxedSSeriesUnit u) = 1 := by simp [ofBoxedSSeriesUnit]

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

@[simp]
theorem toFormalCoordinate_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    (ofBoxedSSeriesUnit u).toFormalCoordinate (isUnit_coeff_one_ofBoxedSSeriesUnit u) =
      (FormalCoordinate.unitsEquiv.symm u)⁻¹ :=
  FormalCoordinate.ext <| by simp [ofBoxedSSeriesUnit]

@[simp]
theorem boxedSSeriesUnit_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    (ofBoxedSSeriesUnit u).boxedSSeriesUnit (isUnit_coeff_one_ofBoxedSSeriesUnit u) = u := by
  rw [boxedSSeriesUnit_def, toFormalCoordinate_ofBoxedSSeriesUnit, inv_inv, Equiv.apply_symm_apply]

@[simp]
theorem boxedSSeries_ofBoxedSSeriesUnit (u : R⟦X⟧ˣ) :
    (ofBoxedSSeriesUnit u).boxedSSeries (isUnit_coeff_one_ofBoxedSSeriesUnit u) = (u : R⟦X⟧) :=
  (val_boxedSSeriesUnit _ _).symm.trans (congrArg Units.val (boxedSSeriesUnit_ofBoxedSSeriesUnit u))

/-- `ofBoxedSSeriesUnit` recovers the positive-degree part of `f` shifted by constant term `1`. -/
@[simp]
theorem ofBoxedSSeriesUnit_boxedSSeriesUnit (f : R⟦X⟧) (hf : IsUnit (coeff 1 f)) :
    ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf) = 1 + (f - C (constantCoeff f)) := by
  rw [ofBoxedSSeriesUnit, boxedSSeriesUnit_def, Equiv.symm_apply_apply, inv_inv,
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
  have hu := congrArg (fun u => coeff n (ofBoxedSSeriesUnit u))
    (Units.ext ((val_boxedSSeriesUnit f hf).trans (h.trans (val_boxedSSeriesUnit g hg).symm)))
  simpa [coeff_one, coeff_C, hn] using hu

/-- Two series with equal constant coefficients and equal boxed S-series are equal. -/
theorem eq_of_constantCoeff_eq_of_boxedSSeries_eq {f g : R⟦X⟧} (hf : IsUnit (coeff 1 f))
    (hg : IsUnit (coeff 1 g)) (h₀ : constantCoeff f = constantCoeff g)
    (hS : f.boxedSSeries hf = g.boxedSSeries hg) : f = g := by
  ext (_ | n)
  · simpa using h₀
  · exact coeff_eq_of_boxedSSeries_eq hf hg hS n.succ_ne_zero

@[simp]
theorem ofBoxedSSeriesUnit_one : ofBoxedSSeriesUnit (1 : R⟦X⟧ˣ) = 1 + X := by
  rw [← boxedSSeriesUnit_one_add_X,
    ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one (by simp)]

/-- `ofBoxedSSeriesUnit` turns Cauchy multiplication in `R⟦X⟧ˣ` into boxed convolution. -/
theorem ofBoxedSSeriesUnit_mul (u v : R⟦X⟧ˣ) :
    ofBoxedSSeriesUnit (u * v) =
      (ofBoxedSSeriesUnit u).boxedConvolution (ofBoxedSSeriesUnit v) :=
  eq_of_constantCoeff_eq_of_boxedSSeries_eq (isUnit_coeff_one_ofBoxedSSeriesUnit (u * v))
    (by rw [coeff_one_boxedConvolution]
        exact (isUnit_coeff_one_ofBoxedSSeriesUnit u).mul (isUnit_coeff_one_ofBoxedSSeriesUnit v))
    (by simp) (by rw [boxedSSeries_ofBoxedSSeriesUnit, boxedSSeries_boxedConvolution
      (isUnit_coeff_one_ofBoxedSSeriesUnit u) (isUnit_coeff_one_ofBoxedSSeriesUnit v),
      boxedSSeries_ofBoxedSSeriesUnit, boxedSSeries_ofBoxedSSeriesUnit, Units.val_mul])

/-- Base change commutes with `ofBoxedSSeriesUnit`. -/
@[simp]
theorem map_ofBoxedSSeriesUnit {S : Type*} [CommRing S] (α : R →+* S) (u : R⟦X⟧ˣ) :
    map α (ofBoxedSSeriesUnit u) = ofBoxedSSeriesUnit (Units.map ↑(map α) u) := by
  rw [ofBoxedSSeriesUnit_def, ofBoxedSSeriesUnit_def, map_add, map_one,
    ← FormalCoordinate.toPowerSeries_map, map_inv, FormalCoordinate.map_unitsEquiv_symm]

/-- Rescaling `ofBoxedSSeriesUnit u` by a unit `c` multiplies `u` by `C c⁻¹`. -/
theorem rescale_ofBoxedSSeriesUnit {c : R} (hc : IsUnit c) (u : R⟦X⟧ˣ) :
    rescale c (ofBoxedSSeriesUnit u) =
      ofBoxedSSeriesUnit (Units.map ↑(C (R := R)) hc.unit⁻¹ * u) := by
  refine eq_of_constantCoeff_eq_of_boxedSSeries_eq
    (by simpa [coeff_rescale] using hc.mul (isUnit_coeff_one_ofBoxedSSeriesUnit u))
    (isUnit_coeff_one_ofBoxedSSeriesUnit _)
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]; simp) ?_
  rw [← val_boxedSSeriesUnit, boxedSSeriesUnit_rescale hc _ (isUnit_coeff_one_ofBoxedSSeriesUnit u),
    boxedSSeriesUnit_ofBoxedSSeriesUnit, boxedSSeries_ofBoxedSSeriesUnit]

end Multiplicativity

end PowerSeries
