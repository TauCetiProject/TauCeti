/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.BoxedConvolution.Monoid
public import TauCeti.Probability.FreeProbability.Cumulant.S.Series

/-!
# Boxed-convolution inverses and the S-series group isomorphism

Over a commutative ring `R`, multiplicativity of `PowerSeries.boxedSSeriesUnit` and its inverse
`PowerSeries.ofBoxedSSeriesUnit` determine the invertible elements for scalar boxed convolution and
identify the group of normalised boxed-convolution units with `R⟦X⟧ˣ`:

* explicit boxed-convolution inverses `PowerSeries.boxedConvolutionInv` for series whose constant
  and linear coefficients are units, together with uniqueness
  (`PowerSeries.eq_boxedConvolutionInv_iff`) and right-invertibility with respect to `X`
  (`PowerSeries.exists_boxedConvolution_eq_X_iff`);
* characterisations of the units of `TauCeti.BoxedConvolution R` and of its normalised submonoid
  `TauCeti.BoxedConvolution.normalizedSubmonoid R`;
* the one-variable boxed-convolution / S-series group isomorphism
  `TauCeti.BoxedConvolution.sSeriesMulEquiv :`
  `(BoxedConvolution.normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ`
  and the full unit splitting
  `TauCeti.BoxedConvolution.unitsMulEquiv : (BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ`;
* the bridge `TauCeti.freeCumulantSeriesNormalizedUnit` identifying `TauCeti.sSeries φ a ha` (for a
  normalised `φ`) with the image of `freeCumulantSeries φ a` under `sSeriesMulEquiv`.

## Main definitions

* `PowerSeries.boxedConvolutionInv`: the boxed-convolution inverse of a series whose constant and
  linear coefficients are units.
* `TauCeti.BoxedConvolution.unitOfIsUnit`, `TauCeti.BoxedConvolution.normalizedUnit`:
  constructors for units of `BoxedConvolution R` and `BoxedConvolution.normalizedSubmonoid R`.
* `TauCeti.BoxedConvolution.sSeriesMulEquiv`: the group isomorphism
  `(BoxedConvolution.normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ` given by the formal S-series.
* `TauCeti.BoxedConvolution.unitsMulEquiv`: the group isomorphism
  `(BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ` pairing the constant coefficient with the formal S-series.
* `TauCeti.freeCumulantSeriesNormalizedUnit`: packages `freeCumulantSeries φ a` for an element of
  unit mean as a unit of `BoxedConvolution.normalizedSubmonoid R`.

## Main results

* `PowerSeries.boxedConvolution_boxedConvolutionInv`,
  `PowerSeries.boxedConvolutionInv_boxedConvolution`,
  `PowerSeries.eq_boxedConvolutionInv_iff`: two-sided inverse equations and uniqueness for
  `boxedConvolutionInv`.
* `PowerSeries.exists_boxedConvolution_eq_X_iff`: a series `f` admits `g` with
  `constantCoeff g = 0` and `f ⊠ g = X` if and only if `IsUnit (coeff 1 f)`.
* `TauCeti.BoxedConvolution.isUnit_iff`,
  `TauCeti.BoxedConvolution.isUnit_normalizedSubmonoid_iff`: characterisations of invertible
  elements under boxed convolution.
* `TauCeti.val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit`: for a normalised `φ`, applying
  `sSeriesMulEquiv` to `freeCumulantSeriesNormalizedUnit φ a ha` yields `sSeries φ a ha`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 17 and 18.
* A. Nica, R. Speicher, *A "Fourier transform" for multiplicative functions on non-crossing
  partitions*, J. Algebraic Combin. 6 (1997), 141–160.
-/

public section

open TauCeti

namespace PowerSeries

section Inverse

variable {R : Type*} [CommRing R]

/-- The boxed-convolution inverse of a power series `f` whose constant and linear coefficients are
units: its constant coefficient is the multiplicative inverse `(constantCoeff f)⁻¹` in `R` and its
positive-degree part agrees with `ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹`. -/
noncomputable def boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) : R⟦X⟧ :=
  C (↑hf₀.unit⁻¹ : R) - 1 + ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹

theorem boxedConvolutionInv_def (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    f.boxedConvolutionInv hf₀ hf₁ =
      C (↑hf₀.unit⁻¹ : R) - 1 + ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹ := (rfl)

@[simp]
theorem constantCoeff_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    constantCoeff (f.boxedConvolutionInv hf₀ hf₁) = Ring.inverse (constantCoeff f) := by
  simp [boxedConvolutionInv, Ring.inverse_of_isUnit hf₀]

/-- `f.boxedConvolutionInv hf₀ hf₁` agrees with `ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹`
at every positive index. -/
theorem coeff_boxedConvolutionInv_eq_coeff_ofBoxedSSeriesUnit (f : R⟦X⟧)
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f)) {n : ℕ} (hn : n ≠ 0) :
    coeff n (f.boxedConvolutionInv hf₀ hf₁) =
      coeff n (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) := by
  simp [boxedConvolutionInv, coeff_C, coeff_one, hn]

/-- The linear coefficient of `f.boxedConvolutionInv hf₀ hf₁` is a unit. -/
theorem isUnit_coeff_one_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    IsUnit (coeff 1 (f.boxedConvolutionInv hf₀ hf₁)) := by
  rw [coeff_boxedConvolutionInv_eq_coeff_ofBoxedSSeriesUnit f hf₀ hf₁ one_ne_zero]
  exact isUnit_coeff_one_ofBoxedSSeriesUnit _

@[simp]
theorem boxedSSeriesUnit_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    (f.boxedConvolutionInv hf₀ hf₁).boxedSSeriesUnit
        (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁) =
      (f.boxedSSeriesUnit hf₁)⁻¹ :=
  (boxedSSeriesUnit_C_sub_one_add _ (isUnit_coeff_one_ofBoxedSSeriesUnit _)).trans
    (boxedSSeriesUnit_ofBoxedSSeriesUnit _)

@[simp]
theorem boxedSSeries_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    (f.boxedConvolutionInv hf₀ hf₁).boxedSSeries
        (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁) =
      (↑(f.boxedSSeriesUnit hf₁)⁻¹ : R⟦X⟧) :=
  (val_boxedSSeriesUnit _ _).symm.trans
    (congrArg Units.val (boxedSSeriesUnit_boxedConvolutionInv f hf₀ hf₁))

/-- *Right boxed-convolution inverse*: `f ⊠ f.boxedConvolutionInv = 1 + X`. -/
@[simp]
theorem boxedConvolution_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    f.boxedConvolution (f.boxedConvolutionInv hf₀ hf₁) = 1 + X :=
  eq_of_constantCoeff_eq_of_boxedSSeries_eq
    (by
      rw [coeff_one_boxedConvolution]
      exact hf₁.mul (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁))
    (by simp)
    (by simp [Ring.mul_inverse_cancel _ hf₀])
    (by
      have h := congrArg Units.val
        (boxedSSeriesUnit_boxedConvolution hf₁ (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁))
      simpa [boxedSSeriesUnit_boxedConvolutionInv] using h)

/-- *Left boxed-convolution inverse*: `f.boxedConvolutionInv ⊠ f = 1 + X`. -/
@[simp]
theorem boxedConvolutionInv_boxedConvolution (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    (f.boxedConvolutionInv hf₀ hf₁).boxedConvolution f = 1 + X := by
  rw [boxedConvolution_comm, boxedConvolution_boxedConvolutionInv]

/-- Uniqueness of the right boxed-convolution inverse: if `f ⊠ g = 1 + X`, then
`g = f.boxedConvolutionInv hf₀ hf₁`. -/
theorem eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X {f g : R⟦X⟧}
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f))
    (hfg : f.boxedConvolution g = 1 + X) :
    g = f.boxedConvolutionInv hf₀ hf₁ := by
  calc
    g = (1 + X : R⟦X⟧).boxedConvolution g := (one_add_X_boxedConvolution g).symm
    _ = ((f.boxedConvolutionInv hf₀ hf₁).boxedConvolution f).boxedConvolution g := by
      rw [boxedConvolutionInv_boxedConvolution]
    _ = (f.boxedConvolutionInv hf₀ hf₁).boxedConvolution (f.boxedConvolution g) :=
      boxedConvolution_assoc _ _ _
    _ = (f.boxedConvolutionInv hf₀ hf₁).boxedConvolution (1 + X) := by rw [hfg]
    _ = f.boxedConvolutionInv hf₀ hf₁ := boxedConvolution_one_add_X _

/-- Characterisation of `f.boxedConvolutionInv hf₀ hf₁` by the right boxed-convolution inverse
equation `f ⊠ g = 1 + X`. -/
theorem eq_boxedConvolutionInv_iff {f g : R⟦X⟧} (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    g = f.boxedConvolutionInv hf₀ hf₁ ↔ f.boxedConvolution g = 1 + X :=
  ⟨by rintro rfl; exact boxedConvolution_boxedConvolutionInv f hf₀ hf₁,
    eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X hf₀ hf₁⟩

/-- Base change commutes with `boxedConvolutionInv`. -/
@[simp]
theorem map_boxedConvolutionInv {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f)) :
    map α (f.boxedConvolutionInv hf₀ hf₁) =
      (map α f).boxedConvolutionInv
        (by simpa [← coeff_zero_eq_constantCoeff_apply (map α f), coeff_map] using hf₀.map α)
        (by simpa using hf₁.map α) := by
  refine eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _ ?_
  rw [← map_boxedConvolution, boxedConvolution_boxedConvolutionInv, map_add, map_one, map_X]

/-- For a normalised series (`constantCoeff f = 1`), `f.boxedConvolutionInv` coincides with
`ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹`. -/
theorem boxedConvolutionInv_of_constantCoeff_eq_one {f : R⟦X⟧} (hf₀ : constantCoeff f = 1)
    {hf₀' : IsUnit (constantCoeff f)} (hf₁ : IsUnit (coeff 1 f)) :
    f.boxedConvolutionInv hf₀' hf₁ = ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹ := by
  have hu : hf₀'.unit = 1 := Units.ext <| by simpa using hf₀
  simp [boxedConvolutionInv_def, hu]

/-- For a normalised series (`constantCoeff f = 1`), `ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹`
is its right boxed-convolution inverse. -/
theorem boxedConvolution_ofBoxedSSeriesUnit_inv {f : R⟦X⟧} (hf₀ : constantCoeff f = 1)
    (hf₁ : IsUnit (coeff 1 f)) :
    f.boxedConvolution (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) = 1 + X := by
  rw [← boxedConvolutionInv_of_constantCoeff_eq_one hf₀ (hf₀' := hf₀ ▸ isUnit_one) hf₁,
    boxedConvolution_boxedConvolutionInv]

/-- For a normalised series (`constantCoeff f = 1`), `ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹`
is its left boxed-convolution inverse. -/
theorem ofBoxedSSeriesUnit_inv_boxedConvolution {f : R⟦X⟧} (hf₀ : constantCoeff f = 1)
    (hf₁ : IsUnit (coeff 1 f)) :
    (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹).boxedConvolution f = 1 + X := by
  rw [boxedConvolution_comm, boxedConvolution_ofBoxedSSeriesUnit_inv hf₀ hf₁]

@[simp]
theorem coeff_one_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    coeff 1 (f.boxedConvolutionInv hf₀ hf₁) = Ring.inverse (coeff 1 f) := by
  have h := congrArg (coeff 1) (boxedConvolution_boxedConvolutionInv f hf₀ hf₁)
  simp only [coeff_one_boxedConvolution, map_add, coeff_one, coeff_X, one_ne_zero, ↓reduceIte,
    zero_add] at h
  have hmul := congrArg (Ring.inverse (coeff 1 f) * ·) h
  rwa [← mul_assoc, Ring.inverse_mul_cancel _ hf₁, one_mul, mul_one] at hmul

/-- A power series `f` admits a series `g` with `constantCoeff g = 0` and `f ⊠ g = X` (in
particular, a boxed-convolution inverse with respect to the identity `X` on series with zero
constant coefficient) if and only if `coeff 1 f` is a unit. -/
theorem exists_boxedConvolution_eq_X_iff {f : R⟦X⟧} :
    (∃ g : R⟦X⟧, constantCoeff g = 0 ∧ f.boxedConvolution g = X) ↔ IsUnit (coeff 1 f) := by
  refine ⟨fun ⟨g, _, hfg⟩ => ?_, fun hf₁ => ?_⟩
  · refine IsUnit.of_mul_eq_one (coeff 1 g) ?_
    simpa [coeff_one_boxedConvolution] using congrArg (coeff 1) hfg
  · refine ⟨ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹ - 1, by simp, ?_⟩
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [coeff_boxedConvolution_congr hn (f' := ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁))
      (fun k hk => by simp [coeff_C, coeff_one, hk])
      (g' := ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹)
      (fun k hk => by simp [coeff_one, hk])]
    have hinv := boxedConvolution_ofBoxedSSeriesUnit_inv
      (constantCoeff_ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁))
      (isUnit_coeff_one_ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁))
    rw [boxedSSeriesUnit_ofBoxedSSeriesUnit] at hinv
    rw [hinv]
    simp [coeff_one, hn]

end Inverse

end PowerSeries

namespace TauCeti

open PowerSeries

namespace BoxedConvolution

variable {R : Type*} [CommRing R]

/-- Constructs a unit of `BoxedConvolution R` from proofs that the constant and linear coefficients
are units in `R`. -/
noncomputable def unitOfIsUnit (x : BoxedConvolution R)
    (hx₀ : IsUnit (constantCoeff x.ofBoxed)) (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    (BoxedConvolution R)ˣ where
  val := x
  inv := toBoxed (x.ofBoxed.boxedConvolutionInv hx₀ hx₁)
  val_inv := BoxedConvolution.ext (boxedConvolution_boxedConvolutionInv x.ofBoxed hx₀ hx₁)
  inv_val := BoxedConvolution.ext (boxedConvolutionInv_boxedConvolution x.ofBoxed hx₀ hx₁)

@[simp]
theorem val_unitOfIsUnit (x : BoxedConvolution R) (hx₀ : IsUnit (constantCoeff x.ofBoxed))
    (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    (unitOfIsUnit x hx₀ hx₁ : BoxedConvolution R) = x := (rfl)

@[simp]
theorem val_inv_unitOfIsUnit (x : BoxedConvolution R) (hx₀ : IsUnit (constantCoeff x.ofBoxed))
    (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    (↑(unitOfIsUnit x hx₀ hx₁)⁻¹ : BoxedConvolution R) =
      toBoxed (x.ofBoxed.boxedConvolutionInv hx₀ hx₁) := (rfl)

/-- An element of `BoxedConvolution R` is a unit if and only if both its constant coefficient and
its linear coefficient are units of `R`. -/
theorem isUnit_iff {x : BoxedConvolution R} :
    IsUnit x ↔ IsUnit (constantCoeff x.ofBoxed) ∧ IsUnit (coeff 1 x.ofBoxed) :=
  ⟨fun hx => ⟨by simpa using hx.map constantCoeffHom, by simpa using hx.map coeffOneHom⟩,
    fun ⟨hx₀, hx₁⟩ => (unitOfIsUnit x hx₀ hx₁).isUnit⟩

/-- `toBoxed f` is a unit of `BoxedConvolution R` if and only if `constantCoeff f` and `coeff 1 f`
are units of `R`. -/
theorem isUnit_toBoxed_iff {f : R⟦X⟧} :
    IsUnit (toBoxed f) ↔ IsUnit (constantCoeff f) ∧ IsUnit (coeff 1 f) :=
  isUnit_iff

/-- Packages a normalised series `f` (`constantCoeff f = 1`) with unit linear coefficient as a unit
of `BoxedConvolution.normalizedSubmonoid R`. -/
noncomputable def normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1)
    (hf₁ : IsUnit (coeff 1 f)) : (normalizedSubmonoid R)ˣ :=
  Units.mkOfMulEqOne
    ⟨toBoxed f, mem_normalizedSubmonoid_iff.mpr hf₀⟩
    ⟨toBoxed (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹),
      mem_normalizedSubmonoid_iff.mpr (constantCoeff_ofBoxedSSeriesUnit _)⟩
    (Subtype.ext <| BoxedConvolution.ext <| boxedConvolution_ofBoxedSSeriesUnit_inv hf₀ hf₁)

@[simp]
theorem coe_val_normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1) (hf₁ : IsUnit (coeff 1 f)) :
    ((normalizedUnit f hf₀ hf₁ : normalizedSubmonoid R) : BoxedConvolution R) = toBoxed f := (rfl)

@[simp]
theorem coe_val_inv_normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1)
    (hf₁ : IsUnit (coeff 1 f)) :
    ((↑(normalizedUnit f hf₀ hf₁)⁻¹ : normalizedSubmonoid R) : BoxedConvolution R) =
      toBoxed (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) := (rfl)

/-- An element of `BoxedConvolution.normalizedSubmonoid R` is a unit if and only if its linear
coefficient is a unit of `R`. -/
theorem isUnit_normalizedSubmonoid_iff {x : normalizedSubmonoid R} :
    IsUnit x ↔ IsUnit (coeff 1 x.1.ofBoxed) := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa using (hx.map (normalizedSubmonoid R).subtype).map coeffOneHom
  · have hu := (normalizedUnit x.1.ofBoxed (mem_normalizedSubmonoid_iff.mp x.2) hx).isUnit
    have hx' : (normalizedUnit x.1.ofBoxed (mem_normalizedSubmonoid_iff.mp x.2) hx :
        normalizedSubmonoid R) = x := Subtype.ext (toBoxed_ofBoxed x.1)
    rwa [hx'] at hu

/-- *The one-variable boxed-convolution / S-series group isomorphism*: the formal S-series
identifies the group of units of `BoxedConvolution.normalizedSubmonoid R` (normalised power series
`1 + ∑_{n ≥ 1} aₙ Xⁿ` with unit linear coefficient `a₁ ∈ Rˣ`, under boxed convolution) with the
multiplicative group `R⟦X⟧ˣ` of unit formal power series (under Cauchy multiplication). Its inverse
sends `v : R⟦X⟧ˣ` to `1 + (X v)⁻¹`, where `(X v)⁻¹` denotes the compositional inverse of `X v`. -/
noncomputable def sSeriesMulEquiv : (normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ where
  toFun u := (u : normalizedSubmonoid R).1.ofBoxed.boxedSSeriesUnit
    (isUnit_normalizedSubmonoid_iff.mp u.isUnit)
  invFun v := normalizedUnit (ofBoxedSSeriesUnit v) (constantCoeff_ofBoxedSSeriesUnit v)
    (isUnit_coeff_one_ofBoxedSSeriesUnit v)
  left_inv u := Units.ext <| Subtype.ext <| BoxedConvolution.ext <| by
    rw [coe_val_normalizedUnit, ofBoxed_toBoxed]
    exact ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one
      (mem_normalizedSubmonoid_iff.mp (u : normalizedSubmonoid R).2)
      (isUnit_normalizedSubmonoid_iff.mp u.isUnit)
  right_inv v := boxedSSeriesUnit_ofBoxedSSeriesUnit v
  map_mul' _ _ := boxedSSeriesUnit_boxedConvolution _ _

theorem sSeriesMulEquiv_apply (u : (normalizedSubmonoid R)ˣ) :
    sSeriesMulEquiv u =
      (u : normalizedSubmonoid R).1.ofBoxed.boxedSSeriesUnit
        (isUnit_normalizedSubmonoid_iff.mp u.isUnit) := (rfl)

theorem val_sSeriesMulEquiv (u : (normalizedSubmonoid R)ˣ) :
    (sSeriesMulEquiv u : R⟦X⟧) =
      (u : normalizedSubmonoid R).1.ofBoxed.boxedSSeries
        (isUnit_normalizedSubmonoid_iff.mp u.isUnit) :=
  val_boxedSSeriesUnit _ _

@[simp]
theorem sSeriesMulEquiv_normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1)
    (hf₁ : IsUnit (coeff 1 f)) :
    sSeriesMulEquiv (normalizedUnit f hf₀ hf₁) = f.boxedSSeriesUnit hf₁ := (rfl)

@[simp]
theorem coe_val_sSeriesMulEquiv_symm (v : R⟦X⟧ˣ) :
    ((sSeriesMulEquiv.symm v : normalizedSubmonoid R) : BoxedConvolution R) =
      toBoxed (ofBoxedSSeriesUnit v) := (rfl)

theorem sSeriesMulEquiv_symm_apply (v : R⟦X⟧ˣ) :
    sSeriesMulEquiv.symm v =
      normalizedUnit (ofBoxedSSeriesUnit v) (constantCoeff_ofBoxedSSeriesUnit v)
        (isUnit_coeff_one_ofBoxedSSeriesUnit v) := (rfl)

/-- *Splitting of the full boxed-convolution unit group*: pairing the constant coefficient with the
formal S-series identifies `(BoxedConvolution R)ˣ` with `Rˣ × R⟦X⟧ˣ`. Its inverse sends `(c, v)`
to `C c + (X v)⁻¹ = C c - 1 + ofBoxedSSeriesUnit v`, where `(X v)⁻¹` denotes the compositional
inverse of `X v`. -/
noncomputable def unitsMulEquiv : (BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ where
  toFun u :=
    (Units.map constantCoeffHom u,
      (u : BoxedConvolution R).ofBoxed.boxedSSeriesUnit
        (by simpa using u.isUnit.map coeffOneHom))
  invFun p :=
    let f : R⟦X⟧ := C (p.1 : R) - 1 + ofBoxedSSeriesUnit p.2
    unitOfIsUnit (toBoxed f) (by simp [f])
      (by simpa [f, coeff_C, coeff_one] using isUnit_coeff_one_ofBoxedSSeriesUnit p.2)
  left_inv u := Units.ext <| BoxedConvolution.ext <| by
    dsimp only
    rw [val_unitOfIsUnit, ofBoxed_toBoxed, ofBoxedSSeriesUnit_boxedSSeriesUnit]
    simp
    ring
  right_inv p := Prod.ext (Units.ext <| by simp) <|
    (boxedSSeriesUnit_C_sub_one_add (p.1 : R) (isUnit_coeff_one_ofBoxedSSeriesUnit p.2)).trans
      (boxedSSeriesUnit_ofBoxedSSeriesUnit p.2)
  map_mul' u₁ u₂ := Prod.ext (map_mul (Units.map constantCoeffHom) u₁ u₂)
    (boxedSSeriesUnit_boxedConvolution _ _)

@[simp]
theorem fst_unitsMulEquiv (u : (BoxedConvolution R)ˣ) :
    (unitsMulEquiv u).1 = Units.map constantCoeffHom u := (rfl)

@[simp]
theorem snd_unitsMulEquiv (u : (BoxedConvolution R)ˣ) :
    (unitsMulEquiv u).2 =
      (u : BoxedConvolution R).ofBoxed.boxedSSeriesUnit
        (by simpa using u.isUnit.map coeffOneHom) := (rfl)

@[simp]
theorem val_unitsMulEquiv_symm (p : Rˣ × R⟦X⟧ˣ) :
    (unitsMulEquiv.symm p : BoxedConvolution R) =
      toBoxed (C (p.1 : R) - 1 + ofBoxedSSeriesUnit p.2) := (rfl)

@[simp]
theorem unitsMulEquiv_unitOfIsUnit (x : BoxedConvolution R)
    (hx₀ : IsUnit (constantCoeff x.ofBoxed)) (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    unitsMulEquiv (unitOfIsUnit x hx₀ hx₁) = (hx₀.unit, x.ofBoxed.boxedSSeriesUnit hx₁) :=
  Prod.ext (Units.ext <| by simp) (rfl)

@[simp]
theorem unitsMulEquiv_map_subtype (u : (normalizedSubmonoid R)ˣ) :
    unitsMulEquiv (Units.map (normalizedSubmonoid R).subtype u) = (1, sSeriesMulEquiv u) :=
  Prod.ext
    (Units.ext <| by simpa using mem_normalizedSubmonoid_iff.mp (u : normalizedSubmonoid R).2)
    (rfl)

@[simp]
theorem unitsMulEquiv_symm_one_mk (v : R⟦X⟧ˣ) :
    unitsMulEquiv.symm (1, v) =
      Units.map (normalizedSubmonoid R).subtype (sSeriesMulEquiv.symm v) :=
  Units.ext <| by simp

end BoxedConvolution

section Monoid

open BoxedConvolution

variable {R A : Type*} [CommRing R] [Monoid A]

/-- Packages the free cumulant series of an element `a` of unit mean as a unit of
`BoxedConvolution.normalizedSubmonoid R`. -/
noncomputable def freeCumulantSeriesNormalizedUnit (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    (normalizedSubmonoid R)ˣ :=
  normalizedUnit (freeCumulantSeries φ a) (constantCoeff_freeCumulantSeries φ a)
    (by rwa [coeff_one_freeCumulantSeries])

@[simp]
theorem coe_val_freeCumulantSeriesNormalizedUnit (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    ((freeCumulantSeriesNormalizedUnit φ a ha : normalizedSubmonoid R) : BoxedConvolution R) =
      toBoxed (freeCumulantSeries φ a) := (rfl)

@[simp]
theorem sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    sSeriesMulEquiv (freeCumulantSeriesNormalizedUnit φ a ha) =
      (freeCumulantSeries φ a).boxedSSeriesUnit (by rwa [coeff_one_freeCumulantSeries]) := (rfl)

/-- For a normalised functional `φ`, applying `BoxedConvolution.sSeriesMulEquiv` to
`freeCumulantSeriesNormalizedUnit φ a ha` yields `sSeries φ a ha`. -/
theorem val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit {φ : A → R} (hφ : φ 1 = 1) (a : A)
    (ha : IsUnit (φ a)) :
    (sSeriesMulEquiv (freeCumulantSeriesNormalizedUnit φ a ha) : R⟦X⟧) = sSeries φ a ha :=
  (congrArg Units.val (sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit φ a ha)).trans
    ((val_boxedSSeriesUnit _ _).trans (sSeries_eq_boxedSSeries_freeCumulantSeries hφ a ha).symm)

end Monoid

end TauCeti
