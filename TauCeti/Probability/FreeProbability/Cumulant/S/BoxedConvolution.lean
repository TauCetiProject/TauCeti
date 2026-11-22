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

* `PowerSeries.boxedConvolution_boxedConvolutionInv_cancel`,
  `PowerSeries.boxedConvolutionInv_boxedConvolution_cancel`,
  `PowerSeries.boxedConvolutionInv_boxedConvolution`,
  `PowerSeries.eq_boxedConvolutionInv_iff`: two-sided inverse equations, multiplicativity,
  involution, rescaling, and uniqueness for `boxedConvolutionInv`.
* `PowerSeries.exists_boxedConvolution_eq_X_iff`: a series `f` admits `g` with
  `constantCoeff g = 0` and `f ⊠ g = X` if and only if `IsUnit (coeff 1 f)`.
* `TauCeti.BoxedConvolution.isUnit_iff`,
  `TauCeti.BoxedConvolution.isUnit_normalizedSubmonoid_iff`: characterisations of invertible
  elements under boxed convolution.
* `TauCeti.BoxedConvolution.sSeriesMulEquiv_mapNormalized`,
  `TauCeti.BoxedConvolution.unitsMulEquiv_map`: base-change naturality for `sSeriesMulEquiv` and
  `unitsMulEquiv`.
* `TauCeti.val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit`,
  `TauCeti.IsFreelyIndependent.freeCumulantSeriesNormalizedUnit_mul`,
  `TauCeti.IsFreelyIndependent.freeCumulantSeriesNormalizedUnit_list_prod`,
  `TauCeti.IsFreelyIndependent.sSeries_list_prod`,
  `TauCeti.IsFreelyIndependentElements.sSeries_list_prod`: for a normalised `φ`,
  `sSeriesMulEquiv` maps `freeCumulantSeriesNormalizedUnit` to `sSeries`, and both
  `freeCumulantSeriesNormalizedUnit` and `sSeries` are multiplicative on free products.

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
  C ((↑hf₀.unit⁻¹ : R) - 1) + ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹

theorem boxedConvolutionInv_def (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    f.boxedConvolutionInv hf₀ hf₁ =
      C ((↑hf₀.unit⁻¹ : R) - 1) + ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹ := (rfl)

@[simp]
theorem constantCoeff_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    constantCoeff (f.boxedConvolutionInv hf₀ hf₁) = Ring.inverse (constantCoeff f) := by
  simp [boxedConvolutionInv_def, Ring.inverse_of_isUnit hf₀]

/-- The constant coefficient of `f.boxedConvolutionInv hf₀ hf₁` is a unit. -/
theorem isUnit_constantCoeff_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    IsUnit (constantCoeff (f.boxedConvolutionInv hf₀ hf₁)) :=
  constantCoeff_boxedConvolutionInv f hf₀ hf₁ ▸ hf₀.ringInverse

/-- `f.boxedConvolutionInv hf₀ hf₁` agrees with `ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹`
at every positive index. -/
theorem coeff_boxedConvolutionInv_eq_coeff_ofBoxedSSeriesUnit (f : R⟦X⟧)
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f)) {n : ℕ} (hn : n ≠ 0) :
    coeff n (f.boxedConvolutionInv hf₀ hf₁) =
      coeff n (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) := by
  simp [boxedConvolutionInv_def, coeff_C, hn]

/-- The linear coefficient of `f.boxedConvolutionInv hf₀ hf₁` is a unit. -/
theorem isUnit_coeff_one_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    IsUnit (coeff 1 (f.boxedConvolutionInv hf₀ hf₁)) :=
  coeff_boxedConvolutionInv_eq_coeff_ofBoxedSSeriesUnit f hf₀ hf₁ one_ne_zero ▸
    isUnit_coeff_one_ofBoxedSSeriesUnit _

@[simp]
theorem boxedSSeriesUnit_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    (f.boxedConvolutionInv hf₀ hf₁).boxedSSeriesUnit
        (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁) =
      (f.boxedSSeriesUnit hf₁)⁻¹ := by
  simp only [boxedConvolutionInv_def, boxedSSeriesUnit_C_add, boxedSSeriesUnit_ofBoxedSSeriesUnit]

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
theorem boxedConvolution_boxedConvolutionInv_cancel (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    f.boxedConvolution (f.boxedConvolutionInv hf₀ hf₁) = 1 + X :=
  eq_of_constantCoeff_eq_of_boxedSSeries_eq
    (by rw [coeff_one_boxedConvolution]; exact hf₁.mul (isUnit_coeff_one_boxedConvolutionInv ..))
    (by simp) (by simp [Ring.mul_inverse_cancel _ hf₀])
    (by
      simpa [boxedSSeriesUnit_boxedConvolutionInv] using congrArg Units.val
        (boxedSSeriesUnit_boxedConvolution hf₁ (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁)))

/-- *Left boxed-convolution inverse*: `f.boxedConvolutionInv ⊠ f = 1 + X`. -/
@[simp]
theorem boxedConvolutionInv_boxedConvolution_cancel (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    (f.boxedConvolutionInv hf₀ hf₁).boxedConvolution f = 1 + X := by
  rw [boxedConvolution_comm, boxedConvolution_boxedConvolutionInv_cancel]

/-- Uniqueness of the right boxed-convolution inverse: if `f ⊠ g = 1 + X`, then
`g = f.boxedConvolutionInv hf₀ hf₁`. -/
theorem eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X {f g : R⟦X⟧}
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f))
    (hfg : f.boxedConvolution g = 1 + X) :
    g = f.boxedConvolutionInv hf₀ hf₁ :=
  BoxedConvolution.toBoxed_inj.mp (left_inv_eq_right_inv
    (BoxedConvolution.ext (boxedConvolutionInv_boxedConvolution_cancel f hf₀ hf₁))
    (BoxedConvolution.ext hfg)).symm

/-- Characterisation of `f.boxedConvolutionInv hf₀ hf₁` by the right boxed-convolution inverse
equation `f ⊠ g = 1 + X`. -/
theorem eq_boxedConvolutionInv_iff {f g : R⟦X⟧} (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    g = f.boxedConvolutionInv hf₀ hf₁ ↔ f.boxedConvolution g = 1 + X :=
  ⟨by rintro rfl; exact boxedConvolution_boxedConvolutionInv_cancel f hf₀ hf₁,
    eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X hf₀ hf₁⟩

@[simp]
theorem boxedConvolutionInv_one_add_X :
    (1 + X : R⟦X⟧).boxedConvolutionInv (by simp) (by simp) = 1 + X :=
  (eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _ (by simp)).symm

/-- Boxed-convolution inversion is an involution. -/
@[simp]
theorem boxedConvolutionInv_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    (f.boxedConvolutionInv hf₀ hf₁).boxedConvolutionInv
        (isUnit_constantCoeff_boxedConvolutionInv f hf₀ hf₁)
        (isUnit_coeff_one_boxedConvolutionInv f hf₀ hf₁) = f :=
  (eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _
    (boxedConvolutionInv_boxedConvolution_cancel f hf₀ hf₁)).symm

/-- Boxed-convolution inversion is multiplicative: `(f ⊠ g)⁻¹ = f⁻¹ ⊠ g⁻¹`. -/
theorem boxedConvolutionInv_boxedConvolution {f g : R⟦X⟧}
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f))
    (hg₀ : IsUnit (constantCoeff g)) (hg₁ : IsUnit (coeff 1 g)) :
    (f.boxedConvolution g).boxedConvolutionInv
        (by rw [constantCoeff_boxedConvolution]; exact hf₀.mul hg₀)
        (by rw [coeff_one_boxedConvolution]; exact hf₁.mul hg₁) =
      (f.boxedConvolutionInv hf₀ hf₁).boxedConvolution (g.boxedConvolutionInv hg₀ hg₁) := by
  refine (eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _ ?_).symm
  apply BoxedConvolution.toBoxed_injective
  simp only [BoxedConvolution.toBoxed_boxedConvolution, BoxedConvolution.toBoxed_one_add_X]
  rw [mul_mul_mul_comm]
  simp only [← BoxedConvolution.toBoxed_boxedConvolution,
    boxedConvolution_boxedConvolutionInv_cancel, BoxedConvolution.toBoxed_one_add_X, mul_one]

/-- Base change commutes with `boxedConvolutionInv`. -/
@[simp]
theorem map_boxedConvolutionInv {S : Type*} [CommRing S] (α : R →+* S) (f : R⟦X⟧)
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f)) :
    map α (f.boxedConvolutionInv hf₀ hf₁) =
      (map α f).boxedConvolutionInv (by simpa using hf₀.map α) (by simpa using hf₁.map α) := by
  refine eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _ ?_
  rw [← map_boxedConvolution, boxedConvolution_boxedConvolutionInv_cancel, map_add, map_one, map_X]

/-- Rescaling a series by a unit `c` rescales its boxed-convolution inverse by `c⁻¹`. -/
theorem boxedConvolutionInv_rescale {c : R} (hc : IsUnit c) (f : R⟦X⟧)
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f)) :
    (rescale c f).boxedConvolutionInv
        (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]; simpa using hf₀)
        (by simpa [coeff_rescale] using hc.mul hf₁) =
      rescale (Ring.inverse c) (f.boxedConvolutionInv hf₀ hf₁) := by
  refine (eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _ ?_).symm
  rw [rescale_boxedConvolution, boxedConvolution_rescale, rescale_rescale]
  simp [Ring.inverse_mul_cancel _ hc]

/-- Rescaling the boxed-convolution inverse of `f` by a unit `c` equals the boxed-convolution
inverse of `rescale c⁻¹ f`. -/
theorem rescale_boxedConvolutionInv {c : R} (hc : IsUnit c) (f : R⟦X⟧)
    (hf₀ : IsUnit (constantCoeff f)) (hf₁ : IsUnit (coeff 1 f)) :
    rescale c (f.boxedConvolutionInv hf₀ hf₁) =
      (rescale (Ring.inverse c) f).boxedConvolutionInv
        (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]; simpa using hf₀)
        (by simpa [coeff_rescale] using hc.ringInverse.mul hf₁) := by
  simpa [Ring.inverse_inverse hc] using (boxedConvolutionInv_rescale hc.ringInverse f hf₀ hf₁).symm

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
    boxedConvolution_boxedConvolutionInv_cancel]

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
  have h := congrArg (coeff 1) (boxedConvolution_boxedConvolutionInv_cancel f hf₀ hf₁)
  simp only [coeff_one_boxedConvolution, map_add, coeff_one, coeff_X, one_ne_zero, ↓reduceIte,
    zero_add] at h
  exact (left_inv_eq_right_inv (Ring.inverse_mul_cancel _ hf₁) h).symm

/-- A power series `f` admits a series `g` with `constantCoeff g = 0` and `f ⊠ g = X` (in
particular, a boxed-convolution inverse with respect to the identity `X` on series with zero
constant coefficient) if and only if `coeff 1 f` is a unit. -/
theorem exists_boxedConvolution_eq_X_iff {f : R⟦X⟧} :
    (∃ g : R⟦X⟧, constantCoeff g = 0 ∧ f.boxedConvolution g = X) ↔ IsUnit (coeff 1 f) := by
  refine ⟨fun ⟨g, _, hfg⟩ => IsUnit.of_mul_eq_one (coeff 1 g)
    (by simpa [coeff_one_boxedConvolution] using congrArg (coeff 1) hfg), fun hf₁ => ?_⟩
  refine ⟨ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹ - 1, by simp, ?_⟩
  ext (_ | n)
  · simp
  · rw [coeff_boxedConvolution_congr n.succ_ne_zero
      (f' := ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁))
      (fun k hk => by simp [coeff_C, coeff_one, hk])
      (g' := ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) (fun k hk => by simp [coeff_one, hk])]
    have hinv := boxedConvolution_ofBoxedSSeriesUnit_inv
      (constantCoeff_ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁))
      (isUnit_coeff_one_ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁))
    rw [boxedSSeriesUnit_ofBoxedSSeriesUnit] at hinv
    rw [hinv]
    simp [coeff_one]

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
  val_inv := BoxedConvolution.ext (boxedConvolution_boxedConvolutionInv_cancel x.ofBoxed hx₀ hx₁)
  inv_val := BoxedConvolution.ext (boxedConvolutionInv_boxedConvolution_cancel x.ofBoxed hx₀ hx₁)

@[simp]
theorem val_unitOfIsUnit (x : BoxedConvolution R) (hx₀ : IsUnit (constantCoeff x.ofBoxed))
    (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    (unitOfIsUnit x hx₀ hx₁ : BoxedConvolution R) = x := (rfl)

@[simp]
theorem val_inv_unitOfIsUnit (x : BoxedConvolution R) (hx₀ : IsUnit (constantCoeff x.ofBoxed))
    (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    (↑(unitOfIsUnit x hx₀ hx₁)⁻¹ : BoxedConvolution R) =
      toBoxed (x.ofBoxed.boxedConvolutionInv hx₀ hx₁) := (rfl)

@[simp]
theorem unitOfIsUnit_one : unitOfIsUnit (1 : BoxedConvolution R) (by simp) (by simp) = 1 :=
  Units.ext <| by simp

theorem unitOfIsUnit_mul (x y : BoxedConvolution R)
    (hx₀ : IsUnit (constantCoeff x.ofBoxed)) (hx₁ : IsUnit (coeff 1 x.ofBoxed))
    (hy₀ : IsUnit (constantCoeff y.ofBoxed)) (hy₁ : IsUnit (coeff 1 y.ofBoxed)) :
    unitOfIsUnit (x * y)
        (by rw [ofBoxed_mul, constantCoeff_boxedConvolution]; exact hx₀.mul hy₀)
        (by rw [ofBoxed_mul, coeff_one_boxedConvolution]; exact hx₁.mul hy₁) =
      unitOfIsUnit x hx₀ hx₁ * unitOfIsUnit y hy₀ hy₁ :=
  Units.ext <| by simp

/-- An element of `BoxedConvolution R` is a unit if and only if both its constant coefficient and
its linear coefficient are units of `R`. -/
theorem isUnit_iff {x : BoxedConvolution R} :
    IsUnit x ↔ IsUnit (constantCoeff x.ofBoxed) ∧ IsUnit (coeff 1 x.ofBoxed) :=
  ⟨fun hx => ⟨by simpa using hx.map constantCoeffHom, by simpa using hx.map coeffOneHom⟩,
    fun ⟨hx₀, hx₁⟩ => (unitOfIsUnit x hx₀ hx₁).isUnit⟩

/-- The underlying power series of `u⁻¹` for any unit `u : (BoxedConvolution R)ˣ` is the
boxed-convolution inverse of `(u : BoxedConvolution R).ofBoxed`. -/
theorem ofBoxed_val_inv (u : (BoxedConvolution R)ˣ) :
    (↑u⁻¹ : BoxedConvolution R).ofBoxed =
      (u : BoxedConvolution R).ofBoxed.boxedConvolutionInv
        (isUnit_iff.mp u.isUnit).1 (isUnit_iff.mp u.isUnit).2 :=
  eq_boxedConvolutionInv_of_boxedConvolution_eq_one_add_X _ _ <| by
    rw [← ofBoxed_mul, Units.mul_inv, ofBoxed_one]

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

@[simp]
theorem normalizedUnit_one_add_X :
    normalizedUnit (1 + X : R⟦X⟧) (by simp) (by simp) = 1 :=
  Units.ext <| Subtype.ext <| by simp

theorem normalizedUnit_boxedConvolution {f g : R⟦X⟧}
    (hf₀ : constantCoeff f = 1) (hf₁ : IsUnit (coeff 1 f))
    (hg₀ : constantCoeff g = 1) (hg₁ : IsUnit (coeff 1 g)) :
    normalizedUnit (f.boxedConvolution g)
        (by rw [constantCoeff_boxedConvolution, hf₀, hg₀, mul_one])
        (by rw [coeff_one_boxedConvolution]; exact hf₁.mul hg₁) =
      normalizedUnit f hf₀ hf₁ * normalizedUnit g hg₀ hg₁ :=
  Units.ext <| Subtype.ext <| by simp

/-- An element of `BoxedConvolution.normalizedSubmonoid R` is a unit if and only if its linear
coefficient is a unit of `R`. -/
theorem isUnit_normalizedSubmonoid_iff {x : normalizedSubmonoid R} :
    IsUnit x ↔ IsUnit (coeff 1 x.val.ofBoxed) := by
  refine ⟨fun hx => by simpa using (hx.map (normalizedSubmonoid R).subtype).map coeffOneHom,
    fun hx => ?_⟩
  have hu := (normalizedUnit x.val.ofBoxed (mem_normalizedSubmonoid_iff.mp x.property) hx).isUnit
  exact (Subtype.ext (toBoxed_ofBoxed x.val) :
    (normalizedUnit x.val.ofBoxed (mem_normalizedSubmonoid_iff.mp x.property) hx :
      normalizedSubmonoid R) = x) ▸ hu

/-- *The one-variable boxed-convolution / S-series group isomorphism*: the formal S-series
identifies the group of units of `BoxedConvolution.normalizedSubmonoid R` (normalised power series
`1 + ∑_{n ≥ 1} aₙ Xⁿ` with unit linear coefficient `a₁ ∈ Rˣ`, under boxed convolution) with the
multiplicative group `R⟦X⟧ˣ` of unit formal power series (under Cauchy multiplication). Its inverse
sends `v : R⟦X⟧ˣ` to `1 + (X v)⁻¹`, where `(X v)⁻¹` denotes the compositional inverse of `X v`. -/
noncomputable def sSeriesMulEquiv : (normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ where
  toFun u := (u : normalizedSubmonoid R).val.ofBoxed.boxedSSeriesUnit
    (isUnit_normalizedSubmonoid_iff.mp u.isUnit)
  invFun v := normalizedUnit (ofBoxedSSeriesUnit v) (constantCoeff_ofBoxedSSeriesUnit v)
    (isUnit_coeff_one_ofBoxedSSeriesUnit v)
  left_inv u := Units.ext <| Subtype.ext <| BoxedConvolution.ext <| by
    rw [coe_val_normalizedUnit, ofBoxed_toBoxed]
    exact ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one
      (mem_normalizedSubmonoid_iff.mp (u : normalizedSubmonoid R).property)
      (isUnit_normalizedSubmonoid_iff.mp u.isUnit)
  right_inv v := boxedSSeriesUnit_ofBoxedSSeriesUnit v
  map_mul' _ _ := boxedSSeriesUnit_boxedConvolution _ _

theorem sSeriesMulEquiv_apply (u : (normalizedSubmonoid R)ˣ) :
    sSeriesMulEquiv u =
      (u : normalizedSubmonoid R).val.ofBoxed.boxedSSeriesUnit
        (isUnit_normalizedSubmonoid_iff.mp u.isUnit) := (rfl)

@[simp]
theorem val_sSeriesMulEquiv (u : (normalizedSubmonoid R)ˣ) :
    (sSeriesMulEquiv u : R⟦X⟧) =
      (u : normalizedSubmonoid R).val.ofBoxed.boxedSSeries
        (isUnit_normalizedSubmonoid_iff.mp u.isUnit) :=
  val_boxedSSeriesUnit _ _

@[simp]
theorem sSeriesMulEquiv_normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1)
    (hf₁ : IsUnit (coeff 1 f)) :
    sSeriesMulEquiv (normalizedUnit f hf₀ hf₁) = f.boxedSSeriesUnit hf₁ := by
  simp [sSeriesMulEquiv_apply]

theorem sSeriesMulEquiv_symm_apply (v : R⟦X⟧ˣ) :
    sSeriesMulEquiv.symm v =
      normalizedUnit (ofBoxedSSeriesUnit v) (constantCoeff_ofBoxedSSeriesUnit v)
        (isUnit_coeff_one_ofBoxedSSeriesUnit v) := (rfl)

@[simp]
theorem coe_val_sSeriesMulEquiv_symm (v : R⟦X⟧ˣ) :
    ((sSeriesMulEquiv.symm v : normalizedSubmonoid R) : BoxedConvolution R) =
      toBoxed (ofBoxedSSeriesUnit v) := by
  rw [sSeriesMulEquiv_symm_apply, coe_val_normalizedUnit]

/-- Base change commutes with `sSeriesMulEquiv`. -/
@[simp]
theorem sSeriesMulEquiv_mapNormalized {S : Type*} [CommRing S] (α : R →+* S)
    (u : (normalizedSubmonoid R)ˣ) :
    sSeriesMulEquiv (Units.map (mapNormalized α) u) =
      Units.map ↑(PowerSeries.map α) (sSeriesMulEquiv u) := by
  simp [sSeriesMulEquiv_apply]

/-- Base change commutes with `sSeriesMulEquiv.symm`. -/
@[simp]
theorem mapNormalized_sSeriesMulEquiv_symm {S : Type*} [CommRing S] (α : R →+* S)
    (v : R⟦X⟧ˣ) :
    Units.map (mapNormalized α) (sSeriesMulEquiv.symm v) =
      sSeriesMulEquiv.symm (Units.map ↑(PowerSeries.map α) v) :=
  Units.ext <| Subtype.ext <| by simp

/-- *Splitting of the full boxed-convolution unit group*: pairing the constant coefficient with the
formal S-series identifies `(BoxedConvolution R)ˣ` with `Rˣ × R⟦X⟧ˣ`. Its inverse sends `(c, v)`
to `C c + (X v)⁻¹ = C (c - 1) + ofBoxedSSeriesUnit v`, where `(X v)⁻¹` denotes the compositional
inverse of `X v`. -/
noncomputable def unitsMulEquiv : (BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ where
  toFun u :=
    (Units.map constantCoeffHom u,
      (u : BoxedConvolution R).ofBoxed.boxedSSeriesUnit
        (by simpa using u.isUnit.map coeffOneHom))
  invFun p :=
    let f : R⟦X⟧ := C ((p.1 : R) - 1) + ofBoxedSSeriesUnit p.2
    unitOfIsUnit (toBoxed f) (by simp [f])
      (by simpa [f, coeff_C] using isUnit_coeff_one_ofBoxedSSeriesUnit p.2)
  left_inv u := Units.ext <| BoxedConvolution.ext <| by
    simp only [val_unitOfIsUnit, ofBoxed_toBoxed, ofBoxedSSeriesUnit_boxedSSeriesUnit,
      Units.coe_map, constantCoeffHom_apply, map_sub, map_one]
    ring
  right_inv p := Prod.ext (Units.ext <| by simp) <| by
    dsimp only
    simp only [val_unitOfIsUnit, ofBoxed_toBoxed, boxedSSeriesUnit_C_add,
      boxedSSeriesUnit_ofBoxedSSeriesUnit]
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
      toBoxed (C ((p.1 : R) - 1) + ofBoxedSSeriesUnit p.2) := (rfl)

@[simp]
theorem unitsMulEquiv_unitOfIsUnit (x : BoxedConvolution R)
    (hx₀ : IsUnit (constantCoeff x.ofBoxed)) (hx₁ : IsUnit (coeff 1 x.ofBoxed)) :
    unitsMulEquiv (unitOfIsUnit x hx₀ hx₁) = (hx₀.unit, x.ofBoxed.boxedSSeriesUnit hx₁) :=
  Prod.ext (Units.ext <| by simp) (by simp)

@[simp]
theorem unitsMulEquiv_map_subtype (u : (normalizedSubmonoid R)ˣ) :
    unitsMulEquiv (Units.map (normalizedSubmonoid R).subtype u) = (1, sSeriesMulEquiv u) :=
  Prod.ext
    (Units.ext <| by
      simpa using mem_normalizedSubmonoid_iff.mp (u : normalizedSubmonoid R).property)
    (by simp [sSeriesMulEquiv_apply])

@[simp]
theorem unitsMulEquiv_symm_one_mk (v : R⟦X⟧ˣ) :
    unitsMulEquiv.symm (1, v) =
      Units.map (normalizedSubmonoid R).subtype (sSeriesMulEquiv.symm v) :=
  Units.ext <| by simp

/-- Base change commutes with `unitsMulEquiv`. -/
@[simp]
theorem unitsMulEquiv_map {S : Type*} [CommRing S] (α : R →+* S)
    (u : (BoxedConvolution R)ˣ) :
    unitsMulEquiv (Units.map (map α) u) =
      (Units.map (α : R →* S) (unitsMulEquiv u).1,
        Units.map ↑(PowerSeries.map α) (unitsMulEquiv u).2) :=
  Prod.ext (Units.ext <| by simp) (by simp)

/-- Base change commutes with `unitsMulEquiv.symm`. -/
@[simp]
theorem map_unitsMulEquiv_symm {S : Type*} [CommRing S] (α : R →+* S)
    (p : Rˣ × R⟦X⟧ˣ) :
    Units.map (map α) (unitsMulEquiv.symm p) =
      unitsMulEquiv.symm (Units.map (α : R →* S) p.1, Units.map ↑(PowerSeries.map α) p.2) :=
  Units.ext <| BoxedConvolution.ext <| by simp

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

theorem freeCumulantSeriesNormalizedUnit_def (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    freeCumulantSeriesNormalizedUnit φ a ha =
      normalizedUnit (freeCumulantSeries φ a) (constantCoeff_freeCumulantSeries φ a)
        (by rwa [coeff_one_freeCumulantSeries]) := (rfl)

@[simp]
theorem coe_val_freeCumulantSeriesNormalizedUnit (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    ((freeCumulantSeriesNormalizedUnit φ a ha : normalizedSubmonoid R) : BoxedConvolution R) =
      toBoxed (freeCumulantSeries φ a) :=
  coe_val_normalizedUnit ..

@[simp]
theorem coe_val_inv_freeCumulantSeriesNormalizedUnit (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    ((↑(freeCumulantSeriesNormalizedUnit φ a ha)⁻¹ : normalizedSubmonoid R) :
        BoxedConvolution R) =
      toBoxed (ofBoxedSSeriesUnit
        ((freeCumulantSeries φ a).boxedSSeriesUnit (by rwa [coeff_one_freeCumulantSeries]))⁻¹) :=
  coe_val_inv_normalizedUnit ..

@[simp]
theorem freeCumulantSeriesNormalizedUnit_one {φ : A → R} (hφ : φ 1 = 1) (h1 : IsUnit (φ 1)) :
    freeCumulantSeriesNormalizedUnit φ (1 : A) h1 = 1 :=
  Units.ext <| Subtype.ext <| by simp [freeCumulantSeries_one hφ]

@[simp]
theorem sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit (φ : A → R) (a : A) (ha : IsUnit (φ a)) :
    sSeriesMulEquiv (freeCumulantSeriesNormalizedUnit φ a ha) =
      (freeCumulantSeries φ a).boxedSSeriesUnit (by rwa [coeff_one_freeCumulantSeries]) :=
  sSeriesMulEquiv_normalizedUnit ..

/-- For a normalised functional `φ`, applying `BoxedConvolution.sSeriesMulEquiv` to
`freeCumulantSeriesNormalizedUnit φ a ha` yields `sSeries φ a ha`. -/
theorem val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit {φ : A → R} (hφ : φ 1 = 1) (a : A)
    (ha : IsUnit (φ a)) :
    (sSeriesMulEquiv (freeCumulantSeriesNormalizedUnit φ a ha) : R⟦X⟧) = sSeries φ a ha :=
  (congrArg Units.val (sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit φ a ha)).trans
    ((val_boxedSSeriesUnit _ _).trans (sSeries_eq_boxedSSeries_freeCumulantSeries hφ a ha).symm)

end Monoid

section FreeProduct

open BoxedConvolution

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- *Multiplicativity of `freeCumulantSeriesNormalizedUnit` on two free variables*: for a
normalised `φ`, letters `a ∈ B i` and `b ∈ B j` (`i ≠ j`) of unit means from a freely independent
family satisfy `freeCumulantSeriesNormalizedUnit φ (a * b) _ =
freeCumulantSeriesNormalizedUnit φ a hua * freeCumulantSeriesNormalizedUnit φ b hub`. -/
theorem IsFreelyIndependent.freeCumulantSeriesNormalizedUnit_mul {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) (hua : IsUnit (φ a)) (hub : IsUnit (φ b)) :
    freeCumulantSeriesNormalizedUnit φ (a * b)
        (h.isUnit_apply_mul_of_ne hφ hij ha hb hua hub) =
      freeCumulantSeriesNormalizedUnit φ a hua * freeCumulantSeriesNormalizedUnit φ b hub :=
  Units.ext <| Subtype.ext <| by simp [h.freeCumulantSeries_mul hφ hij ha hb]

/-- *Multiplicativity of `freeCumulantSeriesNormalizedUnit` on two free elements*: for distinct
indices `i ≠ j` of a freely independent family `c` with unit means under a normalised `φ`,
`freeCumulantSeriesNormalizedUnit φ (c i * c j) _ =
freeCumulantSeriesNormalizedUnit φ (c i) hua * freeCumulantSeriesNormalizedUnit φ (c j) hub`. -/
theorem IsFreelyIndependentElements.freeCumulantSeriesNormalizedUnit_mul {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hua : IsUnit (φ (c i))) (hub : IsUnit (φ (c j))) :
    freeCumulantSeriesNormalizedUnit φ (c i * c j)
        (h.isUnit_apply_mul_of_ne hφ hij hua hub) =
      freeCumulantSeriesNormalizedUnit φ (c i) hua *
        freeCumulantSeriesNormalizedUnit φ (c j) hub :=
  (isFreelyIndependentElements_iff.mp h).freeCumulantSeriesNormalizedUnit_mul hφ hij
    (Algebra.self_mem_adjoin_singleton R _) (Algebra.self_mem_adjoin_singleton R _) hua hub

/-- *Multiplicativity of `freeCumulantSeriesNormalizedUnit` on finite products of free variables*:
for a normalised `φ`, a freely independent family `B`, and a list `l : List (ι × A)` with
pairwise distinct indices whose letters `p.2 ∈ B p.1` have unit means, the normalised
free-cumulant unit of `(l.map Prod.snd).prod` is the product of the units of the letters. -/
theorem IsFreelyIndependent.freeCumulantSeriesNormalizedUnit_list_prod {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {l : List (ι × A)}
    (hnodup : (l.map Prod.fst).Nodup) (hl : ∀ p ∈ l, p.2 ∈ B p.1)
    (hu : ∀ p ∈ l, IsUnit (φ p.2)) :
    freeCumulantSeriesNormalizedUnit φ (l.map Prod.snd).prod
        (h.isUnit_apply_list_prod hφ hnodup hl hu) =
      (l.attach.map fun p =>
        freeCumulantSeriesNormalizedUnit φ p.val.2 (hu p.val p.property)).prod :=
  Units.ext <| Subtype.ext <| by
    rw [coe_val_freeCumulantSeriesNormalizedUnit,
      h.toBoxed_freeCumulantSeries_list_prod hφ hnodup hl]
    simpa [Function.comp_def, ← l.attach_map_val] using
      (map_list_prod ((normalizedSubmonoid R).subtype.comp (Units.coeHom _))
        (l.attach.map fun p =>
          freeCumulantSeriesNormalizedUnit φ p.val.2 (hu p.val p.property))).symm

/-- *Multiplicativity of `freeCumulantSeriesNormalizedUnit` on finite products of free elements*:
for a duplicate-free list `l` of indices of a freely independent family `c` with unit means under a
normalised `φ`, the normalised free-cumulant unit of `(l.map c).prod` is the product of the units
of the factors. -/
theorem IsFreelyIndependentElements.freeCumulantSeriesNormalizedUnit_list_prod {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {l : List ι} (hnodup : l.Nodup)
    (hu : ∀ i ∈ l, IsUnit (φ (c i))) :
    freeCumulantSeriesNormalizedUnit φ (l.map c).prod
        (h.isUnit_apply_list_prod hφ hnodup hu) =
      (l.attach.map fun i =>
        freeCumulantSeriesNormalizedUnit φ (c i.val) (hu i.val i.property)).prod := by
  have h1 := (isFreelyIndependentElements_iff.mp h).freeCumulantSeriesNormalizedUnit_list_prod hφ
    (l := l.map fun i => (i, c i)) (by simpa [Function.comp_def] using hnodup)
    (by simp [Algebra.self_mem_adjoin_singleton]) (by simpa using hu)
  simpa [List.attach_map, Function.comp_def] using
    (Units.ext <| Subtype.ext <| by simp [Function.comp_def]).trans h1

/-- *Multiplicativity of the formal S-series on finite products of free variables*: for a
normalised `φ`, a freely independent family `B`, and a list `l : List (ι × A)` with pairwise
distinct indices whose letters `p.2 ∈ B p.1` have unit means, the formal S-series of
`(l.map Prod.snd).prod` is the product of the formal S-series of the letters. -/
theorem IsFreelyIndependent.sSeries_list_prod {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {l : List (ι × A)}
    (hnodup : (l.map Prod.fst).Nodup) (hl : ∀ p ∈ l, p.2 ∈ B p.1)
    (hu : ∀ p ∈ l, IsUnit (φ p.2)) :
    sSeries φ (l.map Prod.snd).prod (h.isUnit_apply_list_prod hφ hnodup hl hu) =
      (l.attach.map fun p => sSeries φ p.val.2 (hu p.val p.property)).prod := by
  simpa only [map_list_prod, MonoidHom.coe_comp, Function.comp_def, Units.coeHom_apply,
    MulEquiv.coe_toMonoidHom, List.map_map,
    val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit hφ] using
    congrArg ((Units.coeHom R⟦X⟧).comp sSeriesMulEquiv.toMonoidHom)
      (h.freeCumulantSeriesNormalizedUnit_list_prod hφ hnodup hl hu)

/-- *Multiplicativity of the formal S-series on finite products of free elements*: for a
duplicate-free list `l` of indices of a freely independent family `c` with unit means under a
normalised `φ`, the S-series of `(l.map c).prod` is the product of the S-series of the factors. -/
theorem IsFreelyIndependentElements.sSeries_list_prod {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {l : List ι} (hnodup : l.Nodup)
    (hu : ∀ i ∈ l, IsUnit (φ (c i))) :
    sSeries φ (l.map c).prod (h.isUnit_apply_list_prod hφ hnodup hu) =
      (l.attach.map fun i => sSeries φ (c i.val) (hu i.val i.property)).prod := by
  simpa only [map_list_prod, MonoidHom.coe_comp, Function.comp_def, Units.coeHom_apply,
    MulEquiv.coe_toMonoidHom, List.map_map,
    val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit hφ] using
    congrArg ((Units.coeHom R⟦X⟧).comp sSeriesMulEquiv.toMonoidHom)
      (h.freeCumulantSeriesNormalizedUnit_list_prod hφ hnodup hu)

end FreeProduct

end TauCeti
