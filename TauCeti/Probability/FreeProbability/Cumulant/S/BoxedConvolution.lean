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
  and linear coefficients are units (and inverses with respect to `X` on series with zero constant
  coefficient);
* characterisations of the units of `PowerSeries.BoxedConvolution R` and of its normalised
  submonoid `PowerSeries.BoxedConvolution.normalizedSubmonoid R`;
* the one-variable boxed-convolution / S-series group isomorphism
  `PowerSeries.BoxedConvolution.sSeriesMulEquiv :`
  `(BoxedConvolution.normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ`
  and the full unit splitting
  `PowerSeries.BoxedConvolution.unitsMulEquiv : (BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ`;
* multiplicativity of `TauCeti.sSeries` along arbitrary duplicate-free finite products of free
  variables over any semiring `A` (`TauCeti.IsFreelyIndependent.sSeries_list_prod`), obtained by
  applying `sSeriesMulEquiv` to `TauCeti.IsFreelyIndependent.toBoxed_freeCumulantSeries_list_prod`.

## Main definitions

* `PowerSeries.boxedConvolutionInv`: the boxed-convolution inverse of a series whose constant and
  linear coefficients are units.
* `PowerSeries.BoxedConvolution.unitOfIsUnit`, `PowerSeries.BoxedConvolution.normalizedUnit`:
  constructors for units of `BoxedConvolution R` and `BoxedConvolution.normalizedSubmonoid R`.
* `PowerSeries.BoxedConvolution.sSeriesMulEquiv`: the group isomorphism
  `(BoxedConvolution.normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ` given by the formal S-series.
* `PowerSeries.BoxedConvolution.unitsMulEquiv`: the group isomorphism
  `(BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ` pairing the constant coefficient with the formal S-series.
* `TauCeti.freeCumulantSeriesNormalizedUnit`: packages `freeCumulantSeries φ a` for an element of
  unit mean as a unit of `BoxedConvolution.normalizedSubmonoid R`.

## Main results

* `PowerSeries.boxedConvolution_boxedConvolutionInv`,
  `PowerSeries.boxedConvolutionInv_boxedConvolution`: two-sided inverse equations for
  `boxedConvolutionInv`.
* `PowerSeries.exists_boxedConvolution_eq_X_iff`: under the zero-constant-coefficient convention,
  invertibility with respect to `X` is equivalent to `IsUnit (coeff 1 f)`.
* `PowerSeries.BoxedConvolution.isUnit_iff`,
  `PowerSeries.BoxedConvolution.isUnit_normalizedSubmonoid_iff`: characterisations of invertible
  elements under boxed convolution.
* `TauCeti.IsFreelyIndependent.sSeries_list_prod`,
  `TauCeti.IsFreelyIndependentElements.sSeries_list_prod`: multiplicativity of `sSeries` on finite
  products of free variables.

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
units: its constant coefficient is `(constantCoeff f)⁻¹` and its positive-degree part has boxed
S-series `(f.boxedSSeriesUnit hf₁)⁻¹`. -/
noncomputable def boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) : R⟦X⟧ :=
  C (↑hf₀.unit⁻¹ : R) +
    (FormalCoordinate.unitsEquiv.symm (f.boxedSSeriesUnit hf₁)⁻¹)⁻¹.toPowerSeries

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
  simp [boxedConvolutionInv, ofBoxedSSeriesUnit_def, coeff_C, coeff_one, hn]

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
  (boxedSSeriesUnit_congr _ (isUnit_coeff_one_ofBoxedSSeriesUnit _) fun _ hk =>
    coeff_boxedConvolutionInv_eq_coeff_ofBoxedSSeriesUnit f hf₀ hf₁ hk).trans
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

@[simp]
theorem coeff_one_boxedConvolutionInv (f : R⟦X⟧) (hf₀ : IsUnit (constantCoeff f))
    (hf₁ : IsUnit (coeff 1 f)) :
    coeff 1 (f.boxedConvolutionInv hf₀ hf₁) = Ring.inverse (coeff 1 f) := by
  have h := congrArg (coeff 1) (boxedConvolution_boxedConvolutionInv f hf₀ hf₁)
  simp only [coeff_one_boxedConvolution, map_add, coeff_one, coeff_X, one_ne_zero, ↓reduceIte,
    zero_add] at h
  have hmul := congrArg (Ring.inverse (coeff 1 f) * ·) h
  rwa [← mul_assoc, Ring.inverse_mul_cancel _ hf₁, one_mul, mul_one] at hmul

/-- Under the zero-constant-coefficient convention (where `X` is the boxed-convolution identity), a
series `f` with `constantCoeff f = 0` admits a boxed-convolution inverse `g` with
`constantCoeff g = 0` and `f ⊠ g = X` if and only if `coeff 1 f` is a unit. -/
theorem exists_boxedConvolution_eq_X_iff {f : R⟦X⟧} (hf₀ : constantCoeff f = 0) :
    (∃ g : R⟦X⟧, constantCoeff g = 0 ∧ f.boxedConvolution g = X) ↔ IsUnit (coeff 1 f) := by
  refine ⟨fun ⟨g, _, hfg⟩ => ?_, fun hf₁ => ?_⟩
  · refine IsUnit.of_mul_eq_one (coeff 1 g) ?_
    simpa [coeff_one_boxedConvolution] using congrArg (coeff 1) hfg
  · refine ⟨(FormalCoordinate.unitsEquiv.symm (f.boxedSSeriesUnit hf₁)⁻¹)⁻¹.toPowerSeries,
      by simp, ?_⟩
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf₀]
    rw [coeff_boxedConvolution_congr hn (f' := 1 + f) (fun k hk => by simp [coeff_one, hk])
      (g' := ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹)
      (fun k hk => by simp [ofBoxedSSeriesUnit_def, coeff_one, hk])]
    have hf1 : IsUnit (coeff 1 (1 + f)) := by simpa [coeff_one] using hf₁
    have hconv : (1 + f) = ofBoxedSSeriesUnit ((1 + f).boxedSSeriesUnit hf1) :=
      (ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one (by simp [hf₀]) hf1).symm
    have heq : (1 + f).boxedSSeriesUnit hf1 = f.boxedSSeriesUnit hf₁ :=
      boxedSSeriesUnit_congr hf1 hf₁ fun k hk => by simp [coeff_one, hk]
    have hinv : (1 + f).boxedConvolution (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) =
        1 + X := by
      calc
        (1 + f).boxedConvolution (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) =
            (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)).boxedConvolution
              (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹) := by
          rw [← heq, ← hconv]
        _ = 1 + X := by rw [← ofBoxedSSeriesUnit_mul, mul_inv_cancel, ofBoxedSSeriesUnit_one]
    rw [hinv]
    simp [coeff_one, hn]

end Inverse

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
theorem inv_unitOfIsUnit (x : BoxedConvolution R) (hx₀ : IsUnit (constantCoeff x.ofBoxed))
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
    (hf₁ : IsUnit (coeff 1 f)) : (normalizedSubmonoid R)ˣ where
  val := ⟨toBoxed f, mem_normalizedSubmonoid_iff.mpr hf₀⟩
  inv := ⟨toBoxed (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹),
    mem_normalizedSubmonoid_iff.mpr (constantCoeff_ofBoxedSSeriesUnit _)⟩
  val_inv := Subtype.ext <| BoxedConvolution.ext <| by
    have hf : f = ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁) :=
      (ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one hf₀ hf₁).symm
    rw [Submonoid.coe_mul, ofBoxed_mul, ofBoxed_toBoxed, ofBoxed_toBoxed, Submonoid.coe_one,
      ofBoxed_one]
    exact (congrArg
        (fun g => g.boxedConvolution (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹)) hf).trans
      ((ofBoxedSSeriesUnit_mul _ _).symm.trans (by rw [mul_inv_cancel, ofBoxedSSeriesUnit_one]))
  inv_val := Subtype.ext <| BoxedConvolution.ext <| by
    have hf : f = ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁) :=
      (ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one hf₀ hf₁).symm
    rw [Submonoid.coe_mul, ofBoxed_mul, ofBoxed_toBoxed, ofBoxed_toBoxed, Submonoid.coe_one,
      ofBoxed_one]
    exact (congrArg
        (fun g => (ofBoxedSSeriesUnit (f.boxedSSeriesUnit hf₁)⁻¹).boxedConvolution g) hf).trans
      ((ofBoxedSSeriesUnit_mul _ _).symm.trans (by rw [inv_mul_cancel, ofBoxedSSeriesUnit_one]))

@[simp]
theorem coe_val_normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1) (hf₁ : IsUnit (coeff 1 f)) :
    ((normalizedUnit f hf₀ hf₁ : normalizedSubmonoid R) : BoxedConvolution R) = toBoxed f := (rfl)

@[simp]
theorem coe_inv_normalizedUnit (f : R⟦X⟧) (hf₀ : constantCoeff f = 1) (hf₁ : IsUnit (coeff 1 f)) :
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
sends `v : R⟦X⟧ˣ` to `1 + (X v)⁻¹`. -/
noncomputable def sSeriesMulEquiv : (normalizedSubmonoid R)ˣ ≃* R⟦X⟧ˣ where
  toFun u := (u : normalizedSubmonoid R).1.ofBoxed.boxedSSeriesUnit
    (isUnit_normalizedSubmonoid_iff.mp u.isUnit)
  invFun v := normalizedUnit (ofBoxedSSeriesUnit v) (constantCoeff_ofBoxedSSeriesUnit v)
    (isUnit_coeff_one_ofBoxedSSeriesUnit v)
  left_inv u := Units.ext <| Subtype.ext <| BoxedConvolution.ext <| by
    simpa using ofBoxedSSeriesUnit_boxedSSeriesUnit_of_constantCoeff_eq_one
      (mem_normalizedSubmonoid_iff.mp (u : normalizedSubmonoid R).2)
      (isUnit_normalizedSubmonoid_iff.mp u.isUnit)
  right_inv v := boxedSSeriesUnit_ofBoxedSSeriesUnit v
  map_mul' _ _ := boxedSSeriesUnit_boxedConvolution _ _

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
to `C c + (X v)⁻¹`. -/
noncomputable def unitsMulEquiv : (BoxedConvolution R)ˣ ≃* Rˣ × R⟦X⟧ˣ where
  toFun u :=
    (Units.map constantCoeffHom u,
      (u : BoxedConvolution R).ofBoxed.boxedSSeriesUnit
        (by simpa using u.isUnit.map coeffOneHom))
  invFun p :=
    let f : R⟦X⟧ := C (p.1 : R) + (FormalCoordinate.unitsEquiv.symm p.2)⁻¹.toPowerSeries
    unitOfIsUnit (toBoxed f) (by simp [f]) (by simp [f])
  left_inv u := Units.ext <| BoxedConvolution.ext <| by
    dsimp only
    rw [val_unitOfIsUnit, ofBoxed_toBoxed, boxedSSeriesUnit_def, Equiv.symm_apply_apply, inv_inv,
      toPowerSeries_toFormalCoordinate]
    simp
  right_inv p := Prod.ext (Units.ext <| by simp) <| by
    dsimp only
    exact (boxedSSeriesUnit_congr _ (isUnit_coeff_one_ofBoxedSSeriesUnit p.2) fun k hk => by
      simp [ofBoxedSSeriesUnit_def, coeff_C, coeff_one, hk]).trans
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
      toBoxed (C (p.1 : R) + (FormalCoordinate.unitsEquiv.symm p.2)⁻¹.toPowerSeries) := (rfl)

end BoxedConvolution

end PowerSeries

namespace TauCeti

open PowerSeries PowerSeries.BoxedConvolution

section Monoid

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

/-- Applying `BoxedConvolution.sSeriesMulEquiv` to `freeCumulantSeriesNormalizedUnit φ a ha` yields
`sSeries φ a ha`. -/
theorem val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit {φ : A → R} (hφ : φ 1 = 1) (a : A)
    (ha : IsUnit (φ a)) :
    (sSeriesMulEquiv (freeCumulantSeriesNormalizedUnit φ a ha) : R⟦X⟧) = sSeries φ a ha :=
  (congrArg Units.val (sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit φ a ha)).trans
    ((val_boxedSSeriesUnit _ _).trans (sSeries_eq_boxedSSeries_freeCumulantSeries hφ a ha).symm)

end Monoid

section FreeProduct

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- Over any semiring `A`, a duplicate-free product of variables of unit means from a freely
independent family has unit mean. -/
theorem IsFreelyIndependent.isUnit_apply_list_prod {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {l : List (ι × A)}
    (hnodup : (l.map Prod.fst).Nodup) (hl : ∀ p ∈ l, p.2 ∈ B p.1)
    (hu : ∀ p ∈ l, IsUnit (φ p.2)) :
    IsUnit (φ (l.map Prod.snd).prod) := by
  rw [h.apply_list_prod hφ hnodup hl]
  exact List.prod_isUnit (l.forall_mem_map.mpr hu)

/-- Over any semiring `A`, a duplicate-free product of free elements of unit means has unit
mean. -/
theorem IsFreelyIndependentElements.isUnit_apply_list_prod {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {l : List ι} (hnodup : l.Nodup)
    (hu : ∀ i ∈ l, IsUnit (φ (c i))) :
    IsUnit (φ (l.map c).prod) := by
  rw [h.apply_list_prod hφ hnodup]
  exact List.prod_isUnit (l.forall_mem_map.mpr hu)

/-- *Multiplicativity of the formal S-series on finite products of free variables*: deduced by
applying the group isomorphism `BoxedConvolution.sSeriesMulEquiv` to
`IsFreelyIndependent.toBoxed_freeCumulantSeries_list_prod`. -/
theorem IsFreelyIndependent.sSeries_list_prod {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {l : List (ι × A)}
    (hnodup : (l.map Prod.fst).Nodup) (hl : ∀ p ∈ l, p.2 ∈ B p.1)
    (hu : ∀ p ∈ l, IsUnit (φ p.2)) :
    sSeries φ (l.map Prod.snd).prod (h.isUnit_apply_list_prod hφ hnodup hl hu) =
      (l.attach.map fun p => sSeries φ p.1.2 (hu p.1 p.2)).prod := by
  have hU : freeCumulantSeriesNormalizedUnit φ (l.map Prod.snd).prod
      (h.isUnit_apply_list_prod hφ hnodup hl hu) =
      (l.attach.map fun p => freeCumulantSeriesNormalizedUnit φ p.1.2 (hu p.1 p.2)).prod := by
    apply Units.ext
    apply Subtype.ext
    have hmap := map_list_prod ((normalizedSubmonoid R).subtype.comp (Units.coeHom _))
      (l.attach.map fun p => freeCumulantSeriesNormalizedUnit φ p.1.2 (hu p.1 p.2))
    have hrhs : (l.attach.map fun p =>
        ((normalizedSubmonoid R).subtype.comp (Units.coeHom _))
          (freeCumulantSeriesNormalizedUnit φ p.1.2 (hu p.1 p.2))) =
        l.map fun p => toBoxed (freeCumulantSeries φ p.2) := by
      simp [List.map_attach_eq_pmap]
    rw [List.map_map, Function.comp_def, hrhs] at hmap
    simpa using (h.toBoxed_freeCumulantSeries_list_prod hφ hnodup hl).trans hmap.symm
  have hS := congrArg (fun u => (sSeriesMulEquiv u : R⟦X⟧)) hU
  have hval := map_list_prod ((Units.coeHom R⟦X⟧).comp sSeriesMulEquiv.toMonoidHom)
    (l.attach.map fun p => freeCumulantSeriesNormalizedUnit φ p.1.2 (hu p.1 p.2))
  rw [val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit hφ] at hS
  refine hS.trans (hval.trans ?_)
  simp only [List.map_map, Function.comp_def, MonoidHom.coe_comp, Units.coeHom_apply,
    MulEquiv.coe_toMonoidHom]
  congr 1
  exact List.map_congr_left fun p _ =>
    val_sSeriesMulEquiv_freeCumulantSeriesNormalizedUnit hφ p.1.2 (hu p.1 p.2)

/-- *Multiplicativity of the formal S-series on finite products of free elements*: for a
duplicate-free list `l` of indices of a freely independent family `c` with unit means under a
normalised `φ`, the S-series of `(l.map c).prod` is the product of the S-series of the factors. -/
theorem IsFreelyIndependentElements.sSeries_list_prod {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {l : List ι} (hnodup : l.Nodup)
    (hu : ∀ i ∈ l, IsUnit (φ (c i))) :
    sSeries φ (l.map c).prod (h.isUnit_apply_list_prod hφ hnodup hu) =
      (l.attach.map fun i => sSeries φ (c i.1) (hu i.1 i.2)).prod := by
  let l' : List (ι × A) := l.map fun i => (i, c i)
  have hprod : (l'.map Prod.snd).prod = (l.map c).prod := by
    simp [l', List.map_map, Function.comp_def]
  have hfst : l'.map Prod.fst = l := by
    simp [l', List.map_map, Function.comp_def]
  have hu' : ∀ p ∈ l', IsUnit (φ p.2) := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact hu i hi
  have hl' : ∀ p ∈ l', p.2 ∈ Algebra.adjoin R {c p.1} := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact Algebra.self_mem_adjoin_singleton R (c i)
  have hunit' := (isFreelyIndependentElements_iff.mp h).isUnit_apply_list_prod hφ
    (hfst.symm ▸ hnodup) hl' hu'
  refine (sSeries_congr (l.map c).prod (h.isUnit_apply_list_prod hφ hnodup hu) hunit'
    (congrArg (momentSeries φ) hprod.symm)).trans ?_
  rw [(isFreelyIndependentElements_iff.mp h).sSeries_list_prod hφ (hfst.symm ▸ hnodup) hl' hu']
  simp [l', List.attach_map, List.map_map, Function.comp_def]

end FreeProduct

end TauCeti
