/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The Radon--Nikodym unitary between the `L²` spaces of equivalent measures

For two σ-finite measures `μ ν` on a measurable space with `μ ≪ ν` and `ν ≪ μ`, the map

```text
f ↦ (x ↦ √((dμ/dν) x) * f x)
```

is a **unitary** `L²(μ) ≃ₗᵢ[ℂ] L²(ν)`, and it commutes with multiplication by any bounded
measurable function.  Together these say that the `L²` space of a measure, *together with its
multiplication operators*, depends only on the **measure class** of `μ` -- the equivalence class
of `μ` under mutual absolute continuity -- and not on `μ` itself.  That is exactly the
invariance that makes measure class, rather than measure, the datum in spectral multiplicity
theory.

The mathematical crux is the change of variables

```text
∫⁻ x, ‖√((dμ/dν) x) * f x‖ₑ² ∂ν = ∫⁻ x, (dμ/dν) x * ‖f x‖ₑ² ∂ν = ∫⁻ x, ‖f x‖ₑ² ∂μ,
```

whose second step is `MeasureTheory.lintegral_rnDeriv_mul` and whose first step is the pointwise
identity `‖√((dμ/dν) x)‖ₑ² = (dμ/dν) x`, valid wherever the derivative is finite -- which is
`ν`-almost everywhere by `Measure.rnDeriv_lt_top`.  Only `μ ≪ ν` is needed for that; the reverse
absolute continuity `ν ≪ μ` enters twice, to move `ν`-a.e. statements to `μ`-a.e. ones and to
make the map invertible, its inverse being the same construction with `dν/dμ`.

## Main results

* `TauCeti.rnDerivSqrt`: the multiplier `x ↦ √((dμ/dν) x)`, as a real-valued function.
* `TauCeti.lintegral_enorm_rnDerivSqrt_mul_sq`: **the change of variables**, in `ℝ≥0∞`-integral
  form.
* `TauCeti.eLpNorm_rnDerivSqrt_mul`: the same, as an equality of `L²` seminorms.
* `TauCeti.rnDerivL2`: the linear isometry `L²(μ) →ₗᵢ[ℂ] L²(ν)`.
* `TauCeti.rnDerivL2_rnDerivL2`: the two isometries, for `dμ/dν` and for `dν/dμ`, are mutually
  inverse.
* `TauCeti.rnDerivL2Equiv`: **the Radon--Nikodym unitary** `L²(μ) ≃ₗᵢ[ℂ] L²(ν)`.
* `TauCeti.mulLp`: multiplication by a bounded measurable function, as a bounded operator on
  `L²`.
* `TauCeti.rnDerivL2Equiv_mulLp`: **the intertwining law** -- the unitary carries multiplication
  by `g` on `L²(μ)` to multiplication by the same `g` on `L²(ν)`.
* `TauCeti.mulLp_eq_conj_rnDerivL2`: the same, as an equality of bounded operators -- the two
  multiplication operators are unitarily equivalent.

## Design notes

**No separability, and no second countability.**  Nothing here constrains the measurable space,
so the result applies verbatim to the uniform-multiplicity decomposition of
the uniform-multiplicity decomposition, were it indexed by cardinals rather than by
`ℕ`.  The hypotheses are `SigmaFinite` on both measures, which is what
`Measure.HaveLebesgueDecomposition` and `Measure.rnDeriv_lt_top` need; finite measures -- in
particular the scalar spectral measures of the Borel calculus -- satisfy it by instance.

The multiplier is carried as a *real* function `rnDerivSqrt` and coerced into `ℂ` at each use.
That keeps `Real.sqrt`'s API (`Real.sq_sqrt`, `Real.sqrt_mul`) directly available, and it makes
the inverse identity `√(dμ/dν) * √(dν/dμ) = 1` a statement about real numbers.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

section Multiplier

/-- **The multiplier of the Radon--Nikodym unitary**: the pointwise square root of the
Radon--Nikodym derivative `dμ/dν`, as a real-valued function.

`Measure.rnDeriv` is `ℝ≥0∞`-valued, so this takes `.toReal` first.  That is harmless: the
derivative is finite `ν`-almost everywhere (`Measure.rnDeriv_lt_top`), and every statement below
is an almost-everywhere one. -/
noncomputable def rnDerivSqrt (μ ν : Measure α) (x : α) : ℝ :=
  Real.sqrt ((μ.rnDeriv ν x).toReal)

/-- The multiplier is nonnegative, being a square root. -/
theorem rnDerivSqrt_nonneg (μ ν : Measure α) (x : α) : 0 ≤ rnDerivSqrt μ ν x :=
  Real.sqrt_nonneg _

/-- The multiplier is measurable, being a continuous function of a measurable one. -/
theorem measurable_rnDerivSqrt (μ ν : Measure α) : Measurable (rnDerivSqrt μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal.sqrt

/-- **The pointwise identity behind the change of variables.**  Squaring the multiplier, in
`ℝ≥0∞`, returns the Radon--Nikodym derivative -- wherever that derivative is finite.

Finiteness is not decoration: `∞.toReal = 0`, so on a set where `dμ/dν = ∞` the multiplier would
vanish and the identity would fail. -/
theorem enorm_rnDerivSqrt_sq {x : α} (hx : μ.rnDeriv ν x ≠ ∞) :
    ‖((rnDerivSqrt μ ν x : ℝ) : ℂ)‖ₑ ^ 2 = μ.rnDeriv ν x := by
  have hnn : (0 : ℝ) ≤ rnDerivSqrt μ ν x := rnDerivSqrt_nonneg μ ν x
  have hsq : rnDerivSqrt μ ν x ^ 2 = (μ.rnDeriv ν x).toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hnn, ← ENNReal.ofReal_pow hnn, hsq,
    ENNReal.ofReal_toReal hx]

/-- **The two multipliers are reciprocal.**  Almost everywhere for `ν`, the multiplier for
`dμ/dν` times the multiplier for `dν/dμ` is `1`.

This is the chain rule `Measure.rnDeriv_mul_rnDeriv` together with `Measure.rnDeriv_self`, and it
is what makes the Radon--Nikodym isometry invertible.  Only `ν ≪ μ` is needed. -/
theorem rnDerivSqrt_mul_rnDerivSqrt [SigmaFinite μ] [SigmaFinite ν] (hνμ : ν ≪ μ) :
    ∀ᵐ x ∂ν, rnDerivSqrt μ ν x * rnDerivSqrt ν μ x = 1 := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (μ := ν) (ν := μ) (κ := ν) hνμ,
    Measure.rnDeriv_self ν] with x h1 h2
  have hprod : μ.rnDeriv ν x * ν.rnDeriv μ x = 1 := by
    rw [Pi.mul_apply] at h1
    rw [mul_comm, h1, h2]
  rw [rnDerivSqrt, rnDerivSqrt, ← Real.sqrt_mul ENNReal.toReal_nonneg, ← ENNReal.toReal_mul,
    hprod, ENNReal.toReal_one, Real.sqrt_one]

end Multiplier

section ChangeOfVariables

/-- **The change of variables, in `ℝ≥0∞`-integral form.**

```text
∫⁻ x, ‖√((dμ/dν) x) · f x‖ₑ² ∂ν = ∫⁻ x, ‖f x‖ₑ² ∂μ
```

This is the mathematical content of the whole file: the multiplier converts the `ν`-integral of a
squared norm into the `μ`-integral of the same squared norm.  Only `μ ≪ ν` is used. -/
theorem lintegral_enorm_rnDerivSqrt_mul_sq [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    {f : α → ℂ} (hf : AEMeasurable f ν) :
    ∫⁻ x, ‖((rnDerivSqrt μ ν x : ℝ) : ℂ) * f x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [← lintegral_rnDeriv_mul hμν (f := fun x => ‖f x‖ₑ ^ 2) (hf.enorm.pow_const 2)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  rw [enorm_mul, mul_pow, enorm_rnDerivSqrt_sq hx.ne]

/-- **The change of variables, as an equality of `L²` seminorms.**  Multiplying by the multiplier
carries the `L²(μ)` seminorm of `f` to the `L²(ν)` seminorm of the product. -/
theorem eLpNorm_rnDerivSqrt_mul [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) {f : α → ℂ}
    (hf : AEMeasurable f ν) :
    eLpNorm (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * f x) 2 ν = eLpNorm f 2 μ := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hfμ : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.mono_ac hμν
  have hfprod : AEStronglyMeasurable
      (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * f x) ν :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_rnDerivSqrt μ ν)).aestronglyMeasurable.mul hf.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfprod,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfμ, h2]
  simp only [ENNReal.rpow_two]
  rw [lintegral_enorm_rnDerivSqrt_mul_sq hμν hf]

/-- **The multiplier carries `L²(μ)` into `L²(ν)`.**

Measurability transfers along `ν ≪ μ`; finiteness of the seminorm is `eLpNorm_rnDerivSqrt_mul`. -/
theorem memLp_two_rnDerivSqrt_mul [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * f x) 2 ν := by
  have hfν : AEStronglyMeasurable f ν := hf.aestronglyMeasurable.mono_ac hνμ
  change eLpNorm (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * f x) 2 ν < ∞
  rw [eLpNorm_rnDerivSqrt_mul hμν hfν.aemeasurable]
  exact hf

end ChangeOfVariables

section Isometry

/-- **Multiplication by `√(dμ/dν)`, as a `ℂ`-linear map** `L²(μ) →ₗ[ℂ] L²(ν)`.

Additivity and homogeneity are the corresponding pointwise identities for representatives; moving
those from `μ`-a.e. to `ν`-a.e. is where `ν ≪ μ` is used. -/
noncomputable def rnDerivLpHom [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν where
  toFun F := MemLp.toLp (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * F x)
    (memLp_two_rnDerivSqrt_mul hμν hνμ (Lp.memLp F))
  map_add' F G := by
    rw [← MemLp.toLp_add (memLp_two_rnDerivSqrt_mul hμν hνμ (Lp.memLp F))
      (memLp_two_rnDerivSqrt_mul hμν hνμ (Lp.memLp G))]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [hνμ.ae_le (Lp.coeFn_add F G)] with x hx
    simp only [Pi.add_apply, hx]
    ring
  map_smul' c F := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c
      (memLp_two_rnDerivSqrt_mul hμν hνμ (Lp.memLp F))]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [hνμ.ae_le (Lp.coeFn_smul c F)] with x hx
    simp only [Pi.smul_apply, hx, smul_eq_mul]
    ring

/-- Multiplication by `√(dμ/dν)`, unfolded. -/
theorem rnDerivLpHom_apply [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) :
    rnDerivLpHom hμν hνμ F = MemLp.toLp (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * F x)
      (memLp_two_rnDerivSqrt_mul hμν hνμ (Lp.memLp F)) := (rfl)

/-- **The Radon--Nikodym isometry** `L²(μ) →ₗᵢ[ℂ] L²(ν)`, `f ↦ √(dμ/dν) · f`.

That it preserves norms is `eLpNorm_rnDerivSqrt_mul`.  It is in fact surjective
(`rnDerivL2_rnDerivL2`), hence unitary; see `rnDerivL2Equiv`. -/
noncomputable def rnDerivL2 [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 ν where
  toLinearMap := rnDerivLpHom hμν hνμ
  norm_map' F := by
    rw [rnDerivLpHom_apply, Lp.norm_toLp, Lp.norm_def,
      eLpNorm_rnDerivSqrt_mul hμν ((Lp.aestronglyMeasurable F).mono_ac hνμ).aemeasurable]

/-- The Radon--Nikodym isometry, unfolded to a class of a representative. -/
theorem rnDerivL2_apply [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) :
    rnDerivL2 hμν hνμ F = MemLp.toLp (fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * F x)
      (memLp_two_rnDerivSqrt_mul hμν hνμ (Lp.memLp F)) := (rfl)

/-- **The Radon--Nikodym isometry really is pointwise multiplication by `√(dμ/dν)`.** -/
theorem coeFn_rnDerivL2 [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) :
    (rnDerivL2 hμν hνμ F : α → ℂ)
      =ᵐ[ν] fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * F x := by
  rw [rnDerivL2_apply]
  exact MemLp.coeFn_toLp _

/-- **The two Radon--Nikodym isometries are mutually inverse.**  Composing the one built from
`dμ/dν` with the one built from `dν/dμ` is the identity of `L²(ν)`, because the two multipliers
are reciprocal (`rnDerivSqrt_mul_rnDerivSqrt`).

In particular `rnDerivL2` is surjective. -/
theorem rnDerivL2_rnDerivL2 [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (G : Lp ℂ 2 ν) : rnDerivL2 hμν hνμ (rnDerivL2 hνμ hμν G) = G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_rnDerivL2 hμν hνμ (rnDerivL2 hνμ hμν G),
    hνμ.ae_le (coeFn_rnDerivL2 hνμ hμν G), rnDerivSqrt_mul_rnDerivSqrt hνμ] with x h1 h2 h3
  rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul, h3, Complex.ofReal_one, one_mul]

/-- **The Radon--Nikodym unitary** `L²(μ) ≃ₗᵢ[ℂ] L²(ν)`, for mutually absolutely continuous
σ-finite measures `μ` and `ν`, given by `f ↦ (x ↦ √((dμ/dν) x) * f x)`.

This is the statement that the Hilbert space `L²(μ)` depends only on the **measure class** of
`μ`.  Surjectivity is `rnDerivL2_rnDerivL2`: the inverse is the same construction run with
`dν/dμ`. -/
noncomputable def rnDerivL2Equiv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν :=
  LinearIsometryEquiv.ofSurjective (rnDerivL2 hμν hνμ)
    fun G => ⟨rnDerivL2 hνμ hμν G, rnDerivL2_rnDerivL2 hμν hνμ G⟩

/-- The Radon--Nikodym unitary is the Radon--Nikodym isometry. -/
@[simp] theorem rnDerivL2Equiv_apply [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) : rnDerivL2Equiv hμν hνμ F = rnDerivL2 hμν hνμ F := (rfl)

/-- **The Radon--Nikodym unitary really is pointwise multiplication by `√(dμ/dν)`.** -/
theorem coeFn_rnDerivL2Equiv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) :
    (rnDerivL2Equiv hμν hνμ F : α → ℂ)
      =ᵐ[ν] fun x => ((rnDerivSqrt μ ν x : ℝ) : ℂ) * F x := by
  rw [rnDerivL2Equiv_apply]
  exact coeFn_rnDerivL2 hμν hνμ F

/-- **The Radon--Nikodym isometry is `star`-equivariant.**

This is the step of the multiplicity-model assembly where equivariance is not formal: the
multiplier is `√(dμ/dν)`, and what makes conjugation pass through it is that the density is a
**real** quantity, so `Complex.conj_ofReal` applies.  A complex reweighting would rotate the
`star`-fixed classes off themselves. -/
theorem star_rnDerivL2 [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) :
    star (rnDerivL2 hμν hνμ F) = rnDerivL2 hμν hνμ (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (rnDerivL2 hμν hνμ F), coeFn_rnDerivL2 hμν hνμ F,
    coeFn_rnDerivL2 hμν hνμ (star F), hνμ.ae_le (Lp.coeFn_star F)] with x h1 h2 h3 h4
  calc ((star (rnDerivL2 hμν hνμ F) : Lp ℂ 2 ν) : α → ℂ) x
      = star (((rnDerivSqrt μ ν x : ℝ) : ℂ) * (F : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = (starRingEnd ℂ) ((rnDerivSqrt μ ν x : ℝ) : ℂ) * (starRingEnd ℂ) ((F : α → ℂ) x) := by
        rw [RCLike.star_def, map_mul]
    _ = ((rnDerivSqrt μ ν x : ℝ) : ℂ) * ((star F : Lp ℂ 2 μ) : α → ℂ) x := by
        rw [Complex.conj_ofReal, h4, Pi.star_apply, RCLike.star_def]
    _ = ((rnDerivL2 hμν hνμ (star F) : Lp ℂ 2 ν) : α → ℂ) x := h3.symm

/-- **The Radon--Nikodym unitary is `star`-equivariant.** -/
theorem star_rnDerivL2Equiv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Lp ℂ 2 μ) :
    star (rnDerivL2Equiv hμν hνμ F) = rnDerivL2Equiv hμν hνμ (star F) := by
  rw [rnDerivL2Equiv_apply, rnDerivL2Equiv_apply]
  exact star_rnDerivL2 hμν hνμ F

/-- **The inverse of the Radon--Nikodym unitary is the Radon--Nikodym unitary of the reversed
pair**, built from `dν/dμ`. -/
theorem rnDerivL2Equiv_symm [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (rnDerivL2Equiv hμν hνμ).symm = rnDerivL2Equiv hνμ hμν := by
  refine LinearIsometryEquiv.ext fun G => (rnDerivL2Equiv hμν hνμ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, rnDerivL2Equiv_apply, rnDerivL2Equiv_apply]
  exact (rnDerivL2_rnDerivL2 hμν hνμ G).symm

end Isometry

section Multiplication

/-- A uniformly bounded measurable function multiplies `L²` into itself. -/
theorem memLp_two_mul_complex (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) : MemLp (fun x => g x * F x) 2 ρ := by
  refine MemLp.mono' ((Lp.memLp F).norm.const_mul C)
    (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)) ?_
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hgC x) (norm_nonneg _)

/-- **The seminorm bound for multiplication by a uniformly bounded function.**

Stated with `|C|` rather than `C`: a bound hypothesis `∀ x, ‖g x‖ ≤ C` does not force `0 ≤ C`
when the space is empty, and `ENNReal.ofReal` would silently truncate a negative `C`. -/
theorem eLpNorm_two_mul_le (ρ : Measure α) {g : α → ℂ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (f : α → ℂ)
    (hf : AEStronglyMeasurable f ρ) :
    eLpNorm (fun x => g x * f x) 2 ρ ≤ ENNReal.ofReal |C| * eLpNorm f 2 ρ := by
  have hle : eLpNorm (fun x => g x * f x) 2 ρ ≤ eLpNorm (((|C| : ℝ) : ℂ) • f) 2 ρ := by
    refine eLpNorm_mono_ae (hg.aestronglyMeasurable.mul hf)
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (norm_nonneg _)
  rw [eLpNorm_const_smul] at hle
  refine hle.trans_eq ?_
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_abs]

/-- **The bound that makes multiplication a bounded operator** on `L²`. -/
theorem norm_toLp_mul_le (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    ‖MemLp.toLp (fun x => g x * F x) (memLp_two_mul_complex ρ hg hgC F)‖ ≤ |C| * ‖F‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_ofReal (abs_nonneg C), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ (eLpNorm_two_mul_le ρ hg hgC _ (Lp.aestronglyMeasurable F))
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)

/-- **Multiplication by a bounded measurable function**, as a bounded operator on `L²`.

This is the "multiplication operator" of the multiplication models of spectral multiplicity
theory, for an arbitrary measure on an arbitrary measurable space. -/
noncomputable def mulLp (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ :=
  LinearMap.mkContinuous
    { toFun := fun F => MemLp.toLp (fun x => g x * F x) (memLp_two_mul_complex ρ hg hgC F)
      map_add' := fun F G => by
        rw [← MemLp.toLp_add (memLp_two_mul_complex ρ hg hgC F) (memLp_two_mul_complex ρ hg hgC G)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        simp only [Pi.add_apply, hx]
        ring
      map_smul' := fun c F => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_two_mul_complex ρ hg hgC F)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simp only [Pi.smul_apply, hx, smul_eq_mul]
        ring }
    |C| (norm_toLp_mul_le ρ hg hgC)

/-- The multiplication operator, unfolded. -/
theorem mulLp_apply (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    mulLp ρ hg hgC F = MemLp.toLp (fun x => g x * F x) (memLp_two_mul_complex ρ hg hgC F) := (rfl)

/-- The multiplication operator really is pointwise multiplication. -/
theorem coeFn_mulLp (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    (mulLp ρ hg hgC F : α → ℂ) =ᵐ[ρ] fun x => g x * F x := by
  rw [mulLp_apply]
  exact MemLp.coeFn_toLp _

/-- **The intertwining law for the Radon--Nikodym isometry.**  For a bounded measurable `g`,

```text
rnDerivL2 (g · F) = g · rnDerivL2 F.
```

The multiplier `√(dμ/dν)` is a pointwise scalar, so it commutes with multiplication by `g`; the
only work is moving the representatives between `μ`-a.e. and `ν`-a.e., which `ν ≪ μ` allows. -/
theorem rnDerivL2_mulLp [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) {g : α → ℂ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 μ) :
    rnDerivL2 hμν hνμ (mulLp μ hg hgC F) = mulLp ν hg hgC (rnDerivL2 hμν hνμ F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_rnDerivL2 hμν hνμ (mulLp μ hg hgC F), hνμ.ae_le (coeFn_mulLp μ hg hgC F),
    coeFn_mulLp ν hg hgC (rnDerivL2 hμν hνμ F), coeFn_rnDerivL2 hμν hνμ F] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

/-- **The intertwining law for the Radon--Nikodym unitary.**  Under the unitary
`L²(μ) ≃ₗᵢ[ℂ] L²(ν)`, multiplication by a bounded measurable `g` on `L²(μ)` corresponds to
multiplication by the *same* `g` on `L²(ν)`.

Together with `rnDerivL2Equiv` this is the statement that a multiplication model is an invariant
of the measure *class*: two multiplication operators built from equivalent measures and the same
symbol are unitarily equivalent. -/
theorem rnDerivL2Equiv_mulLp [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 μ) :
    rnDerivL2Equiv hμν hνμ (mulLp μ hg hgC F) = mulLp ν hg hgC (rnDerivL2Equiv hμν hνμ F) := by
  rw [rnDerivL2Equiv_apply, rnDerivL2Equiv_apply]
  exact rnDerivL2_mulLp hμν hνμ hg hgC F

/-- **The intertwining law, as an equality of bounded operators.**

```text
Φ ∘ M_g = M_g ∘ Φ,    Φ = rnDerivL2 hμν hνμ.
```
-/
theorem comp_mulLp_rnDerivL2 [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    (rnDerivL2 hμν hνμ).toContinuousLinearMap.comp (mulLp μ hg hgC)
      = (mulLp ν hg hgC).comp (rnDerivL2 hμν hνμ).toContinuousLinearMap := by
  refine ContinuousLinearMap.ext fun F => ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  exact rnDerivL2_mulLp hμν hνμ hg hgC F

/-- **The two multiplication operators are unitarily equivalent.**  Conjugating multiplication by
`g` on `L²(μ)` by the Radon--Nikodym unitary -- whose inverse is the isometry of the reversed
pair -- returns multiplication by the same `g` on `L²(ν)`.

This is the form the multiplicity theory consumes: two multiplication models built from
*equivalent* measures and the same symbol define unitarily equivalent operators, so the invariant
carried by a model is the measure class, not the measure. -/
theorem mulLp_eq_conj_rnDerivL2 [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    mulLp ν hg hgC = (rnDerivL2 hμν hνμ).toContinuousLinearMap.comp
      ((mulLp μ hg hgC).comp (rnDerivL2 hνμ hμν).toContinuousLinearMap) := by
  refine ContinuousLinearMap.ext fun G => ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [rnDerivL2_mulLp hμν hνμ hg hgC, rnDerivL2_rnDerivL2 hμν hνμ]

end Multiplication

end TauCeti
