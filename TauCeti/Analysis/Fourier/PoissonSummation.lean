/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import TauCeti.Analysis.Distribution.SchwartzSpace.ZLattice
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Poisson summation over the lattice spanned by an orthonormal basis

Let `o` be an orthonormal basis of a finite-dimensional real inner product space `E`, indexed by
a finite type `ι`, and let `L = span ℤ (range o)` be the lattice it spans; for
`E = EuclideanSpace ℝ ι` and the standard basis this is `ℤ^ι`. For a Schwartz function
`f : 𝓢(E, ℂ)` and `v : E`, **Poisson's summation formula** reads

`∑' ℓ : L, f (v + ℓ) = ∑' m : L, 𝓕 f m * exp (2πi ⟪v, m⟫)`

(`SchwartzMap.tsum_eq_tsum_fourier_span_orthonormalBasis`), with Mathlib's Fourier transform
`𝓕 f w = ∫ x, exp (-2πi ⟪x, w⟫) f x`. The lattice `L` is its own dual
(`ZLattice.dual_span_orthonormalBasis`) and has covolume one, so this is the formula
`∑' ℓ : L, f (v + ℓ) = (covolume L)⁻¹ * ∑' m : L^∨, 𝓕 f m * exp (2πi ⟪v, m⟫)` for this `L`. Every
full lattice is the image of `L` under a linear automorphism
(`ZLattice.exists_comap_span_orthonormalBasis_eq`), and the Fourier transform changes under it by
`ContinuousLinearEquiv.fourier_comp`, so this is the base case of that formula for every full
lattice.

The proof is the classical one, in all dimensions at once rather than one coordinate at a time.
The periodization `P x = ∑' ℓ : L, f (x + ℓ)` is continuous and `L`-periodic, so it descends to a
continuous function on the torus `UnitAddTorus ι = (ℝ/ℤ)^ι` through the coordinates of `o`. Its
`n`-th Fourier coefficient is an integral over the fundamental domain `D` of `L`; unfolding the
periodization and reassembling the translates `ℓ + D` into `E`
(`MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''`) shows that this coefficient is the
value of `𝓕 f` at the lattice point with coordinates `n`. These coefficients are summable, since
`𝓕 f` is again a Schwartz function, so the multivariate Fourier series of the periodization
converges to it pointwise (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`). The
one-dimensional case of this argument is Mathlib's `Real.tsum_eq_tsum_fourier`.

## Main statements

* `SchwartzMap.tsum_eq_tsum_fourier_span_orthonormalBasis`: Poisson summation over the lattice
  spanned by an orthonormal basis.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. VII,
  Corollary 2.6.
-/

public section

open Complex Module MeasureTheory Set Submodule UnitAddTorus
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

namespace OrthonormalBasis

variable (o : OrthonormalBasis ι ℝ E)

/-! ### The torus of the lattice spanned by `o` -/

/-- The coordinates of `x` in the orthonormal basis `o`, read on the torus `(ℝ/ℤ)^ι`. -/
private noncomputable def toTorus (x : E) : UnitAddTorus ι :=
  fun i ↦ (o.repr x i : UnitAddCircle)

private theorem toTorus_def (x : E) : o.toTorus x = fun i ↦ (o.repr x i : UnitAddCircle) := rfl

/-- Two vectors have the same image on the torus exactly when they differ by a vector of the
lattice spanned by `o`. -/
private theorem toTorus_eq_toTorus_iff {x y : E} :
    o.toTorus x = o.toTorus y ↔ x - y ∈ span ℤ (range o.toBasis) := by
  rw [o.toBasis.mem_span_iff_repr_mem ℤ]
  simp [toTorus, funext_iff, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]

private theorem toTorus_add (x : E) (ℓ : span ℤ (range o.toBasis)) :
    o.toTorus (x + ℓ) = o.toTorus x :=
  o.toTorus_eq_toTorus_iff.2 (by rw [add_sub_cancel_left]; exact ℓ.2)

/-- The torus is the quotient of `E` by the lattice spanned by `o`. -/
private theorem isQuotientMap_toTorus : Topology.IsQuotientMap o.toTorus :=
  (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap.comp
    ((EuclideanSpace.equiv ι ℝ).toHomeomorph.isQuotientMap.comp o.repr.toHomeomorph.isQuotientMap)

/-- The lattice vector with coordinates `n` in the basis `o`. -/
private noncomputable def latticeEquiv : (ι → ℤ) ≃ₗ[ℤ] span ℤ (range o.toBasis) :=
  (o.toBasis.restrictScalars ℤ).equivFun.symm

private theorem repr_latticeEquiv (n : ι → ℤ) (i : ι) : o.repr (o.latticeEquiv n : E) i = n i := by
  rw [← o.coe_toBasis_repr_apply, ← o.toBasis.restrictScalars_repr_apply ℤ, latticeEquiv,
    ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp

/-- The exponential monomial of index `n` on the torus is the character `x ↦ exp (2πi ⟪x, m⟫)`
of the lattice vector `m` with coordinates `n`. -/
private theorem mFourier_toTorus (n : ι → ℤ) (x : E) :
    mFourier n (o.toTorus x) = 𝐞 ⟪x, (o.latticeEquiv n : E)⟫ := by
  have h : ⟪x, (o.latticeEquiv n : E)⟫ = ∑ i, o.repr x i * n i := by
    rw [← o.sum_inner_mul_inner]
    simp only [real_inner_comm _ x, ← o.repr_apply_apply, repr_latticeEquiv]
  rw [h, mFourier]
  simp only [ContinuousMap.coe_mk, toTorus, fourier_coe_apply, Real.fourierChar_apply,
    ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1 with i
  ring

private theorem mFourier_neg_toTorus (n : ι → ℤ) (x : E) :
    mFourier (-n) (o.toTorus x) = 𝐞 (-⟪x, (o.latticeEquiv n : E)⟫) := by
  rw [mFourier_toTorus, map_neg, Submodule.coe_neg, inner_neg_right]

/-! ### Measure theory of the coordinates -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The coordinates in the basis `o`, as a measurable equivalence onto `ι → ℝ`. -/
private noncomputable def coords : E ≃ᵐ (ι → ℝ) :=
  o.measurableEquiv.trans (MeasurableEquiv.toLp 2 (ι → ℝ)).symm

omit [FiniteDimensional ℝ E] in
private theorem coords_apply (x : E) : o.coords x = ⇑(o.repr x) := rfl

private theorem measurePreserving_coords : MeasurePreserving o.coords :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).comp
    o.measurePreserving_measurableEquiv

/-- The cube `(0, 1]^ι` in the coordinates of `o` is the fundamental domain of the lattice
spanned by `o`, up to a null set. -/
private theorem coords_preimage_ae_eq_fundamentalDomain :
    o.coords ⁻¹' {y : ι → ℝ | ∀ i, y i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =ᵐ[volume]
      ZSpan.fundamentalDomain o.toBasis := by
  have hcube : {y : ι → ℝ | ∀ i, y i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =ᵐ[volume]
      univ.pi fun _ : ι ↦ Ico (0 : ℝ) 1 := by
    have := (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : ι ↦ (volume : Measure ℝ))
      (f := 0) (g := 1)).trans (Measure.univ_pi_Ico_ae_eq_Icc (f := 0) (g := 1)).symm
    simpa [Set.pi, volume_pi] using this
  have hset : o.coords ⁻¹' (univ.pi fun _ : ι ↦ Ico (0 : ℝ) 1) =
      ZSpan.fundamentalDomain o.toBasis := by
    ext x
    simp only [mem_preimage, mem_univ_pi, coords_apply, ZSpan.mem_fundamentalDomain,
      o.coe_toBasis_repr_apply]
  rw [← hset]
  exact o.measurePreserving_coords.quasiMeasurePreserving.preimage_ae_eq hcube

end OrthonormalBasis

namespace SchwartzMap

open OrthonormalBasis

variable (f : 𝓢(E, ℂ)) (o : OrthonormalBasis ι ℝ E)

/-! ### The periodization of a Schwartz function -/

variable [FiniteDimensional ℝ E]

/-- The periodization `x ↦ ∑' ℓ, f (x + ℓ)` of `f` over the lattice spanned by `o`, on `E`. -/
private noncomputable def periodizationAux : C(E, ℂ) :=
  ⟨fun x ↦ ∑' ℓ : span ℤ (range o.toBasis), f (x + ℓ), ZLattice.continuous_tsum_poisson_left _ f⟩

private theorem factorsThrough_periodizationAux :
    Function.FactorsThrough (periodizationAux f o) o.toTorus := fun x y h ↦ by
  obtain ⟨ℓ₀, rfl⟩ : ∃ ℓ₀ : span ℤ (range o.toBasis), y + ℓ₀ = x :=
    ⟨⟨x - y, o.toTorus_eq_toTorus_iff.1 h⟩, add_sub_cancel _ _⟩
  -- Translating by the lattice vector `ℓ₀` permutes the terms of the periodization.
  simp only [periodizationAux, ContinuousMap.coe_mk, add_assoc]
  exact (Equiv.addLeft ℓ₀).tsum_eq fun ℓ ↦ f (y + ℓ)

/-- The periodization of `f` over the lattice spanned by `o`, on the torus. -/
private noncomputable def periodization : C(UnitAddTorus ι, ℂ) :=
  o.isQuotientMap_toTorus.lift (f := ⟨o.toTorus, o.isQuotientMap_toTorus.continuous⟩)
    (periodizationAux f o) (factorsThrough_periodizationAux f o)

private theorem periodization_toTorus (x : E) :
    periodization f o (o.toTorus x) = ∑' ℓ : span ℤ (range o.toBasis), f (x + ℓ) :=
  DFunLike.congr_fun (o.isQuotientMap_toTorus.lift_comp
    (f := ⟨o.toTorus, o.isQuotientMap_toTorus.continuous⟩) (periodizationAux f o)
    (factorsThrough_periodizationAux f o)) x

/-! ### The Fourier coefficients of the periodization -/

variable [MeasurableSpace E] [BorelSpace E]

/-- The `n`-th Fourier coefficient of the periodization, as an integral over the fundamental
domain of the lattice spanned by `o`. -/
private theorem mFourierCoeff_periodization_eq_setIntegral (n : ι → ℤ) :
    mFourierCoeff (periodization f o) n =
      ∫ x in ZSpan.fundamentalDomain o.toBasis,
        mFourier (-n) (o.toTorus x) * ∑' ℓ : span ℤ (range o.toBasis), f (x + ℓ) := by
  rw [mFourierCoeff_eq_integral _ n 0,
    ← o.measurePreserving_coords.setIntegral_preimage_emb o.coords.measurableEmbedding,
    setIntegral_congr_set o.coords_preimage_ae_eq_fundamentalDomain]
  refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet o.toBasis) fun x _ ↦ ?_
  -- At `o.coords x`, the coordinates read on the torus are `o.toTorus x`.
  simp only [coords_apply, ← toTorus_def, smul_eq_mul, periodization_toTorus]

/-- Over the bounded fundamental domain, the periodization may be integrated term by term
against a character. -/
private theorem setIntegral_mul_tsum (n : ι → ℤ) :
    ∫ x in ZSpan.fundamentalDomain o.toBasis,
        mFourier (-n) (o.toTorus x) * ∑' ℓ : span ℤ (range o.toBasis), f (x + ℓ) =
      ∑' ℓ : span ℤ (range o.toBasis),
        ∫ x in ZSpan.fundamentalDomain o.toBasis, mFourier (-n) (o.toTorus x) * f (x + ℓ) := by
  set D := ZSpan.fundamentalDomain o.toBasis
  have hD := ZSpan.fundamentalDomain_isBounded o.toBasis
  have hχ : Continuous fun x ↦ mFourier (-n) (o.toTorus x) :=
    (mFourier (-n)).continuous.comp o.isQuotientMap_toTorus.continuous
  obtain ⟨R, hR⟩ := hD.subset_closedBall 0
  obtain ⟨u, hu, hle⟩ := ZLattice.exists_summable_forall_norm_poisson_left_le
    (span ℤ (range o.toBasis)) f R
  have hint (ℓ : span ℤ (range o.toBasis)) :
      Integrable (fun x ↦ mFourier (-n) (o.toTorus x) * f (x + ℓ)) (volume.restrict D) :=
    ((hχ.mul (f.continuous.comp (continuous_add_const _))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)).mono_set hR
  -- The character has norm one, so the integral of the `ℓ`-th term is at most `u ℓ * vol D`.
  have hsum : Summable fun ℓ : span ℤ (range o.toBasis) ↦
      ∫ x in D, ‖mFourier (-n) (o.toTorus x) * f (x + ℓ)‖ := by
    refine Summable.of_nonneg_of_le (fun ℓ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun ℓ ↦ ?_) (hu.mul_right (volume.real D))
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := D)
      (f := fun x ↦ ‖mFourier (-n) (o.toTorus x) * f (x + ℓ)‖) (C := u ℓ) hD.measure_lt_top
      fun x hx ↦ by simpa [mFourier_neg_toTorus] using hle ℓ x (hR hx)
    rwa [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] at this
  simp_rw [← tsum_mul_left]
  exact (integral_tsum_of_summable_integral_norm hint hsum).symm

/-- The `n`-th Fourier coefficient of the periodization is the Fourier transform of `f` at the
lattice vector with coordinates `n`. -/
private theorem mFourierCoeff_periodization (n : ι → ℤ) :
    mFourierCoeff (periodization f o) n = 𝓕 (f : E → ℂ) (o.latticeEquiv n) := by
  have : VAddInvariantMeasure (span ℤ (range o.toBasis)) E volume :=
    inferInstanceAs (VAddInvariantMeasure (span ℤ (range o.toBasis)).toAddSubgroup E volume)
  rw [mFourierCoeff_periodization_eq_setIntegral, setIntegral_mul_tsum, Real.fourier_eq,
    (ZSpan.isAddFundamentalDomain o.toBasis volume).integral_eq_tsum'' _
      ((Real.fourierIntegral_convergent_iff _).2 f.integrable)]
  -- Reassemble the translates of the fundamental domain: the character is `L`-periodic.
  congr 1 with ℓ
  refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet o.toBasis) fun x _ ↦ ?_
  simp only [Submodule.vadd_def, vadd_eq_add, Circle.smul_def, smul_eq_mul, add_comm (ℓ : E) x]
  rw [← mFourier_neg_toTorus, toTorus_add]

private theorem summable_mFourierCoeff_periodization :
    Summable (mFourierCoeff (periodization f o)) := by
  have h : Summable fun ℓ : span ℤ (range o.toBasis) ↦ 𝓕 (f : E → ℂ) ℓ := by
    simpa [SchwartzMap.fourier_coe] using
      ZLattice.summable_poisson_left (span ℤ (range o.toBasis)) (𝓕 f) 0
  convert o.latticeEquiv.toEquiv.summable_iff.2 h using 1
  ext n
  exact mFourierCoeff_periodization f o n

/-! ### Poisson summation -/

/-- **Poisson's summation formula** over the lattice `L` spanned by an orthonormal basis `o` of a
finite-dimensional real inner product space: for a Schwartz function `f` and `v : E`,
`∑' ℓ : L, f (v + ℓ) = ∑' m : L, 𝓕 f m * exp (2πi ⟪v, m⟫)`. For the standard basis of
`EuclideanSpace ℝ ι` this is Poisson summation over `ℤ^ι`. -/
theorem tsum_eq_tsum_fourier_span_orthonormalBasis (v : E) :
    ∑' ℓ : span ℤ (Set.range o), f (v + ℓ) =
      ∑' m : span ℤ (Set.range o), 𝓕 (f : E → ℂ) m * cexp (2 * π * I * ⟪v, (m : E)⟫) := by
  have h := hasSum_mFourier_series_apply_of_summable (summable_mFourierCoeff_periodization f o)
    (o.toTorus v)
  rw [periodization_toTorus] at h
  rw [← o.coe_toBasis, ← h.tsum_eq, ← o.latticeEquiv.toEquiv.tsum_eq]
  congr 1 with n
  rw [LinearEquiv.coe_toEquiv, mFourierCoeff_periodization, mFourier_toTorus, smul_eq_mul,
    Real.fourierChar_apply]
  congr 2
  push_cast
  ring

end SchwartzMap
