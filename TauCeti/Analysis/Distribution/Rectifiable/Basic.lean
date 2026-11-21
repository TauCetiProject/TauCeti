/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.InnerProductSpace.Comass
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Currents of oriented sets with multiplicity

Let `V` be a finite-dimensional real inner product space with its normalized `k`-dimensional
Hausdorff measure `μHE[k]`, and let `Ω` be an open subset of `V`. A *multiplicity* `θ : V → ℝ`
and a field of *orientation frames* `τ : V → Fin k → V`, orthonormal wherever `θ` does not vanish,
define the `k`-current on `Ω`

`frameCurrent θ τ ω = ∫ θ(x) ω_x(τ(x)) dμHE[k](x)`

(`Distribution.frameCurrent`), integrating a test `k`-form over the set where `θ ≠ 0`, weighted by
`θ`, in the orientation of the frames. When the set where `θ ≠ 0` is countably `k`-rectifiable, `θ`
is integer-valued and the frames span its approximate tangent planes, these are the
integer-rectifiable currents of Federer and Fleming (`TauCeti.Analysis.Distribution.Rectifiable.
IntegerRectifiable`). Pairing with a frame is the evaluation of forms at the simple unit `k`-vector
`τ₁ ∧ ⋯ ∧ τₖ`, so this is the current `θ μHE[k] ∧ ξ` with orientation `ξ = τ₁ ∧ ⋯ ∧ τₖ`.

The current is the integral of the field of `k`-vectors `x ↦ θ(x) τ₁(x) ∧ ⋯ ∧ τₖ(x)` against
`μHE[k]`, paired with forms by `exteriorPower.formVectorPairing`, through Mathlib's
`TestFunction.integralAgainstBilinCLM`; it is defined to be zero when this field is not locally
integrable on `Ω`. It is so when `θ` is locally integrable on `Ω` and the
frames are measurable (`Distribution.frameCurrent_apply`), since a form of norm at most one takes
values of absolute value at most one on orthonormal frames.

The current only depends on the pointwise products `θ(x) ω_x(τ(x))` on `Ω`, up to null sets
(`Distribution.frameCurrent_eq_of_ae`). In particular it is additive in the multiplicity
(`Distribution.frameCurrent_add`), changes sign with it (`Distribution.frameCurrent_neg`), and a
change of orthonormal frame within the same plane multiplies the multiplicity by the determinant
`±1` of the change (`Distribution.frameCurrent_eq_det_inner_mul`): the frames enter only through
the orientations of the planes they span. Its local mass on a set `U` is at most `∫_U |θ| dμHE[k]`
(`Distribution.localMass_frameCurrent_le`), so the current has locally finite mass
(`Distribution.hasLocallyFiniteMass_frameCurrent`).

## Main declarations

* `Distribution.frameCurrent θ τ`: the current `ω ↦ ∫ θ(x) ω_x(τ(x)) dμHE[k](x)`.
* `Distribution.frameCurrent_apply`: its value on a test form, for locally integrable `θ`.
* `Distribution.frameCurrent_eq_of_ae`: data with almost everywhere equal pairings have the same
  current.
* `Distribution.frameCurrent_add`, `Distribution.frameCurrent_neg`: linearity in the multiplicity.
* `Distribution.frameCurrent_eq_det_inner_mul`: changing the frames within the same planes.
* `Distribution.localMass_frameCurrent_le`, `Distribution.hasLocallyFiniteMass_frameCurrent`: the
  mass bound.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.28 (rectifiable currents).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3 (integer multiplicity
  rectifiable currents `τ(M, θ, ξ)`).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory exteriorPower
open scoped Distributions ENNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {k : ℕ}

/-- The determinant of the overlap matrix `(⟪σ(x) i, τ(x) j⟫)` of two measurable fields of frames is
measurable. -/
theorem Measurable.det_inner [SecondCountableTopology V] {α : Type*} [MeasurableSpace α]
    {σ τ : α → Fin k → V}
    (hσ : Measurable σ) (hτ : Measurable τ) :
    Measurable fun x ↦ (Matrix.of fun j i ↦ ⟪σ x i, τ x j⟫).det := by
  have hc : Continuous fun M : Fin k → Fin k → ℝ ↦ (Matrix.of M).det :=
    Continuous.matrix_det (A := fun M : Fin k → Fin k → ℝ ↦ Matrix.of M) continuous_id
  refine hc.measurable.comp (measurable_pi_iff.2 fun j ↦ measurable_pi_iff.2 fun i ↦ ?_)
  exact Measurable.inner (f := fun x ↦ σ x i) (g := fun x ↦ τ x j)
    ((measurable_pi_apply i).comp hσ) ((measurable_pi_apply j).comp hτ)

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {n : ℕ∞} {k : ℕ}

/-- The field of `k`-vectors whose integral against `μHE[k]` is the frame current: at `x` it is
`θ(x) τ₁(x) ∧ ⋯ ∧ τₖ(x)`. -/
def frameDensity (θ : V → ℝ) (τ : V → Fin k → V) (x : V) : ⋀[ℝ]^k V :=
  θ x • ιMulti ℝ k (τ x)

/-- The **current of an oriented set with multiplicity**: the `k`-current on `Ω` sending a test
`k`-form `ω` to `∫ θ(x) ω_x(τ(x)) dμHE[k](x)`, for a multiplicity `θ` and orientation frames `τ`.
It is zero by convention when the field of `k`-vectors `x ↦ θ(x) τ₁(x) ∧ ⋯ ∧ τₖ(x)` is not locally
integrable on `Ω`; for locally integrable `θ` and measurable orthonormal frames, see
`Distribution.frameCurrent_apply`. -/
def frameCurrent (θ : V → ℝ) (τ : V → Fin k → V) : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  integralAgainstBilinCLM formVectorPairing μHE[k] (frameDensity θ τ)

omit [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem formVectorPairing_frameDensity (θ : V → ℝ) (τ : V → Fin k → V) (x : V)
    (ω : V [⋀^Fin k]→L[ℝ] ℝ) : formVectorPairing ω (frameDensity θ τ x) = θ x * ω (τ x) := by
  simp [frameDensity]

omit [MeasurableSpace V] [BorelSpace V] in
/-- At an orthonormal frame the wedge has norm one, so the density has norm at most `|θ|`. -/
theorem norm_frameDensity_le {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) : ‖frameDensity θ τ x‖ ≤ ‖θ x‖ := by
  by_cases hθ : θ x = 0
  · simp [frameDensity, hθ]
  · simp [frameDensity, norm_smul, (hx hθ).norm_ιMulti]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- At an orthonormal frame, `|θ(x) φ(τ(x))| ≤ |θ(x)| ‖φ‖`. -/
private theorem norm_mul_apply_le {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) (φ : V [⋀^Fin k]→L[ℝ] ℝ) :
    ‖θ x * φ (τ x)‖ ≤ ‖θ x‖ * ‖φ‖ := by
  by_cases hθ : θ x = 0
  · simp [hθ]
  rw [norm_mul]
  gcongr
  simpa [(hx hθ).1] using φ.le_opNorm (τ x)

/-- For a multiplicity locally integrable on `Ω` and measurable frames, orthonormal where the
multiplicity does not vanish, the field of `k`-vectors defining the frame current is locally
integrable on `Ω`. -/
theorem locallyIntegrableOn_frameDensity {θ : V → ℝ} {τ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    LocallyIntegrableOn (frameDensity θ τ) Ω μHE[k] := fun x hx ↦ by
  obtain ⟨t, ht, hint⟩ := hθ x hx
  refine ⟨t, ht, Integrable.mono hint (hint.aestronglyMeasurable.smul ?_)
    (ae_of_all _ fun y ↦ norm_frameDensity_le (hτo y))⟩
  exact (exteriorPower.ιMulti ℝ k (M := V)).toMultilinearMap.continuous_of_finiteDimensional
    |>.comp_aestronglyMeasurable hτ.aestronglyMeasurable

/-- The value of the frame current on a test form, for a multiplicity locally integrable on `Ω`
and measurable frames, orthonormal where the multiplicity does not vanish. -/
theorem frameCurrent_apply {θ : V → ℝ} {τ : V → Fin k → V} (hθ : LocallyIntegrableOn θ Ω μHE[k])
    (hτ : Measurable τ) (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x))
    (ω : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ)) :
    frameCurrent θ τ ω = ∫ x, θ x * ω x (τ x) ∂μHE[k] := by
  simp [frameCurrent, integralAgainstBilinCLM_eq_integral
    (locallyIntegrableOn_frameDensity hθ hτ hτo)]

/-- The integrand of the frame current on a test form is integrable. -/
theorem integrable_frameCurrent_integrand {θ : V → ℝ} {τ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) (ω : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ)) :
    Integrable (fun x ↦ θ x * ω x (τ x)) μHE[k] := by
  simpa using ω.integrable_bilin formVectorPairing
    (locallyIntegrableOn_frameDensity hθ hτ hτo)

/-- **The frame current depends only on the pairings on `Ω`.** If the pairings
`θ(x) ω(τ(x))` and `θ'(x) ω(τ'(x))` agree for almost every `x ∈ Ω` and every form `ω`, the two
frame currents agree. -/
theorem frameCurrent_eq_of_ae {θ θ' : V → ℝ} {τ τ' : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) (hθ' : LocallyIntegrableOn θ' Ω μHE[k])
    (hτ' : Measurable τ') (hτo' : ∀ x, θ' x ≠ 0 → Orthonormal ℝ (τ' x))
    (h : ∀ᵐ x ∂μHE[k], x ∈ Ω → ∀ ω : V [⋀^Fin k]→L[ℝ] ℝ, θ x * ω (τ x) = θ' x * ω (τ' x)) :
    (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) = frameCurrent θ' τ' := by
  ext ω
  rw [frameCurrent_apply hθ hτ hτo, frameCurrent_apply hθ' hτ' hτo']
  refine integral_congr_ae (h.mono fun x hx ↦ ?_)
  by_cases hxΩ : x ∈ Ω
  · exact hx hxΩ (ω x)
  · simp [image_eq_zero_of_notMem_tsupport fun hmem ↦ hxΩ (ω.tsupport_subset hmem)]

/-- **Additivity in the multiplicity.** If the pairing of `(θ, τ)` is almost everywhere on `Ω` the
sum of the pairings of `(θ₁, τ₁)` and `(θ₂, τ₂)`, the frame current of `(θ, τ)` is the sum of the
other two. -/
theorem frameCurrent_add {θ θ₁ θ₂ : V → ℝ} {τ τ₁ τ₂ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) (hθ₁ : LocallyIntegrableOn θ₁ Ω μHE[k])
    (hτ₁ : Measurable τ₁) (hτo₁ : ∀ x, θ₁ x ≠ 0 → Orthonormal ℝ (τ₁ x))
    (hθ₂ : LocallyIntegrableOn θ₂ Ω μHE[k]) (hτ₂ : Measurable τ₂)
    (hτo₂ : ∀ x, θ₂ x ≠ 0 → Orthonormal ℝ (τ₂ x))
    (h : ∀ᵐ x ∂μHE[k], x ∈ Ω → ∀ ω : V [⋀^Fin k]→L[ℝ] ℝ,
      θ x * ω (τ x) = θ₁ x * ω (τ₁ x) + θ₂ x * ω (τ₂ x)) :
    (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      frameCurrent θ₁ τ₁ + frameCurrent θ₂ τ₂ := by
  ext ω
  rw [add_apply, frameCurrent_apply hθ hτ hτo, frameCurrent_apply hθ₁ hτ₁ hτo₁,
    frameCurrent_apply hθ₂ hτ₂ hτo₂,
    ← integral_add (integrable_frameCurrent_integrand hθ₁ hτ₁ hτo₁ ω)
      (integrable_frameCurrent_integrand hθ₂ hτ₂ hτo₂ ω)]
  refine integral_congr_ae (h.mono fun x hx ↦ ?_)
  by_cases hxΩ : x ∈ Ω
  · exact hx hxΩ (ω x)
  · simp [image_eq_zero_of_notMem_tsupport fun hmem ↦ hxΩ (ω.tsupport_subset hmem)]

/-- Negating the multiplicity negates the frame current. -/
@[simp]
theorem frameCurrent_neg (θ : V → ℝ) (τ : V → Fin k → V) :
    (frameCurrent (-θ) τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) = -frameCurrent θ τ := by
  have hd : frameDensity (-θ) τ = -frameDensity θ τ := by
    funext x
    simp [frameDensity]
  ext ω
  by_cases h : LocallyIntegrableOn (frameDensity θ τ) Ω μHE[k]
  · simp [frameCurrent, hd, integralAgainstBilinCLM_eq_integral h,
      integralAgainstBilinCLM_eq_integral h.neg, integral_neg]
  · have h' : ¬LocallyIntegrableOn (frameDensity (-θ) τ) Ω μHE[k] := fun h' ↦
      h (by simpa [hd] using h'.neg)
    simp [frameCurrent, integralAgainstBilinCLM_eq_zero h, integralAgainstBilinCLM_eq_zero h']

/-- The frame current of the zero multiplicity is zero. -/
@[simp]
theorem frameCurrent_zero (τ : V → Fin k → V) :
    (frameCurrent 0 τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  ext ω
  simp [frameCurrent, frameDensity]

/-- **Change of frame within the same planes.** If, wherever `θ` does not vanish, the orthonormal
frame `τ' x` lies in the plane spanned by the orthonormal frame `τ x`, the frame current of
`(θ, τ')` is that of `(det (⟪τ i, τ' j⟫) θ, τ)`. The determinant is `±1`
(`Orthonormal.det_inner_eq_one_or_eq_neg_one`), so the current only depends on the orientations of
the planes spanned by the frames. -/
theorem frameCurrent_eq_det_inner_mul {θ : V → ℝ} {τ τ' : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) (hτ' : Measurable τ')
    (hτo' : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ' x))
    (h : ∀ x, θ x ≠ 0 → ∀ j, τ' x j ∈ Submodule.span ℝ (range (τ x))) :
    (frameCurrent θ τ' : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      frameCurrent (fun x ↦ (Matrix.of fun j i ↦ ⟪τ x i, τ' x j⟫).det * θ x) τ := by
  set d : V → ℝ := fun x ↦ (Matrix.of fun j i ↦ ⟪τ x i, τ' x j⟫).det
  have hd (x : V) (hx : θ x ≠ 0) : |d x| = 1 := by
    rcases Orthonormal.det_inner_eq_one_or_eq_neg_one (hτo x hx) (hτo' x hx) (h x hx)
      with h1 | h1 <;> simp [d, h1]
  have hdm : Measurable d := hτ.det_inner hτ'
  have hθ' : LocallyIntegrableOn (fun x ↦ d x * θ x) Ω μHE[k] := fun x hx ↦ by
    obtain ⟨t, ht, hint⟩ := hθ x hx
    refine ⟨t, ht, Integrable.mono hint (hdm.aestronglyMeasurable.mul hint.aestronglyMeasurable)
      (ae_of_all _ fun y ↦ ?_)⟩
    by_cases hy : θ y = 0
    · simp [hy]
    · rw [norm_mul, Real.norm_eq_abs (d y), hd y hy, one_mul]
  refine frameCurrent_eq_of_ae hθ hτ' hτo' hθ' hτ (fun x hx ↦ hτo x (right_ne_zero_of_mul hx))
    (ae_of_all _ fun x _ ω ↦ ?_)
  by_cases hx : θ x = 0
  · simp [hx]
  · have hω : ω (τ' x) = d x * ω (τ x) := by
      simpa [d] using ω.toAlternatingMap.map_eq_det_inner_smul_of_mem_span (hτo x hx) (h x hx)
    rw [hω]
    ring

/-- **The mass bound.** The local mass of the frame current on a set `U` is at most
`∫_U |θ| dμHE[k]`, whenever the frames are orthonormal where `θ` does not vanish. -/
theorem localMass_frameCurrent_le {θ : V → ℝ} {τ : V → Fin k → V}
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) (U : Set V) :
    localMass (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) U ≤
      ∫⁻ x in U, ‖θ x‖ₑ ∂μHE[k] := by
  refine localMass_le_iff.2 fun φ hφU hφ ↦ ?_
  by_cases h : LocallyIntegrableOn (frameDensity θ τ) Ω μHE[k]
  · rw [frameCurrent, integralAgainstBilinCLM_eq_integral h]
    refine (eNorm_integral_le_lintegral_eNorm _).trans
      ((lintegral_mono fun x ↦ ?_).trans (lintegral_indicator_le _ _))
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, formVectorPairing_frameDensity, eNorm_le_iff_norm_le]
      exact (norm_mul_apply_le (hτo x) (φ x)).trans (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
    · simp [image_eq_zero_of_notMem_tsupport fun hmem ↦ hx (hφU hmem)]
  · simp [frameCurrent, integralAgainstBilinCLM_eq_zero h]

/-- **Locally finite mass.** For a multiplicity locally integrable on `Ω` and frames orthonormal
where it does not vanish, the frame current has locally finite mass. -/
theorem hasLocallyFiniteMass_frameCurrent {θ : V → ℝ} {τ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    HasLocallyFiniteMass (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  (hasLocallyFiniteMass_iff_localMass_ne_top _).2 fun _K hK hKΩ ↦
    ((localMass_frameCurrent_le hτo _).trans_lt (hθ.integrableOn_compact_subset hKΩ hK).2).ne

end Distribution
