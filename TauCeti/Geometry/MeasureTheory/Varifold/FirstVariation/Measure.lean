/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Polar.Vector
public import TauCeti.Geometry.MeasureTheory.Varifold.Euclidean
public import TauCeti.Geometry.MeasureTheory.Varifold.Stationary
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite

/-!
# The total variation measure of the first variation

Let `E` be a finite-dimensional real inner product space, `W ⊆ E` open and `V` a `k`-varifold on
`W` with locally bounded first variation (`Euclidean.HasLocallyBoundedFirstVariation`). The first
variation `δV` is then a linear functional of locally finite mass on the `C¹` vector fields with
compact support in `W`, so the Riesz representation for vector fields
(`Distribution.apply_eq_integral_inner_polarVector`) gives

* the **total variation measure** `‖δV‖` (`Euclidean.firstVariationMeasure`), a Radon measure on
  `W` with `‖δV‖(W ∩ U) = sup {δV(X) : X of class C¹ with compact support in U, |X| ≤ 1}` for
  every open `U`, which is the total first variation `Euclidean.firstVariationMass V U`
  (`Euclidean.firstVariationMeasure_preimage_coe`);
* a vector field `η` (`Euclidean.firstVariationVector`) with `|η| = 1` at `‖δV‖`-almost every
  point and `δV(X) = ∫ ⟪η, X⟫ d‖δV‖` (`Euclidean.firstVariation_eq_integral_inner`).

The formula `X ↦ ∫ ⟪η, X⟫ d‖δV‖` extends `δV` to the compactly supported continuous vector
fields on `W` (`Euclidean.firstVariationExt`, the extension `Distribution.extendContinuous` of
`δV` through `L¹(‖δV‖)`). The extension satisfies the same local bound
`|δV(X)| ≤ ∫ |X| d‖δV‖` (`Euclidean.enorm_firstVariationExt_apply_le`), it is the
only extension with locally finite mass (`Euclidean.eq_firstVariationExt`), and its mass
measure is `‖δV‖` (`Euclidean.massMeasure_firstVariationExt`). Hence the supremum defining
`‖δV‖(U)` may equally be taken over continuous fields
(`Euclidean.firstVariationMass_eq_iSup_firstVariationExt`). This is the first part of Simon,
*Lectures on Geometric Measure Theory*, 39.3, in Euclidean space.

When `V` does not have locally bounded first variation, `‖δV‖`, `η` and the extension are `0` by
convention.

## Main results

* `Euclidean.hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass`: locally bounded first
  variation is local finiteness of the mass of `δV`.
* `Euclidean.firstVariationMeasure_eq_zero_iff`: `V` is stationary if and only if `‖δV‖ = 0`.
* `Euclidean.support_firstVariationMeasure_subset`: `spt ‖δV‖ ⊆ spt ‖V‖`, and so the extended
  first variation of a continuous field depends only on its values on `spt ‖V‖`
  (`Euclidean.firstVariationExt_eq_of_eqOn`).
* `Euclidean.firstVariationMeasure_add_le`, `Euclidean.firstVariationMeasure_smul`:
  `‖δ(V₁ + V₂)‖ ≤ ‖δV₁‖ + ‖δV₂‖` and `‖δ(cV)‖ = c ‖δV‖`.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 4.
* L. Simon, *Lectures on Geometric Measure Theory*, §39.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Distribution TestFunction
open scoped Distributions Topology NNReal ENNReal RealInnerProductSpace

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ} {W : Opens E}
  {V V₁ V₂ : Measure (W × grassmannian ℝ E k)} {U : Set E}

/-! ### The total variation measure -/

/-- The total first variation of a set is the local mass of the first variation. -/
theorem firstVariationMass_eq_localMass (V : Measure (W × grassmannian ℝ E k)) (U : Set E) :
    firstVariationMass V U = localMass (firstVariation V) U := by
  rw [firstVariationMass_def, localMass_eq_iSup_ofReal_apply]

/-- **Locally bounded first variation is locally finite mass.** A varifold has locally bounded
first variation if and only if its first variation has locally finite mass. -/
theorem hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass :
    HasLocallyBoundedFirstVariation V ↔ HasLocallyFiniteMass (firstVariation V) := by
  rw [hasLocallyBoundedFirstVariation_def, hasLocallyFiniteMass_iff_localMass_ne_top]
  refine ⟨fun h K hK hKW ↦ ?_, fun h K hK hKW ↦ ?_⟩
  · obtain ⟨C, hC⟩ := h K hK hKW
    rw [← firstVariationMass_eq_localMass]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (firstVariationMass_le_iff.2 fun X hXK hX ↦
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC X hXK hX)))
  · have hK : firstVariationMass V K ≠ ⊤ := by
      rw [firstVariationMass_eq_localMass]
      exact h K hK hKW
    exact ⟨(firstVariationMass V K).toReal, fun X hXK hX ↦ by
      simpa using abs_firstVariation_le_mul_firstVariationMass hK hXK hX⟩

alias ⟨HasLocallyBoundedFirstVariation.hasLocallyFiniteMass, _⟩ :=
  hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass

/-- The **total variation measure** `‖δV‖` of the first variation of a varifold `V` on an open
set `W` of a Euclidean space: the mass measure of `δV`. When `V` has locally bounded first
variation, it is the Radon measure on `W` whose value on `W ∩ U`, for `U` open, is the total first
variation `‖δV‖(U)` (`Euclidean.firstVariationMeasure_preimage_coe`; Simon, *Lectures on
Geometric Measure Theory*, 39.3). Otherwise it is `0` by convention. -/
def firstVariationMeasure (V : Measure (W × grassmannian ℝ E k)) : Measure W :=
  massMeasure (firstVariation V)

/-- Unfolding lemma for `Euclidean.firstVariationMeasure`. -/
theorem firstVariationMeasure_def (V : Measure (W × grassmannian ℝ E k)) :
    firstVariationMeasure V = massMeasure (firstVariation V) :=
  (rfl)

/-- The total variation measure is regular. -/
instance (V : Measure (W × grassmannian ℝ E k)) : (firstVariationMeasure V).Regular := by
  rw [firstVariationMeasure_def]
  infer_instance

/-- **The total variation measure on open sets.** If `V` has locally bounded first variation,
then `‖δV‖(W ∩ U) = sup {δV(X) : X ∈ C¹_c(U ∩ W), |X| ≤ 1}` for every open `U`. -/
theorem firstVariationMeasure_preimage_coe (hV : HasLocallyBoundedFirstVariation V)
    (hU : IsOpen U) : firstVariationMeasure V ((↑) ⁻¹' U) = firstVariationMass V U := by
  rw [firstVariationMeasure_def, massMeasure_preimage_coe hV.hasLocallyFiniteMass hU,
    firstVariationMass_eq_localMass]

/-- The total mass of `‖δV‖` is the total first variation of `W`. -/
theorem firstVariationMeasure_univ (hV : HasLocallyBoundedFirstVariation V) :
    firstVariationMeasure V univ = firstVariationMass V W := by
  have h := firstVariationMeasure_preimage_coe hV W.isOpen
  rwa [Subtype.coe_preimage_self] at h

/-- Without locally bounded first variation, the total variation measure is `0` by
convention. -/
@[simp]
theorem firstVariationMeasure_of_not_hasLocallyBoundedFirstVariation
    (hV : ¬HasLocallyBoundedFirstVariation V) : firstVariationMeasure V = 0 :=
  massMeasure_of_not_hasLocallyFiniteMass
    (mt hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass.2 hV)

/-- **Stationarity is the vanishing of the total variation measure.** A varifold with locally
bounded first variation is stationary if and only if `‖δV‖ = 0`. -/
theorem firstVariationMeasure_eq_zero_iff (hV : HasLocallyBoundedFirstVariation V) :
    firstVariationMeasure V = 0 ↔ IsStationary V := by
  rw [← Measure.measure_univ_eq_zero, firstVariationMeasure_univ hV,
    isStationary_iff_firstVariationMass_eq_zero]

/-- A stationary varifold has total variation measure `0`. -/
theorem IsStationary.firstVariationMeasure_eq_zero (h : IsStationary V) :
    firstVariationMeasure V = 0 :=
  (firstVariationMeasure_eq_zero_iff h.hasLocallyBoundedFirstVariation).2 h

/-! ### The polar vector field and the representation of `δV` -/

/-- The **polar vector field** `η` of the first variation of `V`: a strongly measurable vector
field on `W` with `|η| = 1` at `‖δV‖`-almost every point
(`Euclidean.ae_norm_firstVariationVector_eq_one`) such that `δV(X) = ∫ ⟪η, X⟫ d‖δV‖` when `V`
has locally bounded first variation (`Euclidean.firstVariation_eq_integral_inner`). It is
determined `‖δV‖`-almost everywhere, and is `0` by convention when `V` does not have locally
bounded first variation. -/
def firstVariationVector (V : Measure (W × grassmannian ℝ E k)) : W → E :=
  polarVector (firstVariation V)

/-- Unfolding lemma for `Euclidean.firstVariationVector`. -/
theorem firstVariationVector_def (V : Measure (W × grassmannian ℝ E k)) :
    firstVariationVector V = polarVector (firstVariation V) :=
  (rfl)

/-- Without locally bounded first variation, the polar vector field of the first variation is `0`
by convention. -/
@[simp]
theorem firstVariationVector_of_not_hasLocallyBoundedFirstVariation
    (hV : ¬HasLocallyBoundedFirstVariation V) : firstVariationVector V = 0 :=
  polarVector_of_not_hasLocallyFiniteMass
    (mt hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass.2 hV)

/-- The polar vector field of the first variation is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable_firstVariationVector :
    StronglyMeasurable (firstVariationVector V) :=
  stronglyMeasurable_polarVector

/-- The polar vector field of the first variation has norm one at `‖δV‖`-almost every point. -/
theorem ae_norm_firstVariationVector_eq_one :
    ∀ᵐ x ∂firstVariationMeasure V, ‖firstVariationVector V x‖ = 1 :=
  ae_norm_polarVector_eq_one

/-- The polar vector field of the first variation is locally integrable for `‖δV‖`. -/
theorem locallyIntegrable_firstVariationVector :
    LocallyIntegrable (firstVariationVector V) (firstVariationMeasure V) :=
  locallyIntegrable_polarVector

/-- **Riesz representation of the first variation.** If `V` has locally bounded first variation,
then `δV(X) = ∫ ⟪η, X⟫ d‖δV‖` for every `C¹` vector field `X` with compact support in `W`. -/
theorem firstVariation_eq_integral_inner (hV : HasLocallyBoundedFirstVariation V)
    (X : 𝓓^{1}(W, E)) :
    firstVariation V X = ∫ x, ⟪firstVariationVector V x, X x⟫ ∂firstVariationMeasure V :=
  apply_eq_integral_inner_polarVector hV.hasLocallyFiniteMass X

/-- **Uniqueness of the polar vector field.** A locally integrable field `η` representing `δV`
against `‖δV‖` agrees with `Euclidean.firstVariationVector V` at `‖δV‖`-almost every point. -/
theorem ae_eq_firstVariationVector {η : W → E}
    (hη : LocallyIntegrable η (firstVariationMeasure V))
    (h : ∀ X : 𝓓^{1}(W, E), firstVariation V X = ∫ x, ⟪η x, X x⟫ ∂firstVariationMeasure V) :
    η =ᵐ[firstVariationMeasure V] firstVariationVector V :=
  ae_eq_polarVector hη h

/-! ### The extension of `δV` to continuous vector fields -/

/-- The **extension of the first variation** to the compactly supported continuous vector fields
on `W`: the extension `Distribution.extendContinuous` of `δV`, which is `X ↦ ∫ ⟪η, X⟫ d‖δV‖` with
`η` the polar vector field of `δV` (`Euclidean.firstVariationExt_apply`). If `V` has locally
bounded first variation, it agrees with `δV` on `C¹` fields (`Euclidean.firstVariationExt_monoCLM`),
and it is the only linear extension with locally finite mass (`Euclidean.eq_firstVariationExt`). -/
def firstVariationExt (V : Measure (W × grassmannian ℝ E k)) : 𝓓^{0}(W, E) →L[ℝ] ℝ :=
  extendContinuous (firstVariation V)

/-- Unfolding lemma for `Euclidean.firstVariationExt`. -/
theorem firstVariationExt_def (V : Measure (W × grassmannian ℝ E k)) :
    firstVariationExt V = extendContinuous (firstVariation V) :=
  (rfl)

/-- The extended first variation integrates `⟪η, X⟫` against `‖δV‖`. -/
theorem firstVariationExt_apply (X : 𝓓^{0}(W, E)) :
    firstVariationExt V X = ∫ x, ⟪firstVariationVector V x, X x⟫ ∂firstVariationMeasure V :=
  extendContinuous_apply_eq_integral_inner X

/-- If `V` does not have locally bounded first variation, its extended first variation is `0`. -/
@[simp]
theorem firstVariationExt_of_not_hasLocallyBoundedFirstVariation
    (hV : ¬HasLocallyBoundedFirstVariation V) : firstVariationExt V = 0 :=
  extendContinuous_of_not_hasLocallyFiniteMass
    (hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass.not.1 hV)

/-- **Domination of the extended first variation by `‖δV‖`.**
`|firstVariationExt V X| ≤ ∫ |X| d‖δV‖`. -/
theorem enorm_firstVariationExt_apply_le (X : 𝓓^{0}(W, E)) :
    ‖firstVariationExt V X‖ₑ ≤ ∫⁻ x, ‖X x‖ₑ ∂firstVariationMeasure V :=
  enorm_extendContinuous_apply_le X

/-- **The extension extends `δV`.** If `V` has locally bounded first variation, the extended first
variation of a `C¹` field is its first variation. -/
@[simp]
theorem firstVariationExt_monoCLM (hV : HasLocallyBoundedFirstVariation V) (X : 𝓓^{1}(W, E)) :
    firstVariationExt V (monoCLM ℝ X) = firstVariation V X :=
  extendContinuous_monoCLM hV.hasLocallyFiniteMass X

/-- **The mass measure of the extension is `‖δV‖`.** -/
@[simp]
theorem massMeasure_firstVariationExt :
    massMeasure (firstVariationExt V) = firstVariationMeasure V :=
  massMeasure_extendContinuous

/-- The extended first variation has locally finite mass: on the fields supported in a compact
`K ⊆ W` with `|X| ≤ 1` it is bounded by `‖δV‖(K)`. -/
theorem hasLocallyFiniteMass_firstVariationExt :
    HasLocallyFiniteMass (firstVariationExt V) :=
  hasLocallyFiniteMass_extendContinuous

/-- **Uniqueness of the extension.** A linear functional of locally finite mass on the compactly
supported continuous vector fields on `W` that agrees with `δV` on the `C¹` fields is the extended
first variation. -/
theorem eq_firstVariationExt {L : 𝓓^{0}(W, E) →ₗ[ℝ] ℝ} (hL : HasLocallyFiniteMass L)
    (h : ∀ X : 𝓓^{1}(W, E), L (monoCLM ℝ X) = firstVariation V X) :
    L = (firstVariationExt V : 𝓓^{0}(W, E) →ₗ[ℝ] ℝ) :=
  extendContinuous_unique hL h

/-- **The local mass of the extension.** If `V` has locally bounded first variation, the local
mass of the extended first variation on an open `U`, a supremum over continuous fields, is the
total first variation `‖δV‖(U)`, a supremum over `C¹` fields. -/
theorem localMass_firstVariationExt (hV : HasLocallyBoundedFirstVariation V) (hU : IsOpen U) :
    localMass (firstVariationExt V) U = firstVariationMass V U := by
  rw [firstVariationExt_def, localMass_extendContinuous hV.hasLocallyFiniteMass hU,
    firstVariationMass_eq_localMass]

/-- **The total first variation over continuous fields.** If `V` has locally bounded first
variation, then for every open `U`,
`‖δV‖(U) = sup {δV(X) : X continuous with compact support in U ∩ W, |X| ≤ 1}`, for the extended
first variation. -/
theorem firstVariationMass_eq_iSup_firstVariationExt (hV : HasLocallyBoundedFirstVariation V)
    (hU : IsOpen U) :
    firstVariationMass V U = ⨆ (X : 𝓓^{0}(W, E)) (_ : tsupport X ⊆ U) (_ : ∀ x, ‖X x‖ ≤ 1),
      ENNReal.ofReal (firstVariationExt V X) := by
  rw [← localMass_eq_iSup_ofReal_apply, localMass_firstVariationExt hV hU]

/-! ### Support, sums and multiples -/

/-- **The support of `‖δV‖` lies in the support of the weight**: `spt ‖δV‖ ⊆ spt ‖V‖`. -/
theorem support_firstVariationMeasure_subset :
    (firstVariationMeasure V).support ⊆ (↑) ⁻¹' (weight V).support := by
  by_cases hV : HasLocallyBoundedFirstVariation V
  swap
  · simp [firstVariationMeasure_of_not_hasLocallyBoundedFirstVariation hV]
  rw [firstVariationMeasure_def, support_massMeasure hV.hasLocallyFiniteMass]
  refine preimage_mono fun x hx ↦ by_contra fun hx' ↦ ?_
  obtain ⟨U, hU, hU0⟩ := Measure.notMem_support_iff_exists.1 hx'
  obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.1 hU
  exact (notMem_dsupport_iff x).2 ⟨U', fun X hXU' ↦ firstVariation_eq_zero_of_weight_eq_zero
    hXU' (measure_mono_null hU'U hU0), hU'o, hxU'⟩ hx

/-- **Locality of the extended first variation.** The extended first variation of a continuous
field depends only on its values on the support of the weight `spt ‖V‖`. -/
theorem firstVariationExt_eq_of_eqOn {X Y : 𝓓^{0}(W, E)}
    (h : EqOn X Y (weight V).support) : firstVariationExt V X = firstVariationExt V Y := by
  rw [firstVariationExt_apply, firstVariationExt_apply]
  refine integral_congr_ae ?_
  filter_upwards [Measure.support_mem_ae (μ := firstVariationMeasure V)] with x hx
  rw [h (support_firstVariationMeasure_subset hx)]

/-- **Subadditivity of the total variation measure in the varifold.**
`‖δ(V₁ + V₂)‖ ≤ ‖δV₁‖ + ‖δV₂‖`. -/
theorem firstVariationMeasure_add_le (h₁ : HasLocallyBoundedFirstVariation V₁)
    (h₂ : HasLocallyBoundedFirstVariation V₂) :
    firstVariationMeasure (V₁ + V₂) ≤ firstVariationMeasure V₁ + firstVariationMeasure V₂ := by
  by_cases h : IsFiniteMeasureOnCompacts (V₁ + V₂)
  swap
  · rw [(isStationary_of_not_isFiniteMeasureOnCompacts h).firstVariationMeasure_eq_zero]
    exact Measure.zero_le _
  obtain ⟨_, _⟩ := isFiniteMeasureOnCompacts_add_iff.1 h
  refine massMeasure_le_of_enorm_apply_le _ fun X ↦ ?_
  rw [firstVariation_add_measure, add_apply, lintegral_add_measure]
  exact (eNorm_add_le _ _).trans (add_le_add
    (enorm_apply_le_lintegral_massMeasure h₁.hasLocallyFiniteMass X)
    (enorm_apply_le_lintegral_massMeasure h₂.hasLocallyFiniteMass X))

/-- **Homogeneity of the total variation measure in the varifold.** `‖δ(cV)‖ = c ‖δV‖` for
`c ≥ 0`. -/
theorem firstVariationMeasure_smul (c : ℝ≥0) (V : Measure (W × grassmannian ℝ E k)) :
    firstVariationMeasure (c • V) = c • firstVariationMeasure V := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, zero_smul, IsStationary.firstVariationMeasure_eq_zero isStationary_zero]
  by_cases hV : HasLocallyBoundedFirstVariation V
  · have hcV := (hasLocallyBoundedFirstVariation_smul_iff hc).2 hV
    refine (eq_massMeasure_of_preimage_coe hcV.hasLocallyFiniteMass _ fun U' hU' ↦ ?_).symm
    rw [smul_apply, firstVariationMeasure_preimage_coe hV hU',
      ← firstVariationMass_eq_localMass, firstVariationMass_smul, ENNReal.smul_def, smul_eq_mul]
  · rw [firstVariationMeasure_of_not_hasLocallyBoundedFirstVariation hV,
      firstVariationMeasure_of_not_hasLocallyBoundedFirstVariation
        ((hasLocallyBoundedFirstVariation_smul_iff hc).not.2 hV), smul_zero]

end Euclidean
