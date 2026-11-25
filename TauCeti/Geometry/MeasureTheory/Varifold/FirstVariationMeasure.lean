/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Polar.Vector
public import TauCeti.Geometry.MeasureTheory.Varifold.Euclidean
public import TauCeti.Geometry.MeasureTheory.Varifold.Stationary
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Measure.Regular
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
fields on `W` (`Euclidean.firstVariationExt`). The extension has locally finite mass, it is the
only extension with locally finite mass (`Euclidean.eq_firstVariationExt`), and its mass
measure is `‖δV‖` (`Euclidean.massMeasure_firstVariationExt`). Hence the supremum defining
`‖δV‖(U)` may equally be taken over continuous fields
(`Euclidean.firstVariationMass_eq_iSup_firstVariationExt`). This is the first part of Simon,
*Lectures on Geometric Measure Theory*, 39.3, in Euclidean space.

When `V` does not have locally bounded first variation, `‖δV‖` and `η` are `0` by convention.

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

omit [FiniteDimensional ℝ E] in
private theorem integrable_inner_of_locallyIntegrable {μ : Measure W} {η : W → E}
    (hη : LocallyIntegrable η μ) (X : 𝓓^{0}(W, E)) : Integrable (fun x ↦ ⟪η x, X x⟫) μ :=
  (integrable_inner_subtype X hη).congr (ae_of_all _ fun _ ↦ real_inner_comm _ _)

/-- The **extension of the first variation** to the compactly supported continuous vector fields
on `W`: `X ↦ ∫ ⟪η, X⟫ d‖δV‖`, with `η` the polar vector field of `δV`. If `V` has locally bounded
first variation, it agrees with `δV` on `C¹` fields (`Euclidean.firstVariationExt_monoCLM`), and
it is the only linear extension with locally finite mass (`Euclidean.eq_firstVariationExt`). -/
def firstVariationExt (V : Measure (W × grassmannian ℝ E k)) : 𝓓^{0}(W, E) →ₗ[ℝ] ℝ where
  toFun X := ∫ x, ⟪firstVariationVector V x, X x⟫ ∂firstVariationMeasure V
  map_add' X Y := by
    simp only [FunLike.coe_add, Pi.add_apply, inner_add_right]
    exact integral_add (integrable_inner_of_locallyIntegrable
      locallyIntegrable_firstVariationVector X)
      (integrable_inner_of_locallyIntegrable locallyIntegrable_firstVariationVector Y)
  map_smul' c X := by
    simp only [FunLike.coe_smul, Pi.smul_apply, inner_smul_right, integral_const_mul,
      RingHom.id_apply, smul_eq_mul]

/-- The extended first variation integrates `⟪η, X⟫` against `‖δV‖`. -/
theorem firstVariationExt_apply (X : 𝓓^{0}(W, E)) :
    firstVariationExt V X = ∫ x, ⟪firstVariationVector V x, X x⟫ ∂firstVariationMeasure V :=
  (rfl)

/-- **The extension extends `δV`.** If `V` has locally bounded first variation, the extended first
variation of a `C¹` field is its first variation. -/
theorem firstVariationExt_monoCLM (hV : HasLocallyBoundedFirstVariation V) (X : 𝓓^{1}(W, E)) :
    firstVariationExt V (monoCLM ℝ X) = firstVariation V X := by
  rw [firstVariationExt_apply, coe_monoCLM_of_le (by simp) le_rfl,
    firstVariation_eq_integral_inner hV]

/-- **The mass measure of the extension is `‖δV‖`.** -/
theorem massMeasure_firstVariationExt :
    massMeasure (firstVariationExt V) = firstVariationMeasure V :=
  massMeasure_eq_of_apply_eq_integral_inner
    stronglyMeasurable_firstVariationVector.aestronglyMeasurable
    ae_norm_firstVariationVector_eq_one fun _ ↦ rfl

/-- The extended first variation has locally finite mass: on the fields supported in a compact
`K ⊆ W` with `|X| ≤ 1` it is bounded by `‖δV‖(K)`. -/
theorem hasLocallyFiniteMass_firstVariationExt :
    HasLocallyFiniteMass (firstVariationExt V) := by
  refine (hasLocallyFiniteMass_iff_localMass_ne_top _).2 fun K hK hKW ↦ ?_
  have hKc := Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKW)
  refine ne_top_of_le_ne_top (hKc.measure_lt_top (μ := firstVariationMeasure V)).ne
    (localMass_le_iff.2 fun X hXK hX ↦ ?_)
  have hη : (fun x ↦ ‖firstVariationVector V x‖ₑ) =ᵐ[firstVariationMeasure V] 1 :=
    ae_norm_firstVariationVector_eq_one.mono fun x hx ↦ by simp [← ofReal_norm, hx]
  have h := enorm_integral_inner_le_withDensity hK.measurableSet hXK hX
    (firstVariationMeasure V) (firstVariationVector V)
  rw [withDensity_congr_ae hη, withDensity_one] at h
  have hcomm : (fun x : W ↦ ⟪firstVariationVector V x, X x⟫) =
      fun x : W ↦ ⟪X x, firstVariationVector V x⟫ :=
    funext fun x ↦ real_inner_comm (X x) _
  rwa [firstVariationExt_apply, hcomm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A linear map of locally finite mass on continuous fields that vanishes on smooth fields is
zero: smooth fields approximate a continuous field uniformly, with supports in a fixed compact
set. -/
private theorem eq_zero_of_hasLocallyFiniteMass {L : 𝓓^{0}(W, E) →ₗ[ℝ] ℝ}
    (hL : HasLocallyFiniteMass L) (h : ∀ ψ : 𝓓(W, E), L (monoCLM ℝ ψ) = 0) : L = 0 := by
  ext φ
  obtain ⟨K, hK, hKW, hφK, happrox⟩ := exists_isCompact_forall_exists_dist_le φ
  have hM := (hasLocallyFiniteMass_iff_localMass_ne_top L).1 hL K hK hKW
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖L φ‖ₑ ≤ localMass L K * ENNReal.ofReal ε := by
    obtain ⟨ψ, hψK, hψφ⟩ := happrox ε hε
    have hsub : tsupport ⇑(φ - (monoCLM ℝ ψ : 𝓓^{0}(W, E))) ⊆ K := by
      rw [FunLike.coe_sub, coe_monoCLM_of_le le_top le_rfl]
      exact (tsupport_sub _ _).trans (union_subset hφK hψK)
    have := enorm_apply_le_localMass_mul_of_forall_enorm_le L hsub fun x ↦ by
      rw [← ofReal_norm, FunLike.coe_sub, Pi.sub_apply, coe_monoCLM_of_le le_top le_rfl,
        ← dist_eq_norm_sub']
      exact ENNReal.ofReal_le_ofReal (hψφ x)
    rwa [map_sub, h ψ, sub_zero] at this
  have h0 : Tendsto ENNReal.ofReal (𝓝[>] (0 : ℝ)) (𝓝 0) := ENNReal.ofReal_zero ▸
    (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := ENNReal.Tendsto.const_mul h0 (Or.inr hM)
  rw [mul_zero] at hlim
  have : ‖L φ‖ₑ ≤ 0 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hbound)
  simpa using this

/-- **Uniqueness of the extension.** A linear functional of locally finite mass on the compactly
supported continuous vector fields on `W` that agrees with `δV` on the `C¹` fields is the extended
first variation. -/
theorem eq_firstVariationExt {L : 𝓓^{0}(W, E) →ₗ[ℝ] ℝ} (hL : HasLocallyFiniteMass L)
    (h : ∀ X : 𝓓^{1}(W, E), L (monoCLM ℝ X) = firstVariation V X) : L = firstVariationExt V := by
  have hV : HasLocallyBoundedFirstVariation V := by
    rw [hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass]
    have hLm := hL.comp_monoCLM (Ω' := W) (m := 1)
    convert hLm using 1
    exact funext fun X ↦ (h X).symm
  refine sub_eq_zero.1 (eq_zero_of_hasLocallyFiniteMass ?_ fun ψ ↦ ?_)
  · have hcoe : ⇑(L - firstVariationExt V) = ⇑L - ⇑(firstVariationExt V) :=
      funext fun X ↦ LinearMap.sub_apply _ _ X
    rw [hcoe]
    exact hL.sub hasLocallyFiniteMass_firstVariationExt
  · have hψ : (monoCLM ℝ ψ : 𝓓^{0}(W, E)) = monoCLM ℝ (monoCLM ℝ ψ : 𝓓^{1}(W, E)) :=
      TestFunction.ext fun x ↦ by simp [coe_monoCLM_of_le le_top le_rfl,
        coe_monoCLM_of_le (show (0 : ℕ∞) ≤ 1 by simp) le_rfl]
    rw [LinearMap.sub_apply, hψ, h, firstVariationExt_monoCLM hV, sub_self]

/-- **The local mass of the extension.** If `V` has locally bounded first variation, the local
mass of the extended first variation on an open `U`, a supremum over continuous fields, is the
total first variation `‖δV‖(U)`, a supremum over `C¹` fields. -/
theorem localMass_firstVariationExt (hV : HasLocallyBoundedFirstVariation V) (hU : IsOpen U) :
    localMass (firstVariationExt V) U = firstVariationMass V U := by
  rw [← massMeasure_preimage_coe hasLocallyFiniteMass_firstVariationExt hU,
    massMeasure_firstVariationExt, firstVariationMeasure_preimage_coe hV hU]

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

/-- The first variation of a field supported in an open set of zero weight is `0`. -/
theorem firstVariation_eq_zero_of_weight_eq_zero (hU : IsOpen U) {X : 𝓓^{1}(W, E)}
    (hXU : tsupport X ⊆ U) (h : weight V U = 0) : firstVariation V X = 0 := by
  by_cases hV : IsFiniteMeasureOnCompacts V
  swap
  · simp [firstVariation_of_not_isFiniteMeasureOnCompacts hV]
  rw [firstVariation_apply]
  refine integral_eq_zero_of_ae ?_
  rw [weight_apply hU.measurableSet] at h
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with p hp
  exact tangentialDivergence_eq_zero_of_notMem_tsupport (fun hx ↦ hp (hXU hx)) _

/-- The total first variation of an open set of zero weight is `0`. -/
theorem firstVariationMass_eq_zero_of_weight_eq_zero (hU : IsOpen U) (h : weight V U = 0) :
    firstVariationMass V U = 0 :=
  nonpos_iff_eq_zero.1 <| firstVariationMass_le_iff.2 fun _ hXU _ ↦ by
    simp [firstVariation_eq_zero_of_weight_eq_zero hU hXU h]

/-- **The support of `‖δV‖` lies in the support of the weight**: `spt ‖δV‖ ⊆ spt ‖V‖`. -/
theorem support_firstVariationMeasure_subset :
    (firstVariationMeasure V).support ⊆ (↑) ⁻¹' (weight V).support := by
  intro x hx
  by_contra hx'
  obtain ⟨U, hU, hU0⟩ := Measure.notMem_support_iff_exists.1 hx'
  obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.1 hU
  have h0 : weight V U' = 0 := measure_mono_null hU'U hU0
  by_cases hV : HasLocallyBoundedFirstVariation V
  · refine Measure.notMem_support_iff_exists.2 ⟨(↑) ⁻¹' U',
      (hU'o.preimage continuous_subtypeVal).mem_nhds hxU', ?_⟩ hx
    rw [firstVariationMeasure_preimage_coe hV hU'o,
      firstVariationMass_eq_zero_of_weight_eq_zero hU'o h0]
  · simp [firstVariationMeasure_of_not_hasLocallyBoundedFirstVariation hV] at hx

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

/-- For `c ≠ 0`, `cV` has locally bounded first variation if and only if `V` does. -/
theorem hasLocallyBoundedFirstVariation_smul_iff {c : ℝ≥0} (hc : c ≠ 0) :
    HasLocallyBoundedFirstVariation (c • V) ↔ HasLocallyBoundedFirstVariation V := by
  simp only [hasLocallyBoundedFirstVariation_iff, firstVariationMass_smul, ne_eq,
    ENNReal.mul_eq_top, ENNReal.coe_ne_top, false_and, ENNReal.coe_eq_zero, hc, not_false_eq_true,
    true_and, or_false]

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
