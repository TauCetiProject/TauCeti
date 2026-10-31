/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure
import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.OrderZero
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Integral.Lebesgue.OpenSet

/-!
# The polar decomposition of a functional of locally finite mass

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `F` be a
finite-dimensional real normed space and let `T` be a continuous real-linear functional on the
`F`-valued tests `𝓓(Ω, F)` with locally finite mass and mass measure `‖T‖`
(`Distribution.massMeasure`). This file represents `T` by integration against `‖T‖`: there is a
strongly measurable field `τ_T : Ω → StrongDual ℝ F` of continuous linear functionals on
the fibre `F`, the **polar density** of `T` (`Distribution.polarDensity`), with

`T φ = ∫ τ_T(x) (φ x) d‖T‖(x)`

for every test `φ`, and `‖τ_T(x)‖ = 1` for `‖T‖`-almost every `x`, the norm being the dual norm
of `StrongDual ℝ F`. It is unique `‖T‖`-almost everywhere. With `F = E [⋀^Fin k]→L[ℝ] ℝ`, `T` is
a `k`-current of locally finite mass; when `E` is an inner product space the operator norm on
forms is the comass, its dual norm on `StrongDual ℝ F` is the mass norm of `k`-vectors, and the
statement is the representation `T = ‖T‖ ∧ τ_T` of the current by its mass measure and a unit
orienting `k`-vector field.

In each direction `v ∈ F`, the scalar distribution `ψ ↦ T (ψ v)` is dominated by `‖v‖ ‖T‖`, so it
has a density bounded by `‖v‖` with respect to `‖T‖`
(`Distribution.exists_eq_integral_mul_of_enorm_apply_le`). Assembling these densities along a
basis of `F` gives `τ_T`. Testing against fields `ψ v` supported in an open set `U` bounds
`|τ_T(x) v|` by `‖v‖` (`TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le`), so
`‖τ_T‖ ≤ 1`. Conversely `‖T‖(U)` is the supremum of `|T φ|` over the tests `φ` supported in `U`
with `‖φ‖ ≤ 1`, which is at most `∫_U ‖τ_T‖ d‖T‖`, so `‖τ_T‖ = 1` almost everywhere.

## Main declarations

* `Distribution.polarDensity`: the polar density `τ_T` of `T`.
* `Distribution.apply_eq_integral_polarDensity`: `T φ = ∫ τ_T(φ) d‖T‖`.
* `Distribution.ae_norm_polarDensity_eq_one`: `‖τ_T‖ = 1` at `‖T‖`-almost every point.
* `Distribution.ae_eq_polarDensity`: uniqueness of `τ_T` among locally integrable fields.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 (currents representable by integration,
  `T = ‖T‖ ∧ τ_T`, with `τ_T` the orienting field).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 1, Theorem 4.14 (the Riesz
  representation theorem for functionals on vector-valued functions), and Chapter 6, §2.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction
open scoped ENNReal NNReal Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {Ω : Opens E} {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, F) ℝ]
  [LinearMapClass 𝓕 ℝ 𝓓(Ω, F) ℝ] {T : 𝓕}

section Existence

variable (hT : HasLocallyFiniteMass T)
include hT

omit [FiniteDimensional ℝ F] in
/-- In each direction `v`, the scalar distribution `ψ ↦ T (ψ v)` is dominated by `‖v‖ ‖T‖`. -/
private theorem enorm_apply_postcompCLM_le (v : F) (ψ : 𝓓(Ω, ℝ)) :
    ‖T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) ψ)‖ₑ ≤
      ‖v‖₊ * ∫⁻ x, ‖ψ x‖ₑ ∂massMeasure T := by
  refine (enorm_apply_le_lintegral_massMeasure hT _).trans_eq ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  congr with x
  simp only [postcompCLM_apply, Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    enorm_eq_nnnorm, nnnorm_smul, ENNReal.coe_mul, mul_comm]

/-- Existence of a density of norm at most one representing `T` against `‖T‖`. -/
private theorem exists_le_one [ContinuousMapClass 𝓕 𝓓(Ω, F) ℝ] :
    ∃ τ : Ω → StrongDual ℝ F, StronglyMeasurable τ ∧ (∀ᵐ x ∂massMeasure T, ‖τ x‖ ≤ 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T := by
  have := Ω.isOpen.locallyCompactSpace
  set lam := massMeasure T
  let b := Module.finBasis ℝ F
  -- The densities of the scalar distributions `ψ ↦ T (ψ bᵢ)` with respect to `‖T‖`.
  choose h hm hle hh using fun i => exists_eq_integral_mul_of_enorm_apply_le
    ((⟨LinearMap.ofClass T, map_continuous T⟩ : 𝓓(Ω, F) →L[ℝ] ℝ) ∘L
      postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i))) lam ‖b i‖₊
    (enorm_apply_postcompCLM_le hT (b i))
  have hloc (i) : LocallyIntegrable (h i) lam := locallyIntegrable_iff.2 fun K hK =>
    Measure.integrableOn_of_bounded hK.measure_lt_top.ne (hm i).aestronglyMeasurable
      (M := ‖b i‖) (ae_restrict_of_ae ((hle i).mono fun x hx =>
        NNReal.coe_le_coe.2 (ENNReal.coe_le_coe.1 hx)))
  -- Assemble them along the coordinate functionals of `b`.
  let c (i) : StrongDual ℝ F := LinearMap.toContinuousLinearMap (b.coord i)
  set τ : Ω → StrongDual ℝ F := fun x => ∑ i, h i x • c i with hτ
  have hτv (x : Ω) (v : F) : τ x v = ∑ i, b.coord i v * h i x := by
    simp [hτ, c, mul_comm]
  have hrep (φ : 𝓓(Ω, F)) : T φ = ∫ x, τ x (φ x) ∂lam := by
    set ψ : _ → 𝓓(Ω, ℝ) := fun i => postcompCLM (c i) φ
    have hφ : φ = ∑ i, postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ψ i) := by
      ext x
      simp [ψ, c, b.sum_repr]
    have hint (i) : Integrable (fun x : Ω => ψ i x * h i x) lam :=
      (ψ i).integrable_bilin_subtype (ContinuousLinearMap.mul ℝ ℝ) (hloc i)
    calc T φ = ∑ i, T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ψ i)) := by
          conv_lhs => rw [hφ]
          rw [map_sum]
      _ = ∑ i, ∫ x, ψ i x * h i x ∂lam := Finset.sum_congr rfl fun i _ => hh i (ψ i)
      _ = ∫ x, τ x (φ x) ∂lam := by
          rw [← integral_finsetSum _ fun i _ => hint i]
          congr with x
          simp [hτv, ψ, c]
  -- In each direction `v`, `|τ v| ≤ ‖v‖` almost everywhere.
  have hdir (v : F) : ∀ᵐ x ∂lam, ‖τ x v‖ₑ ≤ ‖v‖ₑ := by
    refine TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le (k := fun _ => ‖v‖ₑ)
      (locallyIntegrable_iff.2 fun K hK => ?_) measurable_const (fun K hK => ?_)
      fun U _ ψ hψU hψ => ?_
    · rw [show (fun x => τ x v) = fun x => ∑ i, b.coord i v * h i x from funext fun x => hτv x v]
      exact integrable_finsetSum _ fun i _ => ((hloc i).integrableOn_isCompact hK).const_mul _
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top enorm_ne_top hK.measure_lt_top.ne
    · rw [setLIntegral_const, massMeasure_preimage_coe hT U.isOpen, mul_comm]
      have : ∫ x, inner ℝ (ψ x) (τ x v) ∂lam =
          T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) ψ) := by
        rw [hrep]
        congr with x
        simp [mul_comm]
      rw [this]
      refine enorm_apply_le_localMass_mul_of_forall_enorm_le T
        (by rw [postcompCLM_apply]; exact (tsupport_comp_subset (map_zero _) ψ).trans hψU)
        fun x => ?_
      simpa [enorm_smul] using mul_le_of_le_one_left (by positivity)
        (by simpa [← ofReal_norm] using hψ x : ‖ψ x‖ₑ ≤ 1)
  refine ⟨τ, by fun_prop, ?_, hrep⟩
  -- Combine the directional bounds along a dense sequence.
  filter_upwards [ae_all_iff.2 fun n => hdir (TopologicalSpace.denseSeq F n)] with x hx
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  refine (TopologicalSpace.denseRange_denseSeq F).induction_on v
    (isClosed_le (τ x).continuous.norm (continuous_const.mul continuous_norm)) fun n => ?_
  have := hx n
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at this
  simpa using this

omit [FiniteDimensional ℝ F] in
/-- A density of norm at most one representing `T` against `‖T‖` has norm one almost
everywhere. -/
private theorem ae_norm_eq_one_of_le_one {τ : Ω → StrongDual ℝ F}
    (hτ1 : ∀ᵐ x ∂massMeasure T, ‖τ x‖ ≤ 1)
    (hτ : ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T) :
    ∀ᵐ x ∂massMeasure T, ‖τ x‖ = 1 := by
  have := Ω.isOpen.locallyCompactSpace
  set lam := massMeasure T
  -- Testing the supremum defining `‖T‖(V)` gives `‖T‖(V) ≤ ∫_V ‖τ‖ d‖T‖` on open sets.
  have hopen (V : Set Ω) (hV : IsOpen V) : lam V ≤ ∫⁻ x in V, ‖τ x‖ₑ ∂lam := by
    have hU : IsOpen (((↑) : Ω → E) '' V) := Ω.isOpen.isOpenMap_subtype_val V hV
    have hUV : ((↑) : Ω → E) ⁻¹' ((↑) '' V) = V := preimage_image_eq V Subtype.val_injective
    rw [← hUV, massMeasure_preimage_coe hT hU, localMass_le_iff]
    intro φ hφU hφ
    rw [hτ, hUV, ← lintegral_indicator hV.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (((τ x).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hφ x)))
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx <| by
        simpa [hUV] using (show (x : E) ∈ ((↑) : Ω → E) '' V from hφU h)
      simp [this]
  filter_upwards [ae_eq_one_of_forall_isOpen_le_setLIntegral
    (hτ1.mono fun x hx => by rwa [← ofReal_norm, ENNReal.ofReal_le_one]) hopen] with x hx
  rwa [← ofReal_norm, ENNReal.ofReal_eq_one] at hx

private theorem exists_polarDensity [ContinuousMapClass 𝓕 𝓓(Ω, F) ℝ] :
    ∃ τ : Ω → StrongDual ℝ F, StronglyMeasurable τ ∧ (∀ᵐ x ∂massMeasure T, ‖τ x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T :=
  let ⟨τ, hτm, hτ1, hτ⟩ := exists_le_one hT
  ⟨τ, hτm, ae_norm_eq_one_of_le_one hT hτ1 hτ, hτ⟩

end Existence

open scoped Classical in
/-- The **polar density** `τ_T` of a continuous linear functional `T` on `F`-valued tests on `Ω`
with locally finite mass: a strongly measurable field `τ_T : Ω → StrongDual ℝ F` with `‖τ_T‖ = 1` at
`‖T‖`-almost every point (`Distribution.ae_norm_polarDensity_eq_one`) such that
`T φ = ∫ τ_T(x) (φ x) d‖T‖(x)` for every test `φ`
(`Distribution.apply_eq_integral_polarDensity`). It is determined `‖T‖`-almost everywhere
(`Distribution.ae_eq_polarDensity`). If no such field exists it is `0` by convention. -/
def polarDensity (T : 𝓕) : Ω → StrongDual ℝ F :=
  if h : ∃ τ : Ω → StrongDual ℝ F, StronglyMeasurable τ ∧ (∀ᵐ x ∂massMeasure T, ‖τ x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T then h.choose
  else 0

omit [FiniteDimensional ℝ F] in
/-- The polar density is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable_polarDensity : StronglyMeasurable (polarDensity T) := by
  unfold polarDensity
  split_ifs with h
  exacts [h.choose_spec.1, stronglyMeasurable_const]

section Spec

variable [ContinuousMapClass 𝓕 𝓓(Ω, F) ℝ] (hT : HasLocallyFiniteMass T)
include hT

private theorem polarDensity_spec :
    (∀ᵐ x ∂massMeasure T, ‖polarDensity T x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, polarDensity T x (φ x) ∂massMeasure T := by
  rw [polarDensity, dite_eq_left (exists_polarDensity hT)]
  exact (exists_polarDensity hT).choose_spec.2

/-- **The polar decomposition `T = τ_T ‖T‖`.** A continuous linear functional of locally finite
mass on `F`-valued tests is integration of the polar density against the mass measure. -/
theorem apply_eq_integral_polarDensity (φ : 𝓓(Ω, F)) :
    T φ = ∫ x, polarDensity T x (φ x) ∂massMeasure T :=
  (polarDensity_spec hT).2 φ

/-- The polar density of a functional of locally finite mass has norm one at almost every point
of its mass measure. -/
theorem ae_norm_polarDensity_eq_one : ∀ᵐ x ∂massMeasure T, ‖polarDensity T x‖ = 1 :=
  (polarDensity_spec hT).1

/-- The polar density of a functional of locally finite mass is locally integrable with respect
to its mass measure. -/
theorem locallyIntegrable_polarDensity : LocallyIntegrable (polarDensity T) (massMeasure T) := by
  have := Ω.isOpen.locallyCompactSpace
  exact locallyIntegrable_iff.2 fun K hK => Measure.integrableOn_of_bounded
    hK.measure_lt_top.ne stronglyMeasurable_polarDensity.aestronglyMeasurable (M := 1)
    (ae_restrict_of_ae ((ae_norm_polarDensity_eq_one hT).mono fun x hx => hx.le))

/-- For every test `φ`, the integrand `x ↦ τ_T(x) (φ x)` of the polar decomposition is
integrable with respect to the mass measure. -/
theorem integrable_polarDensity_apply (φ : 𝓓(Ω, F)) :
    Integrable (fun x => polarDensity T x (φ x)) (massMeasure T) :=
  (integrable_bilin_subtype (NormedSpace.inclusionInDoubleDual ℝ F)
    (locallyIntegrable_polarDensity hT) φ).congr (ae_of_all _ fun x => by simp)

/-- **Uniqueness of the polar density.** A locally integrable field `τ` of functionals on `F`
with `T φ = ∫ τ(x) (φ x) d‖T‖(x)` for every test `φ` agrees with the polar density at almost
every point of the mass measure. -/
theorem ae_eq_polarDensity {τ : Ω → StrongDual ℝ F} (hτ : LocallyIntegrable τ (massMeasure T))
    (h : ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T) :
    τ =ᵐ[massMeasure T] polarDensity T := by
  have := Ω.isOpen.locallyCompactSpace
  have hτ' := locallyIntegrable_polarDensity hT
  -- In each direction `v`, `(τ - τ_T) v` vanishes almost everywhere.
  have hdir (v : F) : ∀ᵐ x ∂massMeasure T, ‖(τ x - polarDensity T x) v‖ₑ ≤ 0 := by
    refine TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le (k := 0)
      (locallyIntegrable_iff.2 fun K hK => ?_) measurable_const (fun _ _ => by simp)
      fun U _ ψ _ _ => ?_
    · exact ((hτ.sub hτ').integrableOn_isCompact hK).apply_continuousLinearMap v
    · set φ := postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) ψ
      have h0 : ∫ x, τ x (φ x) - polarDensity T x (φ x) ∂massMeasure T = 0 := by
        rw [integral_sub ((φ.integrable_bilin_subtype (NormedSpace.inclusionInDoubleDual ℝ F)
          hτ).congr (ae_of_all _ fun x => by simp)) (integrable_polarDensity_apply hT φ), ← h,
          ← apply_eq_integral_polarDensity hT, sub_self]
      have : ∫ x, inner ℝ (ψ x) ((τ x - polarDensity T x) v) ∂massMeasure T = 0 := by
        rw [← h0]
        congr with x
        simp [φ, mul_sub, mul_comm]
      rw [this]
      simp
  filter_upwards [ae_all_iff.2 fun i => hdir (Module.finBasis ℝ F i)] with x hx
  refine sub_eq_zero.1 (ContinuousLinearMap.coe_injective ((Module.finBasis ℝ F).ext fun i => ?_))
  simpa [sub_eq_zero] using hx i

end Spec

end Distribution
