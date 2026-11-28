/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.RadonNikodymProperty.Basic
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Normed.Module.Dual.Separable
import TauCeti.Analysis.Normed.Operator.Extend
import TauCeti.MeasureTheory.Function.StronglyMeasurable.ScalarTests
import TauCeti.MeasureTheory.VectorMeasure.WithDensity

/-!
# Separable dual spaces have the Radon–Nikodým property

Let `X` be a real normed space whose dual `X⋆` is separable. This file proves that `X⋆` has the
Radon–Nikodým property with respect to every σ-finite measure, and in particular has the intrinsic
Radon–Nikodým property. Thus separable duals such as `ℓ¹ = c₀⋆` admit Bochner densities for all
their vector measures of finite variation. In the duality theory of Bochner spaces this is the
hypothesis on `X⋆` under which functionals on `Lᵖ(μ; X)` are represented by `L^q(μ; X⋆)` densities.

The main step is a bounded version on a finite measure space: a vector measure `m` with
`‖m A‖ ≤ C ν(A)` has a strongly measurable density `φ` with `‖φ s‖ ≤ C` everywhere
(`TauCeti.exists_density_strongDual_of_norm_le`).

For each `x` in the predual, the scalar measure `A ↦ m A x` has a Radon–Nikodým derivative
`gₓ` with `|gₓ| ≤ C ‖x‖` almost everywhere, and `x ↦ gₓ` is additive up to null sets. The predual
is separable (`TauCeti.separableSpace_of_separableSpace_strongDual`), so a countable dense additive
subgroup gives a single null set off which `x ↦ gₓ s` is additive and bounded on that subgroup.
There it extends to a functional `φ s` of norm at most `C`. The evaluations of `φ` are measurable,
and the dual is separable, so Pettis' measurability theorem makes `φ` strongly measurable; it is
then a Bochner density of `m`.

A general vector measure `m` of finite variation is dominated by its variation `|m|`, so it has
a bounded density with respect to `|m|`; if `|m| ≪ μ` for a σ-finite `μ`, multiplying by
`d|m|/dμ` gives a density with respect to `μ`.

## Main declarations

* `TauCeti.exists_density_strongDual_of_norm_le`: bounded densities for dual-valued measures
  dominated by a finite measure.
* `TauCeti.hasRNPWith_strongDual_of_separable`: a separable dual space has the Radon–Nikodým
  property with respect to every σ-finite measure.
* `TauCeti.hasRNP_strongDual_of_separable`: a separable dual space has the Radon–Nikodým
  property.

## References

* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Mathematical Surveys 15, American Mathematical
  Society, 1977, Chapter III, §3, Theorem 1 (the Dunford–Pettis theorem).
* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, Theorem 1.3.21.
-/

public section

open MeasureTheory Filter Set TopologicalSpace Topology NormedSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {S X : Type*} [MeasurableSpace S] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A family `g x` of real functions that is additive in `x` and bounded by `C ‖x‖` up to null
sets, with exceptional sets depending on `x`, is determined almost everywhere by its values on a
dense set: a function `φ` with values in the dual whose evaluations agree with `g` on that set off
a single null set has evaluations `φ · x` equal to `g x` almost everywhere, for every `x`. -/
private theorem ae_eq_apply_of_denseRange {ν : Measure S} {g : X → S → ℝ}
    (hadd : ∀ x y, g (x + y) =ᵐ[ν] g x + g y) {C : ℝ}
    (hbound : ∀ x, ∀ᵐ s ∂ν, |g x s| ≤ C * ‖x‖) {ι : Type*} {e : ι → X} (he : DenseRange e)
    {φ : S → StrongDual ℝ X} (hφ : ∀ᵐ s ∂ν, ∀ i, φ s (e i) = g (e i) s) (x : X) :
    (fun s ↦ φ s x) =ᵐ[ν] g x := by
  obtain ⟨y, hy, hyx⟩ := mem_closure_iff_seq_limit.1 (he x)
  choose l hl using hy
  have hlx : Tendsto (fun n ↦ e (l n)) atTop (𝓝 x) := by simpa only [hl] using hyx
  filter_upwards [hφ, ae_all_iff.2 fun n ↦ hadd (e (l n)) (x - e (l n)),
    ae_all_iff.2 fun n ↦ hbound (x - e (l n))] with s hs h₁ h₂
  -- The bound controls `g x - g (e (l n))`, which tends to zero.
  have hdist (n : ℕ) : ‖φ s (e (l n)) - g x s‖ ≤ C * ‖x - e (l n)‖ := by
    have h := h₁ n
    rw [add_sub_cancel, Pi.add_apply] at h
    rw [hs, h, Real.norm_eq_abs, sub_add_cancel_left, abs_neg]
    exact h₂ n
  refine tendsto_nhds_unique (((φ s).continuous.tendsto x).comp hlx) ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) hdist ?_)
  simpa using ((tendsto_const_nhds (x := x)).sub hlx).norm.const_mul C

/-- On a separable space, a family `g x` of real functions that is additive in `x` and bounded by
`C ‖x‖` up to null sets, with exceptional sets depending on `x`, is the family of evaluations of a
single function with values in the dual ball of radius `C`. -/
private theorem exists_strongDual_ae_eq_apply [SeparableSpace X] {ν : Measure S}
    {g : X → S → ℝ} (hg : ∀ x, Measurable (g x)) (hadd : ∀ x y, g (x + y) =ᵐ[ν] g x + g y)
    {C : ℝ≥0} (hbound : ∀ x, ∀ᵐ s ∂ν, |g x s| ≤ C * ‖x‖) :
    ∃ φ : S → StrongDual ℝ X, (∀ x, Measurable fun s ↦ φ s x) ∧ (∀ s, ‖φ s‖ ≤ C) ∧
      ∀ x, (fun s ↦ φ s x) =ᵐ[ν] g x := by
  obtain ⟨u, hu⟩ := exists_dense_seq X
  -- The integer combinations of a dense sequence form a countable dense additive subgroup.
  let e : (ℕ →₀ ℤ) →ₗ[ℤ] X := (Finsupp.linearCombination ℤ u).toAddMonoidHom.toIntLinearMap
  have he : DenseRange e := hu.mono <| by
    rintro _ ⟨n, rfl⟩
    exact ⟨Finsupp.single n 1, by simp [e]⟩
  -- The set where additivity and the bound hold on that subgroup has full measure.
  let G : Set S := (⋂ l, ⋂ l', {s | g (e l + e l') s = g (e l) s + g (e l') s}) ∩
    ⋂ l, {s | |g (e l) s| ≤ C * ‖e l‖}
  have hGm : MeasurableSet G :=
    (MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_eq_fun (hg _) ((hg _).add (hg _))).inter
      (MeasurableSet.iInter fun _ ↦
        measurableSet_le (continuous_abs.measurable.comp (hg _)) measurable_const)
  have hG : ∀ᵐ s ∂ν, s ∈ G := by
    filter_upwards [ae_all_iff.2 fun l ↦ ae_all_iff.2 fun l' ↦ hadd (e l) (e l'),
      ae_all_iff.2 fun l ↦ hbound (e l)] with s h₁ h₂
    exact ⟨mem_iInter.2 fun l ↦ mem_iInter.2 fun l' ↦ h₁ l l', mem_iInter.2 h₂⟩
  -- On `G` the values on the subgroup are additive and bounded; off `G` they are set to zero.
  let F (s : S) : (ℕ →₀ ℤ) →+ ℝ := AddMonoidHom.mk' (fun l ↦ G.indicator (g (e l)) s)
    fun l l' ↦ by
      by_cases hs : s ∈ G
      · simp only [indicator_of_mem hs, map_add]
        exact mem_iInter.1 (mem_iInter.1 hs.1 l) l'
      · simp [hs]
  have hF (s : S) (l : ℕ →₀ ℤ) : ‖F s l‖ ≤ C * ‖e l‖ := by
    by_cases hs : s ∈ G
    · simpa [F, indicator_of_mem hs, Real.norm_eq_abs] using mem_iInter.1 hs.2 l
    · simp only [F, AddMonoidHom.mk'_apply, indicator_of_notMem hs, norm_zero]
      positivity
  -- Extend by continuity and upgrade the resulting continuous additive map to a real-linear one.
  let Φ (s : S) : X →L[ℤ] ℝ := (F s).toIntLinearMap.extendOfBound e C (hF s)
  let φ (s : S) : StrongDual ℝ X :=
    (Φ s).toLinearMap.toAddMonoidHom.toRealLinearMap (Φ s).continuous
  have hφe (s : S) (l : ℕ →₀ ℤ) : φ s (e l) = G.indicator (g (e l)) s :=
    LinearMap.extendOfBound_apply _ _ _ _ he l
  have hφle (s : S) (x : X) : ‖φ s x‖ ≤ C * ‖x‖ :=
    LinearMap.norm_extendOfBound_apply_le _ _ _ _ he x
  refine ⟨φ, fun x ↦ ?_, fun s ↦ (φ s).opNorm_le_bound C.coe_nonneg (hφle s),
    ae_eq_apply_of_denseRange hadd hbound he ?_⟩
  · -- Measurability holds on the dense subgroup and passes to pointwise limits.
    refine he.induction_on x (IsSeqClosed.isClosed fun y x hy hyx ↦ ?_) fun l ↦ ?_
    · exact measurable_of_tendsto_metrizable hy
        (tendsto_pi_nhds.2 fun s ↦ ((φ s).continuous.tendsto x).comp hyx)
    · simpa only [hφe] using (hg _).indicator hGm
  · filter_upwards [hG] with s hs l
    rw [hφe, indicator_of_mem hs]

/-- The evaluations `A ↦ m A x` of a dual-valued measure dominated by `C` times a finite measure
`ν` have Radon–Nikodým derivatives `g x` with respect to `ν`. They are additive in `x` and bounded
by `C ‖x‖` up to null sets, the exceptional sets depending on `x`. -/
private theorem exists_scalar_densities {ν : Measure S} [IsFiniteMeasure ν]
    {m : VectorMeasure S (StrongDual ℝ X)} {C : ℝ≥0}
    (hm : ∀ A, MeasurableSet A → ‖m A‖ ≤ C * ν.real A) :
    ∃ g : X → S → ℝ, (∀ x, Measurable (g x)) ∧
      (∀ x A, MeasurableSet A → ∫ s in A, g x s ∂ν = m A x) ∧
      (∀ x y, g (x + y) =ᵐ[ν] g x + g y) ∧ ∀ x, ∀ᵐ s ∂ν, |g x s| ≤ C * ‖x‖ := by
  have hmx (x : X) (A : Set S) (hA : MeasurableSet A) : ‖m A x‖ ≤ C * ‖x‖ * ν.real A :=
    calc ‖m A x‖ ≤ ‖m A‖ * ‖x‖ := (m A).le_opNorm x
      _ ≤ C * ν.real A * ‖x‖ := by gcongr; exact hm A hA
      _ = C * ‖x‖ * ν.real A := by ring
  let mx (x : X) : SignedMeasure S := VectorMeasure.mapRangeL (inclusionInDoubleDual ℝ X x) m
  have hmx_apply (x : X) (A : Set S) : mx x A = m A x := by
    rw [VectorMeasure.mapRangeL_apply, NormedSpace.dual_def]
  let g (x : X) : S → ℝ := (mx x).rnDeriv ν
  have hgi (x : X) : Integrable (g x) ν := SignedMeasure.integrable_rnDeriv _ _
  have hint (x : X) (A : Set S) (hA : MeasurableSet A) : ∫ s in A, g x s ∂ν = m A x := by
    -- The scalar measure is dominated by `C ‖x‖ ν`, hence absolutely continuous.
    have hac : (mx x).variation ≪ ν :=
      Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal (C * ‖x‖)) <|
        VectorMeasure.variation_le_of_forall_eNorm_le fun B hB ↦ by
          rw [smul_apply, smul_eq_mul, ← ofReal_norm, hmx_apply,
            ← ENNReal.ofReal_toReal (measure_ne_top ν B), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hmx x B hB)
    rw [← withDensityᵥ_apply (hgi x) hA,
      SignedMeasure.withDensityᵥ_rnDeriv_eq_of_variation _ _ hac, hmx_apply]
  have hadd (x y : X) : g (x + y) =ᵐ[ν] g x + g y :=
    (hgi _).ae_eq_of_forall_setIntegral_eq _ _ ((hgi x).add (hgi y)) fun A hA _ ↦ by
      simp only [Pi.add_apply]
      rw [integral_add (hgi x).integrableOn (hgi y).integrableOn, hint _ _ hA, hint _ _ hA,
        hint _ _ hA, map_add]
  have hle (y : X) : ∀ᵐ s ∂ν, g y s ≤ C * ‖y‖ := by
    refine ae_le_of_forall_setIntegral_le (hgi y) (integrable_const _) fun A hA _ ↦ ?_
    rw [hint y A hA, setIntegral_const, smul_eq_mul, mul_comm]
    exact (Real.le_norm_self _).trans (hmx y A hA)
  refine ⟨g, fun x ↦ SignedMeasure.measurable_rnDeriv _ _, hint, hadd, fun x ↦ ?_⟩
  -- The bound for `-x` and additivity give the lower bound.
  filter_upwards [hle x, hle (-x), hadd x (-x), hadd 0 0] with s h₁ h₂ h₃ h₄
  have h₀ : g 0 s = 0 := by simpa using h₄
  rw [add_neg_cancel, h₀, Pi.add_apply] at h₃
  rw [norm_neg] at h₂
  exact abs_le.2 ⟨by linarith, h₁⟩

/-- **Bounded densities in a separable dual.** Let `X` be a real normed space with separable
dual. A dual-valued vector measure dominated by `C` times a finite measure `ν`, in the sense that
`‖m A‖ ≤ C ν(A)` for every measurable `A`, has a `ν`-integrable density bounded by `C`
everywhere. -/
theorem exists_density_strongDual_of_norm_le [SeparableSpace (StrongDual ℝ X)] {ν : Measure S}
    [IsFiniteMeasure ν] {m : VectorMeasure S (StrongDual ℝ X)} {C : ℝ≥0}
    (hm : ∀ A, MeasurableSet A → ‖m A‖ ≤ C * ν.real A) :
    ∃ φ : S → StrongDual ℝ X, Integrable φ ν ∧ (∀ s, ‖φ s‖ ≤ C) ∧ m = ν.withDensityᵥ φ := by
  have : SeparableSpace X := separableSpace_of_separableSpace_strongDual ℝ X
  obtain ⟨g, hgm, hint, hadd, hbound⟩ := exists_scalar_densities hm
  obtain ⟨φ, hφm, hφC, hφg⟩ := exists_strongDual_ae_eq_apply hgm hadd hbound
  -- Pettis: the evaluations at the predual separate the points of the separable dual.
  have hφ : StronglyMeasurable φ := by
    borelize (StrongDual ℝ X)
    have hT := evalMeasurableSpace_eq_borel_of_separating (𝕜 := ℝ)
      (T := range (inclusionInDoubleDual ℝ X)) fun y hy ↦ by
        ext x
        simpa using hy _ ⟨x, rfl⟩
    have h : Measurable[_, evalMeasurableSpace (range (inclusionInDoubleDual ℝ X))] φ :=
      measurable_evalMeasurableSpace_iff.2 fun _ ⟨x, hx⟩ ↦ by simpa [← hx] using hφm x
    exact (hT ▸ h).stronglyMeasurable
  have hφi : Integrable φ ν := .of_bound hφ.aestronglyMeasurable C (ae_of_all _ hφC)
  refine ⟨φ, hφi, hφC, ?_⟩
  ext A hA : 1
  rw [withDensityᵥ_apply hφi hA]
  ext x
  rw [ContinuousLinearMap.integral_apply hφi.integrableOn x, ← hint x A hA]
  exact setIntegral_congr_ae hA ((hφg x).mono fun s hs _ ↦ hs.symm)

/-- **Separable dual spaces have the Radon–Nikodým property** with respect to every σ-finite
measure. -/
theorem hasRNPWith_strongDual_of_separable [SeparableSpace (StrongDual ℝ X)] (μ : Measure S)
    [SigmaFinite μ] : HasRNPWith (StrongDual ℝ X) μ := by
  refine hasRNPWith_def.2 fun m _ hac ↦ ?_
  -- A vector measure is dominated by its variation, so it has a density with respect to it.
  obtain ⟨φ, hφ, -, hm⟩ := exists_density_strongDual_of_norm_le (ν := m.variation) (C := 1)
    fun A _ ↦ by simpa using VectorMeasure.norm_measure_le_variation (μ := m) (E := A)
  exact ⟨_, (integrable_rnDeriv_smul_iff hac).2 hφ,
    ((withDensityᵥ_rnDeriv_smul hac hφ).trans hm.symm).symm⟩

/-- **Separable dual spaces have the Radon–Nikodým property.** -/
theorem hasRNP_strongDual_of_separable [SeparableSpace (StrongDual ℝ X)] :
    HasRNP (StrongDual ℝ X) :=
  hasRNP_def.2 (hasRNPWith_strongDual_of_separable _)

end TauCeti
