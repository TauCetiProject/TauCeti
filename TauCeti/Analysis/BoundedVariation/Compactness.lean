/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
import TauCeti.Analysis.BoundedVariation.Multiplication
import TauCeti.Analysis.BoundedVariation.Translation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.Lp.Subsequence
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Integral.Lebesgue.Cutoff

/-!
# Compactness of families of bounded variation

Let `Ω` be an open set of a finite-dimensional real inner product space `E` with an additive Haar
measure. This file proves that a family of functions bounded in `L¹(Ω)` and in total variation on
`Ω` is relatively compact in `L¹_loc(Ω)`: its restrictions to any compact `K ⊆ Ω` form a totally
bounded subset of `L¹(K)`. This is the compactness theorem for functions of bounded variation
used to extract convergent subsequences in the direct method and in blow-up arguments for sets of
finite perimeter; lower semicontinuity of the variation
(`TauCeti.totalVariationOn_le_liminf`) then controls the variation of the limit.

The proof follows the Fréchet–Kolmogorov criterion
(`TauCeti.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`), whose hypotheses
come from two estimates of independent interest.

* **The translation estimate.** If the segments `x + [0, 1] h` starting in `V` lie in `Ω`, then
  `∫_V |u (x + h) - u x| dx ≤ ‖h‖ |Du|(Ω)`. By the duality `∫_V |w| = sup ∫ w g` over scalar test
  functions `|g| ≤ 1` on `V`, it suffices to bound `∫ (u (x + h) - u x) g x dx`. Translation
  invariance turns this into `∫ u (g (· - h) - g)`, and `g (y - h) - g y = div ψ y` for the test
  vector field `ψ y = -(∫₀¹ g (y - t h) dt) h`, of norm at most `‖h‖`
  (`TauCeti.setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn`, in
  `TauCeti.Analysis.BoundedVariation.Translation`).
* **Multiplication by a smooth cutoff.** For smooth `χ` with `|χ| ≤ c`,
  `|D(χ u)|(Ω') ≤ c |Du|(Ω) + ∫_{Ω'} ‖Dχ‖ |u|` whenever `tsupport χ ∩ Ω' ⊆ Ω`
  (`TauCeti.totalVariationOn_mul_le`, in `TauCeti.Analysis.BoundedVariation.Multiplication`).

A cutoff equal to one near `K` and supported in `Ω` turns the family into one supported in a fixed
compact set, bounded in `L¹` and in variation on the whole space, to which the translation
estimate and the Fréchet–Kolmogorov criterion apply.

A diagonal argument over a compact exhaustion of `Ω`
(`TauCeti.exists_subseq_tendsto_eLpNorm_sub_of_isCompact_closure`) turns this into sequential
compactness: a sequence locally bounded in `L¹` and in variation on `Ω` has a subsequence
converging in `L¹_loc(Ω)`. For indicators, the limit is again an indicator up to a null set, so
a sequence of sets with locally bounded perimeter in `Ω` has a subsequence converging locally in
measure to a measurable set, whose perimeter is controlled by `TauCeti.perimeter_le_liminf`. No
bound on the volumes is needed, as in the blow-up arguments for sets of finite perimeter.

When the global inclusion `BV.toL1CLM : BV μ Ω →L[ℝ] (E →₁[μ.restrict Ω] ℝ)` is a compact operator
(for an arbitrary measure `μ` and open set `Ω`), the same compactness conclusions hold globally on
`Ω`: norm-bounded sequences in `BV μ Ω` have `L¹(Ω)`-convergent subsequences respecting the norm
bound and lower semicontinuity of variation, bounded families are totally bounded and relatively
compact in `L¹(Ω)`, and on finite-measure domains sequences of sets with uniformly bounded
perimeter converge globally in measure on `Ω` along a subsequence. Compactness of `BV.toL1CLM` is
also invariant under positive scalar rescaling of the measure `μ`.

## Main results

* `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le` and
  `TauCeti.isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le`: a family bounded in
  `L¹(Ω)` and in variation on `Ω` is totally bounded, and relatively compact, in `L¹(K)` for every
  compact `K ⊆ Ω`.
* `TauCeti.exists_subseq_tendsto_setLIntegral_enorm_sub_of_totalVariationOn_le`: a sequence locally
  bounded in `L¹` and in variation on `Ω` has a subsequence converging in `L¹_loc(Ω)`.
* `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le`: compactness for sets of
  locally finite perimeter.
* `TauCeti.BV.isCompactOperator_toL1CLM_smul_measure` and
  `TauCeti.BV.isCompactOperator_toL1CLM_smul_measure_iff`: invariance of compactness of
  `BV.toL1CLM` under positive rescaling of the measure.
* `TauCeti.BV.exists_subseq_tendsto_toL1_of_isCompactOperator`,
  `TauCeti.totallyBounded_of_isCompactOperator_toL1CLM`,
  `TauCeti.isCompact_closure_of_isCompactOperator_toL1CLM`,
  `TauCeti.exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM`, and
  `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_isCompactOperator_toL1CLM`: global
  compactness consequences of `IsCompactOperator BV.toL1CLM`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.23 and Remark 3.24.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2,
  Theorem 5.5, and §5.2.3, Theorem 4.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 12.26 and
  Corollary 12.27.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Filter Function Metric Set TopologicalSpace TestFunction
open scoped ENNReal NNReal ContDiff Distributions Topology symmDiff

section Haar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω V : Opens E}
  {u : E → ℝ} {h : E}

/-! ### Compactness -/

variable {K : Set E} {S : Set (E → ℝ)} {M : ℝ≥0∞}

/-- **The Fréchet--Kolmogorov step.** A family in `L¹(μ)` vanishing almost everywhere off a bounded
set `L`, bounded in `L¹` and in total variation on the whole space, is totally bounded in `L¹(μ)`:
the translation estimate gives the equicontinuity under translations. -/
theorem totallyBounded_of_lintegral_le_of_totalVariationOn_le {S : Set (Lp ℝ 1 μ)} {L : Set E}
    {B : ℝ≥0∞} (hL : Bornology.IsBounded L) (hM : M ≠ ⊤) (hB : B ≠ ⊤)
    (hsupp : ∀ f ∈ S, ∀ᵐ x ∂μ, x ∉ L → f x = 0)
    (hnorm : ∀ f ∈ S, ∫⁻ x, ‖f x‖ₑ ∂μ ≤ M)
    (hvar : ∀ f ∈ S, totalVariationOn μ ⊤ f ≤ B) :
    TotallyBounded S := by
  refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl ENNReal.one_ne_top
    hL hsupp hM (fun f hf => ?_) fun ε hε => ?_
  · rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f)]
    exact hnorm f hf
  · obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hB hε.ne'
    refine ⟨δ, by exact_mod_cast hδ, fun f hf h hh => ?_⟩
    have hint := L1.integrable_coeFn f
    rw [eLpNorm_one_eq_lintegral_eNorm (f := fun x => f (x + h) - f x)
      ((hint.comp_add_right h).sub hint).aestronglyMeasurable]
    refine (lintegral_enorm_comp_add_sub_le_mul_totalVariationOn hint.locallyIntegrable h).trans ?_
    refine (mul_le_mul' ?_ (hvar f hf)).trans hδε.le
    exact eNorm_le_coe.mpr (by exact_mod_cast hh.le)

/-- **Compactness of families of bounded variation.** Let `S` be a family of functions on `Ω`
that is bounded in `L¹(Ω)` and in variation on `Ω`: `∫_Ω |u| ≤ M` and `|Du|(Ω) ≤ M` for every
`u ∈ S`, with `M < ∞`. Then for every compact `K ⊆ Ω` the restrictions to `K` of the members of
`S` form a totally bounded subset of `L¹(K)`.

Since only a neighbourhood of `K` enters, a family that is merely locally bounded in `L¹` and in
variation is totally bounded in `L¹(K)` for every compact `K ⊆ Ω`: apply this to an open
neighbourhood of `K` with compact closure in `Ω`. -/
theorem totallyBounded_of_setLIntegral_le_of_totalVariationOn_le (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hM : M ≠ ⊤) (hmeas : ∀ u ∈ S, AEStronglyMeasurable u (μ.restrict Ω))
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M) (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    TotallyBounded {f : Lp ℝ 1 (μ.restrict K) | ∃ u ∈ S, f =ᵐ[μ.restrict K] u} := by
  -- Multiply by a smooth cutoff `χ` equal to one near `K` and supported in `Ω`.
  obtain ⟨χ, hχ, hχ01, hχK, hχc, hχΩ⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one Ω.isOpen hKΩ
  obtain ⟨C, hC⟩ := (hχ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hχc.fderiv ℝ).norm
  have hχ1 (x : E) : |χ x| ≤ 1 := by
    obtain ⟨h0, h1⟩ := hχ01 (mem_range_self x)
    rwa [abs_of_nonneg h0]
  -- The cut-off functions `χ u` are integrable, and bounded in `L¹` and in variation on the
  -- whole space.
  have hnorm (u : E → ℝ) : ∫⁻ x, ‖(χ * u) x‖ₑ ∂μ ≤ ∫⁻ x in Ω, ‖u x‖ₑ ∂μ :=
    lintegral_enorm_mul_le_setLIntegral_of_support_subset hχ1 ((subset_tsupport χ).trans hχΩ) u
  have huΩ (u : E → ℝ) (hu : u ∈ S) : IntegrableOn u Ω μ :=
    ⟨hmeas u hu, (hbdd u hu).trans_lt hM.lt_top⟩
  have hint (u : E → ℝ) (hu : u ∈ S) : Integrable (χ * u) μ :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero ((huΩ u hu).bdd_mul
      hχ.continuous.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hχ1 x))
      fun x hx => by simp [image_eq_zero_of_notMem_tsupport fun hmem => hx (hχΩ hmem)]
  have hB : M + ENNReal.ofReal C * M ≠ ⊤ := by finiteness
  have hvarχ (u : E → ℝ) (hu : u ∈ S) :
      totalVariationOn μ ⊤ (χ * u) ≤ M + ENNReal.ofReal C * M :=
    (totalVariationOn_top_mul_le hχ hχ1 hχΩ (fun x => hC (mem_range_self x))
      (huΩ u hu).locallyIntegrableOn).trans (by gcongr <;> simp [hvar u hu, hbdd u hu])
  -- The Fréchet--Kolmogorov criterion applies to the family of the `χ u` in `L¹`.
  have hT := totallyBounded_of_lintegral_le_of_totalVariationOn_le
    (S := {f : Lp ℝ 1 μ | ∃ u ∈ S, f =ᵐ[μ] χ * u}) hχc.isCompact.isBounded hM hB
    (fun f ⟨u, _, hf⟩ => by
      filter_upwards [hf] with x hx hxL
      simp [hx, image_eq_zero_of_notMem_tsupport hxL])
    (fun f ⟨u, hu, hf⟩ => by
      refine le_trans (le_of_eq (lintegral_congr_ae ?_)) ((hnorm u).trans (hbdd u hu))
      filter_upwards [hf] with x hx
      rw [hx])
    fun f ⟨u, hu, hf⟩ => by
      rw [totalVariationOn_congr_ae (ae_restrict_of_ae hf)]
      exact hvarχ u hu
  exact totallyBounded_restrict_of_forall_eqOn (g := (χ * ·)) hK.measurableSet
    (fun u hu => memLp_one_iff_integrable.2 (hint u hu))
    (fun u _ x hx => by
      rw [Pi.mul_apply, (hχK x hx).self_of_nhds, one_mul]) hT

/-- **Compactness of families of bounded variation**, in the form of a compact embedding: under
the hypotheses of `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le`, the closure in
`L¹(K)` of the restrictions to `K` of the members of `S` is compact. -/
theorem isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hM : M ≠ ⊤) (hmeas : ∀ u ∈ S, AEStronglyMeasurable u (μ.restrict Ω))
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M) (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    IsCompact (closure {f : Lp ℝ 1 (μ.restrict K) | ∃ u ∈ S, f =ᵐ[μ.restrict K] u}) :=
  (totallyBounded_of_setLIntegral_le_of_totalVariationOn_le hK hKΩ hM hmeas hbdd
    hvar).closure.isCompact_of_isClosed isClosed_closure

/-! ### Sequential compactness in `L¹_loc` -/

/-- **Sequential compactness of sequences of locally bounded variation.** Let `u n` be a sequence
of functions that is locally bounded in `L¹` and in variation on `Ω`: every compact `K ⊆ Ω` has an
open neighbourhood `U ⊆ Ω` on which `∫_U |u n|` and `|D(u n)|(U)` are bounded uniformly in `n`.
Then a subsequence converges in `L¹_loc(Ω)` to a locally integrable function `v`: for every
compact `K ⊆ Ω`, `∫_K |u (φ j) - v| → 0`.

The variation of the limit is controlled by lower semicontinuity
(`TauCeti.totalVariationOn_le_liminf`). -/
theorem exists_subseq_tendsto_setLIntegral_enorm_sub_of_totalVariationOn_le {u : ℕ → E → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (u n) (μ.restrict Ω))
    (hbdd : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ U ≤ Ω ∧ ∃ M : ℝ≥0,
      ∀ n, ∫⁻ x in U, ‖u n x‖ₑ ∂μ ≤ M ∧ totalVariationOn μ U (u n) ≤ M) :
    ∃ v : E → ℝ, LocallyIntegrableOn v Ω μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ Ω →
        Tendsto (fun j => ∫⁻ x in K, ‖u (φ j) x - v x‖ₑ ∂μ) atTop (𝓝 0) := by
  have hint (n : ℕ) (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      MemLp (u n) 1 (μ.restrict K) := by
    obtain ⟨U, hKU, hUΩ, M, hb⟩ := hbdd K hK hKΩ
    refine memLp_one_iff_integrable.2 (IntegrableOn.mono_set ?_ hKU)
    exact ⟨(hmeas n).mono_measure (Measure.restrict_mono hUΩ le_rfl),
      (hb n).1.trans_lt ENNReal.coe_lt_top⟩
  -- On each compact `K ⊆ Ω` the sequence is relatively compact in `L¹(K)`.
  obtain ⟨v, hv, φ, hφ, hlim⟩ := exists_subseq_tendsto_eLpNorm_sub_of_isCompact_closure Ω.isOpen
    hint fun K hK hKΩ => by
      obtain ⟨U, hKU, hUΩ, M, hb⟩ := hbdd K hK hKΩ
      simpa using isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le (S := range u)
        (M := M) hK hKU ENNReal.coe_ne_top
        (by rintro _ ⟨n, rfl⟩; exact (hmeas n).mono_measure (Measure.restrict_mono hUΩ le_rfl))
        (by rintro _ ⟨n, rfl⟩; exact (hb n).1) (by rintro _ ⟨n, rfl⟩; exact (hb n).2)
  refine ⟨v, (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun K hKΩ hK =>
    memLp_one_iff_integrable.1 (hv K hK hKΩ), φ, hφ, fun K hK hKΩ =>
      (hlim K hK hKΩ).congr fun j => ?_⟩
  rw [eLpNorm_one_eq_lintegral_eNorm ((hint _ K hK hKΩ).aestronglyMeasurable.sub
    (hv K hK hKΩ).aestronglyMeasurable)]
  simp only [Pi.sub_apply]

/-- **Compactness for sets of locally finite perimeter.** Let `s n` be a sequence of
null-measurable sets with locally bounded perimeter in `Ω`: every compact `K ⊆ Ω` has an open
neighbourhood `U ⊆ Ω` with `P(s n; U)` bounded uniformly in `n`. Then a subsequence converges
locally in measure in `Ω` to a measurable set `t`: `μ ((s (φ j) ∆ t) ∩ K) → 0` for every compact
`K ⊆ Ω`. No bound on the volumes of the sets is needed.

By lower semicontinuity (`TauCeti.perimeter_le_liminf`), `P(t; U) ≤ liminf P(s (φ j); U)` for
every open `U ⊆ Ω`, so `t` has locally finite perimeter in `Ω`. -/
theorem exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le {s : ℕ → Set E}
    (hs : ∀ n, NullMeasurableSet (s n) μ)
    (hP : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ U ≤ Ω ∧ ∃ M : ℝ≥0,
      ∀ n, perimeter μ U (s n) ≤ M) :
    ∃ t, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun j => μ ((s (φ j) ∆ t) ∩ K)) atTop (𝓝 0) := by
  -- The indicators are locally bounded in `L¹`, since `μ` is locally finite.
  have hbdd (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ U ≤ Ω ∧ ∃ M : ℝ≥0,
        ∀ n, ∫⁻ x in U, ‖(s n).indicator (1 : E → ℝ) x‖ₑ ∂μ ≤ M ∧
          totalVariationOn μ U ((s n).indicator 1) ≤ M := by
    obtain ⟨U, hKU, hUΩ, M, hM⟩ := hP K hK hKΩ
    obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
    refine ⟨⟨V, hV⟩, hKV, (subset_closure.trans hVU).trans hUΩ,
      M + (μ (closure V)).toNNReal, fun n => ⟨?_, ?_⟩⟩
    · calc ∫⁻ x in V, ‖(s n).indicator (1 : E → ℝ) x‖ₑ ∂μ ≤ ∫⁻ _ in V, 1 ∂μ :=
            lintegral_mono fun x => (eNorm_indicator_le_eNorm_self _ x).trans (by simp)
        _ ≤ (μ (closure V)).toNNReal := by
            rw [setLIntegral_one, ENNReal.coe_toNNReal hVc.measure_lt_top.ne]
            exact measure_mono subset_closure
        _ ≤ _ := by gcongr; exact le_add_self
    · rw [← perimeter_def]
      calc perimeter μ ⟨V, hV⟩ (s n) ≤ perimeter μ U (s n) :=
            perimeter_mono (Ω' := ⟨V, hV⟩) (Ω := U) (subset_closure.trans hVU)
        _ ≤ _ := (hM n).trans (by gcongr; exact le_self_add)
  obtain ⟨v, hv, φ, hφ, hlim⟩ := exists_subseq_tendsto_setLIntegral_enorm_sub_of_totalVariationOn_le
    (fun n => (aestronglyMeasurable_const.indicator₀ (hs n)).restrict) hbdd
  -- The limit is close to the indicator of the set `t` where a measurable representative `w` of
  -- `v` exceeds `1/2`, since `|1_s - 1_t| ≤ 2 |1_s - w|` pointwise.
  let w := hv.aestronglyMeasurable.mk v
  have hw : Measurable w := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  refine ⟨{x | 1 / 2 < w x}, measurableSet_lt measurable_const hw, φ, hφ, fun K hK hKΩ => ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.const_mul (a := 2) (hlim K hK hKΩ) (.inr (by simp)))
    (fun _ => zero_le) fun j => ?_
  have hpt (x : E) : (s (φ j) ∆ {x | 1 / 2 < w x}).indicator 1 x ≤
      2 * ‖(s (φ j)).indicator (1 : E → ℝ) x - w x‖ₑ := by
    have key {r : ℝ} (hr : 1 / 2 ≤ |r|) : (1 : ℝ≥0∞) ≤ 2 * ‖r‖ₑ := by
      rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ENNReal.one_le_ofReal]
      linarith
    by_cases h₁ : x ∈ s (φ j) <;> by_cases h₂ : 1 / 2 < w x
    · rw [indicator_of_notMem (by simp [mem_symmDiff, h₁]; linarith)]
      exact zero_le
    · rw [indicator_of_mem (by simp [mem_symmDiff, h₁]; linarith), indicator_of_mem h₁,
        Pi.one_apply, Pi.one_apply]
      exact key (by rw [abs_of_nonneg (by linarith)]; linarith)
    · rw [indicator_of_mem (by simp [mem_symmDiff, h₁]; linarith), indicator_of_notMem h₁,
        Pi.one_apply]
      exact key (by rw [zero_sub, abs_neg, abs_of_pos (by linarith)]; linarith)
    · rw [indicator_of_notMem (by simp [mem_symmDiff, h₁]; linarith)]
      exact zero_le
  calc μ ((s (φ j) ∆ {x | 1 / 2 < w x}) ∩ K)
      = ∫⁻ x in K, (s (φ j) ∆ {x | 1 / 2 < w x}).indicator 1 x ∂μ := by
        rw [lintegral_indicator_one₀ (((hs _).symmDiff
          (measurableSet_lt measurable_const hw).nullMeasurableSet).mono Measure.restrict_le_self),
          Measure.restrict_apply' hK.isClosed.measurableSet]
    _ ≤ ∫⁻ x in K, 2 * ‖(s (φ j)).indicator (1 : E → ℝ) x - v x‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hKΩ
          hv.aestronglyMeasurable.ae_eq_mk] with x hx
        rw [hx]
        exact hpt x
    _ = 2 * ∫⁻ x in K, ‖(s (φ j)).indicator (1 : E → ℝ) x - v x‖ₑ ∂μ :=
        lintegral_const_mul' _ _ (by simp)

end Haar

section CompactOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}

/-- View a `BV (c • μ) Ω` class as a `BV μ Ω` class for a nonzero scalar `c : ℝ≥0`. -/
private def BV.ofSmulMeasureAux {c : ℝ≥0} (hc : c ≠ 0) (u : BV (c • μ) Ω) : BV μ Ω :=
  BV.ofFunction u <| memBV_iff.mpr
    ⟨by simpa only [IntegrableOn, Measure.restrict_smul, inv_smul_smul₀ hc] using
        u.integrableOn.smul_measure_nnreal (c := c⁻¹),
      lt_top_iff_ne_top.mpr fun h => u.totalVariationOn_lt_top.ne (by simp [h, hc])⟩

/-- Transporting `BV.ofSmulMeasureAux hc u` back to `L¹((c • μ).restrict Ω)` via
`Lp.LpToLpOfMeasureLeSMul` recovers `u.toL1`. -/
private theorem LpToLpOfMeasureLeSMul_toL1_ofSmulMeasureAux {c : ℝ≥0} (hc : c ≠ 0)
    (hle : (c • μ).restrict Ω ≤ (c : ℝ≥0∞) • μ.restrict Ω) (u : BV (c • μ) Ω) :
    Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hle (BV.ofSmulMeasureAux hc u).toL1 = u.toL1 :=
  Lp.ext <| (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hle _).trans <|
    (Measure.absolutelyContinuous_of_le_smul hle).ae_eq <|
      BV.coeFn_ofFunction (μ := μ) (Ω := Ω) (u : E → ℝ) _

/-- The `BV (c • μ) Ω` norm is `c` times the `BV μ Ω` norm of `BV.ofSmulMeasureAux hc u`. -/
private theorem norm_eq_mul_norm_ofSmulMeasureAux {c : ℝ≥0} (hc : c ≠ 0) (u : BV (c • μ) Ω) :
    ‖u‖ = (c : ℝ) * ‖BV.ofSmulMeasureAux hc u‖ := by
  have hL1 (f : E → ℝ) : eLpNorm f 1 ((c • μ).restrict Ω) =
      (c : ℝ≥0∞) * eLpNorm f 1 (μ.restrict Ω) := by
    rw [Measure.restrict_smul, ENNReal.smul_def, eLpNorm_one_smul_measure]
  rw [BV.ofSmulMeasureAux, BV.norm_def, BV.norm_def, Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (BV.coeFn_ofFunction (μ := μ) (Ω := Ω) u _), hL1 u,
    totalVariationOn_smul_measure, BV.totalVariationOn_ofFunction, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal, mul_add]

/-- Scalar rescaling of the ambient measure by `c : ℝ≥0` preserves compactness of `BV.toL1CLM`. -/
theorem BV.isCompactOperator_toL1CLM_smul_measure (c : ℝ≥0)
    (hcpt : IsCompactOperator (BV.toL1CLM (μ := μ) (Ω := Ω))) :
    IsCompactOperator (BV.toL1CLM (μ := c • μ) (Ω := Ω)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]
    suffices (BV.toL1CLM (μ := 0) (Ω := Ω) : BV (0 : Measure E) Ω → _) = 0 from
      this ▸ isCompactOperator_zero
    ext1 u
    exact Lp.ext (ae_restrict_of_ae (ae_zero.symm ▸ Filter.eventually_bot))
  have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  have hle : (c • μ).restrict Ω ≤ (c : ℝ≥0∞) • μ.restrict Ω :=
    le_of_eq (by rw [Measure.restrict_smul, ENNReal.smul_def])
  let T : (E →₁[μ.restrict Ω] ℝ) →L[ℝ] (E →₁[(c • μ).restrict Ω] ℝ) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hle
  refine (isCompactOperator_iff_totallyBounded_image_closedBall _ zero_lt_one).mpr ?_
  refine ((hcpt.totallyBounded_image_closedBall (c : ℝ)⁻¹).image T.uniformContinuous).subset ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨(BV.ofSmulMeasureAux hc u).toL1,
    ⟨BV.ofSmulMeasureAux hc u, mem_closedBall_zero_iff.mpr ?_, BV.toL1CLM_apply _⟩,
    (LpToLpOfMeasureLeSMul_toL1_ofSmulMeasureAux hc hle u).trans (BV.toL1CLM_apply u).symm⟩
  rw [inv_eq_one_div, le_div_iff₀' hcpos, ← norm_eq_mul_norm_ofSmulMeasureAux hc u]
  exact mem_closedBall_zero_iff.mp hu

/-- **Invariance of compactness of `BV.toL1CLM` under positive rescaling of the measure.** -/
theorem BV.isCompactOperator_toL1CLM_smul_measure_iff {c : ℝ≥0} (hc : c ≠ 0) :
    IsCompactOperator (BV.toL1CLM (μ := c • μ) (Ω := Ω)) ↔
      IsCompactOperator (BV.toL1CLM (μ := μ) (Ω := Ω)) :=
  ⟨fun h => by
      rw [← inv_smul_smul₀ hc μ]
      exact BV.isCompactOperator_toL1CLM_smul_measure c⁻¹ h,
    BV.isCompactOperator_toL1CLM_smul_measure c⟩

/-- **Sequential `L¹` compactness for bounded sequences in `BV`.** If `BV.toL1CLM` is a compact
operator on `Ω`, every sequence `u` in `BV μ Ω` with `‖u n‖ ≤ R` has a subsequence whose `L¹(Ω)`
classes converge to `v.toL1` for some `v : BV μ Ω` satisfying lower semicontinuity of total
variation and `‖v‖ ≤ R`. -/
theorem BV.exists_subseq_tendsto_toL1_of_isCompactOperator
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {u : ℕ → BV μ Ω} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : BV μ Ω) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => (u (φ k)).toL1) atTop (𝓝 v.toL1) ∧
      totalVariationOn μ Ω v ≤ liminf (fun k => totalVariationOn μ Ω (u (φ k))) atTop ∧
      ‖v‖ ≤ R := by
  obtain ⟨w, φ, hφ, hw⟩ := hcpt.exists_subseq_tendsto hu
  have hw' : Tendsto (fun k => (u (φ k)).toL1) atTop (𝓝 w) := by
    simpa only [ContinuousLinearMap.coe_coe, BV.toL1CLM_apply] using hw
  have hw_norm : ‖w‖ ≤ R :=
    le_of_tendsto hw'.norm (.of_forall fun k => (BV.norm_toL1_le _).trans (hu _))
  have hstep (k : ℕ) :
      totalVariationOn μ Ω (u (φ k)) ≤ ENNReal.ofReal (R - ‖(u (φ k)).toL1‖) := by
    have hsub : 0 ≤ R - ‖(u (φ k)).toL1‖ :=
      sub_nonneg.mpr ((BV.norm_toL1_le _).trans (hu _))
    refine (ENNReal.le_ofReal_iff_toReal_le (u (φ k)).totalVariationOn_lt_top.ne hsub).mpr ?_
    linarith [BV.norm_def (u (φ k)), hu (φ k)]
  have hlim :
      Tendsto (fun k => ENNReal.ofReal (R - ‖(u (φ k)).toL1‖)) atTop
        (𝓝 (ENNReal.ofReal (R - ‖w‖))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hw'.norm)
  have hlsc : totalVariationOn μ Ω w ≤ liminf (fun k => totalVariationOn μ Ω (u (φ k))) atTop :=
    totalVariationOn_le_liminf_of_tendsto_L1 hw'
  have htvR : totalVariationOn μ Ω w ≤ ENNReal.ofReal (R - ‖w‖) :=
    hlsc.trans ((liminf_le_liminf (.of_forall hstep)).trans_eq hlim.liminf_eq)
  have hwBV : MemBV μ Ω w :=
    memBV_iff.mpr ⟨L1.integrable_coeFn w, htvR.trans_lt ENNReal.ofReal_lt_top⟩
  let v : BV μ Ω := BV.ofFunction w hwBV
  have hv_toL1 : v.toL1 = w :=
    (BV.toL1_ofFunction w hwBV).trans (Integrable.toL1_coeFn w (L1.integrable_coeFn w))
  refine ⟨v, φ, hφ, hv_toL1.symm ▸ hw', ?_, ?_⟩
  · rwa [BV.totalVariationOn_ofFunction]
  · rw [BV.norm_def, hv_toL1]
    linarith [ENNReal.toReal_le_of_le_ofReal (sub_nonneg.mpr hw_norm) htvR]

/-- **Total boundedness in `L¹(Ω)` from compactness of `BV.toL1CLM`.** If `BV.toL1CLM` is a compact
operator on `Ω`, any family `S` of functions on `Ω` with `∫_Ω |u| ≤ M` and `|Du|(Ω) ≤ M` (`M < ∞`)
gives a totally bounded set of classes in `L¹(Ω)`. Unlike the local criterion on compact subsets,
no separate measurability assumption on `S` is required: any `f : Lp ℝ 1 (μ.restrict Ω)` agreeing
almost everywhere with `u ∈ S` is already measurable. -/
theorem totallyBounded_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {S : Set (E → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    TotallyBounded {f : Lp ℝ 1 (μ.restrict Ω) | ∃ u ∈ S, f =ᵐ[μ.restrict Ω] u} := by
  refine (hcpt.totallyBounded_image_closedBall (2 * M.toReal)).subset ?_
  rintro f ⟨u, hu, hf⟩
  have hfe : ‖f‖ₑ ≤ M := by
    rw [Lp.eNorm_def, eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f),
      lintegral_congr_ae (hf.mono fun x hx => by rw [hx])]
    exact hbdd u hu
  have hftv : totalVariationOn μ Ω f ≤ M :=
    (totalVariationOn_congr_ae hf).trans_le (hvar u hu)
  have hfBV : MemBV μ Ω f := memBV_iff.mpr ⟨L1.integrable_coeFn f, hftv.trans_lt hM.lt_top⟩
  refine ⟨BV.ofFunction f hfBV, mem_closedBall_zero_iff.mpr ?_, ?_⟩
  · have h₁ : ‖(BV.ofFunction f hfBV).toL1‖ ≤ M.toReal := by
      rw [BV.toL1_ofFunction, Integrable.toL1_coeFn f (L1.integrable_coeFn f), ← toReal_eNorm]
      exact ENNReal.toReal_mono hM hfe
    have h₂ : (totalVariationOn μ Ω (BV.ofFunction f hfBV)).toReal ≤ M.toReal := by
      rw [BV.totalVariationOn_ofFunction]
      exact ENNReal.toReal_mono hM hftv
    rw [BV.norm_def]
    linarith
  · rw [ContinuousLinearMap.coe_coe, BV.toL1CLM_apply, BV.toL1_ofFunction]
    exact Integrable.toL1_coeFn f (L1.integrable_coeFn f)

/-- **Relative compactness in `L¹(Ω)` from compactness of `BV.toL1CLM`.** Under the hypotheses of
`TauCeti.totallyBounded_of_isCompactOperator_toL1CLM`, the closure in `L¹(Ω)` of the classes of
members of `S` is compact. -/
theorem isCompact_closure_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {S : Set (E → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    IsCompact (closure {f : Lp ℝ 1 (μ.restrict Ω) | ∃ u ∈ S, f =ᵐ[μ.restrict Ω] u}) :=
  (totallyBounded_of_isCompactOperator_toL1CLM hcpt hM hbdd hvar).closure.isCompact_of_isClosed
    isClosed_closure

/-- **Global `L¹(Ω)` sequential compactness of unbundled BV sequences.** If `BV.toL1CLM` is a
compact operator on `Ω` and `u : ℕ → E → ℝ` is a sequence of `μ.restrict Ω`-almost-everywhere
measurable functions bounded in `L¹(Ω)` and in total variation on `Ω` by `M < ∞`, then a
subsequence converges globally in `L¹(Ω)` to a function `v` belonging to `MemBV μ Ω`, with
`totalVariationOn μ Ω v ≤ liminf_j totalVariationOn μ Ω (u (φ j))`. -/
theorem exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {u : ℕ → E → ℝ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hmeas : ∀ n, AEStronglyMeasurable (u n) (μ.restrict Ω))
    (hbdd : ∀ n, ∫⁻ x in Ω, ‖u n x‖ₑ ∂μ ≤ M)
    (hvar : ∀ n, totalVariationOn μ Ω (u n) ≤ M) :
    ∃ v : E → ℝ, MemBV μ Ω v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => ∫⁻ x in Ω, ‖u (φ j) x - v x‖ₑ ∂μ) atTop (𝓝 0) ∧
      totalVariationOn μ Ω v ≤ liminf (fun j => totalVariationOn μ Ω (u (φ j))) atTop := by
  have huBV (n : ℕ) : MemBV μ Ω (u n) :=
    memBV_iff.mpr ⟨⟨hmeas n, (hbdd n).trans_lt hM.lt_top⟩, (hvar n).trans_lt hM.lt_top⟩
  let b : ℕ → BV μ Ω := fun n => BV.ofFunction (u n) (huBV n)
  have hb_norm (n : ℕ) : ‖b n‖ ≤ 2 * M.toReal := by
    have h₁ : ‖(b n).toL1‖ ≤ M.toReal := by
      rw [← toReal_eNorm, Lp.eNorm_def, eLpNorm_congr_ae (BV.coeFn_ofFunction (u n) (huBV n)),
        eLpNorm_one_eq_lintegral_eNorm (hmeas n)]
      exact ENNReal.toReal_mono hM (hbdd n)
    have h₂ : (totalVariationOn μ Ω (b n)).toReal ≤ M.toReal := by
      rw [BV.totalVariationOn_ofFunction]
      exact ENNReal.toReal_mono hM (hvar n)
    rw [BV.norm_def]
    linarith
  obtain ⟨v, φ, hφ, hv, hlsc, -⟩ :=
    BV.exists_subseq_tendsto_toL1_of_isCompactOperator hcpt hb_norm
  refine ⟨v, v.memBV, φ, hφ, ?_, ?_⟩
  · refine (tendsto_iff_edist_tendsto_0.mp hv).congr fun j => ?_
    rw [L1.edist_def]
    refine lintegral_congr_ae ?_
    filter_upwards [BV.coeFn_ofFunction (u (φ j)) (huBV (φ j))] with x hx
    simp [b, hx, eDist_eq_eNorm_sub]
  · simpa only [b, BV.totalVariationOn_ofFunction] using hlsc

/-- **Global compactness for sets of bounded perimeter.** If `BV.toL1CLM` is a compact operator on
`Ω`, `μ Ω ≠ ∞`, and `s : ℕ → Set E` is a sequence of `μ.restrict Ω`-null-measurable sets with
`perimeter μ Ω (s n) ≤ M` (`M < ∞`), then a subsequence converges globally in measure on `Ω` to a
measurable set `t`, that is `μ ((s (φ j) ∆ t) ∩ Ω) → 0`, with
`perimeter μ Ω t ≤ liminf_j perimeter μ Ω (s (φ j))`. -/
theorem exists_subseq_tendsto_measure_symmDiff_inter_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _)) (hμΩ : μ Ω ≠ ⊤)
    {s : ℕ → Set E} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hs : ∀ n, NullMeasurableSet (s n) (μ.restrict Ω))
    (hP : ∀ n, perimeter μ Ω (s n) ≤ M) :
    ∃ t : Set E, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => μ ((s (φ j) ∆ t) ∩ Ω)) atTop (𝓝 0) ∧
      perimeter μ Ω t ≤ liminf (fun j => perimeter μ Ω (s (φ j))) atTop := by
  have hB : max (μ Ω) M ≠ ⊤ := (max_lt_iff.mpr ⟨hμΩ.lt_top, hM.lt_top⟩).ne
  have hind (A : Set E) : ∫⁻ x in Ω, ‖A.indicator (1 : E → ℝ) x‖ₑ ∂μ ≤ μ Ω :=
    (lintegral_mono (g := fun _ => (1 : ℝ≥0∞)) fun x =>
      (eNorm_indicator_le_eNorm_self _ x).trans (by simp)).trans_eq (by simp)
  obtain ⟨v, hv, φ, hφ, hlim, -⟩ :=
    exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM
      (u := fun n => (s n).indicator 1) hcpt hB
      (fun n => aestronglyMeasurable_const.indicator₀ (hs n))
      (fun n => (hind (s n)).trans (le_max_left _ _))
      fun n => by simpa [perimeter_def] using (hP n).trans (le_max_right _ _)
  let w := hv.integrableOn.aestronglyMeasurable.mk v
  have hw : Measurable w := hv.integrableOn.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  let t : Set E := {x | 1 / 2 < w x}
  have ht : MeasurableSet t := measurableSet_lt measurable_const hw
  have hsymm : Tendsto (fun j => μ ((s (φ j) ∆ t) ∩ Ω)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun j =>
        (∫⁻ x in Ω, ‖(s (φ j)).indicator (1 : E → ℝ) x - v x‖ₑ ∂μ) / ENNReal.ofReal (1 / 2))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.div_const hlim
        (.inr (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun _ => zero_le) fun j => ?_
    rw [← Measure.restrict_apply' Ω.isOpen.measurableSet, symmDiff_comm]
    refine ((μ.restrict Ω).measure_symmDiff_setOf_lt_indicator_le
      hv.integrableOn.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable (hs (φ j))
      (by norm_num : (0 : ℝ) < 1 / 2) le_rfl (by norm_num)).trans_eq ?_
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hv.integrableOn.aestronglyMeasurable.ae_eq_mk] with x hx
    rw [← hx, ← eNorm_neg, neg_sub]
  refine ⟨t, ht, φ, hφ, hsymm, ?_⟩
  have : IsFiniteMeasure (μ.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμΩ.lt_top⟩
  have hper (A : Set E) : perimeter (μ.restrict Ω) Ω A = perimeter μ Ω A := by
    rw [← perimeter_congr_of_inter_eq (s := A ∩ Ω) (t := A) (by simp),
      perimeter_restrict_of_subset inter_subset_right,
      perimeter_congr_of_inter_eq (s := A ∩ Ω) (t := A) (by simp)]
  simp_rw [← hper]
  refine perimeter_le_liminf (.of_forall fun j => hs (φ j)) ht.nullMeasurableSet fun K _ _ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsymm
    (fun _ => zero_le) fun j => ?_
  rw [Measure.restrict_apply' Ω.isOpen.measurableSet]
  exact measure_mono (inter_subset_inter_left _ inter_subset_left)

end CompactOperator

end TauCeti
