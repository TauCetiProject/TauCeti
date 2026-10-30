/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.BoundedVariation.Multiplication
import TauCeti.Analysis.BoundedVariation.Translation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Function.Lp.Subsequence
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

## Main results

* `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le` and
  `TauCeti.isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le`: a family bounded in
  `L¹(Ω)` and in variation on `Ω` is totally bounded, and relatively compact, in `L¹(K)` for every
  compact `K ⊆ Ω`.
* `TauCeti.exists_subseq_tendsto_setLIntegral_enorm_sub_of_totalVariationOn_le`: a sequence locally
  bounded in `L¹` and in variation on `Ω` has a subsequence converging in `L¹_loc(Ω)`.
* `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le`: compactness for sets of
  locally finite perimeter.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.23.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2,
  Theorem 5.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 12.26 and
  Corollary 12.27.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Function Metric Set TopologicalSpace TestFunction
open scoped ENNReal NNReal ContDiff Distributions Topology symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω V : Opens E}
  {u : E → ℝ} {h : E}

/-! ### Compactness -/

variable {K : Set E} {S : Set (E → ℝ)} {M : ℝ≥0∞}

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
  obtain ⟨χ, hχ, hχ01, hχK, hχc, hχΩ⟩ := hK.exists_contDiff_cutoff Ω.isOpen hKΩ
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
  set T : Set (Lp ℝ 1 μ) := {f | ∃ u ∈ S, f =ᵐ[μ] χ * u}
  have hT : TotallyBounded T := by
    refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl ENNReal.one_ne_top
      hχc.isCompact.isBounded ?_ hM ?_ ?_
    · rintro f ⟨u, -, hf⟩
      filter_upwards [hf] with x hx hxs
      rw [hx, Pi.mul_apply, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
    · rintro f ⟨u, hu, hf⟩
      rw [eLpNorm_congr_ae hf, eLpNorm_one_eq_lintegral_enorm (hint u hu).aestronglyMeasurable]
      exact (hnorm u).trans (hbdd u hu)
    · intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hB hε.ne'
      refine ⟨δ, by exact_mod_cast hδ, fun f ⟨u, hu, hf⟩ h hh => ?_⟩
      have hfh : (fun x => f (x + h)) =ᵐ[μ] fun x => (χ * u) (x + h) :=
        (measurePreserving_add_right μ h).quasiMeasurePreserving.ae_eq_comp hf
      have hinc : (fun x => f (x + h) - f x) =ᵐ[μ] fun x => (χ * u) (x + h) - (χ * u) x := by
        filter_upwards [hfh, hf] with x h₁ h₂
        rw [h₁, h₂]
      rw [eLpNorm_congr_ae hinc, eLpNorm_one_eq_lintegral_enorm
        (f := fun x => (χ * u) (x + h) - (χ * u) x)
        (((hint u hu).comp_add_right h).sub (hint u hu)).aestronglyMeasurable]
      refine (lintegral_enorm_comp_add_sub_le_mul_totalVariationOn
        (hint u hu).locallyIntegrable h).trans ?_
      refine (mul_le_mul' ?_ (hvarχ u hu)).trans hδε.le
      exact enorm_le_coe.mpr (by exact_mod_cast hh.le)
  -- Restricting to `K`, where `χ = 1`, recovers the members of `S`.
  let res : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (μ.restrict K) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (by simpa using Measure.restrict_le_self)
  refine (hT.image res.uniformContinuous).subset ?_
  rintro f ⟨u, hu, hfu⟩
  refine ⟨(hint u hu).toL1 _, ⟨u, hu, Integrable.coeFn_toL1 _⟩, ?_⟩
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (μ := μ.restrict K) ENNReal.one_ne_top
      (by simpa using Measure.restrict_le_self) ((hint u hu).toL1 _),
    ae_restrict_of_ae (Integrable.coeFn_toL1 (hint u hu)), ae_restrict_mem hK.measurableSet,
    hfu] with x h₁ h₂ hx h₃
  have hχx : χ x = 1 := interior_subset (hχK hx)
  rw [h₁, h₂, h₃, Pi.mul_apply, hχx, one_mul]

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
  rw [eLpNorm_one_eq_lintegral_enorm ((hint _ K hK hKΩ).aestronglyMeasurable.sub
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
            lintegral_mono fun x => (enorm_indicator_le_enorm_self _ x).trans (by simp)
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
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
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

end TauCeti
