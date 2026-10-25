/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.BoundedVariation.Multiplication
import TauCeti.Analysis.BoundedVariation.Translation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
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

## Main results

* `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le` and
  `TauCeti.isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le`: a family bounded in
  `L¹(Ω)` and in variation on `Ω` is totally bounded, and relatively compact, in `L¹(K)` for every
  compact `K ⊆ Ω`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.23.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2,
  Theorem 5.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 12.26.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Function Metric Set TopologicalSpace TestFunction
open scoped ENNReal NNReal ContDiff Distributions Topology

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

end TauCeti
