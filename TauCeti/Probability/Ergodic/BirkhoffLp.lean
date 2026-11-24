/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Dynamics.BirkhoffSum.Average
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Birkhoff averages on `Lᵖ` and `Lᵖ` contractivity

The Birkhoff sums and averages of the composition (Koopman) operator of a measure-preserving map
`T` on `Lᵖ` are elements of `Lᵖ`, while the ergodic theorems a probabilist states are about the
pointwise Birkhoff averages `birkhoffAverage 𝕜 T f n` of an observable. This file records that the
two agree: an `Lᵖ` Birkhoff average of `g` is represented by the pointwise Birkhoff average of the
coercion `⇑g`. For another representative `f =ᵐ[μ] ⇑g`, compose with Mathlib's
`QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq`.

It also collects the `Lᵖ` (`1 ≤ p`) and `L¹` contractivity properties of pointwise Birkhoff
averages under a measure-preserving map `T`.

## Main results

* `MeasureTheory.Lp.coeFn_iterate_compMeasurePreserving` — iterating the composition operator
  composes with the iterated transformation;
* `MeasureTheory.Lp.coeFn_birkhoffSum_compMeasurePreserving` and
  `MeasureTheory.Lp.coeFn_birkhoffAverage_compMeasurePreserving` — the Birkhoff sums and averages
  of the composition operator are represented by the pointwise Birkhoff sums and averages of the
  coercion of the argument; the averages may be taken over any normed division ring acting
  boundedly on the target;
* `MeasureTheory.MeasurePreserving.eLpNorm_birkhoffAverage_le` and
  `MeasureTheory.MeasurePreserving.integral_norm_birkhoffAverage_le` — `Lᵖ` (`1 ≤ p`) and `L¹`
  contractivity of Birkhoff averaging.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω} {p : ℝ≥0∞}
  {T : Ω → Ω}

/-- Iterating the `Lᵖ` composition operator composes with the iterated transformation. -/
theorem coeFn_iterate_compMeasurePreserving (g : Lp E p μ) (hT : MeasurePreserving T μ μ)
    (n : ℕ) : ⇑((compMeasurePreserving T hT)^[n] g) =ᵐ[μ] ⇑g ∘ T^[n] := by
  rw [compMeasurePreserving_iterate hT n]
  exact coeFn_compMeasurePreserving g (hT.iterate n)

/-- The Birkhoff sums of the `Lᵖ` composition operator are represented by the pointwise Birkhoff
sums of the coercion of `g`. -/
theorem coeFn_birkhoffSum_compMeasurePreserving (g : Lp E p μ) (hT : MeasurePreserving T μ μ)
    (n : ℕ) : ⇑(birkhoffSum (compMeasurePreserving T hT) id n g) =ᵐ[μ] birkhoffSum T (⇑g) n := by
  have hsum : birkhoffSum T (⇑g) n = ∑ k ∈ Finset.range n, ⇑g ∘ T^[k] := by
    ext ω
    simp [birkhoffSum]
  rw [hsum, birkhoffSum]
  exact (coeFn_finsetSum _ _).trans
    (eventuallyEq_sum fun k _ => coeFn_iterate_compMeasurePreserving g hT k)

/-- The Birkhoff averages of the `Lᵖ` composition operator are represented by the pointwise
Birkhoff averages of the coercion of `g`. -/
theorem coeFn_birkhoffAverage_compMeasurePreserving (𝕜 : Type*) [NormedDivisionRing 𝕜]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (g : Lp E p μ) (hT : MeasurePreserving T μ μ) (n : ℕ) :
    ⇑(birkhoffAverage 𝕜 (compMeasurePreserving T hT) id n g) =ᵐ[μ] birkhoffAverage 𝕜 T (⇑g) n := by
  filter_upwards [coeFn_birkhoffSum_compMeasurePreserving g hT n,
    coeFn_smul ((n : 𝕜)⁻¹) (birkhoffSum (compMeasurePreserving T hT) id n g)] with ω hsum hsmul
  rw [birkhoffAverage, hsmul, Pi.smul_apply, hsum, birkhoffAverage]

end MeasureTheory.Lp

namespace MeasureTheory.MeasurePreserving

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {T : Ω → Ω} {f : Ω → E}

/-- Birkhoff averaging under a measure-preserving map is a contraction on `Lᵖ` for `1 ≤ p`. -/
theorem eLpNorm_birkhoffAverage_le (hT : MeasurePreserving T μ μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : Ω → E) (n : ℕ) :
    eLpNorm (birkhoffAverage ℝ T f n) p μ ≤ eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  case neg =>
    rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [TauCeti.birkhoffAverage_eq_smul_sum_comp_iterate, eLpNorm_const_smul]
  calc
    ‖(n : ℝ)⁻¹‖ₑ * eLpNorm (∑ k ∈ Finset.range n, f ∘ T^[k]) p μ
      ≤ ‖(n : ℝ)⁻¹‖ₑ * ∑ k ∈ Finset.range n, eLpNorm (f ∘ T^[k]) p μ :=
        mul_le_mul_right (eLpNorm_sum_le hp) _
    _ = ‖(n : ℝ)⁻¹‖ₑ * ∑ _k ∈ Finset.range n, eLpNorm f p μ := by
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ eLpNorm_comp_measurePreserving hf (hT.iterate k)
    _ = ((n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)) * eLpNorm f p μ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        congr 2
        rw [eNorm_inv (Nat.cast_ne_zero.mpr hn), Real.eNorm_of_nonneg (Nat.cast_nonneg n),
          ENNReal.ofReal_natCast]
    _ = eLpNorm f p μ := by
        rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n), one_mul]

/-- Birkhoff averaging under a measure-preserving map contracts the `L¹` norm. -/
theorem integral_norm_birkhoffAverage_le (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (n : ℕ) :
    ∫ x, ‖birkhoffAverage ℝ T f n x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ :=
  hf.integral_norm_le_integral_norm_of_eLpNorm_one_le (hT.eLpNorm_birkhoffAverage_le le_rfl f n)

end MeasureTheory.MeasurePreserving
