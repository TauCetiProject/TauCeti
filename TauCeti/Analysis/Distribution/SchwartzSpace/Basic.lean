/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport

/-!
# Weighted bounds and integrability of Schwartz functions

A Schwartz function is bounded and decays faster than any power. Pointwise, it absorbs any
polynomial weight `⟨c x⟩ ^ m = (1 + ‖c x‖²) ^ (m / 2)` and still decays like `(1 + ‖x‖) ^ (-k)`.
Consequently `‖x‖ ^ k ‖f x‖²` is
integrable against any measure of temperate growth. This is the integrability input for weighted
`L²` estimates such as the weighted Plancherel identity. Likewise the pointwise inner product of two
Schwartz functions is integrable, which justifies splitting `L²` pairings of Schwartz functions.

## Main declarations

* `SchwartzMap.one_add_norm_smul_sq_rpow_mul_norm_le`: `⟨c x⟩ ^ m ‖f x‖` is bounded by a finite
  supremum of Schwartz seminorms of `f` times `(1 + ‖x‖) ^ (-k)`.
* `SchwartzMap.integrable_norm_pow_mul_norm_sq`: `‖x‖ ^ k ‖f x‖²` is integrable.
* `SchwartzMap.integrable_inner`: `⟪f x, g x⟫` is integrable.
* `SchwartzMap.integrable_one_add_norm_sq_rpow_mul_norm`: `(1 + ‖x‖ ^ 2) ^ r ‖f x‖` is integrable
  for every real `r`.
* `SchwartzMap.integrable_one_add_norm_smul_sq_rpow_mul_norm`: `⟨c x⟩ ^ m ‖f x‖` is integrable
  against any measure of temperate growth.
* `SchwartzMap.integrable_norm_iteratedFDeriv`: `‖D^k f x‖` is integrable.
* `SchwartzMap.integrable_iteratedFDeriv_comp_left`,
  `SchwartzMap.integral_norm_iteratedFDeriv_comp_left_le`: for a continuous linear map `L`, the
  derivatives of `L ∘ f` are integrable, with `∫ ‖D^k (L ∘ f)‖ ≤ ‖L‖ ∫ ‖D^k f‖`.
* `SchwartzMap.integral_norm_sq_eq_zero_iff`: a Schwartz function vanishes exactly when the
  integral of its squared norm does, for a measure charging every nonempty open set.
* `TauCeti.eq_zero_of_forall_integral_apply_eq_zero`: a continuous operator-valued function that
  integrates to zero against every Schwartz function vanishes.
* `HasCompactSupport.toSchwartzMap_toLp`: the `Lᵖ` class of a smooth compactly supported function
  is the same whether built through `HasCompactSupport.toSchwartzMap` or from `MemLp`.
-/

public section

open MeasureTheory

namespace SchwartzMap

open scoped SchwartzMap InnerProductSpace

section Weight

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- A Schwartz function absorbs the polynomial weight `⟨c x⟩ ^ m = (1 + ‖c x‖²) ^ (m / 2)` and
still decays like `(1 + ‖x‖) ^ (-k)`, with a constant given by a finite supremum of Schwartz
seminorms. -/
theorem one_add_norm_smul_sq_rpow_mul_norm_le (c m : ℝ) (k : ℕ) (f : 𝓢(E, F)) (x : E) :
    (1 + ‖c • x‖ ^ 2) ^ (m / 2) * ‖f x‖ ≤
      max 1 |c| ^ ⌈m⌉₊ * 2 ^ (⌈m⌉₊ + k) *
        (Finset.Iic (⌈m⌉₊ + k, 0)).sup (fun n ↦ SchwartzMap.seminorm 𝕜 n.1 n.2) f *
        (1 + ‖x‖) ^ (-(k : ℝ)) := by
  set K := ⌈m⌉₊
  set S := (Finset.Iic (K + k, 0)).sup (fun n ↦ SchwartzMap.seminorm 𝕜 n.1 n.2) f
  set t := ‖c • x‖
  have ht : t = |c| * ‖x‖ := by
    simp [t, norm_smul]
  have hx : 0 < 1 + ‖x‖ := by positivity
  -- The bracket of order `m` is dominated by a polynomial weight of degree `K = ⌈m⌉₊`.
  have hweight : (1 + t ^ 2) ^ (m / 2) ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ K := by
    calc (1 + t ^ 2) ^ (m / 2) ≤ (1 + t ^ 2) ^ ((K : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith)
            (by gcongr; exact Nat.le_ceil m)
      _ ≤ ((1 + t) ^ 2) ^ ((K : ℝ) / 2) := by
          gcongr
          nlinarith [norm_nonneg (c • x)]
      _ = (1 + t) ^ K := by
          rw [← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * ((K : ℝ) / 2) = (K : ℝ) by push_cast; ring, Real.rpow_natCast]
      _ ≤ (max 1 |c| * (1 + ‖x‖)) ^ K := by
          gcongr
          rw [ht]
          nlinarith [le_max_left 1 |c|, le_max_right 1 |c|, norm_nonneg x]
      _ = max 1 |c| ^ K * (1 + ‖x‖) ^ K := mul_pow _ _ _
  -- The Schwartz function decays like `(1 + ‖x‖) ^ (-(K + k))`.
  have hdecay : (1 + ‖x‖) ^ (K + k) * ‖f x‖ ≤ 2 ^ (K + k) * S := by
    simpa using f.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K + k, 0)) le_rfl le_rfl x
  have hsplit : (1 + ‖x‖) ^ K = (1 + ‖x‖) ^ (-(k : ℝ)) * (1 + ‖x‖) ^ (K + k) := by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, pow_add]
    field_simp
  calc (1 + t ^ 2) ^ (m / 2) * ‖f x‖ ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ K * ‖f x‖ := by gcongr
    _ = max 1 |c| ^ K * (1 + ‖x‖) ^ (-(k : ℝ)) * ((1 + ‖x‖) ^ (K + k) * ‖f x‖) := by
        rw [hsplit]; ring
    _ ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ (-(k : ℝ)) * (2 ^ (K + k) * S) := by gcongr
    _ = _ := by ring

end Weight

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.HasTemperateGrowth]

/-- For a Schwartz function `f`, the function `‖x‖ ^ k ‖f x‖²` is integrable. -/
theorem integrable_norm_pow_mul_norm_sq (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖ ^ 2) μ := by
  refine ((f.integrable_pow_mul μ k).const_mul (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (by fun_prop) (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), sq, ← mul_assoc, mul_comm _ ‖f x‖]
  gcongr
  exact f.norm_le_seminorm ℝ x

/-- A Schwartz function vanishes if and only if the integral of its squared norm does, against a
measure of temperate growth that charges every nonempty open set. -/
theorem integral_norm_sq_eq_zero_iff [μ.IsOpenPosMeasure] {f : 𝓢(E, F)} :
    ∫ x, ‖f x‖ ^ 2 ∂μ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    simpa using f.integrable_norm_pow_mul_norm_sq (μ := μ) 0
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖) hint).mp h
  have hcont : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have := (hcont.ae_eq_iff_eq μ continuous_zero).mp hae
  exact SchwartzMap.ext fun x => by simpa using congrFun this x

/-- For Schwartz functions `f` and `g` with values in a real inner product space, the pointwise
inner product `⟪f x, g x⟫` is integrable. -/
theorem integrable_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : 𝓢(E, H)) : Integrable (fun x ↦ ⟪f x, g x⟫_ℝ) μ := by
  convert (pairing (innerSL ℝ) f g).integrable (μ := μ) using 1
  ext x
  rw [pairing_apply_apply, innerSL_apply_apply]

/-- For a Schwartz function `f` and every real `r`, the function `(1 + ‖x‖ ^ 2) ^ r ‖f x‖` is
integrable. With `r = s / 2` this is the Japanese bracket weight `⟨x⟩ ^ s ‖f x‖`. -/
theorem integrable_one_add_norm_sq_rpow_mul_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {ν : Measure V} [ν.HasTemperateGrowth] (r : ℝ) (f : 𝓢(V, F)) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) ^ r * ‖f x‖) ν := by
  have hg := Function.hasTemperateGrowth_one_add_norm_sq_rpow V r
  refine ((smulLeftCLM F (fun x : V ↦ (1 + ‖x‖ ^ 2) ^ r) f).integrable (μ := ν)).norm.congr
    (.of_forall fun x ↦ ?_)
  dsimp only
  rw [smulLeftCLM_apply_apply hg, norm_smul, Real.norm_of_nonneg (by positivity)]

omit [SecondCountableTopology E] in
/-- For a Schwartz function `f` and real `c`, `m`, the function
`⟨c x⟩ ^ m ‖f x‖ = (1 + ‖c x‖ ^ 2) ^ (m / 2) ‖f x‖` is integrable. -/
theorem integrable_one_add_norm_smul_sq_rpow_mul_norm (c m : ℝ) (f : 𝓢(E, F)) :
    Integrable (fun x ↦ (1 + ‖c • x‖ ^ 2) ^ (m / 2) * ‖f x‖) μ :=
  ((Measure.integrable_pow_neg_integrablePower μ).const_mul _).mono'
    ((((continuous_const.add ((continuous_const_smul _).norm.pow 2)).rpow_const
      fun x ↦ Or.inl (by positivity : (1 : ℝ) + ‖c • x‖ ^ 2 ≠ 0)).mul
        f.continuous.norm).aestronglyMeasurable)
    (.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact f.one_add_norm_smul_sq_rpow_mul_norm_le (𝕜 := ℝ) c m μ.integrablePower x)

/-- The norms of the derivatives of a Schwartz function are integrable. -/
theorem integrable_norm_iteratedFDeriv (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ k f x‖) μ := by
  simpa only [pow_zero, one_mul] using f.integrable_pow_mul_iteratedFDeriv μ 0 k

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- For a Schwartz function `f` and a continuous linear map `L`, the derivatives of `L ∘ f` are
integrable. -/
theorem integrable_iteratedFDeriv_comp_left (L : F →L[ℝ] G) (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (iteratedFDeriv ℝ k (⇑L ∘ ⇑f)) μ :=
  ((f.integrable_norm_iteratedFDeriv k).const_mul ‖L‖).mono'
    ((L.contDiff.comp (f.smooth ⊤)).continuous_iteratedFDeriv
      (mod_cast le_top)).aestronglyMeasurable
    (.of_forall fun _ ↦ L.norm_iteratedFDeriv_comp_left (f.smooth ⊤).contDiffAt (mod_cast le_top))

/-- For a Schwartz function `f` and a continuous linear map `L`,
`∫ ‖D^k (L ∘ f)‖ ≤ ‖L‖ ∫ ‖D^k f‖`. -/
theorem integral_norm_iteratedFDeriv_comp_left_le (L : F →L[ℝ] G) (f : 𝓢(E, F)) (k : ℕ) :
    ∫ x, ‖iteratedFDeriv ℝ k (⇑L ∘ ⇑f) x‖ ∂μ ≤ ‖L‖ * ∫ x, ‖iteratedFDeriv ℝ k f x‖ ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
    ((f.integrable_norm_iteratedFDeriv k).const_mul ‖L‖)
    (.of_forall fun _ ↦ L.norm_iteratedFDeriv_comp_left (f.smooth ⊤).contDiffAt (mod_cast le_top))

end SchwartzMap

namespace TauCeti

open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]
  [μ.IsOpenPosMeasure]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [CompleteSpace W]

/-- A continuous function `g : E → V →L[ℂ] W` such that `∫ g ζ (f ζ) ∂μ = 0` for every Schwartz
function `f`, against a locally finite measure charging every nonempty open set, vanishes. -/
theorem eq_zero_of_forall_integral_apply_eq_zero {g : E → V →L[ℂ] W} (hg : Continuous g)
    (h : ∀ f : 𝓢(E, V), ∫ ζ, g ζ (f ζ) ∂μ = 0) (ζ : E) : g ζ = 0 := by
  ext v
  -- Test against `f = φ • v` with `φ` real, smooth and compactly supported.
  have hgv : Continuous fun ζ ↦ g ζ v := hg.clm_apply continuous_const
  have hae : ∀ᵐ η ∂μ, g η v = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hgv.locallyIntegrable fun φ hφ hφc ↦ ?_
    have hf : HasCompactSupport fun η ↦ φ η • v := hφc.smul_right
    simpa [ContinuousLinearMap.map_smul_of_tower] using
      h (hf.toSchwartzMap (hφ.smul contDiff_const))
  exact congrFun ((hgv.ae_eq_iff_eq μ continuous_zero).1 hae) ζ

end TauCeti

section CompactSupport

open scoped ENNReal ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopologyEither E F]
  {μ : Measure E} [μ.HasTemperateGrowth]

/-- The `Lᵖ` class of a smooth compactly supported function does not depend on whether it is
built through `HasCompactSupport.toSchwartzMap` or from any proof of `Lᵖ` membership. -/
theorem HasCompactSupport.toSchwartzMap_toLp {f : E → F} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ ∞ f) {p : ℝ≥0∞} (h : MemLp f p μ) :
    (hc.toSchwartzMap hf).toLp p μ = h.toLp f :=
  Lp.ext (((hc.toSchwartzMap hf).coeFn_toLp p μ).trans h.coeFn_toLp.symm)

end CompactSupport
