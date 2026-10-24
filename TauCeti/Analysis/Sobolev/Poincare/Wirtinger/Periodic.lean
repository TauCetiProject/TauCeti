/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Wirtinger
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Sharp periodic Wirtinger inequality for weak derivatives

For `a < b`, a function with a square-integrable weak derivative on `(a, b)` has a unique
continuous representative on `[a, b]`. Its endpoint values agree exactly when the integral of its
weak derivative vanishes. Under this intrinsic periodicity condition, the sharp Wirtinger inequality
holds with constant `((b - a) / (2π))²`. Equality holds exactly for a first harmonic plus the
mean, as an almost-everywhere identity. Both statements are independent of representatives.

The vector-valued results use `HasWeakLineDerivOn`, and the scalar results apply directly to
`W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2`, with its recorded weak gradient. The proof uses the
continuous representative and weak FTC from `WeakDeriv.Interval`, identifies its classical
and weak derivatives almost everywhere, and applies the AC inequality and equality theorem
`TauCeti.integral_norm_sub_average_sq_eq_iff`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.2
  (continuous representatives of one-dimensional Sobolev functions).
* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Theorem 258
  (the sharp periodic Wirtinger inequality).
-/

public section

open MeasureTheory Set Real intervalIntegral
open scoped Interval

namespace TauCeti

namespace HasWeakLineDerivOn

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {a b : ℝ} {u u' : ℝ → V}

/-- Transfer the sharp inequality and its equality analysis through the AC representative. -/
private theorem integral_norm_sub_average_sq_le_and_eq_iff
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (hab : a < b)
    (hu' : MemLp u' 2 (volume.restrict (Ioo a b))) (hperiod : ∫ t in a..b, u' t = 0) :
    (∫ t in a..b, ‖u t - ⨍ s in a..b, u s‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ t in a..b, ‖u' t‖ ^ 2) ∧
    ((∫ t in a..b, ‖u t - ⨍ s in a..b, u s‖ ^ 2) =
        ((b - a) / (2 * π)) ^ 2 * ∫ t in a..b, ‖u' t‖ ^ 2 ↔
      ∃ x y : V, (fun t ↦ u t - ⨍ s in a..b, u s) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ cos (2 * π * t / (b - a)) • x + sin (2 * π * t / (b - a)) • y) := by
  -- Construct the closed AC representative and transport the mean and squared deviation.
  have hint := hu'.integrable one_le_two
  obtain ⟨v, hv, hae, hvab⟩ :=
    (h.integral_eq_zero_iff_exists_absolutelyContinuousOnInterval hint hab.le).1 hperiod
  have hvc : ContinuousOn v (Icc a b) := uIcc_of_le hab.le ▸ hv.continuousOn
  have hae' : u =ᵐ[volume.restrict (uIoc a b)] v := by
    simpa only [uIoc_of_le hab.le, restrict_Ioo_eq_restrict_Ioc] using hae
  have hm : (⨍ s in a..b, u s) = ⨍ s in a..b, v s := by
    rw [interval_average_eq, interval_average_eq, integral_congr_ae_restrict hae']
  have hd : (∫ t in a..b, ‖u t - ⨍ s in a..b, u s‖ ^ 2) =
      ∫ t in a..b, ‖v t - ⨍ s in a..b, v s‖ ^ 2 := by
    apply integral_congr_ae_restrict
    filter_upwards [hae'] with t ht
    rw [ht, hm]
  have hp : MemLp u' 2 (volume.restrict (Ioc a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Ioc] using hu'
  have hder := h.ae_hasDerivAt hint hvc hae hab.le
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact TauCeti.integral_norm_sub_average_sq_le hab hv hder hvab hp
  -- For equality, continuous functions agreeing almost everywhere agree at the endpoints too.
  rw [hd, TauCeti.integral_norm_sub_average_sq_eq_iff hab hv
    hder hvab hp]
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, hm, hxy t (Ioo_subset_Icc_self hmem)]
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    have heq : (fun t ↦ v t - ⨍ s in a..b, v s) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ cos (2 * π * t / (b - a)) • x + sin (2 * π * t / (b - a)) • y := by
      filter_upwards [hae, hxy] with t ht hxy
      rwa [ht, hm] at hxy
    have hl : ContinuousOn (fun t ↦ v t - ⨍ s in a..b, v s) (Icc a b) :=
      hvc.sub continuousOn_const
    have hr : ContinuousOn
        (fun t ↦ cos (2 * π * t / (b - a)) • x + sin (2 * π * t / (b - a)) • y)
        (Icc a b) := by fun_prop
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne
      (by simpa only [restrict_Ioo_eq_restrict_Icc] using heq) hl hr

/-- Sharp periodic Wirtinger inequality for a weakly differentiable function. The vanishing
integral of the weak derivative says that the endpoint traces agree. -/
theorem integral_norm_sub_average_sq_le
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (hab : a < b)
    (hu' : MemLp u' 2 (volume.restrict (Ioo a b))) (hperiod : ∫ t in a..b, u' t = 0) :
    ∫ t in a..b, ‖u t - ⨍ s in a..b, u s‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ t in a..b, ‖u' t‖ ^ 2 :=
  (integral_norm_sub_average_sq_le_and_eq_iff h hab hu' hperiod).1

/-- Equality in the sharp periodic weak Wirtinger inequality holds exactly for a first
harmonic plus the mean, almost everywhere on the interval. -/
theorem integral_norm_sub_average_sq_eq_iff
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (hab : a < b)
    (hu' : MemLp u' 2 (volume.restrict (Ioo a b))) (hperiod : ∫ t in a..b, u' t = 0) :
    (∫ t in a..b, ‖u t - ⨍ s in a..b, u s‖ ^ 2) =
        ((b - a) / (2 * π)) ^ 2 * ∫ t in a..b, ‖u' t‖ ^ 2 ↔
      ∃ x y : V, (fun t ↦ u t - ⨍ s in a..b, u s) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ cos (2 * π * t / (b - a)) • x + sin (2 * π * t / (b - a)) • y :=
  (integral_norm_sub_average_sq_le_and_eq_iff h hab hu' hperiod).2

end HasWeakLineDerivOn

namespace W1p

variable {a b : ℝ} (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2)

/-- A scalar `W¹,²` class is periodic exactly when its recorded gradient has integral zero.
Periodicity means that an AC representative has matching endpoint values. -/
theorem integral_gradient_eq_zero_iff_exists_absolutelyContinuousOnInterval (hab : a ≤ b) :
    (∫ t in a..b, W1p.gradient u t) = 0 ↔
      ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
        W1p.value u =ᵐ[volume.restrict (Ioo a b)] v ∧ v a = v b := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (W1p.value u) (W1p.gradient u) 1 := by
    simpa using (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  have hp : MemLp (W1p.gradient u) 2 (volume.restrict (Ioo a b)) := Lp.memLp _
  exact hw.integral_eq_zero_iff_exists_absolutelyContinuousOnInterval
    (hp.integrable one_le_two) hab

/-- The sharp periodic Wirtinger inequality on the canonical scalar weak Sobolev space. -/
theorem integral_norm_sub_average_sq_le (hab : a < b)
    (hperiod : ∫ t in a..b, W1p.gradient u t = 0) :
    ∫ t in a..b, ‖W1p.value u t - ⨍ s in a..b, W1p.value u s‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ t in a..b, ‖W1p.gradient u t‖ ^ 2 := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (W1p.value u) (W1p.gradient u) 1 := by
    simpa using (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  exact hw.integral_norm_sub_average_sq_le hab (Lp.memLp _) hperiod

/-- Equality in the canonical scalar periodic `W¹,²` inequality characterizes first harmonics
almost everywhere; arbitrary choices of representatives of the Sobolev class are allowed. -/
theorem integral_norm_sub_average_sq_eq_iff (hab : a < b)
    (hperiod : ∫ t in a..b, W1p.gradient u t = 0) :
    (∫ t in a..b, ‖W1p.value u t - ⨍ s in a..b, W1p.value u s‖ ^ 2) =
        ((b - a) / (2 * π)) ^ 2 * ∫ t in a..b, ‖W1p.gradient u t‖ ^ 2 ↔
      ∃ x y : ℝ, (fun t ↦ W1p.value u t - ⨍ s in a..b, W1p.value u s) =ᵐ[
        volume.restrict (Ioo a b)]
        fun t ↦ cos (2 * π * t / (b - a)) * x + sin (2 * π * t / (b - a)) * y := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (W1p.value u) (W1p.gradient u) 1 := by
    simpa using (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  exact hw.integral_norm_sub_average_sq_eq_iff hab (Lp.memLp _) hperiod

end W1p

end TauCeti
