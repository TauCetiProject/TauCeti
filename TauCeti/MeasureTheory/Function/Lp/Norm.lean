/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Norm inequalities in `Lᵖ` spaces

This file contains norm estimates for `Lᵖ` functions derived from almost-everywhere pointwise
bounds.

## Main declarations

* `TauCeti.Lp.norm_le_add_of_ae_norm_le`: an `Lᵖ` norm bound from pointwise domination by a
  two-term linear combination.
* `MeasureTheory.L1.norm_eq_integral_of_nonneg`: the norm of a nonnegative real `L¹` function is
  its integral.
* `MeasureTheory.Lp.integral_norm_sq_eq_norm_sq`: the integral of the squared pointwise
  norm of an `L²` function is its squared `L²` norm.
* `MeasureTheory.tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub`: L² convergence implies
  convergence of the integral of the squared norm.
* `MeasureTheory.lpNorm_congr_ae`: the `Lᵖ` norm of a function depends only on its almost
  everywhere class.
* `MeasureTheory.Lp.norm_eq_lpNorm_of_ae_eq`: the norm of an element of `Lᵖ(ν)` is the `Lᵖ` norm of
  any representative.
* `MeasureTheory.lpNorm_le_norm_of_ae_eq_of_le`: for `ν ≤ ν'`, the `Lᵖ(ν)` norm of a
  representative of an element of `Lᵖ(ν')` is at most its norm.
* `MeasureTheory.Lp.ae_norm_le_norm_top` and `MeasureTheory.Lp.norm_top_le_of_ae_bound`: an `L∞`
  function is bounded almost everywhere by its norm, and an almost everywhere bound bounds the
  norm, for any measure.
* `MeasureTheory.Lp.ae_eq_max_min_norm_top`: a representative of a real `L∞` class agrees almost
  everywhere with its truncation to `[-‖f‖, ‖f‖]`.
* `MeasureTheory.Lp.measure_lt_norm_ne_zero`: every level strictly below the `L∞` norm is
  exceeded on a set of nonzero measure.
* `MeasureTheory.Lp.integral_norm_le_mul_norm`: on a finite measure space, the `L¹` norm of an
  `Lᵖ` function, `1 ≤ p`, is at most `μ(univ)^{1 - 1/p}` times its `Lᵖ` norm.
* `MeasureTheory.Lp.norm_integral_le_of_ae_norm_le_mul`: the resulting bound on the integral of a
  function dominated pointwise by a multiple of the norm of an `Lᵖ` function.
* `MeasureTheory.Lp.setIntegral_norm_sq_le_norm_sq`: so its integral over a subset of the set it
  lives on is at most its squared `L²` norm.
* `MeasureTheory.MemLp.integrableOn_of_subset` and
  `MeasureTheory.MemLp.integrableOn_norm_sub_sq_of_subset`: a function in `Lᵖ(t)`, `1 ≤ p`, is
  integrable on every subset of `t` of finite measure, and for `p = 2` so is its squared distance
  to any constant.
* `MeasureTheory.MemLp.norm_toLp_le_measureReal_rpow_mul`: on a set `s` of finite measure, a
  function bounded by `M` has `Lᵖ(s)` norm at most `μ(s)^{1/p} M`, `1 ≤ p < ∞`.
* `MeasureTheory.MemLp.eLpNorm_rpow_toReal_eq_enorm_integral`: for `0 < q < ∞`, the `q`-th power of
  the `L^q` norm of `f` is the norm of the integral of `‖f‖ ^ q`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- The norm of an `Lᵖ` function dominated pointwise by a two-term combination of two other
`Lᵖ` functions obeys the same bound in norm. -/
theorem Lp.norm_le_add_of_ae_norm_le {alpha F G H : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H] {m : Measure alpha}
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Lp F q m} {g : Lp G q m} {h : Lp H q m} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hle : ∀ᵐ z ∂m, ‖f z‖ ≤ a * ‖g z‖ + b * ‖h z‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖h‖ := by
  obtain ⟨A, hAnorm, hAcoe⟩ : ∃ A : Lp ℝ q m, ‖A‖ = ‖g‖ ∧ ∀ᵐ z ∂m, A z = ‖g z‖ :=
    ⟨(Lp.memLp g).norm.toLp _,
      by rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable g), ← Lp.norm_def],
      (Lp.memLp g).norm.coeFn_toLp⟩
  obtain ⟨B, hBnorm, hBcoe⟩ : ∃ B : Lp ℝ q m, ‖B‖ = ‖h‖ ∧ ∀ᵐ z ∂m, B z = ‖h z‖ :=
    ⟨(Lp.memLp h).norm.toLp _,
      by rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable h), ← Lp.norm_def],
      (Lp.memLp h).norm.coeFn_toLp⟩
  calc ‖f‖ ≤ ‖a • A + b • B‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [hle, hAcoe, hBcoe, Lp.coeFn_add (a • A) (b • B), Lp.coeFn_smul a A,
          Lp.coeFn_smul b B] with z hz hA hB hadd hsA hsB
        rw [hadd, Pi.add_apply, hsA, hsB, Pi.smul_apply, Pi.smul_apply, hA, hB, smul_eq_mul,
          smul_eq_mul, Real.norm_of_nonneg (add_nonneg (mul_nonneg ha (norm_nonneg _))
            (mul_nonneg hb (norm_nonneg _)))]
        exact hz
    _ ≤ ‖a • A‖ + ‖b • B‖ := norm_add_le _ _
    _ = a * ‖g‖ + b * ‖h‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hAnorm, hBnorm]

end TauCeti

namespace MeasureTheory

open Filter
open scoped ENNReal Topology

/-- The `Lᵖ` norm of a function depends only on its almost everywhere class. -/
theorem lpNorm_congr_ae {alpha F : Type*} [MeasurableSpace alpha] [NormedAddCommGroup F]
    {ν : Measure alpha} {p : ℝ≥0∞} {f g : alpha → F} (h : f =ᵐ[ν] g) :
    lpNorm f p ν = lpNorm g p ν := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae h]

/-- The norm of an element of `Lᵖ(ν)` is the `Lᵖ` norm of any of its representatives. -/
theorem Lp.norm_eq_lpNorm_of_ae_eq {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {ν : Measure alpha} {p : ℝ≥0∞} {f : Lp F p ν} {g : alpha → F}
    (h : f =ᵐ[ν] g) : ‖f‖ = lpNorm g p ν := by
  rw [← lpNorm_congr_ae h, Lp.norm_def, toReal_eLpNorm]

/-- The `Lᵖ(ν)` norm of a function agreeing `ν`-almost everywhere with an element of `Lᵖ(ν')`, for
`ν ≤ ν'`, is at most the norm of that element. -/
theorem lpNorm_le_norm_of_ae_eq_of_le {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {ν ν' : Measure alpha} {p : ℝ≥0∞} {f : alpha → F} {g : Lp F p ν'}
    (hν : ν ≤ ν') (h : f =ᵐ[ν] g) : lpNorm f p ν ≤ ‖g‖ := by
  rw [lpNorm_congr_ae h, ← toReal_eLpNorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _ hν)

/-- An `L∞` function is bounded almost everywhere by its norm. -/
theorem Lp.ae_norm_le_norm_top {alpha F : Type*} [MeasurableSpace alpha] [NormedAddCommGroup F]
    {m : Measure alpha} (f : Lp F ∞ m) : ∀ᵐ x ∂m, ‖f x‖ ≤ ‖f‖ := by
  simpa [Lp.norm_def, toReal_eLpNorm] using ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- An almost everywhere bound on an `L∞` function bounds its norm, whatever the measure. Compare
`MeasureTheory.Lp.norm_le_of_ae_bound`, which needs a finite measure. -/
theorem Lp.norm_top_le_of_ae_bound {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {m : Measure alpha} {f : Lp F ∞ m} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ x ∂m, ‖f x‖ ≤ c) : ‖f‖ ≤ c := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_le_of_le_ofReal hc (eLpNormEssSup_le_of_ae_bound h)

/-- A representative `g` of a real `L∞` class `f` agrees almost everywhere with its truncation to
`[-‖f‖, ‖f‖]`. The truncation is bounded everywhere by `‖f‖` (`TauCeti.abs_max_min_le`). -/
theorem Lp.ae_eq_max_min_norm_top {alpha : Type*} [MeasurableSpace alpha] {m : Measure alpha}
    {f : Lp ℝ ∞ m} {g : alpha → ℝ} (hg : f =ᵐ[m] g) :
    g =ᵐ[m] fun x => max (-‖f‖) (min ‖f‖ (g x)) := by
  filter_upwards [hg, Lp.ae_norm_le_norm_top f] with x h hx
  rw [h, Real.norm_eq_abs, abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Every nonnegative level strictly below the `L∞` norm of `f` is exceeded by `‖f‖` on a set
of nonzero measure. -/
theorem Lp.measure_lt_norm_ne_zero {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {m : Measure alpha} {f : Lp F ∞ m} {c : ℝ} (hc_nonneg : 0 ≤ c)
    (hc : c < ‖f‖) : m {x | c < ‖f x‖} ≠ 0 := by
  intro hms
  have hae : ∀ᵐ x ∂m, ‖f x‖ ≤ c :=
    (measure_eq_zero_iff_ae_notMem.mp hms).mono fun x hx ↦ le_of_not_gt hx
  exact (not_lt_of_ge (Lp.norm_top_le_of_ae_bound hc_nonneg hae)) hc

/-- The norm of a nonnegative real `L¹` function is its integral. -/
theorem L1.norm_eq_integral_of_nonneg {alpha : Type*} [MeasurableSpace alpha] {m : Measure alpha}
    {f : Lp ℝ 1 m} (hf : 0 ≤ f) : ‖f‖ = ∫ x, f x ∂m := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (((Lp.coeFn_nonneg f).2 hf).mono fun x hx => Real.norm_of_nonneg hx)

/-- For `0 < p < ∞`, the integral of the `p`-th power of the pointwise norm of an `Lᵖ` function
is the `p`-th power of its `Lᵖ` norm. -/
theorem Lp.integral_norm_rpow_eq_norm_rpow {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp F p m) :
    ∫ x, ‖f x‖ ^ p.toReal ∂m = ‖f‖ ^ p.toReal := by
  have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂m :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hp (Lp.aestronglyMeasurable f),
    ← Real.rpow_mul h_nonneg, inv_mul_cancel₀ (ENNReal.toReal_pos hp0 hp).ne', Real.rpow_one]

/-- The integral of the squared pointwise norm of an `L²` function is its squared `L²` norm. -/
theorem Lp.integral_norm_sq_eq_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] (f : Lp F 2 m) :
    ∫ x, ‖f x‖ ^ 2 ∂m = ‖f‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    Lp.integral_norm_rpow_eq_norm_rpow (by norm_num) (by norm_num) f

/-- L² convergence implies convergence of the integral of the squared norm, for any measure
and any normed additive group of values. -/
theorem tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub {α F ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α} {f : α → F}
    {g : ι → α → F} {l : Filter ι} (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (ht : Tendsto (fun i ↦ eLpNorm (g i - f) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, ‖g i x‖ ^ 2 ∂μ) l (𝓝 (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  have hLp : Tendsto (fun i ↦ (hg i).toLp (g i)) l (𝓝 (hf.toLp f)) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp] using ht
  have hnorm (u : α → F) (hu : MemLp u 2 μ) :
      ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    exact integral_congr_ae (hu.coeFn_toLp.fun_comp fun y ↦ ‖y‖ ^ 2)
  simpa only [hnorm] using hLp.norm.pow 2

/-- On a finite measure space, the `L¹` norm of an `Lᵖ` function, `1 ≤ p`, is at most
`μ(univ)^{1 - 1/p}` times its `Lᵖ` norm. -/
theorem Lp.integral_norm_le_mul_norm {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [IsFiniteMeasure m] [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp F p m) :
    ∫ x, ‖f x‖ ∂m ≤ (m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  have hexp : 0 ≤ 1 - 1 / p.toReal := by
    rcases eq_or_ne p ∞ with rfl | hp
    · simp
    · have h1p : 1 ≤ p.toReal := by
        simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
      exact sub_nonneg.2 (div_le_one_of_le₀ h1p (zero_le_one.trans h1p))
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := p) (μ := m) Fact.out
    (Lp.aestronglyMeasurable f)
  rw [ENNReal.toReal_one, div_one] at h
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def, mul_comm,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top m _))) h

/-- On a finite measure space, a function dominated pointwise by `K ‖f‖` for an `Lᵖ` function
`f`, `1 ≤ p`, has norm of its integral at most `K μ(univ)^{1 - 1/p} ‖f‖`. -/
theorem Lp.norm_integral_le_of_ae_norm_le_mul {alpha F G : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [IsFiniteMeasure m] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp F p m) {g : alpha → G} {K : ℝ}
    (hK : 0 ≤ K) (hg : ∀ᵐ x ∂m, ‖g x‖ ≤ K * ‖f x‖) :
    ‖∫ x, g x ∂m‖ ≤ K * (m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  calc ‖∫ x, g x ∂m‖ ≤ ∫ x, K * ‖f x‖ ∂m :=
        norm_integral_le_of_norm_le (((Lp.memLp f).integrable Fact.out).norm.const_mul K) hg
    _ = K * ∫ x, ‖f x‖ ∂m := integral_const_mul _ _
    _ ≤ K * ((m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖) := by
        gcongr
        exact Lp.integral_norm_le_mul_norm f
    _ = K * (m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := (mul_assoc _ _ _).symm

/-- For an `L²` function `f` on `t`, the integral of `‖f‖²` over a subset `s ⊆ t` is at most the
squared `L²` norm of `f`. -/
theorem Lp.setIntegral_norm_sq_le_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {s t : Set alpha} (f : Lp F 2 (m.restrict t))
    (hst : s ⊆ t) : ∫ x in s, ‖f x‖ ^ 2 ∂m ≤ ‖f‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  exact setIntegral_mono_set ((Lp.memLp f).integrable_norm_pow two_ne_zero)
    (ae_of_all _ fun _ => by positivity) hst.eventuallyLE

section Restrict

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F] {g : X → F}
  {s t : Set X}

/-- A function in `Lᵖ(t)`, `1 ≤ p`, is integrable on every subset `s ⊆ t` of finite measure. -/
theorem MemLp.integrableOn_of_subset {p : ℝ≥0∞}
    (hg : MemLp g p (μ.restrict t)) (hp : 1 ≤ p) (hst : s ⊆ t) (hs : μ s ≠ ⊤) :
    IntegrableOn g s μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hgs : MemLp g p (μ.restrict s) := by
    simpa [Measure.restrict_restrict_of_subset hst] using hg.restrict s
  exact hgs.integrable hp

/-- For a function `g` in `L²(t)`, the squared distance `‖g - c‖²` to a constant `c` is integrable
on every subset `s ⊆ t` of finite measure. -/
theorem MemLp.integrableOn_norm_sub_sq_of_subset
    (hg : MemLp g 2 (μ.restrict t)) (hst : s ⊆ t) (hs : μ s ≠ ⊤) (c : F) :
    IntegrableOn (fun x ↦ ‖g x - c‖ ^ 2) s μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hgs : MemLp g 2 (μ.restrict s) := by
    simpa [Measure.restrict_restrict_of_subset hst] using hg.restrict s
  exact (hgs.sub (memLp_const c)).integrable_norm_pow two_ne_zero

/-- On a set `s` of finite measure, a function in `Lᵖ(s)`, `1 ≤ p < ∞`, bounded almost
everywhere on `s` by `M` has `Lᵖ(s)` norm at most `μ(s)^{1/p} M`. Unlike
`MeasureTheory.Lp.norm_le_of_ae_bound`, no sign condition on `M` is needed. -/
theorem MemLp.norm_toLp_le_measureReal_rpow_mul {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hs : μ s ≠ ⊤) (hg : MemLp g p (μ.restrict s)) {M : ℝ}
    (hgM : ∀ᵐ x ∂μ.restrict s, ‖g x‖ ≤ M) :
    ‖hg.toLp g‖ ≤ μ.real s ^ p.toReal⁻¹ * M := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · -- On a null set both sides vanish.
    have hp0 : p.toReal⁻¹ ≠ 0 :=
      inv_ne_zero (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp).ne'
    rw [Lp.norm_toLp, Measure.restrict_eq_zero.2 h0, eLpNorm_measure_zero, measureReal_def, h0,
      ENNReal.toReal_zero, Real.zero_rpow hp0, zero_mul]
  · -- Otherwise the bound holds at some point, so `0 ≤ M`.
    have : (ae (μ.restrict s)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
    obtain ⟨x, hx⟩ := hgM.exists
    have h := Lp.norm_le_of_ae_bound ((norm_nonneg _).trans hx) (f := hg.toLp g) (by
      filter_upwards [hg.coeFn_toLp, hgM] with y hy hyM
      rwa [hy])
    rwa [← measureReal_restrict_apply_univ]

end Restrict

section IntegralRpow

variable {α 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

/-- For `0 < q < ∞`, the `q`-th power of the `L^q` norm of `f` is the norm of the integral of
`‖f‖ ^ q`. -/
theorem MemLp.eLpNorm_rpow_toReal_eq_enorm_integral {V : Type*} [NormedAddCommGroup V]
    {f : α → V} {q : ℝ≥0∞} (hf : MemLp f q μ) (hq0 : q ≠ 0) (hq : q ≠ ∞) :
    eLpNorm f q μ ^ q.toReal = ‖∫ x, ((‖f x‖ ^ q.toReal : ℝ) : 𝕜) ∂μ‖ₑ := by
  have hr := ENNReal.toReal_pos hq0 hq
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ q.toReal ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [hf.eLpNorm_eq_integral_rpow_norm hq0 hq, ENNReal.ofReal_rpow_of_nonneg
    (Real.rpow_nonneg hI _) hr.le, Real.rpow_inv_rpow hI hr.ne', integral_ofReal, ← ofReal_norm,
    RCLike.norm_ofReal, abs_of_nonneg hI]

end IntegralRpow

end MeasureTheory
