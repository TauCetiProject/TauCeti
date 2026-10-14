/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Norm inequalities in `Lᵖ` spaces

This file contains norm estimates for `Lᵖ` functions derived from almost-everywhere pointwise
bounds.

## Main declarations

* `TauCeti.Lp.norm_le_add_of_ae_norm_le`: an `Lᵖ` norm bound from pointwise domination by a
  two-term linear combination.
* `MeasureTheory.Lp.integral_norm_sq_eq_norm_sq`: the integral of the squared pointwise
  norm of an `L²` function is its squared `L²` norm.
* `MeasureTheory.Lp.integral_norm_mul_norm_le`: Cauchy--Schwarz, `∫ ‖f‖ ‖g‖ ≤ ‖f‖ ‖g‖` for
  `L²` functions, integrated against a measure dominated by theirs.
* `MeasureTheory.integrable_of_norm_le_mul_norm_mul_norm`: a function bounded almost everywhere
  by a constant times the product of the norms of two `L²` functions is integrable.
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

open scoped ENNReal

/-- The integral of the squared pointwise norm of an `L²` function is its squared `L²` norm. -/
theorem Lp.integral_norm_sq_eq_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] (f : Lp F 2 m) :
    ∫ x, ‖f x‖ ^ 2 ∂m = ‖f‖ ^ 2 := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hptop : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_lp := lpNorm_eq_integral_norm_rpow_toReal hp0 hptop (Lp.aestronglyMeasurable f)
  rw [ENNReal.toReal_ofNat] at h_lp
  have h_norm : ‖f‖ = lpNorm (⇑f) 2 m := by
    rw [Lp.norm_def, toReal_eLpNorm]
  have h_rpow : (fun x => ‖f x‖ ^ (2 : ℝ)) = fun x => ‖f x‖ ^ 2 := by
    funext x
    exact Real.rpow_two (‖f x‖)
  rw [h_rpow] at h_lp
  have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂m := integral_nonneg fun x => sq_nonneg _
  rw [h_norm, h_lp, ← Real.rpow_two, ← Real.rpow_mul h_nonneg, inv_mul_cancel₀ (by norm_num),
    Real.rpow_one]

/-- **Cauchy--Schwarz for `L²` functions on dominating measures.** If `m ≤ m₁` and `m ≤ m₂`,
then for `f ∈ L²(m₁)` and `g ∈ L²(m₂)` the integral of `‖f‖ ‖g‖` against `m` is at most
`‖f‖ ‖g‖`. Restricting both functions to a smaller set is the case `m = μ.restrict s`. -/
theorem Lp.integral_norm_mul_norm_le {alpha F G : Type*} [MeasurableSpace alpha]
    {m m₁ m₂ : Measure alpha} [NormedAddCommGroup F] [NormedAddCommGroup G] (h₁ : m ≤ m₁)
    (h₂ : m ≤ m₂) (f : Lp F 2 m₁) (g : Lp G 2 m₂) : ∫ x, ‖f x‖ * ‖g x‖ ∂m ≤ ‖f‖ * ‖g‖ := by
  have hf := ((Lp.memLp f).mono_measure h₁).norm
  have hg := ((Lp.memLp g).mono_measure h₂).norm
  -- The `L²(m)` inner product of the pointwise norms.
  have h := real_inner_le_norm (hf.toLp _) (hg.toLp _)
  rw [L2.inner_def, Lp.norm_toLp, Lp.norm_toLp,
    eLpNorm_norm _ ((Lp.aestronglyMeasurable f).mono_measure h₁),
    eLpNorm_norm _ ((Lp.aestronglyMeasurable g).mono_measure h₂)] at h
  calc ∫ x, ‖f x‖ * ‖g x‖ ∂m = ∫ x, inner ℝ (hf.toLp _ x) (hg.toLp _ x) ∂m := by
        refine integral_congr_ae ?_
        filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
        simp [h1, h2, mul_comm]
    _ ≤ (eLpNorm f 2 m).toReal * (eLpNorm g 2 m).toReal := h
    _ ≤ ‖f‖ * ‖g‖ := by
        rw [Lp.norm_def, Lp.norm_def]
        exact mul_le_mul (ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _ h₁))
          (ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_mono_measure _ h₂))
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- A function bounded almost everywhere by a constant times the product of the norms of two `L²`
functions is integrable. -/
theorem integrable_of_norm_le_mul_norm_mul_norm {alpha F G : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] [NormedAddCommGroup G] {m : Measure alpha} {h : alpha → ℝ}
    {P : alpha → F} {R : alpha → G} {C : ℝ} (hP : MemLp P 2 m) (hR : MemLp R 2 m)
    (hh : AEStronglyMeasurable h m) (hle : ∀ᵐ x ∂m, ‖h x‖ ≤ C * (‖P x‖ * ‖R x‖)) :
    Integrable h m :=
  ((hP.norm.integrable_mul hR.norm).const_mul C).mono' hh hle

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

end MeasureTheory
