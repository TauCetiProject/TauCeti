/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Oscillatory

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Abelian Laplace-moment theorems for iterated improper tail integrals

This file relates the repeated improper tail integrals `TauCeti.iteratedTailIntegral f (n + 1) 0` of
a Bochner-measurable function `f : ℝ → E` on `[0, ∞)` to the `p → 0⁺` limit of its Laplace moments
`∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t` and of the `n`-th derivatives of its Laplace
transform `p ↦ ∫ t in Ioi 0, exp (-(p * t)) • f t`.

Crucially, `f` and its intermediate tail integrals are **not** required to be absolutely integrable
on `(0, ∞)`: only conditional convergence of the improper integrals
`R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` as `R → ∞` for `m ≤ n` is needed. Combining this
Abelian theorem with `TauCeti.HasOscillatoryDecay` yields unconditional Laplace-derivative formulas
for the repeated tail integrals of oscillatory functions such as Fresnel integrals and negative-axis
oscillatory special functions.

## Main results

* `TauCeti.locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul`: integrability of
  `t ↦ exp (-(p * t)) • f t` on `(a, ∞)` implies `LocallyIntegrableOn f (Ici a)`.
* `TauCeti.integrableOn_exp_neg_mul_pow_smul_of_lt`: integrability of `t ↦ exp (-(q * t)) • f t` on
  `(0, ∞)` implies integrability of all polynomial moments `t ↦ (exp (-(p * t)) * t ^ j) • f t` for
  every `p > q`.
* `TauCeti.hasDerivAt_integral_exp_neg_mul_pow_smul` and
  `TauCeti.iteratedDeriv_integral_exp_neg_mul_smul`: differentiation under the Laplace integral on
  `{p | q < p}`.
* `TauCeti.tendsto_integral_exp_neg_mul_smul_nhdsGT_zero` and
  `TauCeti.tendsto_integral_exp_neg_mul_pow_smul_nhdsGT_zero`: if `t ↦ exp (-(p * t)) • f t` is
  integrable on `(0, ∞)` for every `p > 0` and all improper integrals
  `R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge as `R → ∞`, then
  `∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t → n ! • iteratedTailIntegral f (n + 1) 0` as
  `p → 0⁺`.
* `TauCeti.tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero`: normalized `n`-th
  derivative form `((-1) ^ n / n !) • iteratedDeriv n L p → iteratedTailIntegral f (n + 1) 0` as
  `p → 0⁺`.
* `TauCeti.HasOscillatoryDecay.tendsto_integral_exp_neg_mul_pow_mul_nhdsGT_zero` and
  `TauCeti.HasOscillatoryDecay.tendsto_iteratedDeriv_integral_exp_neg_mul_mul_nhdsGT_zero`:
  unconditional Abelian Laplace limits for functions satisfying `HasOscillatoryDecay`.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology
open scoped Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Exponential integrability and parametric differentiation of Laplace integrals -/

/-- If `t ↦ exp (-(p * t)) • f t` is integrable on `(a, ∞)`, then `f` is locally integrable on
`[a, ∞)`. -/
theorem locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul {f : ℝ → E} {a p : ℝ}
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi a)) :
    LocallyIntegrableOn f (Ici a) := by
  have hIci : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ici a) :=
    (integrableOn_Ici_iff_integrableOn_Ioi eNorm_ne_top).mpr hf
  have hmul : LocallyIntegrableOn
      (fun t : ℝ ↦ Real.exp (p * t) • (Real.exp (-(p * t)) • f t)) (Ici a) :=
    hIci.locallyIntegrableOn.continuousOn_smul isClosed_Ici.isLocallyClosed (by fun_prop)
  refine hmul.congr (ae_of_all _ fun t ↦ ?_)
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- Pointwise factorial bound `exp (-(p * t)) * t ^ j ≤ (j ! / (p - q) ^ j) * exp (-(q * t))` for
`q < p` and `0 ≤ t`. -/
private theorem exp_neg_mul_pow_le_of_lt {q p t : ℝ} (hqp : q < p) (ht : 0 ≤ t) (j : ℕ) :
    Real.exp (-(p * t)) * t ^ j ≤ (j.factorial / (p - q) ^ j) * Real.exp (-(q * t)) := by
  have hδ : 0 < p - q := sub_pos.mpr hqp
  have hfac := Real.pow_div_factorial_le_exp ((p - q) * t) (mul_nonneg hδ.le ht) j
  have h1 : (p - q) ^ j * (Real.exp (-(p * t)) * t ^ j) ≤ j.factorial * Real.exp (-(q * t)) := by
    have hmul := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (Nat.cast_pos.mpr j.factorial_pos)).mp hfac) (Real.exp_pos (-(p * t))).le
    calc
      (p - q) ^ j * (Real.exp (-(p * t)) * t ^ j)
          = ((p - q) * t) ^ j * Real.exp (-(p * t)) := by rw [mul_pow]; ring
      _ ≤ (Real.exp ((p - q) * t) * j.factorial) * Real.exp (-(p * t)) := hmul
      _ = j.factorial * Real.exp (-(q * t)) := by
          rw [mul_right_comm, ← Real.exp_add]
          ring_nf
  exact ((le_div_iff₀' (pow_pos hδ j)).mpr h1).trans_eq (div_mul_eq_mul_div _ _ _).symm

/-- If `t ↦ exp (-(q * t)) • f t` is Bochner integrable on `(0, ∞)` and `q < p`, then every
polynomial moment `t ↦ (exp (-(p * t)) * t ^ j) • f t` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_pow_smul_of_lt {f : ℝ → E} {q p : ℝ} (hqp : q < p)
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t)) • f t) (Ioi 0)) (j : ℕ) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • f t) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • f t) (volume.restrict (Ioi 0)) := by
    refine (((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-((p - q) * t)) * t ^ j)
      |>.aestronglyMeasurable).smul hf.aestronglyMeasurable).congr (ae_of_all _ fun t ↦ ?_)
    change (Real.exp (-((p - q) * t)) * t ^ j) • (Real.exp (-(q * t)) • f t) = _
    rw [smul_smul, mul_right_comm, ← Real.exp_add]
    have hexp : -((p - q) * t) + -(q * t) = -(p * t) := by ring
    rw [hexp]
  refine (hf.norm.const_mul (j.factorial / (p - q) ^ j)).mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_smul, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _)),
    Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (exp_neg_mul_pow_le_of_lt hqp ht.le j) (norm_nonneg _)

/-- Differentiation under the integral sign for the Laplace moments
`r ↦ ∫ t in Ioi 0, (exp (-(r * t)) * t ^ j) • f t` on `{r | q < r}`. -/
theorem hasDerivAt_integral_exp_neg_mul_pow_smul {f : ℝ → E} {q p : ℝ} (hqp : q < p)
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t)) • f t) (Ioi 0)) (j : ℕ) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ioi 0, (Real.exp (-(r * t)) * t ^ j) • f t)
      (-(∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ (j + 1)) • f t)) p := by
  let m := (q + p) / 2
  have hqm : q < m := by dsimp [m]; linarith
  have hmp : m < p := by dsimp [m]; linarith
  let F : ℝ → ℝ → E := fun r t ↦ (Real.exp (-(r * t)) * t ^ j) • f t
  let F' : ℝ → ℝ → E := fun r t ↦ -((Real.exp (-(r * t)) * t ^ (j + 1)) • f t)
  have hF_meas : ∀ᶠ r in 𝓝 p, AEStronglyMeasurable (F r) (volume.restrict (Ioi 0)) := by
    filter_upwards [Ioi_mem_nhds hqp] with r (hr : q < r)
    exact (integrableOn_exp_neg_mul_pow_smul_of_lt hr hf j).aestronglyMeasurable
  have hbound_int : Integrable (fun t : ℝ ↦ ‖(Real.exp (-(m * t)) * t ^ (j + 1)) • f t‖)
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_neg_mul_pow_smul_of_lt hqm hf (j + 1)).norm
  have hF'_meas : AEStronglyMeasurable (F' p) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_neg_mul_pow_smul_of_lt hqp hf (j + 1)).neg.aestronglyMeasurable
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioi m) (Ioi_mem_nhds hmp)
    hF_meas (integrableOn_exp_neg_mul_pow_smul_of_lt hqp hf j) hF'_meas ?_ hbound_int ?_
  · simpa [F, F', integral_neg] using hdom.2
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (ht : 0 < t) r (hr : m < r)
    simp only [F', norm_neg, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (pow_nonneg ht.le _))
      (norm_nonneg _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _ r _
    have hd : HasDerivAt (fun r : ℝ ↦ Real.exp (-(r * t)) * t ^ j)
        (-(Real.exp (-(r * t)) * t ^ (j + 1))) r :=
      ((((hasDerivAt_id r).mul_const t).neg.exp).mul_const (t ^ j)).congr_deriv
        (by simp [pow_succ]; ring)
    exact (hd.smul_const (f t)).congr_deriv (neg_smul _ _)

/-- Formula for the `n`-th derivative of the Laplace integral
`r ↦ ∫ t in Ioi 0, exp (-(r * t)) • f t` at any `p > q` where `t ↦ exp (-(q * t)) • f t` is
integrable on `(0, ∞)`. -/
theorem iteratedDeriv_integral_exp_neg_mul_smul {f : ℝ → E} {q p : ℝ} (hqp : q < p)
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t)) • f t) (Ioi 0)) (n : ℕ) :
    iteratedDeriv n (fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) • f t) p =
      (-1 : ℝ) ^ n • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ n) • f t := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : (iteratedDeriv n fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) • f t) =ᶠ[𝓝 p]
        ((-1 : ℝ) ^ n • fun r : ℝ ↦ ∫ t in Ioi 0, (Real.exp (-(r * t)) * t ^ n) • f t) := by
      filter_upwards [Ioi_mem_nhds hqp] with r hr using ih hr
    rw [heq.deriv_eq,
      ((hasDerivAt_integral_exp_neg_mul_pow_smul hqp hf n).const_smul ((-1 : ℝ) ^ n)).deriv,
      smul_neg, ← neg_smul, pow_succ, mul_neg, mul_one]

/-! ### Fubini integration by parts on `[0, R]` and `(0, ∞)` -/

/-- Auxiliary triangle kernel on `(0, R] × (0, R]` for finite-interval integration by parts of a
locally integrable function `g : ℝ → E` against a `C¹` scalar weight. -/
private def ibpTriangleKernel (φ' : ℝ → ℝ) (g : ℝ → E) (R : ℝ) (x : ℝ × ℝ) : E :=
  {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R}.indicator (fun x ↦ φ' x.1 • g x.2) x

/-- Product integrability of `ibpTriangleKernel φ' g R` on `ℝ × ℝ`. -/
private theorem integrable_ibpTriangleKernel {φ' : ℝ → ℝ} {g : ℝ → E} {R : ℝ}
    (hg : LocallyIntegrableOn g (Ici 0)) (hφ' : ContinuousOn φ' (Icc 0 R)) :
    Integrable (ibpTriangleKernel φ' g R) (volume.prod volume) := by
  have hS : MeasurableSet {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_fst continuous_snd).measurableSet.inter
        (isClosed_le continuous_snd continuous_const).measurableSet)
  have hφ_int : Integrable ((Icc 0 R).indicator φ') volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hφ'.integrableOn_Icc
  have hg_int : Integrable ((Ioc 0 R).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((hg.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).mono_set
        Ioc_subset_Icc_self)
  refine ((hφ_int.smul_prod hg_int).indicator hS).congr (ae_of_all _ fun ⟨s, t⟩ ↦ ?_)
  simp only [ibpTriangleKernel]
  by_cases hx : 0 < s ∧ s < t ∧ t ≤ R
  · have hx' : (s, t) ∈ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R} := hx
    rw [indicator_of_mem hx', indicator_of_mem hx',
      indicator_of_mem (show s ∈ Icc 0 R from ⟨hx.1.le, hx.2.1.le.trans hx.2.2⟩),
      indicator_of_mem (show t ∈ Ioc 0 R from ⟨hx.1.trans hx.2.1, hx.2.2⟩)]
  · have hx' : (s, t) ∉ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R} := hx
    rw [indicator_of_notMem hx', indicator_of_notMem hx']

/-- Horizontal and vertical slice integrals of `ibpTriangleKernel φ' g R`. -/
private theorem slice_integrals_ibpTriangleKernel [CompleteSpace E] {φ φ' : ℝ → ℝ} {g : ℝ → E}
    {R : ℝ} (hφ : ∀ s ∈ Icc 0 R, HasDerivAt φ (φ' s) s) (hφ' : ContinuousOn φ' (Icc 0 R)) :
    (∀ s : ℝ, (∫ t, ibpTriangleKernel φ' g R (s, t)) =
        (Ioc 0 R).indicator (fun r ↦ φ' r • ∫ t in r..R, g t) s) ∧
      (∀ t : ℝ, (∫ s, ibpTriangleKernel φ' g R (s, t)) =
        (Ioc 0 R).indicator (fun r ↦ (φ r - φ 0) • g r) t) := by
  refine ⟨fun s ↦ ?_, fun t ↦ ?_⟩
  · by_cases hs : s ∈ Ioc 0 R
    · have hpt : (fun t ↦ ibpTriangleKernel φ' g R (s, t)) =
          (Ioc s R).indicator fun t ↦ φ' s • g t := by
        ext t; simp only [ibpTriangleKernel]
        by_cases ht : t ∈ Ioc s R
        · rw [indicator_of_mem (show (s, t) ∈ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R} from
            ⟨hs.1, ht.1, ht.2⟩), indicator_of_mem ht]
        · rw [indicator_of_notMem (show (s, t) ∉ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R}
            from fun h ↦ ht ⟨h.2.1, h.2.2⟩), indicator_of_notMem ht]
      rw [hpt, indicator_of_mem hs, integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hs.2, intervalIntegral.integral_smul]
    · have hpt : (fun t ↦ ibpTriangleKernel φ' g R (s, t)) = 0 := by
        ext t; simp only [ibpTriangleKernel, Pi.zero_apply]
        exact indicator_of_notMem (show (s, t) ∉ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R}
          from fun h ↦ hs ⟨h.1, h.2.1.le.trans h.2.2⟩) _
      simp [hpt, hs]
  · by_cases ht : t ∈ Ioc 0 R
    · have hpt : (fun s ↦ ibpTriangleKernel φ' g R (s, t)) =
          (Ioo 0 t).indicator fun s ↦ φ' s • g t := by
        ext s; simp only [ibpTriangleKernel]
        by_cases hs : s ∈ Ioo 0 t
        · rw [indicator_of_mem (show (s, t) ∈ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R} from
            ⟨hs.1, hs.2, ht.2⟩), indicator_of_mem hs]
        · rw [indicator_of_notMem (show (s, t) ∉ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R}
            from fun h ↦ hs ⟨h.1, h.2.1⟩), indicator_of_notMem hs]
      have hsub : uIcc 0 t ⊆ Icc 0 R := by
        rw [uIcc_of_le ht.1.le]; exact Icc_subset_Icc_right ht.2
      have hftc : ∫ s in 0..t, φ' s = φ t - φ 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦ hφ s (hsub hs))
          (hφ'.mono hsub).intervalIntegrable
      rw [hpt, indicator_of_mem ht, integral_indicator measurableSet_Ioo,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le,
        intervalIntegral.integral_smul_const, hftc]
    · have hpt : (fun s ↦ ibpTriangleKernel φ' g R (s, t)) = 0 := by
        ext s; simp only [ibpTriangleKernel, Pi.zero_apply]
        exact indicator_of_notMem (show (s, t) ∉ {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 ≤ R}
          from fun h ↦ ht ⟨h.1.trans h.2.1, h.2.2⟩) _
      simp [hpt, ht]

/-- Finite-interval integration by parts on `[0, R]` (`0 ≤ R`) for a locally integrable function
`g : ℝ → E` against a `C¹` scalar weight `φ` via Fubini's theorem. -/
private theorem intervalIntegral_smul_eq_add_integral_deriv_smul [CompleteSpace E]
    {φ φ' : ℝ → ℝ} {g : ℝ → E} {R : ℝ} (hR : 0 ≤ R) (hg : LocallyIntegrableOn g (Ici 0))
    (hφ : ∀ s ∈ Icc 0 R, HasDerivAt φ (φ' s) s) (hφ' : ContinuousOn φ' (Icc 0 R)) :
    ∫ t in 0..R, φ t • g t = φ 0 • (∫ t in 0..R, g t) + ∫ s in 0..R, φ' s • (∫ t in s..R, g t) := by
  have hK := integrable_ibpTriangleKernel hg hφ'
  obtain ⟨hslice_s, hslice_t⟩ := slice_integrals_ibpTriangleKernel (g := g) hφ hφ'
  have hswap : ∫ s in 0..R, φ' s • (∫ t in s..R, g t) = ∫ t in 0..R, (φ t - φ 0) • g t := by
    rw [intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR,
      ← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
    calc
      ∫ s, (Ioc 0 R).indicator (fun r ↦ φ' r • ∫ t in r..R, g t) s
          = ∫ s, ∫ t, ibpTriangleKernel φ' g R (s, t) :=
            integral_congr_ae (ae_of_all _ fun s ↦ (hslice_s s).symm)
      _ = ∫ t, ∫ s, ibpTriangleKernel φ' g R (s, t) := integral_integral_swap hK
      _ = ∫ t, (Ioc 0 R).indicator (fun r ↦ (φ r - φ 0) • g r) t :=
            integral_congr_ae (ae_of_all _ hslice_t)
  have hg_int : IntervalIntegrable g volume 0 R :=
    (hg.integrableOn_compact_subset
      (by rw [uIcc_of_le hR]; exact Icc_subset_Ici_self) isCompact_uIcc).intervalIntegrable
  have hφ_cont : ContinuousOn φ [[0, R]] := by
    rw [uIcc_of_le hR]
    exact fun s hs ↦ (hφ s hs).continuousAt.continuousWithinAt
  have hφg_int : IntervalIntegrable (fun t ↦ φ t • g t) volume 0 R :=
    hg_int.continuousOn_smul hφ_cont
  rw [hswap]
  simp_rw [sub_smul]
  rw [intervalIntegral.integral_sub hφg_int
      (show IntervalIntegrable (fun t ↦ φ 0 • g t) volume 0 R from hg_int.smul (φ 0)),
    intervalIntegral.integral_smul, add_sub_cancel]

omit [NormedSpace ℝ E] in
/-- A function that is continuous on `[0, ∞)` and tends to `0` at `+∞` is uniformly bounded in norm
on `[0, ∞)`. -/
private theorem exists_norm_le_of_continuousOn_of_tendsto_zero {h : ℝ → E}
    (hh_cont : ContinuousOn h (Ici 0)) (hh_top : Tendsto h atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ici (0 : ℝ), ‖h s‖ ≤ C := by
  obtain ⟨R₀, hR₀⟩ :=
    eventually_atTop.mp (hh_top.eventually (Metric.closedBall_mem_nhds 0 zero_lt_one))
  let M := max 0 R₀
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hh_cont.mono (Icc_subset_Ici_self : Icc 0 M ⊆ Ici 0))
  refine ⟨max C₀ 1, le_max_of_le_right zero_le_one, fun s (hs : 0 ≤ s) ↦ ?_⟩
  rcases le_total s M with hsM | hMs
  · exact (hC₀ s ⟨hs, hsM⟩).trans (le_max_left _ _)
  · have h1 : ‖h s‖ ≤ 1 := by simpa using hR₀ s ((le_max_right 0 R₀).trans hMs)
    exact h1.trans (le_max_right _ _)

/-- Improper integration by parts on `(0, ∞)` for a conditionally convergent improper tail integral
`G := iteratedTailIntegral g 1` against a `C¹` weight `φ` whose derivative `φ'` is integrable on
`(0, ∞)`. -/
private theorem integral_Ioi_smul_eq_of_tendsto [CompleteSpace E] {φ φ' : ℝ → ℝ} {g : ℝ → E}
    (hg_loc : LocallyIntegrableOn g (Ici 0))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, g t) atTop (𝓝 L))
    (hφ : ∀ s ≥ 0, HasDerivAt φ (φ' s) s) (hφ' : ContinuousOn φ' (Ici 0))
    (hφ'_int : IntegrableOn φ' (Ioi 0)) (hφg_int : IntegrableOn (fun t ↦ φ t • g t) (Ioi 0)) :
    IntegrableOn (fun s ↦ φ' s • iteratedTailIntegral g 1 s) (Ioi 0) ∧
      ∫ t in Ioi 0, φ t • g t =
        φ 0 • iteratedTailIntegral g 1 0 + ∫ s in Ioi 0, φ' s • iteratedTailIntegral g 1 s := by
  have hg_loc0 : LocallyIntegrableOn (iteratedTailIntegral g 0) (Ici 0) := by simpa using hg_loc
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral g 0 t)
      atTop (𝓝 L) := by simpa using hg_conv
  set G := iteratedTailIntegral g 1
  have hG_cont : ContinuousOn G (Ici 0) := continuousOn_iteratedTailIntegral_succ hg_loc0 hL
  have hG_top : Tendsto G atTop (𝓝 0) := tendsto_iteratedTailIntegral_succ_atTop hg_loc0 hL
  obtain ⟨C, _, hC⟩ := exists_norm_le_of_continuousOn_of_tendsto_zero hG_cont hG_top
  have hφ'G_int : IntegrableOn (fun s ↦ φ' s • G s) (Ioi 0) :=
    hφ'_int.smul_bdd C ((hG_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ hC s hs.le)
  refine ⟨hφ'G_int, ?_⟩
  have hLHS : Tendsto (fun R : ℝ ↦ ∫ t in 0..R, φ t • g t) atTop (𝓝 (∫ t in Ioi 0, φ t • g t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hφg_int tendsto_id
  have hRHS : Tendsto (fun R : ℝ ↦
      φ 0 • (G 0 - G R) + (∫ s in 0..R, φ' s • G s) - (∫ s in 0..R, φ' s) • G R) atTop
      (𝓝 (φ 0 • G 0 + ∫ s in Ioi 0, φ' s • G s)) := by
    have h1 : Tendsto (fun R : ℝ ↦ φ 0 • (G 0 - G R)) atTop (𝓝 (φ 0 • G 0)) := by
      simpa using (tendsto_const_nhds.sub hG_top).const_smul (φ 0)
    have h2 : Tendsto (fun R : ℝ ↦ ∫ s in 0..R, φ' s • G s) atTop (𝓝 (∫ s in Ioi 0, φ' s • G s)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hφ'G_int tendsto_id
    have h3 : Tendsto (fun R : ℝ ↦ (∫ s in 0..R, φ' s) • G R) atTop (𝓝 0) := by
      simpa using (intervalIntegral_tendsto_integral_Ioi 0 hφ'_int tendsto_id).smul hG_top
    simpa using (h1.add h2).sub h3
  refine tendsto_nhds_unique hLHS (hRHS.congr' ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hibp := intervalIntegral_smul_eq_add_integral_deriv_smul hR hg_loc
    (fun s hs ↦ hφ s hs.1) (hφ'.mono Icc_subset_Ici_self)
  have h0R : ∫ t in 0..R, g t = G 0 - G R := by
    simpa using (iteratedTailIntegral_succ_sub_eq_intervalIntegral hg_loc0 hL hR).symm
  have hsR : ∫ s in 0..R, φ' s • (∫ t in s..R, g t) =
      (∫ s in 0..R, φ' s • G s) - (∫ s in 0..R, φ' s) • G R := by
    have hcongr : ∫ s in 0..R, φ' s • (∫ t in s..R, g t) =
        ∫ s in 0..R, (φ' s • G s - φ' s • G R) := by
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le hR] at hs
      have hsub := iteratedTailIntegral_succ_sub_eq_intervalIntegral
        (hg_loc0.mono_set (Ici_subset_Ici.mpr hs.1))
        (tendsto_intervalIntegral_iteratedTailIntegral_of_ge hg_loc0 hL hs.1) hs.2
      simp only [iteratedTailIntegral_zero_eq] at hsub
      rw [← hsub, smul_sub]
    have hi1 : IntervalIntegrable (fun s ↦ φ' s • G s) volume 0 R :=
      (ContinuousOn.smul (hφ'.mono Icc_subset_Ici_self)
        (hG_cont.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc hR
    have hi2 : IntervalIntegrable (fun s ↦ φ' s • G R) volume 0 R :=
      (ContinuousOn.smul (hφ'.mono Icc_subset_Ici_self)
        continuousOn_const).intervalIntegrable_of_Icc hR
    rw [hcongr, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_smul_const]
  rw [hibp, h0R, hsR, add_sub_assoc]

/-- Improper integration by parts for `∫ t in Ioi 0, exp (-(p * t)) • g t` (`0 < p`). -/
private theorem integral_Ioi_exp_neg_mul_smul_eq [CompleteSpace E] {g : ℝ → E} {p : ℝ} (hp : 0 < p)
    (hg_loc : LocallyIntegrableOn g (Ici 0))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, g t) atTop (𝓝 L))
    (hg_int : IntegrableOn (fun t ↦ Real.exp (-(p * t)) • g t) (Ioi 0)) :
    ∫ t in Ioi 0, Real.exp (-(p * t)) • g t =
      iteratedTailIntegral g 1 0 -
        p • ∫ s in Ioi 0, Real.exp (-(p * s)) • iteratedTailIntegral g 1 s := by
  have hφ : ∀ s ≥ 0, HasDerivAt (fun t : ℝ ↦ Real.exp (-(p * t)))
      (-p * Real.exp (-(p * s))) s := fun s _ ↦
    (((hasDerivAt_id s).const_mul p).neg.exp).congr_deriv (by simp; ring)
  have hφ'_int : IntegrableOn (fun s : ℝ ↦ -p * Real.exp (-(p * s))) (Ioi 0) :=
    IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi 0 hp).const_mul (-p))
      (fun s _ ↦ by simp only [neg_mul]) measurableSet_Ioi
  obtain ⟨_, heq⟩ := integral_Ioi_smul_eq_of_tendsto hg_loc hg_conv hφ (by fun_prop) hφ'_int hg_int
  rw [heq, mul_zero, neg_zero, Real.exp_zero, one_smul]
  simp_rw [mul_smul, neg_smul]
  rw [integral_neg, integral_smul, sub_eq_add_neg]

/-- Improper integration by parts for `∫ t in Ioi 0, (exp (-(p * t)) * t ^ (m + 1)) • g t`
(`0 < p`). -/
private theorem integral_Ioi_exp_neg_mul_pow_succ_smul_eq [CompleteSpace E] {g : ℝ → E} {p : ℝ}
    (hp : 0 < p) (m : ℕ) (hg_loc : LocallyIntegrableOn g (Ici 0))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, g t) atTop (𝓝 L))
    (hg_int : IntegrableOn (fun t ↦ (Real.exp (-(p * t)) * t ^ (m + 1)) • g t) (Ioi 0)) :
    ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ (m + 1)) • g t =
      ((m + 1 : ℝ) • ∫ s in Ioi 0, (Real.exp (-(p * s)) * s ^ m) • iteratedTailIntegral g 1 s) -
        p • ∫ s in Ioi 0, (Real.exp (-(p * s)) * s ^ (m + 1)) • iteratedTailIntegral g 1 s := by
  have hg_loc0 : LocallyIntegrableOn (iteratedTailIntegral g 0) (Ici 0) := by simpa using hg_loc
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral g 0 t)
      atTop (𝓝 L) := by simpa using hg_conv
  let G := iteratedTailIntegral g 1
  let φ' : ℝ → ℝ := fun s ↦
    (m + 1 : ℝ) * (Real.exp (-(p * s)) * s ^ m) - p * (Real.exp (-(p * s)) * s ^ (m + 1))
  have hφ : ∀ s ≥ 0, HasDerivAt (fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ (m + 1)) (φ' s) s := by
    intro s _
    have hd1 : HasDerivAt (fun t : ℝ ↦ Real.exp (-(p * t))) (-p * Real.exp (-(p * s))) s :=
      (((hasDerivAt_id s).const_mul p).neg.exp).congr_deriv (by simp; ring)
    have hd2 : HasDerivAt (fun t : ℝ ↦ t ^ (m + 1)) ((m + 1 : ℝ) * s ^ m) s := by
      simpa using hasDerivAt_pow (m + 1) s
    exact (hd1.mul hd2).congr_deriv (by dsimp [φ']; ring)
  have hpow_int (k : ℕ) : IntegrableOn (fun s : ℝ ↦ Real.exp (-(p * s)) * s ^ k) (Ioi 0) := by
    simpa only [mul_comm] using integrableOn_pow_mul_exp_neg_mul_Ioi k hp
  have hφ'_int : IntegrableOn φ' (Ioi 0) :=
    ((hpow_int m).const_mul (m + 1 : ℝ)).sub ((hpow_int (m + 1)).const_mul p)
  obtain ⟨_, heq⟩ := integral_Ioi_smul_eq_of_tendsto hg_loc hg_conv hφ (by fun_prop) hφ'_int hg_int
  have hG_cont : ContinuousOn G (Ici 0) := continuousOn_iteratedTailIntegral_succ hg_loc0 hL
  obtain ⟨C, _, hC⟩ := exists_norm_le_of_continuousOn_of_tendsto_zero hG_cont
    (tendsto_iteratedTailIntegral_succ_atTop hg_loc0 hL)
  have hG_int (k : ℕ) : IntegrableOn (fun s : ℝ ↦ (Real.exp (-(p * s)) * s ^ k) • G s) (Ioi 0) :=
    (hpow_int k).smul_bdd C
      ((hG_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ hC s hs.le)
  rw [heq, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_smul, zero_add]
  have hpt : (fun s : ℝ ↦ φ' s • G s) =
      ((m + 1 : ℝ) • fun s : ℝ ↦ (Real.exp (-(p * s)) * s ^ m) • G s) -
        (p • fun s : ℝ ↦ (Real.exp (-(p * s)) * s ^ (m + 1)) • G s) := by
    ext s
    simp only [φ', Pi.sub_apply, Pi.smul_apply]
    rw [sub_smul, mul_smul (m + 1 : ℝ), mul_smul p]
  dsimp [G] at hpt hG_int
  rw [hpt, Pi.sub_def, integral_sub ((hG_int m).smul (m + 1 : ℝ)) ((hG_int (m + 1)).smul p),
    Pi.smul_def, Pi.smul_def, integral_smul, integral_smul]

/-! ### Vanishing of rescaled Laplace moments and the Abelian theorem -/

/-- Leaf case (`k = 0`): if `h` is continuous on `[0, ∞)` and `h(t) → 0` as `t → ∞`, then
`p ^ (j + 1) • ∫ t in Ioi 0, (exp (-(p * t)) * t ^ j) • h t → 0` as `p → 0⁺`. -/
private theorem tendsto_pow_succ_smul_integral_exp_neg_mul_pow_smul_zero {h : ℝ → E}
    (hh_cont : ContinuousOn h (Ici 0)) (hh_top : Tendsto h atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun p : ℝ ↦ p ^ (j + 1) • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_le_of_continuousOn_of_tendsto_zero hh_cont hh_top
  let F : ℝ → ℝ → E := fun p u ↦ (Real.exp (-u) * u ^ j) • h (u / p)
  have hchg {p : ℝ} (hp : 0 < p) :
      p ^ (j + 1) • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t = ∫ u in Ioi 0, F p u := by
    have hsub := integral_comp_mul_left_Ioi' (F p) (0 : ℝ) hp
    rw [mul_zero] at hsub
    rw [← hsub, pow_succ', mul_smul]
    congr 1
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    dsimp [F]
    rw [mul_div_cancel_left₀ t hp.ne', smul_smul]
    congr 1
    rw [mul_pow]
    ring
  have hdom : Tendsto (fun p : ℝ ↦ ∫ u in Ioi 0, F p u)
      (𝓝[>] 0) (𝓝 (∫ _ in Ioi (0 : ℝ), (0 : E))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ ↦ C * (u ^ j * Real.exp (-u))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
      have hdiv : ContinuousOn (fun u : ℝ ↦ h (u / p)) (Ioi 0) :=
        hh_cont.comp ((continuous_id.div_const p).continuousOn) fun u (hu : 0 < u) ↦
          div_nonneg hu.le hp.le
      exact (ContinuousOn.smul
        ((by fun_prop : Continuous fun u : ℝ ↦ Real.exp (-u) * u ^ j).continuousOn)
        hdiv).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u (hu : 0 < u)
      dsimp [F]
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hu.le _)),
        mul_comm (Real.exp (-u)), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC (u / p) (div_nonneg hu.le hp.le))
        (mul_nonneg (pow_nonneg hu.le _) (Real.exp_pos _).le)
    · simpa only [one_mul] using (integrableOn_pow_mul_exp_neg_mul_Ioi j one_pos).const_mul C
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u (hu : 0 < u)
      dsimp [F]
      have hutop : Tendsto (fun p : ℝ ↦ u / p) (𝓝[>] 0) atTop :=
        (Tendsto.const_mul_atTop hu tendsto_inv_nhdsGT_zero).congr fun p ↦ (div_eq_mul_inv u p).symm
      simpa using (hh_top.comp hutop).const_smul (Real.exp (-u) * u ^ j)
  rw [integral_zero] at hdom
  exact hdom.congr' (by filter_upwards [self_mem_nhdsWithin] with p hp using (hchg hp).symm)

/-- Inductive vanishing lemma (`k ≤ j`): if `h` is continuous on `[0, ∞)`, `h(t) → 0` as `t → ∞`,
and all repeated improper tail integrals `R ↦ ∫ t in 0..R, iteratedTailIntegral h r t` (`r < k`)
converge as `R → ∞`, then
`p ^ (j + 1 - k) • ∫ t in Ioi 0, (exp (-(p * t)) * t ^ j) • h t → 0` as `p → 0⁺`. -/
private theorem tendsto_pow_sub_smul_integral_exp_neg_mul_pow_smul_zero [CompleteSpace E] :
    ∀ {k j : ℕ}, k ≤ j → ∀ {h : ℝ → E}, ContinuousOn h (Ici 0) → Tendsto h atTop (𝓝 0) →
      (∀ r < k, ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral h r t) atTop (𝓝 L)) →
      Tendsto (fun p : ℝ ↦ p ^ (j + 1 - k) • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t)
        (𝓝[>] 0) (𝓝 0)
  | 0, j, _, h, hh_cont, hh_top, _ => by
      simpa using tendsto_pow_succ_smul_integral_exp_neg_mul_pow_smul_zero hh_cont hh_top j
  | k + 1, j, hkj, h, hh_cont, hh_top, hh_conv => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hkm : k ≤ m := Nat.le_of_succ_le_succ hkj
      have hloc : LocallyIntegrableOn h (Ici 0) := hh_cont.locallyIntegrableOn measurableSet_Ici
      have hloc0 : LocallyIntegrableOn (iteratedTailIntegral h 0) (Ici 0) := by simpa using hloc
      obtain ⟨L0, hL0⟩ := hh_conv 0 (Nat.zero_lt_succ k)
      have hconv0 : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, h t) atTop (𝓝 L) :=
        ⟨L0, by simpa using hL0⟩
      let H := iteratedTailIntegral h 1
      have hH_cont : ContinuousOn H (Ici 0) := continuousOn_iteratedTailIntegral_succ hloc0 hL0
      have hH_top : Tendsto H atTop (𝓝 0) := tendsto_iteratedTailIntegral_succ_atTop hloc0 hL0
      have hH_conv : ∀ r < k,
          ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral H r t) atTop (𝓝 L) := by
        intro r hr
        dsimp [H]
        simpa only [← iteratedTailIntegral_succ'] using hh_conv (r + 1) (Nat.succ_lt_succ hr)
      obtain ⟨C, _, hC⟩ := exists_norm_le_of_continuousOn_of_tendsto_zero hh_cont hh_top
      have hh_int {p : ℝ} (hp : 0 < p) :
          IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ (m + 1)) • h t) (Ioi 0) := by
        have hpow : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ (m + 1)) (Ioi 0) := by
          simpa only [mul_comm] using integrableOn_pow_mul_exp_neg_mul_Ioi (m + 1) hp
        exact hpow.smul_bdd C
          ((hh_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ hC t ht.le)
      have ht1 := (tendsto_pow_sub_smul_integral_exp_neg_mul_pow_smul_zero hkm hH_cont hH_top
        hH_conv).const_smul (m + 1 : ℝ)
      have ht2 := tendsto_pow_sub_smul_integral_exp_neg_mul_pow_smul_zero (Nat.le_succ_of_le hkm)
        hH_cont hH_top hH_conv
      have hdiff : Tendsto (fun p : ℝ ↦
          ((m + 1 : ℝ) • (p ^ (m + 1 - k) • ∫ s in Ioi 0, (Real.exp (-(p * s)) * s ^ m) • H s)) -
            p ^ (m + 2 - k) • ∫ s in Ioi 0, (Real.exp (-(p * s)) * s ^ (m + 1)) • H s)
          (𝓝[>] 0) (𝓝 0) := by
        simpa using ht1.sub ht2
      refine hdiff.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
      have hexp1 : m + 1 + 1 - (k + 1) = m + 1 - k := by omega
      have hexp2 : m + 2 - k = m + 1 - k + 1 := by omega
      dsimp [H]
      rw [hexp1, integral_Ioi_exp_neg_mul_pow_succ_smul_eq hp m hloc hconv0 (hh_int hp),
        smul_sub, smul_comm, hexp2, pow_succ, mul_smul]

/-- Base case (`n = 0`) of the Abelian Laplace theorem assuming `[CompleteSpace E]`. -/
private theorem tendsto_integral_exp_neg_mul_smul_nhdsGT_zero_aux [CompleteSpace E] {f : ℝ → E}
    (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, f t) atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) • f t) (𝓝[>] 0)
      (𝓝 (iteratedTailIntegral f 1 0)) := by
  have hloc := locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul (hf 1 one_pos)
  have hloc0 : LocallyIntegrableOn (iteratedTailIntegral f 0) (Ici 0) := by simpa using hloc
  obtain ⟨L0, hL0⟩ : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral f 0 t)
      atTop (𝓝 L) := by simpa using hconv
  let G := iteratedTailIntegral f 1
  have hrem : Tendsto (fun p : ℝ ↦ p • ∫ s in Ioi 0, Real.exp (-(p * s)) • G s)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_pow_succ_smul_integral_exp_neg_mul_pow_smul_zero
      (continuousOn_iteratedTailIntegral_succ hloc0 hL0)
      (tendsto_iteratedTailIntegral_succ_atTop hloc0 hL0) 0
  have hlim : Tendsto (fun p : ℝ ↦ G 0 - p • ∫ s in Ioi 0, Real.exp (-(p * s)) • G s)
      (𝓝[>] 0) (𝓝 (G 0)) := by
    simpa using tendsto_const_nhds.sub hrem
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  exact (integral_Ioi_exp_neg_mul_smul_eq hp hloc hconv (hf p hp)).symm

/-- **Abelian Laplace-moment theorem for `iteratedTailIntegral`.** If `t ↦ exp (-(p * t)) • f t` is
Bochner integrable on `(0, ∞)` for every `p > 0` and all improper tail integrals
`R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge as `R → ∞`, then
`∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t → n ! • iteratedTailIntegral f (n + 1) 0` as
`p → 0⁺`. -/
theorem tendsto_integral_exp_neg_mul_pow_smul_nhdsGT_zero {f : ℝ → E} {n : ℕ}
    (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∀ m ≤ n, ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral f m t)
      atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ n) • f t) (𝓝[>] 0)
      (𝓝 ((n.factorial : ℝ) • iteratedTailIntegral f (n + 1) 0)) := by
  by_cases hE : CompleteSpace E
  swap
  · have hzero : iteratedTailIntegral f (n + 1) 0 = 0 := by
      rw [iteratedTailIntegral_succ]
      simp_rw [intervalIntegral, integral_of_not_completeSpace hE, sub_zero]
      exact tendsto_const_nhds.limUnder_eq
    simp_rw [integral_of_not_completeSpace hE, hzero, smul_zero]
    exact tendsto_const_nhds
  induction n generalizing f with
  | zero =>
    simpa using tendsto_integral_exp_neg_mul_smul_nhdsGT_zero_aux hf (by simpa using hconv 0 le_rfl)
  | succ n ih =>
    have hloc := locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul (hf 1 one_pos)
    have hloc0 : LocallyIntegrableOn (iteratedTailIntegral f 0) (Ici 0) := by simpa using hloc
    obtain ⟨L0, hL0⟩ := hconv 0 (Nat.zero_le _)
    have hconv0 : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, f t) atTop (𝓝 L) :=
      ⟨L0, by simpa using hL0⟩
    let G := iteratedTailIntegral f 1
    have hG_cont : ContinuousOn G (Ici 0) := continuousOn_iteratedTailIntegral_succ hloc0 hL0
    have hG_top : Tendsto G atTop (𝓝 0) := tendsto_iteratedTailIntegral_succ_atTop hloc0 hL0
    obtain ⟨C, _, hC⟩ := exists_norm_le_of_continuousOn_of_tendsto_zero hG_cont hG_top
    have hG_lap : ∀ p > 0, IntegrableOn (fun s : ℝ ↦ Real.exp (-(p * s)) • G s) (Ioi 0) := by
      intro p hp
      have hexp : IntegrableOn (fun s : ℝ ↦ Real.exp (-(p * s))) (Ioi 0) := by
        simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hp
      exact hexp.smul_bdd C
        ((hG_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs ↦ hC s hs.le)
    have hG_conv : ∀ m ≤ n,
        ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral G m t) atTop (𝓝 L) := by
      intro m hm
      dsimp [G]
      simpa only [← iteratedTailIntegral_succ'] using hconv (m + 1) (Nat.succ_le_succ hm)
    have hlim := ((ih hG_lap hG_conv).const_smul (n + 1 : ℝ)).sub
      (tendsto_pow_sub_smul_integral_exp_neg_mul_pow_smul_zero (le_rfl : n + 1 ≤ n + 1)
        hG_cont hG_top fun r hr ↦ hG_conv r (Nat.le_of_lt_succ hr))
    dsimp [G] at hlim
    rw [sub_zero, ← iteratedTailIntegral_succ' f (n + 1), smul_smul] at hlim
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
    have hf_pow :=
      integrableOn_exp_neg_mul_pow_smul_of_lt (half_lt_self hp) (hf (p / 2) (half_pos hp)) (n + 1)
    simpa [G] using (integral_Ioi_exp_neg_mul_pow_succ_smul_eq hp n hloc hconv0 hf_pow).symm

/-- **Abel's theorem for conditionally convergent Laplace integrals.** If
`t ↦ exp (-(p * t)) • f t` is Bochner integrable on `(0, ∞)` for every `p > 0` and the improper
integral `R ↦ ∫ t in 0..R, f t` converges as `R → ∞`, then
`∫ t in Ioi 0, exp (-(p * t)) • f t → iteratedTailIntegral f 1 0` as `p → 0⁺`. -/
theorem tendsto_integral_exp_neg_mul_smul_nhdsGT_zero {f : ℝ → E}
    (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, f t) atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) • f t) (𝓝[>] 0)
      (𝓝 (iteratedTailIntegral f 1 0)) := by
  simpa using tendsto_integral_exp_neg_mul_pow_smul_nhdsGT_zero (n := 0) hf fun m hm ↦ by
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    simpa using hconv

/-- **Abelian Laplace-derivative theorem for `iteratedTailIntegral`.** Under the hypotheses of
`tendsto_integral_exp_neg_mul_pow_smul_nhdsGT_zero`, the normalized `n`-th derivative of the
Laplace integral `q ↦ ∫ t in Ioi 0, exp (-(q * t)) • f t` converges to
`iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`. -/
theorem tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero {f : ℝ → E}
    {n : ℕ} (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∀ m ≤ n, ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral f m t)
      atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ((-1 : ℝ) ^ n / n.factorial) •
        iteratedDeriv n (fun q : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(q * t)) • f t) p)
      (𝓝[>] 0) (𝓝 (iteratedTailIntegral f (n + 1) 0)) := by
  have hm := (tendsto_integral_exp_neg_mul_pow_smul_nhdsGT_zero hf hconv).const_smul
    ((n.factorial : ℝ)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul] at hm
  refine hm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  rw [iteratedDeriv_integral_exp_neg_mul_smul (half_lt_self hp) (hf (p / 2) (half_pos hp)) n,
    smul_smul, div_eq_mul_inv, mul_right_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-! ### Oscillatory Abelian Laplace corollaries -/

namespace HasOscillatoryDecay

/-- Every locally integrable function on `[a, ∞)` satisfying `HasOscillatoryDecay c q α₀ f` has an
absolutely convergent Laplace integral on `(a, ∞)` for every `p > 0`. -/
theorem integrableOn_exp_neg_mul_mul {c q α₀ a p : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici a)) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * f t) (Ioi a) := by
  have hexp : f =O[atTop] fun t : ℝ ↦ Real.exp ((p / 2) * t) :=
    hf.isBigO_rpow_neg.trans (isLittleO_rpow_exp_pos_mul_atTop (-α₀) (half_pos hp)).isBigO
  have hIci := integrableOn_exp_neg_mul_of_isBigO_exp hloc hexp (half_lt_self hp)
  simpa only [neg_mul] using hIci.mono_set Ioi_subset_Ici_self

/-- **Oscillatory Abelian Laplace-moment theorem.** If `f` is locally integrable on `[0, ∞)` and
satisfies `HasOscillatoryDecay c q α₀ f` with `c ≠ 0`, `1 ≤ q`, and `0 < α₀ + q - 1`, then for
every `n : ℕ`,
`∫ t in Ioi 0, exp (-(p * t)) * t ^ n * f t → n ! * iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`.
-/
theorem tendsto_integral_exp_neg_mul_pow_mul_nhdsGT_zero {c q α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hq : 1 ≤ q) (hα : 0 < α₀ + q - 1)
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) * t ^ n * f t) (𝓝[>] 0)
      (𝓝 ((n.factorial : ℝ) * TauCeti.iteratedTailIntegral f (n + 1) 0)) := by
  have hconv : ∀ m ≤ n, ∃ L, Tendsto
      (fun R : ℝ ↦ ∫ t in 0..R, TauCeti.iteratedTailIntegral f m t) atTop (𝓝 L) :=
    fun m _ ↦ ⟨_, hf.tendsto_iteratedTailIntegral hc hq hα m 0⟩
  simpa only [smul_eq_mul] using
    tendsto_integral_exp_neg_mul_pow_smul_nhdsGT_zero
      (fun p hp ↦ hf.integrableOn_exp_neg_mul_mul hloc hp) hconv

/-- **Oscillatory Abelian Laplace-derivative theorem.** Under the hypotheses of
`HasOscillatoryDecay.tendsto_integral_exp_neg_mul_pow_mul_nhdsGT_zero`, the normalized `n`-th
derivative of the Laplace integral `r ↦ ∫ t in Ioi 0, exp (-(r * t)) * f t` tends to
`iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`. -/
theorem tendsto_iteratedDeriv_integral_exp_neg_mul_mul_nhdsGT_zero {c q α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hq : 1 ≤ q) (hα : 0 < α₀ + q - 1)
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    Tendsto (fun p : ℝ ↦ (-1 : ℝ) ^ n / n.factorial *
        iteratedDeriv n (fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) * f t) p)
      (𝓝[>] 0) (𝓝 (TauCeti.iteratedTailIntegral f (n + 1) 0)) := by
  have hconv : ∀ m ≤ n, ∃ L, Tendsto
      (fun R : ℝ ↦ ∫ t in 0..R, TauCeti.iteratedTailIntegral f m t) atTop (𝓝 L) :=
    fun m _ ↦ ⟨_, hf.tendsto_iteratedTailIntegral hc hq hα m 0⟩
  simpa only [smul_eq_mul] using
    tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero
      (fun p hp ↦ hf.integrableOn_exp_neg_mul_mul hloc hp) hconv

end HasOscillatoryDecay

end TauCeti
