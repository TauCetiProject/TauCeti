/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Topology.Instances.Real.TSupport

/-!
# Basic identities for Mellin transforms

For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` is the upper Mellin integral
`∫ u in Ioi a, u ^ (s - 1) • f u`, and it converges exactly when that integrand is integrable
on `Ioi a`. These identities let a Mellin transform be split into tails over `(0, a]` and
`(a, ∞)`.

The substitution `t = e^{-u}` turns the Mellin integrand of `f` at `s` into
`e^{-su} f(e^{-u})` on the whole real line, and the substitution `t ↦ 1/t` relates the Mellin
transform of `t⁻¹ f(t⁻¹)` at `s` to that of `f` at `1 - s`, and exchanges the Mellin integrals
over `(0, 1]` and `(1, ∞)`; the substitution `u = x t` moves their common endpoint `1` to `x`.
Power bounds at `0+` and `+∞` give absolute convergence and holomorphy of these two partial
Mellin integrals.

The Mellin transform reads a function only on `(0, ∞)`, so functions agreeing there have the same
transform, with the same convergence. Kernels that are extended by zero off `(0, ∞)` are compared
with their unextended forms this way.

## Main results

* `TauCeti.hasMellin_congr`: functions agreeing on `(0, ∞)` have the same Mellin transform.
* `TauCeti.mellinConvergent_indicator_Ioi_iff`: convergence of the Mellin transform of an
  upper-tail indicator is integrability of the upper Mellin integrand.
* `TauCeti.mellin_indicator_Ioi`, `TauCeti.mellin_indicator_Ici`: the Mellin transform of an
  open or closed upper-tail indicator is the upper Mellin integral.
* `TauCeti.mellinConvergent_indicator_iff_of_subset_Ioi`,
  `TauCeti.mellin_indicator_of_subset_Ioi`: the same for the indicator of any measurable subset of
  `(0, ∞)`.
* `TauCeti.mellinConvergent_comp_inv_iff`: the Mellin transform of `t ↦ f t⁻¹` converges at `s`
  exactly when that of `f` converges at `-s`.
* `TauCeti.integral_Ioc_cpow_smul_eq_integral_Ioi_comp_inv`,
  `TauCeti.integrableOn_Ioc_cpow_smul_iff_integrableOn_Ioi_comp_inv`: the substitution `t ↦ t⁻¹`
  exchanges the Mellin integrals over `(0, 1]` and `(1, ∞)`, with their absolute convergence.
* `TauCeti.integrableOn_Ioc_cpow_smul_cpow_smul`, `TauCeti.integral_Ioc_cpow_smul_cpow_smul`: for
  `0 < Re (z + w)`, `∫₀¹ t^{z-1} t^w c dt = c / (z + w)`, with absolute convergence.
* `TauCeti.continuousOn_sum_cpow_smul`, `TauCeti.locallyIntegrableOn_sum_cpow_smul`,
  `TauCeti.locallyIntegrableOn_cpow_smul`: finite power sums `∑_{k<n} t^{w_k} c_k` are continuous
  on `(0, ∞)`, and multiplying by `t^z` keeps local integrability there.
* `TauCeti.intervalIntegral_cpow_smul_cpow_smul`, `TauCeti.intervalIntegral_cpow_smul_sum`: for
  `z + w ≠ 0`, `∫_1^R t^{z-1} t^w c dt = (R^{z+w} - 1)/(z + w) c`, and the same termwise for a
  finite power sum.
* `TauCeti.integral_Ioc_add_integral_Ioi_eq`: moving the common endpoint of
  `∫_{(0,1]} F + ∫_{(1,∞)} G` from `1` to `R > 0` adds `∫_1^R (F - G)`.
* `TauCeti.sum_cpow_smul_cpow_smul_eq_sum_mul_cpow_smul`: rescaling the variable of a finite power
  sum, `∑ t^{w_k} x^{w_k} c_k = ∑ (x t)^{w_k} c_k` for `0 ≤ x`.
* `TauCeti.integral_Ioc_cpow_smul_comp_mul_left`, `TauCeti.integral_Ioi_cpow_smul_comp_mul_left`:
  the substitution `u = x t` turns the Mellin integrals of `t ↦ g (x t)` over `(0, 1]` and
  `(1, ∞)` into `x^{-z}` times those of `g` over `(0, x]` and `(x, ∞)`.
* `TauCeti.integrableOn_Ioc_cpow_smul_of_isBigO`, `TauCeti.integrableOn_Ioi_cpow_smul_of_isBigO`,
  `TauCeti.differentiableAt_integral_Ioc_cpow_smul_of_isBigO`,
  `TauCeti.differentiableAt_integral_Ioi_cpow_smul_of_isBigO`: absolute convergence and
  holomorphy of the Mellin integrals over `(0, 1]` and `(1, ∞)` from power bounds.
* `TauCeti.mellin_ofReal_zero`, `TauCeti.mellinConvergent_ofReal_zero_iff`: at `s = 0` the
  Mellin transform of a real function is the real integral `∫_{(0,∞)} f(x) dx/x`.
* `MellinConvergent.of_support_inter_Ioi_subset_Icc`: for a function vanishing on `(0, ∞)` off a
  compact interval `[a, b]` with `0 < a`, convergence at one exponent gives convergence at every
  exponent.
* `MeasureTheory.LocallyIntegrableOn.mellinConvergent_of_isCompact_tsupport_inter_Ioi`,
  `MeasureTheory.LocallyIntegrableOn.differentiable_mellin_of_isCompact_tsupport_inter_Ioi`: a
  function locally integrable on `(0, ∞)` with compact positive closed support
  `tsupport f ∩ Ioi 0` is Mellin convergent at every exponent, and its Mellin transform is entire.
* `TauCeti.mellinConvergent_ofReal_of_support_inter_Ioi_subset_Icc`: a real function vanishing on
  `(0, ∞)` off a compact interval `[a, b]` with `0 < a`, with `x ↦ f x / x` integrable on
  `(0, ∞)`, converges at every exponent.
* `TauCeti.mellinConvergent_iff_integrable_exp_smul`, `TauCeti.mellin_eq_integral_exp_smul`:
  absolute convergence and value of the Mellin transform in logarithmic coordinates.
* `TauCeti.mellinConvergent_inv_smul_comp_inv`, `TauCeti.mellin_inv_smul_comp_inv`: the Mellin
  transform of `t⁻¹ f(t⁻¹)` at `s` is that of `f` at `1 - s`.
* `TauCeti.intervalIntegral_mul_exp_comp_exp`: logarithmic coordinates turn a finite real Mellin
  integral into an exponentially weighted integral.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Functions that agree on `(0, ∞)` have the same Mellin transform, with the same convergence. -/
theorem hasMellin_congr {f g : ℝ → E} (h : EqOn f g (Ioi 0)) {s : ℂ} {m : E} :
    HasMellin f s m ↔ HasMellin g s m := by
  have h' : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) (fun t ↦ (t : ℂ) ^ (s - 1) • g t)
      (Ioi 0) := fun t ht ↦ by simp only [h ht]
  simp only [HasMellin, MellinConvergent, mellin,
    MeasureTheory.integrableOn_congr_fun h' measurableSet_Ioi,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h']

/-- For a measurable `s ⊆ (0, ∞)`, the Mellin transform of `s.indicator f` converges exactly when
the Mellin integrand of `f` is integrable on `s`. -/
theorem mellinConvergent_indicator_iff_of_subset_Ioi {f : ℝ → E} {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) {z : ℂ} :
    MellinConvergent (s.indicator f) z ↔ IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • f t) s := by
  simp_rw [MellinConvergent, ← indicator_smul, integrableOn_indicator_iff hs.nullMeasurableSet,
    inter_eq_left.mpr hs0]

/-- For a measurable `s ⊆ (0, ∞)`, the Mellin transform of `s.indicator f` is the Mellin integral
of `f` over `s`. -/
theorem mellin_indicator_of_subset_Ioi (f : ℝ → E) {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) (z : ℂ) :
    mellin (s.indicator f) z = ∫ t : ℝ in s, (t : ℂ) ^ (z - 1) • f t := by
  simp_rw [mellin, ← indicator_smul, setIntegral_indicator hs, inter_eq_right.mpr hs0]

/-- For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` converges at `s` exactly when the
upper Mellin integrand `u ^ (s - 1) • f u` is integrable on `Ioi a`. -/
theorem mellinConvergent_indicator_Ioi_iff {f : ℝ → E} {a : ℝ} (ha : 0 ≤ a) {s : ℂ} :
    MellinConvergent ((Ioi a).indicator f) s ↔
      IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi a) :=
  mellinConvergent_indicator_iff_of_subset_Ioi measurableSet_Ioi (Ioi_subset_Ioi ha)

/-- For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` is the upper Mellin integral of
`f` over `Ioi a`. -/
theorem mellin_indicator_Ioi (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    mellin ((Ioi a).indicator f) s = ∫ (u : ℝ) in Ioi a, (u : ℂ) ^ (s - 1) • f u :=
  mellin_indicator_of_subset_Ioi f measurableSet_Ioi (Ioi_subset_Ioi ha) s

/-- The Mellin transform of an upper closed-ray indicator equals the upper Mellin integral.
The boundary point has measure zero; the cutoff may be zero. -/
theorem mellin_indicator_Ici (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    mellin ((Ici a).indicator f) s = ∫ (u : ℝ) in Ioi a, (u : ℂ) ^ (s - 1) • f u := by
  rw [← mellin_indicator_Ioi f ha s]
  simp only [mellin]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set (f := f)
    (Ioi_ae_eq_Ici (a := a)))] with t ht
  rw [ht]

/-- The Mellin integral of `t ↦ f t⁻¹` converges absolutely at `s` exactly when that of `f`
converges absolutely at `-s`; this is the convergence companion of `mellin_comp_inv`. -/
theorem mellinConvergent_comp_inv_iff (f : ℝ → E) (s : ℂ) :
    MellinConvergent (fun t ↦ f t⁻¹) s ↔ MellinConvergent f (-s) := by
  have hs : s / ((-1 : ℝ) : ℂ) = -s := by push_cast; ring
  simpa only [Real.rpow_neg_one, hs] using
    MellinConvergent.comp_rpow (f := f) (s := s) (a := -1) (by norm_num)

/-- Restricting `t ↦ f t⁻¹` to `(1, ∞)` and substituting `t⁻¹` restricts `f` to `(0, 1)`. -/
private theorem indicator_Ioi_one_comp_inv {F : Type*} [Zero F] (f : ℝ → F) :
    (fun t : ℝ ↦ (Ioi 1).indicator (fun u ↦ f u⁻¹) t⁻¹) = (Ioo 0 1).indicator f := by
  ext t
  rcases lt_or_ge 0 t with ht | ht
  · simp only [indicator_apply, mem_Ioi, mem_Ioo, inv_inv, one_lt_inv₀ ht, ht, true_and]
  · rw [indicator_of_notMem fun h ↦ (inv_nonpos.mpr ht).not_gt (zero_lt_one.trans h),
      indicator_of_notMem fun (h : t ∈ Ioo 0 1) ↦ ht.not_gt h.1]

/-- The substitution `t ↦ t⁻¹` exchanges the Mellin integrals over `(0, 1]` and `(1, ∞)`:
`∫₀¹ t^{z-1} f(t) dt = ∫₁^∞ t^{-z-1} f(t⁻¹) dt`. -/
theorem integral_Ioc_cpow_smul_eq_integral_Ioi_comp_inv (f : ℝ → E) (z : ℂ) :
    ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • f t = ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-z - 1) • f t⁻¹ := by
  rw [integral_Ioc_eq_integral_Ioo, ← mellin_indicator_of_subset_Ioi f measurableSet_Ioo
    Ioo_subset_Ioi_self, ← indicator_Ioi_one_comp_inv, mellin_comp_inv,
    mellin_indicator_Ioi _ zero_le_one]

/-- The substitution `t ↦ t⁻¹` exchanges absolute convergence of the Mellin integrals over
`(0, 1]` and `(1, ∞)`. -/
theorem integrableOn_Ioc_cpow_smul_iff_integrableOn_Ioi_comp_inv (f : ℝ → E) (z : ℂ) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • f t) (Ioc 0 1) ↔
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1) • f t⁻¹) (Ioi 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo, ← mellinConvergent_indicator_iff_of_subset_Ioi
    measurableSet_Ioo Ioo_subset_Ioi_self, ← indicator_Ioi_one_comp_inv,
    ← mellinConvergent_indicator_Ioi_iff zero_le_one, mellinConvergent_comp_inv_iff]

/-- For `0 < Re (z + w)`, the function `t ↦ t^{z-1} t^w c` is integrable on `(0, 1]`. -/
theorem integrableOn_Ioc_cpow_smul_cpow_smul {z w : ℂ} (hzw : 0 < (z + w).re) (c : E) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • ((t : ℂ) ^ w • c)) (Ioc 0 1) := by
  have h := ((mellinConvergent_indicator_iff_of_subset_Ioi measurableSet_Ioc
    Ioc_subset_Ioi_self).mp (hasMellin_cpow_Ioc w (by rwa [← add_re])).1).smul_const c
  simpa only [smul_assoc, IntegrableOn] using h

/-- For `0 < Re (z + w)`, `∫₀¹ t^{z-1} t^w c dt = c / (z + w)`. -/
theorem integral_Ioc_cpow_smul_cpow_smul [CompleteSpace E] {z w : ℂ}
    (hzw : 0 < (z + w).re) (c : E) :
    ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • ((t : ℂ) ^ w • c) = (z + w)⁻¹ • c := by
  have h := (hasMellin_cpow_Ioc w (s := z) (by rwa [← add_re])).2
  rw [mellin_indicator_of_subset_Ioi _ measurableSet_Ioc Ioc_subset_Ioi_self] at h
  simp_rw [← smul_assoc]
  rw [integral_smul_const, h, one_div]

/-! ### Finite power sums and the split point -/

/-- The function `t ↦ ∑_{k<n} t^{w_k} c_k` is continuous on `(0, ∞)`. -/
theorem continuousOn_sum_cpow_smul (w : ℕ → ℂ) (c : ℕ → E) (n : ℕ) :
    ContinuousOn (fun t : ℝ ↦ ∑ k ∈ Finset.range n, (t : ℂ) ^ w k • c k) (Ioi 0) :=
  continuousOn_finsetSum _ fun _ _ _ ht ↦
    ((continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).smul
      continuousAt_const).continuousWithinAt

/-- The function `t ↦ ∑_{k<n} t^{w_k} c_k` is locally integrable on `(0, ∞)`. -/
theorem locallyIntegrableOn_sum_cpow_smul (w : ℕ → ℂ) (c : ℕ → E) (n : ℕ) :
    LocallyIntegrableOn (fun t : ℝ ↦ ∑ k ∈ Finset.range n, (t : ℂ) ^ w k • c k) (Ioi 0) :=
  (continuousOn_sum_cpow_smul w c n).locallyIntegrableOn measurableSet_Ioi

/-- The function `t ↦ t^z • g t` is locally integrable on `(0, ∞)` when `g` is. -/
theorem locallyIntegrableOn_cpow_smul {g : ℝ → E} (hg : LocallyIntegrableOn g (Ioi 0))
    (z : ℂ) : LocallyIntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ z • g t) (Ioi 0) :=
  hg.continuousOn_smul isOpen_Ioi.isLocallyClosed fun _ ht ↦
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).continuousWithinAt

/-- Moving the common endpoint of `∫_{(0,1]} F + ∫_{(1,∞)} G` from `1` to `R > 0` adds
`∫_1^R (F - G)`. -/
theorem integral_Ioc_add_integral_Ioi_eq {F G : ℝ → E}
    (hF : LocallyIntegrableOn F (Ioi 0)) (hG : LocallyIntegrableOn G (Ioi 0))
    (hF1 : IntegrableOn F (Ioc 0 1)) (hG1 : IntegrableOn G (Ioi 1)) {R : ℝ} (hR : 0 < R) :
    (∫ t in Ioc 0 R, F t) + ∫ t in Ioi R, G t =
      (∫ t in Ioc 0 1, F t) + (∫ t in Ioi 1, G t) + ∫ t in (1 : ℝ)..R, (F t - G t) := by
  have hsub : uIcc 1 R ⊆ Ioi 0 := fun t ht ↦
    (lt_min one_pos hR).trans_le (by simpa only [uIcc, mem_Icc] using ht.1)
  have hFi := (hF.integrableOn_compact_subset hsub isCompact_uIcc).intervalIntegrable
  have hGc := hG.integrableOn_compact_subset hsub isCompact_uIcc
  have hGR : IntegrableOn G (Ioi R) := (hGc.union hG1).mono_set fun t ht ↦ by
    by_cases h1 : 1 < t
    · exact Or.inr h1
    · exact Or.inl ⟨min_le_of_right_le (le_of_lt ht), le_max_of_le_left (not_lt.mp h1)⟩
  rw [← intervalIntegral.integral_of_le hR.le, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hF1) hFi,
    ← intervalIntegral.integral_interval_add_Ioi' hGc.intervalIntegrable hGR,
    intervalIntegral.integral_sub hFi hGc.intervalIntegrable]
  abel

/-- `∫_1^R t^{z-1} t^w c dt = (R^{z+w} - 1)/(z + w) c` for `R > 0` and `z + w ≠ 0`. -/
theorem intervalIntegral_cpow_smul_cpow_smul [CompleteSpace E] {z w : ℂ} (hzw : z + w ≠ 0)
    {R : ℝ} (hR : 0 < R) (c : E) :
    ∫ t in (1 : ℝ)..R, (t : ℂ) ^ (z - 1) • ((t : ℂ) ^ w • c) =
      ((z + w)⁻¹ * ((R : ℂ) ^ (z + w) - 1)) • c := by
  have hcongr : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • ((t : ℂ) ^ w • c))
      (fun t : ℝ ↦ (t : ℂ) ^ (z + w - 1) • c) (uIcc 1 R) := fun t ht ↦ by
    have ht0 : (t : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (ne_of_mem_of_not_mem ht (notMem_uIcc_of_lt one_pos hR))
    simp only [smul_smul, ← cpow_add _ _ ht0]
    ring_nf
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_smul_const,
    integral_cpow (Or.inr ⟨fun h ↦ hzw (by linear_combination h), notMem_uIcc_of_lt one_pos hR⟩)]
  simp only [sub_add_cancel, ofReal_one, one_cpow]
  rw [div_eq_inv_mul]

/-- `∫_1^R t^{z-1} ∑_{k<n} t^{w_k} c_k dt = ∑_{k<n} (R^{z+w_k} - 1)/(z + w_k) c_k`. -/
theorem intervalIntegral_cpow_smul_sum [CompleteSpace E] {z : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hzw : ∀ k < n, z + w k ≠ 0) {R : ℝ} (hR : 0 < R) (c : ℕ → E) :
    ∫ t in (1 : ℝ)..R, (t : ℂ) ^ (z - 1) • ∑ k ∈ Finset.range n, (t : ℂ) ^ w k • c k =
      ∑ k ∈ Finset.range n, ((z + w k)⁻¹ * ((R : ℂ) ^ (z + w k) - 1)) • c k := by
  simp_rw [Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ ↦ ?_]
  · exact Finset.sum_congr rfl fun k hk ↦
      intervalIntegral_cpow_smul_cpow_smul (hzw k (Finset.mem_range.mp hk)) hR (c k)
  · refine ((locallyIntegrableOn_cpow_smul (locallyIntegrableOn_cpow_smul
      (locallyIntegrableOn_const (c k)) (w k)) (z - 1)).integrableOn_compact_subset
      (fun t (ht : t ∈ uIcc 1 R) ↦ ?_) isCompact_uIcc).intervalIntegrable
    exact (lt_min one_pos hR).trans_le ht.1

/-- Rescaling the variable of a finite power sum: for `0 ≤ x`,
`∑_{k<n} t^{w_k} x^{w_k} c_k = ∑_{k<n} (x t)^{w_k} c_k`. -/
theorem sum_cpow_smul_cpow_smul_eq_sum_mul_cpow_smul {x : ℝ} (hx : 0 ≤ x) (w : ℕ → ℂ)
    (c : ℕ → E) (n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range n, (t : ℂ) ^ w k • (x : ℂ) ^ w k • c k =
      ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ w k • c k :=
  Finset.sum_congr rfl fun k _ ↦ by rw [smul_smul, ofReal_mul, ofReal_mul_cpow hx, mul_comm]

/-! ### Rescaling the variable -/

/-- Rescaling the argument multiplies the Mellin integrand by a power: for `x > 0`,
`t^{z-1} g(xt) = (x^{-z} x) ((xt)^{z-1} g(xt))`. -/
private theorem cpow_smul_comp_mul_left (g : ℝ → E) (z : ℂ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (t : ℂ) ^ (z - 1) • g (x * t) =
      ((x : ℂ) ^ (-z) * x) • (((x * t : ℝ) : ℂ) ^ (z - 1) • g (x * t)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have : (x : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  rw [smul_smul, ofReal_mul, ofReal_mul_cpow hx.le, cpow_neg, cpow_sub _ _ hx0, cpow_one]
  congr 1
  field_simp

/-- For `x > 0`, the Mellin integral over `(0, 1]` of `t ↦ g (x t)` is `x^{-z}` times the Mellin
integral of `g` over `(0, x]`. -/
theorem integral_Ioc_cpow_smul_comp_mul_left (g : ℝ → E) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • g (x * t) =
      (x : ℂ) ^ (-z) • ∫ u : ℝ in Ioc 0 x, (u : ℂ) ^ (z - 1) • g u := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ cpow_smul_comp_mul_left g z hx t,
    integral_smul, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun u : ℝ ↦ (u : ℂ) ^ (z - 1) • g u) hx.ne',
    mul_zero, mul_one, intervalIntegral.integral_of_le hx.le, ← Complex.coe_smul, smul_smul,
    ofReal_inv, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

/-- For `x > 0`, the Mellin integral over `(1, ∞)` of `t ↦ g (x t)` is `x^{-z}` times the Mellin
integral of `g` over `(x, ∞)`. -/
theorem integral_Ioi_cpow_smul_comp_mul_left (g : ℝ → E) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) • g (x * t) =
      (x : ℂ) ^ (-z) • ∫ u : ℝ in Ioi x, (u : ℂ) ^ (z - 1) • g u := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ cpow_smul_comp_mul_left g z hx t,
    integral_smul, integral_comp_mul_left_Ioi (fun u : ℝ ↦ (u : ℂ) ^ (z - 1) • g u) 1 hx,
    mul_one, ← Complex.coe_smul, smul_smul, ofReal_inv, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

/-! ### Mellin integrals over `(0, 1]` and `(1, ∞)` from power bounds -/

section Truncated

open Filter Asymptotics
open scoped Topology

variable {g : ℝ → E}

omit [NormedSpace ℂ E] in
/-- The restriction of `g` to `(0, 1]` keeps the Mellin hypotheses of `g` at `0+` and has every
power decay at `+∞`. -/
private theorem indicator_Ioc_mellin_hyp (hg : LocallyIntegrableOn g (Ioi 0)) {b : ℝ}
    (hg0 : g =O[𝓝[>] 0] (· ^ (-b))) (a : ℝ) :
    LocallyIntegrableOn ((Ioc 0 1).indicator g) (Ioi 0) ∧
      (Ioc 0 1).indicator g =O[atTop] (· ^ (-a)) ∧
      (Ioc 0 1).indicator g =O[𝓝[>] 0] (· ^ (-b)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed] at hg ⊢
    exact fun k hk hkc ↦ (hg k hk hkc).indicator measurableSet_Ioc
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact (indicator_of_notMem (fun (h : t ∈ Ioc 0 1) ↦ ht.not_ge h.2) g).symm
  · refine hg0.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact (indicator_of_mem (Ioo_subset_Ioc_self ht) g).symm

omit [NormedSpace ℂ E] in
/-- The restriction of `g` to `(1, ∞)` keeps the Mellin hypotheses of `g` at `+∞` and has every
power bound at `0+`. -/
private theorem indicator_Ioi_mellin_hyp (hg : LocallyIntegrableOn g (Ioi 0)) {a : ℝ}
    (hg1 : g =O[atTop] (· ^ (-a))) (b : ℝ) :
    LocallyIntegrableOn ((Ioi 1).indicator g) (Ioi 0) ∧
      (Ioi 1).indicator g =O[atTop] (· ^ (-a)) ∧
      (Ioi 1).indicator g =O[𝓝[>] 0] (· ^ (-b)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed] at hg ⊢
    exact fun k hk hkc ↦ (hg k hk hkc).indicator measurableSet_Ioi
  · refine hg1.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact (indicator_of_mem ht g).symm
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact (indicator_of_notMem (fun (h : 1 < t) ↦ ht.2.not_gt h) g).symm

/-- The Mellin integral over `(0, 1]` converges absolutely on `b < Re z` when the function is
locally integrable on `(0, ∞)` and `O(t^{-b})` as `t → 0+`. -/
theorem integrableOn_Ioc_cpow_smul_of_isBigO (hg : LocallyIntegrableOn g (Ioi 0)) {b : ℝ}
    (hg0 : g =O[𝓝[>] 0] (· ^ (-b))) {z : ℂ} (hz : b < z.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • g t) (Ioc 0 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := indicator_Ioc_mellin_hyp hg hg0 (z.re + 1)
  exact (mellinConvergent_indicator_iff_of_subset_Ioi measurableSet_Ioc Ioc_subset_Ioi_self).mp
    (mellinConvergent_of_isBigO_rpow h₁ h₂ (lt_add_one _) h₃ hz)

/-- The Mellin integral over `(1, ∞)` converges absolutely on `Re z < a` when the function is
locally integrable on `(0, ∞)` and `O(t^{-a})` as `t → +∞`. -/
theorem integrableOn_Ioi_cpow_smul_of_isBigO (hg : LocallyIntegrableOn g (Ioi 0)) {a : ℝ}
    (hg1 : g =O[atTop] (· ^ (-a))) {z : ℂ} (hz : z.re < a) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • g t) (Ioi 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := indicator_Ioi_mellin_hyp hg hg1 (z.re - 1)
  exact (mellinConvergent_indicator_iff_of_subset_Ioi measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one)).mp (mellinConvergent_of_isBigO_rpow h₁ h₂ hz h₃ (sub_one_lt _))

/-- The Mellin integral over `(0, 1]` is holomorphic on `b < Re z` when the function is locally
integrable on `(0, ∞)` and `O(t^{-b})` as `t → 0+`. -/
theorem differentiableAt_integral_Ioc_cpow_smul_of_isBigO (hg : LocallyIntegrableOn g (Ioi 0))
    {b : ℝ} (hg0 : g =O[𝓝[>] 0] (· ^ (-b))) {z : ℂ} (hz : b < z.re) :
    DifferentiableAt ℂ (fun w : ℂ ↦ ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (w - 1) • g t) z := by
  obtain ⟨h₁, h₂, h₃⟩ := indicator_Ioc_mellin_hyp hg hg0 (z.re + 1)
  have h := mellin_differentiableAt_of_isBigO_rpow h₁ h₂ (lt_add_one _) h₃ hz
  rwa [show mellin ((Ioc 0 1).indicator g) = _ from
    funext (mellin_indicator_of_subset_Ioi g measurableSet_Ioc Ioc_subset_Ioi_self)] at h

/-- The Mellin integral over `(1, ∞)` is holomorphic on `Re z < a` when the function is locally
integrable on `(0, ∞)` and `O(t^{-a})` as `t → +∞`. -/
theorem differentiableAt_integral_Ioi_cpow_smul_of_isBigO (hg : LocallyIntegrableOn g (Ioi 0))
    {a : ℝ} (hg1 : g =O[atTop] (· ^ (-a))) {z : ℂ} (hz : z.re < a) :
    DifferentiableAt ℂ (fun w : ℂ ↦ ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (w - 1) • g t) z := by
  obtain ⟨h₁, h₂, h₃⟩ := indicator_Ioi_mellin_hyp hg hg1 (z.re - 1)
  have h := mellin_differentiableAt_of_isBigO_rpow h₁ h₂ hz h₃ (sub_one_lt _)
  rwa [show mellin ((Ioi 1).indicator g) = _ from
    funext (mellin_indicator_Ioi g zero_le_one)] at h

end Truncated

/-- For a real function `f`, the Mellin transform of `f` at `0` is the real integral
`∫_{(0,∞)} f(x) dx/x`. -/
theorem mellin_ofReal_zero (f : ℝ → ℝ) :
    mellin (fun x ↦ (f x : ℂ)) 0 = ((∫ x in Ioi 0, f x / x : ℝ) : ℂ) := by
  rw [mellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
  simp [cpow_neg_one, div_eq_inv_mul]

/-- For a real function `f`, absolute convergence of the Mellin transform at `0` is
integrability of `x ↦ f x / x` on `(0, ∞)`. -/
theorem mellinConvergent_ofReal_zero_iff (f : ℝ → ℝ) :
    MellinConvergent (fun x ↦ (f x : ℂ)) 0 ↔ IntegrableOn (fun x ↦ f x / x) (Ioi 0) := by
  rw [MellinConvergent, integrableOn_congr_fun (g := fun x ↦ ((f x / x : ℝ) : ℂ))
    (fun x _ ↦ by simp [cpow_neg_one, div_eq_inv_mul]) measurableSet_Ioi]
  exact (Integrable.iff_ofReal (𝕜 := ℂ)).symm

private lemma exp_smul_cpow_smul_comp_neg (f : ℝ → E) (s : ℂ) (u : ℝ) :
    Real.exp (-1 * u) • ((Real.exp (-1 * u) : ℂ) ^ (s - 1) • f (Real.exp (-1 * u))) =
      cexp (-s * u) • f (Real.exp (-u)) := by
  rw [neg_one_mul, ← Complex.coe_smul, smul_smul, ofReal_exp,
    cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simp [Real.pi_pos])
      (by simp [Real.pi_nonneg]), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Under the substitution `t = e^{-u}`, absolute Mellin convergence of `f` at `s` is
integrability of `u ↦ e^{-su} f(e^{-u})` on the real line. -/
theorem mellinConvergent_iff_integrable_exp_smul (f : ℝ → E) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun u : ℝ ↦ cexp (-s * u) • f (Real.exp (-u))) := by
  rw [MellinConvergent, ← integrable_comp_exp,
    ← integrable_comp_mul_left_iff _ (neg_ne_zero.mpr one_ne_zero)]
  simp only [exp_smul_cpow_smul_comp_neg]

/-- The Mellin transform in logarithmic coordinates: `𝓜f(s) = ∫_ℝ e^{-su} f(e^{-u}) du`. -/
theorem mellin_eq_integral_exp_smul (f : ℝ → E) (s : ℂ) :
    mellin f s = ∫ u : ℝ, cexp (-s * u) • f (Real.exp (-u)) := by
  calc mellin f s = ∫ x : ℝ, Real.exp x • ((Real.exp x : ℂ) ^ (s - 1) • f (Real.exp x)) :=
        (integral_comp_exp _).symm
    _ = ∫ u : ℝ, Real.exp (-1 * u) •
          ((Real.exp (-1 * u) : ℂ) ^ (s - 1) • f (Real.exp (-1 * u))) := by
        have h := Measure.integral_comp_mul_left
          (fun x : ℝ ↦ Real.exp x • ((Real.exp x : ℂ) ^ (s - 1) • f (Real.exp x))) (-1)
        rw [inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
        exact h.symm
    _ = _ := by simp only [exp_smul_cpow_smul_comp_neg]

/-- If the Mellin transform of `f` converges absolutely at `1 - s`, then that of
`t ↦ t⁻¹ f(t⁻¹)` converges absolutely at `s`. -/
theorem mellinConvergent_inv_smul_comp_inv {f : ℝ → E} {s : ℂ}
    (hf : MellinConvergent f (1 - s)) :
    MellinConvergent (fun t : ℝ ↦ (t : ℂ)⁻¹ • f t⁻¹) s := by
  have hi : MellinConvergent (fun t ↦ f t⁻¹) (s - 1) :=
    (mellinConvergent_comp_inv_iff f (s - 1)).mpr (by rwa [neg_sub])
  simpa only [cpow_neg_one] using
    (MellinConvergent.cpow_smul (f := fun t ↦ f t⁻¹) (s := s) (a := -1)).mpr
      (by rwa [← sub_eq_add_neg])

/-- The Mellin transform of `t ↦ t⁻¹ f(t⁻¹)` at `s` is the Mellin transform of `f` at
`1 - s`. -/
theorem mellin_inv_smul_comp_inv (f : ℝ → E) (s : ℂ) :
    mellin (fun t : ℝ ↦ (t : ℂ)⁻¹ • f t⁻¹) s = mellin f (1 - s) := by
  have h := mellin_cpow_smul (fun t ↦ f t⁻¹) s (-1)
  simp only [cpow_neg_one] at h
  rw [h, mellin_comp_inv, neg_add, neg_neg, ← sub_eq_neg_add]

/-- Logarithmic coordinates convert a finite Mellin integral to an exponentially weighted
integral. The identity holds in either orientation. -/
theorem intervalIntegral_mul_exp_comp_exp (f : ℝ → ℝ) (a b θ : ℝ) :
    (∫ u in a..b, f (Real.exp u) * Real.exp (-θ * u)) =
      ∫ y in Real.exp a..Real.exp b, f y * y ^ (-(θ + 1)) := by
  refine Eq.trans (intervalIntegral.integral_congr ?_) <|
    intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (g := fun y ↦ f y * y ^ (-(θ + 1))) Real.continuous_exp.continuousOn
      (fun u _ ↦ Real.hasDerivAt_exp u) (fun u _ ↦ (Real.exp_pos u).le)
  intro u _
  simp only [Function.comp_apply, smul_eq_mul, ← Real.exp_mul, mul_left_comm (Real.exp u),
    ← Real.exp_add]
  ring_nf

end TauCeti

/-- A function vanishing on `(0, ∞)` off a compact interval `[a, b]` with `0 < a`, whose Mellin
transform converges absolutely at one exponent, converges absolutely at every exponent. -/
theorem MellinConvergent.of_support_inter_Ioi_subset_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hf : Function.support f ∩ Ioi 0 ⊆ Icc a b)
    {s₀ : ℂ} (h : MellinConvergent f s₀) (s : ℂ) : MellinConvergent f s := by
  have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s - s₀)) (Icc a b) := fun t ht ↦
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (ha.trans_le ht.1).ne')).continuousWithinAt
  have hsub : Icc a b ⊆ Ioi 0 := fun t ht ↦ ha.trans_le ht.1
  have hI := (IntegrableOn.mono_set h hsub).continuousOn_smul hc isCompact_Icc
  refine ((integrableOn_congr_fun (fun t ht ↦ ?_) measurableSet_Icc).mp hI).of_forall_sdiff_eq_zero
    measurableSet_Ioi fun t ht ↦ ?_
  · rw [smul_smul, ← cpow_add _ _ (ofReal_ne_zero.mpr (ha.trans_le ht.1).ne'), sub_add_sub_cancel]
  · rw [Function.notMem_support.mp fun h ↦ ht.2 (hf ⟨h, ht.1⟩), smul_zero]

/-- A function locally integrable on `(0, ∞)` whose positive closed support `tsupport f ∩ Ioi 0`
is compact is Mellin convergent at every exponent. -/
theorem MeasureTheory.LocallyIntegrableOn.mellinConvergent_of_isCompact_tsupport_inter_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0)) (s : ℂ) :
    MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hf
    (hc.eventuallyEq_zero_atTop_of_tsupport_inter_Ioi.trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)
    (hc.eventuallyEq_zero_nhdsGT_of_tsupport_inter_Ioi.trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)

/-- The Mellin transform of a function locally integrable on `(0, ∞)` with compact positive closed
support is entire. -/
theorem MeasureTheory.LocallyIntegrableOn.differentiable_mellin_of_isCompact_tsupport_inter_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}
    (hf : LocallyIntegrableOn f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0)) :
    Differentiable ℂ (mellin f) := fun s ↦
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hf
    (hc.eventuallyEq_zero_atTop_of_tsupport_inter_Ioi.trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)
    (hc.eventuallyEq_zero_nhdsGT_of_tsupport_inter_Ioi.trans_isBigO
      (Asymptotics.isBigO_zero _ _)) (by linarith)

namespace TauCeti

/-- A real function vanishing on `(0, ∞)` off a compact interval `[a, b]` with `0 < a`, with
`x ↦ f x / x` integrable on `(0, ∞)`, is Mellin convergent at every exponent. -/
theorem mellinConvergent_ofReal_of_support_inter_Ioi_subset_Icc {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hf : Function.support f ∩ Ioi 0 ⊆ Icc a b)
    (hfi : IntegrableOn (fun x ↦ f x / x) (Ioi 0)) (s : ℂ) :
    MellinConvergent (fun x ↦ (f x : ℂ)) s :=
  ((mellinConvergent_ofReal_zero_iff f).mpr hfi).of_support_inter_Ioi_subset_Icc ha
    (by simpa only [Function.support, ne_eq, ofReal_eq_zero] using hf) s

end TauCeti
