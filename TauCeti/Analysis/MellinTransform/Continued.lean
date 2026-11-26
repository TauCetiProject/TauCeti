/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Analysis.MellinTransform
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continued Mellin transforms (DLMF 2.5.17–2.5.28)

Let `f` be locally integrable on `(0, ∞)`. Its Mellin transform `𝓜f(z) = ∫₀^∞ t^{z-1} f(t) dt`
converges absolutely only on a vertical strip, whose left edge is set by the behaviour of `f` at
`0+` and whose right edge by its behaviour at `+∞`. An asymptotic expansion of `f` at either end
continues `𝓜f` across that edge, with simple poles: residue `a_k` at `-α_k` for an expansion at
`0+`, and residue `-b_k` at `β_k` for an expansion at `+∞`.

If `f(t) ∼ ∑ a_k t^{α_k}` as `t → 0+`, subtracting the first `n` terms on `(0, 1]` and integrating
them exactly gives (DLMF 2.5.26)

`mellinContAtZero f a α n z = ∫₀¹ t^{z-1} (f(t) - ∑_{k<n} a_k t^{α_k}) dt + ∑_{k<n} a_k/(z + α_k)
  + ∫₁^∞ t^{z-1} f(t) dt`,

and if `f(t) ∼ ∑ b_k t^{-β_k}` as `t → +∞`, symmetrically (DLMF 2.5.28)

`mellinContAtTop f b β n z = ∫₀¹ t^{z-1} f(t) dt + ∫₁^∞ t^{z-1} (f(t) - ∑_{k<n} b_k t^{-β_k}) dt
  - ∑_{k<n} b_k/(z - β_k)`.

The expansions are `Asymptotics.HasAsymptoticExpansion` in the scales `t ↦ t^{α_k}` along `𝓝[>] 0`
and `t ↦ t^{-β_k}` along `atTop`. For `f = O(t^{-b})` at `+∞`, `mellinContAtZero f a α n` minus
its principal parts `a_k/(z + α_k)` is holomorphic on the strip `-Re α_n < Re z < b`, and for
`f = O(t^c)` at `0+`, `mellinContAtTop f b β n` plus `b_k/(z - β_k)` is holomorphic on
`-c < Re z < Re β_n`. Successive continuations agree where both are defined, and every one of them
equals `𝓜f(z)` wherever the Mellin integral converges absolutely. The last statement needs no
restriction on `z`: a nonzero coefficient `a_k` of an expansion with strictly increasing
`Re α_k` forces `Re (z + α_k) > 0` at every point of absolute convergence.

The two continuations are exchanged by the substitution `t ↦ t⁻¹`
(`TauCeti.mellinContAtTop_eq_mellinContAtZero`), which is how the results at `+∞` are derived
from those at `0+`. The split point `1` of the defining formulas may be moved to any `R > 0`, the
explicit terms `a_k/(z + α_k)` becoming `a_k R^{z+α_k}/(z + α_k)`; with the substitution `u = x t`
this shows that the continuation of `t ↦ f(x t)`, whose coefficients are `x^{α_k} a_k` (respectively
`x^{-β_k} b_k`), is `x^{-z}` times that of `f`, as for the Mellin transform itself.

These continuations are the analytic input of the Mellin-transform methods for the asymptotics
of integrals `∫₀^∞ f(t) h(xt) dt` (DLMF §2.5(iii)) and of the distributional methods of DLMF §2.6.

## Main definitions

* `TauCeti.mellinContAtZero f a α n`: the continuation through `n` terms of an expansion at `0+`.
* `TauCeti.mellinContAtTop f b β n`: the continuation through `n` terms of an expansion at `+∞`.

## Main results

* `TauCeti.mellinContAtZero_zero_eq_mellin`, `TauCeti.mellinContAtTop_zero_eq_mellin`: with no
  terms subtracted, each continuation is the Mellin integral split at `1`.
* `TauCeti.mellinContAtZero_eq_mellin`, `TauCeti.mellinContAtTop_eq_mellin`: the continuations
  agree with `mellin f` wherever it converges absolutely.
* `TauCeti.mellinContAtZero_eq_of_le`, `TauCeti.mellinContAtTop_eq_of_le`: independence of the
  number of terms where the domains overlap.
* `TauCeti.differentiableOn_mellinContAtZero_sub_sum`,
  `TauCeti.differentiableOn_mellinContAtTop_add_sum`: holomorphy on the whole strip after removing
  the principal parts `a_k/(z + α_k)` (DLMF 2.5.25) and `-b_k/(z - β_k)` (DLMF 2.5.27).
* `TauCeti.differentiableAt_mellinContAtZero`, `TauCeti.differentiableAt_mellinContAtTop`:
  holomorphy away from the poles `-α_k` and `β_k`.
* `TauCeti.add_re_pos_of_mellinConvergent`, `TauCeti.re_lt_of_mellinConvergent`: a nonzero
  coefficient bounds the strip of absolute convergence.
* `TauCeti.mellinContAtZero_spec`, `TauCeti.mellinContAtTop_spec`: these properties assembled
  for a continuation through an expansion with strictly increasing real parts of the exponents.
* `TauCeti.mellinContAtZero_eq_split`, `TauCeti.mellinContAtTop_eq_split`: the defining formulas
  with the split point `1` moved to any `R > 0`.
* `TauCeti.mellinContAtZero_comp_mul_left`, `TauCeti.mellinContAtTop_comp_mul_left`: rescaling the
  variable by `x > 0` multiplies the continuation by `x^{-z}`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.5(ii)–(iii),
  <https://dlmf.nist.gov/2.5.ii>.
* R. Wong, *Asymptotic Approximations of Integrals*, Academic Press, 1989, Chapter III.
-/

public section

noncomputable section

open Filter Set Complex MeasureTheory Asymptotics
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Continuation through an expansion at `0+` -/

/-- The Mellin transform of `f` continued to the left through the first `n` terms of an expansion
`f(t) ∼ ∑ a_k t^{α_k}` as `t → 0+` (DLMF 2.5.26):
`∫₀¹ t^{z-1} (f(t) - ∑_{k<n} a_k t^{α_k}) dt + ∑_{k<n} a_k/(z + α_k) + ∫₁^∞ t^{z-1} f(t) dt`.
When `a`, `α` form an asymptotic expansion of `f` at `0+` with strictly increasing `Re α_k`, every
`n` gives `mellin f z` where the Mellin integral converges absolutely
(`TauCeti.mellinContAtZero_eq_mellin`). -/
def mellinContAtZero (f : ℝ → E) (a : ℕ → E) (α : ℕ → ℂ) (n : ℕ) (z : ℂ) : E :=
  (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) +
    ∑ k ∈ Finset.range n, (z + α k)⁻¹ • a k + ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) • f t

theorem mellinContAtZero_def (f : ℝ → E) (a : ℕ → E) (α : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    mellinContAtZero f a α n z =
      (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) +
        ∑ k ∈ Finset.range n, (z + α k)⁻¹ • a k + ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) • f t :=
  (rfl)

section AtZero

variable {f : ℝ → E} {a : ℕ → E} {α : ℕ → ℂ} {n : ℕ} {z : ℂ}

/-- With no terms subtracted, the continued transform is the Mellin integral split at `1`. -/
theorem mellinContAtZero_zero_eq_mellin (hf : MellinConvergent f z) :
    mellinContAtZero f a α 0 z = mellin f z := by
  rw [mellinContAtZero_def, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi zero_le_one))]
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, add_zero]

/-- Subtracting one more term leaves the continued transform unchanged, provided the remainder
integral converges and the new term is zero or has convergent Mellin integral over `(0, 1]`. -/
theorem mellinContAtZero_succ [CompleteSpace E]
    (hint : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) (Ioc 0 1))
    (hn : a n = 0 ∨ 0 < (z + α n).re) :
    mellinContAtZero f a α (n + 1) z = mellinContAtZero f a α n z := by
  rcases hn with hn | hn
  · simp only [mellinContAtZero_def, Finset.sum_range_succ, hn, smul_zero, add_zero]
  have hsplit : (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) •
      (f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ α k • a k)) = fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k) -
        (t : ℂ) ^ (z - 1) • ((t : ℂ) ^ α n • a n) := by
    ext t
    rw [Finset.sum_range_succ, ← sub_sub, smul_sub]
  rw [mellinContAtZero_def, mellinContAtZero_def, hsplit,
    integral_sub hint (integrableOn_Ioc_cpow_smul_cpow_smul hn _),
    integral_Ioc_cpow_smul_cpow_smul hn, Finset.sum_range_succ]
  abel

/-- The continued transforms through `n ≤ m` terms agree on the domain `-Re α_n < Re z` of the
first, for an expansion at `0+` with `Re α_k` increasing. -/
theorem mellinContAtZero_eq_of_le [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (hexp : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) ↦ (t : ℂ) ^ α k) a f)
    (hα : Monotone fun k ↦ (α k).re) {m : ℕ} (hnm : n ≤ m) (hz : -(α n).re < z.re) :
    mellinContAtZero f a α m z = mellinContAtZero f a α n z := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hzm : -(α m).re < z.re := (neg_le_neg (hα hnm)).trans_lt hz
    have hm := (hexp.isBigO m).trans (isBigO_ofReal_cpow_rpow eventually_mem_nhdsWithin _)
    rw [← neg_neg (α m).re] at hm
    rw [mellinContAtZero_succ (integrableOn_Ioc_cpow_smul_of_isBigO
      ((hf.sub (locallyIntegrableOn_sum_cpow_smul α a m))) hm hzm)
      (Or.inr (by rw [add_re]; linarith)), ih]

/-- Removing the principal parts `a_k/(z + α_k)` leaves a function holomorphic on the whole strip
`-Re α_n < Re z < b`, for `f = O(t^{-b})` at `+∞` (DLMF 2.5.25). The bound at `0+` is the `n`th
remainder bound of an expansion `HasAsymptoticExpansion (𝓝[>] 0) (fun k t ↦ t ^ α k) a f`. -/
theorem differentiableOn_mellinContAtZero_sub_sum (hf : LocallyIntegrableOn f (Ioi 0))
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ α n)
    {b : ℝ} (hb : f =O[atTop] (· ^ (-b))) :
    DifferentiableOn ℂ
      (fun z ↦ mellinContAtZero f a α n z - ∑ k ∈ Finset.range n, (z + α k)⁻¹ • a k)
      {z | -(α n).re < z.re ∧ z.re < b} := by
  intro z hz
  have hn' := hn.trans (isBigO_ofReal_cpow_rpow eventually_mem_nhdsWithin _)
  rw [← neg_neg (α n).re] at hn'
  have h := (differentiableAt_integral_Ioc_cpow_smul_of_isBigO
    (hf.sub (locallyIntegrableOn_sum_cpow_smul α a n)) hn' hz.1).add
    (differentiableAt_integral_Ioi_cpow_smul_of_isBigO hf hb hz.2)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)).differentiableWithinAt
  simp only [mellinContAtZero_def, Pi.add_apply, Pi.sub_apply]
  abel

/-- The continued transform is holomorphic on the strip `-Re α_n < Re z < b` away from the poles
`-α_k`, `k < n`. -/
theorem differentiableAt_mellinContAtZero (hf : LocallyIntegrableOn f (Ioi 0))
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ α n)
    {b : ℝ} (hb : f =O[atTop] (· ^ (-b))) (hz : -(α n).re < z.re) (hzb : z.re < b)
    (hpole : ∀ k < n, z + α k ≠ 0) :
    DifferentiableAt ℂ (mellinContAtZero f a α n) z := by
  have hopen : IsOpen {z : ℂ | -(α n).re < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have h₁ := (differentiableOn_mellinContAtZero_sub_sum hf hn hb).differentiableAt
    (hopen.mem_nhds ⟨hz, hzb⟩)
  have h₂ : DifferentiableAt ℂ (fun w ↦ ∑ k ∈ Finset.range n, (w + α k)⁻¹ • a k) z :=
    DifferentiableAt.fun_sum fun k hk ↦
      (((differentiableAt_fun_id (x := z)).add_const (α k)).inv
        (hpole k (Finset.mem_range.mp hk))).smul_const (a k)
  simpa only [sub_add_cancel] using h₁.fun_add h₂

/-- If the Mellin integral of `f` converges absolutely at `z` and the earlier nonzero coefficients
satisfy `0 < Re (z + α_j)`, the remainder after `n` terms has absolutely convergent Mellin integral
over `(0, 1]`. -/
private theorem integrableOn_Ioc_sub_sum_of_mellinConvergent (hfz : MellinConvergent f z)
    (h : ∀ j < n, a j ≠ 0 → 0 < (z + α j).re) :
    IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) (Ioc 0 1) := by
  simp_rw [smul_sub, Finset.smul_sum]
  refine (hfz.mono_set Ioc_subset_Ioi_self).sub (integrable_finsetSum _ fun j hj ↦ ?_)
  by_cases hj0 : a j = 0
  · simp only [hj0, smul_zero]
    exact integrableOn_zero
  · exact integrableOn_Ioc_cpow_smul_cpow_smul (h j (Finset.mem_range.mp hj) hj0) _

/-- If the remainder after `k + 1` terms is `O(t ^ α_{k+1})` with `Re α_k < Re α_{k+1}` and
`a_k ≠ 0`, then near `0` the remainder after `k` terms is so large that
`t ^ (Re (z + α_k) - 1) ≤ (2 / ‖a_k‖) ‖t^{z-1} (f(t) - ∑_{j<k} a_j t^{α_j})‖`. -/
private theorem eventually_rpow_le_norm_cpow_smul_sub_sum {k : ℕ}
    (hk1 : (fun t : ℝ ↦ f t - ∑ j ∈ Finset.range (k + 1), (t : ℂ) ^ α j • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ α (k + 1))
    (hα : (α k).re < (α (k + 1)).re) (hk : a k ≠ 0) (z : ℂ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, t ^ ((z + α k).re - 1) ≤
      2 / ‖a k‖ * ‖(t : ℂ) ^ (z - 1) • (f t - ∑ j ∈ Finset.range k, (t : ℂ) ^ α j • a j)‖ := by
  have hA : 0 < ‖a k‖ := norm_pos_iff.mpr hk
  set g : ℕ → ℝ → E := fun n (t : ℝ) ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ α j • a j with hg
  -- Near `0`, `‖g (k + 1) t‖ ≤ C t ^ Re α_{k+1}`, and `C t ^ (Re α_{k+1} - Re α_k) < ‖a_k‖ / 2`.
  obtain ⟨C, hC⟩ := (hk1.trans (isBigO_ofReal_cpow_rpow self_mem_nhdsWithin (α (k + 1)))).bound
  filter_upwards [hC, eventually_mul_rpow_lt_nhdsGT_zero (sub_pos.mpr hα) C (half_pos hA),
    self_mem_nhdsWithin] with t ht₁ ht₂ (ht₀ : 0 < t)
  have hnorm (w : ℂ) (x : E) : ‖(t : ℂ) ^ w • x‖ = t ^ w.re * ‖x‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht₀]
  have hpow : t ^ ((z + α k).re - 1) = t ^ (z - 1).re * t ^ (α k).re := by
    rw [← Real.rpow_add ht₀, add_re, sub_re, one_re]
    congr 1
    ring
  have hsucc : g k t = g (k + 1) t + (t : ℂ) ^ α k • a k := by
    simp only [hg, Finset.sum_range_succ]
    abel
  have hQ : 0 < t ^ (α k).re := Real.rpow_pos_of_pos ht₀ _
  have hsplit : t ^ (α (k + 1)).re = t ^ ((α (k + 1)).re - (α k).re) * t ^ (α k).re := by
    rw [← Real.rpow_add ht₀, sub_add_cancel]
  rw [hsplit, Real.norm_of_nonneg (by positivity)] at ht₁
  have hlow : t ^ (α k).re * ‖a k‖ ≤ ‖g k t‖ + ‖g (k + 1) t‖ :=
    calc t ^ (α k).re * ‖a k‖ = ‖g k t - g (k + 1) t‖ := by rw [hsucc, add_sub_cancel_left, hnorm]
      _ ≤ ‖g k t‖ + ‖g (k + 1) t‖ := norm_sub_le _ _
  have hG : t ^ (α k).re ≤ 2 / ‖a k‖ * ‖g k t‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
    nlinarith [mul_le_mul_of_nonneg_right ht₂.le hQ.le]
  calc t ^ ((z + α k).re - 1) = t ^ (z - 1).re * t ^ (α k).re := hpow
    _ ≤ t ^ (z - 1).re * (2 / ‖a k‖ * ‖g k t‖) := by gcongr
    _ = 2 / ‖a k‖ * ‖(t : ℂ) ^ (z - 1) • g k t‖ := by rw [hnorm]; ring

/-- A nonzero coefficient `a_k` of an expansion of `f` at `0+` with strictly increasing `Re α_k`
bounds the strip of absolute convergence of the Mellin transform of `f`: if it converges at `z`,
then `0 < Re (z + α_k)`. -/
theorem add_re_pos_of_mellinConvergent
    (hexp : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) ↦ (t : ℂ) ^ α k) a f)
    (hα : StrictMono fun k ↦ (α k).re) (hfz : MellinConvergent f z) {k : ℕ} (hk : a k ≠ 0) :
    0 < (z + α k).re := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  by_contra hle
  push Not at hle
  -- By induction the remainder after `k` terms is integrable against `t^{z-1}` on `(0, 1]`, and
  -- near `0` it dominates a multiple of `t ^ (Re (z + α_k) - 1)`, which is then integrable too.
  have hint := integrableOn_Ioc_sub_sum_of_mellinConvergent hfz fun j hj hj0 ↦ ih j hj hj0
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_rpow_le_norm_cpow_smul_sub_sum (hexp.isBigO (k + 1))
      (hα (Nat.lt_succ_self k)) hk z)
  have hδ : 0 < min u 1 := lt_min hu zero_lt_one
  have hpow : IntegrableOn (fun t : ℝ ↦ t ^ ((z + α k).re - 1)) (Ioo 0 (min u 1)) := by
    refine Integrable.mono' ((hint.mono_set (Ioo_subset_Ioc_self.trans
      (Ioc_subset_Ioc_right (min_le_right _ _)))).norm.const_mul (2 / ‖a k‖)) ?_ ?_
    · exact (ContinuousOn.rpow_const continuousOn_id fun t (ht : t ∈ Ioo 0 (min u 1)) ↦
        Or.inl (ne_of_gt ht.1))
        |>.aestronglyMeasurable measurableSet_Ioo
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ ?_
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      exact hsub ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  -- But `t ^ r` is integrable near `0` only for `-1 < r`.
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp hpow
  linarith

/-- Wherever the Mellin integral of `f` converges absolutely, every continued transform through an
expansion of `f` at `0+` with strictly increasing `Re α_k` equals `mellin f z`. -/
theorem mellinContAtZero_eq_mellin [CompleteSpace E]
    (hexp : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) ↦ (t : ℂ) ^ α k) a f)
    (hα : StrictMono fun k ↦ (α k).re) (hfz : MellinConvergent f z) (n : ℕ) :
    mellinContAtZero f a α n z = mellin f z := by
  induction n with
  | zero => exact mellinContAtZero_zero_eq_mellin hfz
  | succ n ih =>
    have hpos : ∀ j, a j ≠ 0 → 0 < (z + α j).re := fun j ↦
      add_re_pos_of_mellinConvergent hexp hα hfz
    rw [mellinContAtZero_succ (integrableOn_Ioc_sub_sum_of_mellinConvergent hfz fun j _ ↦
      hpos j) (or_iff_not_imp_left.mpr (hpos n)), ih]

/-- The continuation at `0+` assembled (DLMF 2.5.25–2.5.26): for an expansion of `f` at `0+` with
strictly increasing `Re α_k` and `f = O(t^{-b})` at `+∞`, `mellinContAtZero f a α n` is holomorphic
on the strip `-Re α_n < Re z < b` away from the poles `-α_k`, agrees with the continuation through
`m` terms on `-Re α_{min n m} < Re z`, equals `mellin f` on `-Re α_0 < Re z < b`, and minus its
principal parts `a_k/(z + α_k)` is holomorphic on the whole strip. -/
theorem mellinContAtZero_spec [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (hexp : HasAsymptoticExpansion (𝓝[>] 0) (fun k (t : ℝ) ↦ (t : ℂ) ^ α k) a f)
    (hα : StrictMono fun k ↦ (α k).re) {b : ℝ} (hb : f =O[atTop] (· ^ (-b))) (n : ℕ) :
    DifferentiableOn ℂ (mellinContAtZero f a α n)
        {z | -(α n).re < z.re ∧ z.re < b ∧ ∀ k < n, z + α k ≠ 0} ∧
      (∀ m, EqOn (mellinContAtZero f a α n) (mellinContAtZero f a α m)
        {z | -(α (min n m)).re < z.re}) ∧
      EqOn (mellinContAtZero f a α n) (mellin f) {z | -(α 0).re < z.re ∧ z.re < b} ∧
      DifferentiableOn ℂ
        (fun z ↦ mellinContAtZero f a α n z - ∑ k ∈ Finset.range n, (z + α k)⁻¹ • a k)
        {z | -(α n).re < z.re ∧ z.re < b} := by
  refine ⟨fun z hz ↦ (differentiableAt_mellinContAtZero hf (hexp.isBigO n) hb hz.1 hz.2.1
      hz.2.2).differentiableWithinAt, fun m z hz ↦ ?_, fun z hz ↦ ?_,
    differentiableOn_mellinContAtZero_sub_sum hf (hexp.isBigO n) hb⟩
  · rcases le_total n m with hnm | hmn
    · exact (mellinContAtZero_eq_of_le hf hexp hα.monotone hnm
        (by rwa [min_eq_left hnm] at hz)).symm
    · exact mellinContAtZero_eq_of_le hf hexp hα.monotone hmn (by rwa [min_eq_right hmn] at hz)
  · have hbot : f =O[𝓝[>] 0] (· ^ (-(-(α 0).re))) := by
      simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, neg_neg] using
        (hexp.isBigO 0).trans (isBigO_ofReal_cpow_rpow eventually_mem_nhdsWithin _)
    exact mellinContAtZero_eq_mellin hexp hα
      (mellinConvergent_of_isBigO_rpow hf hb hz.2 hbot hz.1) n

/-- The continuation at `0+` may be split at any `R > 0` instead of `1`:
`∫₀^R t^{z-1} (f(t) - ∑_{k<n} a_k t^{α_k}) dt + ∑_{k<n} a_k R^{z+α_k}/(z + α_k)
  + ∫_R^∞ t^{z-1} f(t) dt`, wherever the integrals of the defining formula converge and no
`z + α_k` vanishes. -/
theorem mellinContAtZero_eq_split [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (h0 : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) (Ioc 0 1))
    (h1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • f t) (Ioi 1))
    (hz : ∀ k < n, z + α k ≠ 0) {R : ℝ} (hR : 0 < R) :
    mellinContAtZero f a α n z =
      (∫ t : ℝ in Ioc 0 R, (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) +
        ∑ k ∈ Finset.range n, ((R : ℂ) ^ (z + α k) * (z + α k)⁻¹) • a k +
        ∫ t : ℝ in Ioi R, (t : ℂ) ^ (z - 1) • f t := by
  have h := integral_Ioc_add_integral_Ioi_eq
    (locallyIntegrableOn_cpow_smul (hf.sub (locallyIntegrableOn_sum_cpow_smul α a n)) (z - 1))
    (locallyIntegrableOn_cpow_smul hf (z - 1)) h0 h1 hR
  simp only [Pi.sub_apply] at h
  simp_rw [← smul_sub, sub_sub_cancel_left, smul_neg, intervalIntegral.integral_neg,
    intervalIntegral_cpow_smul_sum hz hR] at h
  have hS : ∑ k ∈ Finset.range n, ((R : ℂ) ^ (z + α k) * (z + α k)⁻¹) • a k =
      ∑ k ∈ Finset.range n, ((z + α k)⁻¹ * ((R : ℂ) ^ (z + α k) - 1)) • a k +
        ∑ k ∈ Finset.range n, (z + α k)⁻¹ • a k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← add_smul]; ring_nf
  rw [mellinContAtZero_def, hS]
  linear_combination (norm := module) -h

/-- Rescaling the variable of the continuation at `0+`: the continuation of `t ↦ f (x t)`, whose
expansion at `0+` has coefficients `x^{α_k} a_k`, is `x^{-z}` times that of `f`. -/
theorem mellinContAtZero_comp_mul_left [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (h0 : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • a k)) (Ioc 0 1))
    (h1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • f t) (Ioi 1))
    (hz : ∀ k < n, z + α k ≠ 0) {x : ℝ} (hx : 0 < x) :
    mellinContAtZero (fun t ↦ f (x * t)) (fun k ↦ (x : ℂ) ^ α k • a k) α n z =
      (x : ℂ) ^ (-z) • mellinContAtZero f a α n z := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hI : ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) •
      (f (x * t) - ∑ k ∈ Finset.range n, (t : ℂ) ^ α k • (x : ℂ) ^ α k • a k) =
      (x : ℂ) ^ (-z) • ∫ u : ℝ in Ioc 0 x, (u : ℂ) ^ (z - 1) •
        (f u - ∑ k ∈ Finset.range n, (u : ℂ) ^ α k • a k) := by
    rw [← integral_Ioc_cpow_smul_comp_mul_left _ z hx]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ by
      rw [sum_cpow_smul_cpow_smul_eq_sum_mul_cpow_smul hx.le]
  rw [mellinContAtZero_def, hI, integral_Ioi_cpow_smul_comp_mul_left f z hx,
    mellinContAtZero_eq_split hf h0 h1 hz hx, smul_add, smul_add, Finset.smul_sum]
  congr 2
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, smul_smul, ← mul_assoc, ← cpow_add _ _ hx0, neg_add_cancel_left]
  ring_nf

end AtZero

/-! ### Continuation through an expansion at `+∞` -/

/-- The Mellin transform of `f` continued to the right through the first `n` terms of an
expansion `f(t) ∼ ∑ b_k t^{-β_k}` as `t → +∞` (DLMF 2.5.28):
`∫₀¹ t^{z-1} f(t) dt + ∫₁^∞ t^{z-1} (f(t) - ∑_{k<n} b_k t^{-β_k}) dt - ∑_{k<n} b_k/(z - β_k)`.
When `b`, `β` form an asymptotic expansion of `f` at `+∞` with strictly increasing `Re β_k`, every
`n` gives `mellin f z` where the Mellin integral converges absolutely
(`TauCeti.mellinContAtTop_eq_mellin`). -/
def mellinContAtTop (f : ℝ → E) (b : ℕ → E) (β : ℕ → ℂ) (n : ℕ) (z : ℂ) : E :=
  (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • f t) +
    (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k)) -
    ∑ k ∈ Finset.range n, (z - β k)⁻¹ • b k

theorem mellinContAtTop_def (f : ℝ → E) (b : ℕ → E) (β : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    mellinContAtTop f b β n z =
      (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • f t) +
        (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) •
          (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k)) -
        ∑ k ∈ Finset.range n, (z - β k)⁻¹ • b k :=
  (rfl)

section AtTop

variable {f : ℝ → E} {b : ℕ → E} {β : ℕ → ℂ} {n : ℕ} {z : ℂ}

/-- Substituting `t⁻¹` turns the remainder of an expansion at `+∞` into the remainder of the
reflected expansion at `0+`. -/
private theorem sub_sum_comp_inv {t : ℝ} (ht : 0 < t) (n : ℕ) :
    f t⁻¹⁻¹ - ∑ k ∈ Finset.range n, ((t⁻¹ : ℝ) : ℂ) ^ β k • b k =
      f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k := by
  simp only [inv_inv, ofReal_inv, inv_cpow_ofReal_nonneg ht.le, cpow_neg]

/-- The continuation at `+∞` is the continuation at `0+` of `t ↦ f t⁻¹`, at `-z`. -/
theorem mellinContAtTop_eq_mellinContAtZero (f : ℝ → E) (b : ℕ → E) (β : ℕ → ℂ) (n : ℕ)
    (z : ℂ) : mellinContAtTop f b β n z = mellinContAtZero (fun t ↦ f t⁻¹) b β n (-z) := by
  have hS : ∑ k ∈ Finset.range n, (-z + β k)⁻¹ • b k =
      -∑ k ∈ Finset.range n, (z - β k)⁻¹ • b k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [neg_add_eq_sub, ← neg_sub, inv_neg, neg_smul]
  have hL : ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (-z - 1) •
      (f t⁻¹ - ∑ k ∈ Finset.range n, (t : ℂ) ^ β k • b k) =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k) := by
    rw [integral_Ioc_cpow_smul_eq_integral_Ioi_comp_inv, neg_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by
      rw [sub_sum_comp_inv (zero_lt_one.trans ht)]
  simp only [mellinContAtTop_def, mellinContAtZero_def, hL, hS,
    integral_Ioc_cpow_smul_eq_integral_Ioi_comp_inv f z]
  abel

/-- With no terms subtracted, the continuation at `+∞` is the Mellin integral split at `1`. -/
theorem mellinContAtTop_zero_eq_mellin (hf : MellinConvergent f z) :
    mellinContAtTop f b β 0 z = mellin f z := by
  rw [mellinContAtTop_eq_mellinContAtZero, mellinContAtZero_zero_eq_mellin
    ((mellinConvergent_comp_inv_iff f (-z)).mpr (by rwa [neg_neg])), mellin_comp_inv, neg_neg]

/-- Subtracting one more term leaves the continuation at `+∞` unchanged, provided the remainder
integral converges and the new term is zero or has convergent Mellin integral over `(1, ∞)`. -/
theorem mellinContAtTop_succ [CompleteSpace E]
    (hint : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k)) (Ioi 1))
    (hn : b n = 0 ∨ z.re < (β n).re) :
    mellinContAtTop f b β (n + 1) z = mellinContAtTop f b β n z := by
  rw [mellinContAtTop_eq_mellinContAtZero, mellinContAtTop_eq_mellinContAtZero]
  refine mellinContAtZero_succ ?_ (hn.imp_right fun h ↦ by rw [add_re, neg_re]; linarith)
  rw [integrableOn_Ioc_cpow_smul_iff_integrableOn_Ioi_comp_inv, neg_neg]
  exact hint.congr_fun (fun t ht ↦ by rw [sub_sum_comp_inv (zero_lt_one.trans ht)])
    measurableSet_Ioi

/-- The continuations at `+∞` through `n ≤ m` terms agree on the domain `Re z < Re β_n` of the
first, for an expansion at `+∞` with `Re β_k` increasing. -/
theorem mellinContAtTop_eq_of_le [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (hexp : HasAsymptoticExpansion atTop (fun k (t : ℝ) ↦ (t : ℂ) ^ (-β k)) b f)
    (hβ : Monotone fun k ↦ (β k).re) {m : ℕ} (hnm : n ≤ m) (hz : z.re < (β n).re) :
    mellinContAtTop f b β m z = mellinContAtTop f b β n z := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hzm : z.re < (β m).re := hz.trans_le (hβ hnm)
    rw [mellinContAtTop_succ (integrableOn_Ioi_cpow_smul_of_isBigO
      (hf.sub (locallyIntegrableOn_sum_cpow_smul (fun k ↦ -β k) b m))
      ((hexp.isBigO m).trans (isBigO_ofReal_cpow_rpow (eventually_gt_atTop 0) _)) hzm)
      (Or.inr hzm), ih]

/-- Removing the principal parts `-b_k/(z - β_k)`, i.e. adding `∑ b_k/(z - β_k)`, leaves a function
holomorphic on the whole strip `-c < Re z < Re β_n`, for `f = O(t^c)` at `0+` (DLMF 2.5.27). The
bound at `+∞` is the `n`th remainder bound of an expansion
`HasAsymptoticExpansion atTop (fun k t ↦ t ^ (-β k)) b f`. -/
theorem differentiableOn_mellinContAtTop_add_sum (hf : LocallyIntegrableOn f (Ioi 0))
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-β n))
    {c : ℝ} (hc : f =O[𝓝[>] 0] (· ^ c)) :
    DifferentiableOn ℂ
      (fun z ↦ mellinContAtTop f b β n z + ∑ k ∈ Finset.range n, (z - β k)⁻¹ • b k)
      {z | -c < z.re ∧ z.re < (β n).re} := by
  intro z hz
  have h := (differentiableAt_integral_Ioc_cpow_smul_of_isBigO hf
    (by simpa only [neg_neg] using hc) hz.1).add
    (differentiableAt_integral_Ioi_cpow_smul_of_isBigO
      (hf.sub (locallyIntegrableOn_sum_cpow_smul (fun k ↦ -β k) b n))
      (hn.trans (isBigO_ofReal_cpow_rpow (eventually_gt_atTop 0) _)) hz.2)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)).differentiableWithinAt
  simp only [mellinContAtTop_def, Pi.add_apply, Pi.sub_apply]
  abel

/-- The continuation at `+∞` is holomorphic on the strip `-c < Re z < Re β_n` away from the poles
`β_k`, `k < n`. -/
theorem differentiableAt_mellinContAtTop (hf : LocallyIntegrableOn f (Ioi 0))
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-β n))
    {c : ℝ} (hc : f =O[𝓝[>] 0] (· ^ c)) (hz : -c < z.re) (hzβ : z.re < (β n).re)
    (hpole : ∀ k < n, z ≠ β k) :
    DifferentiableAt ℂ (mellinContAtTop f b β n) z := by
  have hopen : IsOpen {z : ℂ | -c < z.re ∧ z.re < (β n).re} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have h₁ := (differentiableOn_mellinContAtTop_add_sum hf hn hc).differentiableAt
    (hopen.mem_nhds ⟨hz, hzβ⟩)
  have h₂ : DifferentiableAt ℂ (fun w ↦ ∑ k ∈ Finset.range n, (w - β k)⁻¹ • b k) z :=
    DifferentiableAt.fun_sum fun k hk ↦
      (((differentiableAt_fun_id (x := z)).sub_const (β k)).inv
        (sub_ne_zero.mpr (hpole k (Finset.mem_range.mp hk)))).smul_const (b k)
  simpa only [add_sub_cancel_right] using h₁.fun_sub h₂

/-- A nonzero coefficient `b_k` of an expansion of `f` at `+∞` with strictly increasing `Re β_k`
bounds the strip of absolute convergence of the Mellin transform of `f`: if it converges at `z`,
then `Re z < Re β_k`. -/
theorem re_lt_of_mellinConvergent
    (hexp : HasAsymptoticExpansion atTop (fun k (t : ℝ) ↦ (t : ℂ) ^ (-β k)) b f)
    (hβ : StrictMono fun k ↦ (β k).re) (hfz : MellinConvergent f z) {k : ℕ} (hk : b k ≠ 0) :
    z.re < (β k).re := by
  have h := add_re_pos_of_mellinConvergent hexp.comp_inv_atTop hβ
    ((mellinConvergent_comp_inv_iff f (-z)).mpr (by rwa [neg_neg])) hk
  rw [add_re, neg_re] at h
  linarith

/-- Wherever the Mellin integral of `f` converges absolutely, every continuation through an
expansion of `f` at `+∞` with strictly increasing `Re β_k` equals `mellin f z`. -/
theorem mellinContAtTop_eq_mellin [CompleteSpace E]
    (hexp : HasAsymptoticExpansion atTop (fun k (t : ℝ) ↦ (t : ℂ) ^ (-β k)) b f)
    (hβ : StrictMono fun k ↦ (β k).re) (hfz : MellinConvergent f z) (n : ℕ) :
    mellinContAtTop f b β n z = mellin f z := by
  rw [mellinContAtTop_eq_mellinContAtZero, mellinContAtZero_eq_mellin
    hexp.comp_inv_atTop hβ
    ((mellinConvergent_comp_inv_iff f (-z)).mpr (by rwa [neg_neg])) n, mellin_comp_inv, neg_neg]

/-- The continuation at `+∞` assembled (DLMF 2.5.27–2.5.28): for an expansion of `f` at `+∞` with
strictly increasing `Re β_k` and `f = O(t^c)` at `0+`, `mellinContAtTop f b β n` is holomorphic on
the strip `-c < Re z < Re β_n` away from the poles `β_k`, agrees with the continuation through `m`
terms on `Re z < Re β_{min n m}`, equals `mellin f` on `-c < Re z < Re β_0`, and with its principal
parts `-b_k/(z - β_k)` removed (i.e. plus `∑ b_k/(z - β_k)`) is holomorphic on the whole strip. -/
theorem mellinContAtTop_spec [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (hexp : HasAsymptoticExpansion atTop (fun k (t : ℝ) ↦ (t : ℂ) ^ (-β k)) b f)
    (hβ : StrictMono fun k ↦ (β k).re) {c : ℝ} (hc : f =O[𝓝[>] 0] (· ^ c)) (n : ℕ) :
    DifferentiableOn ℂ (mellinContAtTop f b β n)
        {z | -c < z.re ∧ z.re < (β n).re ∧ ∀ k < n, z ≠ β k} ∧
      (∀ m, EqOn (mellinContAtTop f b β n) (mellinContAtTop f b β m)
        {z | z.re < (β (min n m)).re}) ∧
      EqOn (mellinContAtTop f b β n) (mellin f) {z | -c < z.re ∧ z.re < (β 0).re} ∧
      DifferentiableOn ℂ
        (fun z ↦ mellinContAtTop f b β n z + ∑ k ∈ Finset.range n, (z - β k)⁻¹ • b k)
        {z | -c < z.re ∧ z.re < (β n).re} := by
  refine ⟨fun z hz ↦ (differentiableAt_mellinContAtTop hf (hexp.isBigO n) hc hz.1 hz.2.1
      hz.2.2).differentiableWithinAt, fun m z hz ↦ ?_, fun z hz ↦ ?_,
    differentiableOn_mellinContAtTop_add_sum hf (hexp.isBigO n) hc⟩
  · rcases le_total n m with hnm | hmn
    · exact (mellinContAtTop_eq_of_le hf hexp hβ.monotone hnm
        (by rwa [min_eq_left hnm] at hz)).symm
    · exact mellinContAtTop_eq_of_le hf hexp hβ.monotone hmn (by rwa [min_eq_right hmn] at hz)
  · have htop : f =O[atTop] (· ^ (-(β 0).re)) := by
      simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, neg_re] using
        (hexp.isBigO 0).trans (isBigO_ofReal_cpow_rpow (eventually_gt_atTop 0) _)
    exact mellinContAtTop_eq_mellin hexp hβ
      (mellinConvergent_of_isBigO_rpow hf htop hz.2 (by simpa only [neg_neg] using hc) hz.1) n

/-- The continuation at `+∞` may be split at any `R > 0` instead of `1`:
`∫₀^R t^{z-1} f(t) dt + ∫_R^∞ t^{z-1} (f(t) - ∑_{k<n} b_k t^{-β_k}) dt
  - ∑_{k<n} b_k R^{z-β_k}/(z - β_k)`, wherever the integrals of the defining formula converge and
no `z - β_k` vanishes. -/
theorem mellinContAtTop_eq_split [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (h0 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • f t) (Ioc 0 1))
    (h1 : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k)) (Ioi 1))
    (hz : ∀ k < n, z ≠ β k) {R : ℝ} (hR : 0 < R) :
    mellinContAtTop f b β n z =
      (∫ t : ℝ in Ioc 0 R, (t : ℂ) ^ (z - 1) • f t) +
        (∫ t : ℝ in Ioi R, (t : ℂ) ^ (z - 1) •
          (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k)) -
        ∑ k ∈ Finset.range n, ((R : ℂ) ^ (z - β k) * (z - β k)⁻¹) • b k := by
  have h := integral_Ioc_add_integral_Ioi_eq (locallyIntegrableOn_cpow_smul hf (z - 1))
    (locallyIntegrableOn_cpow_smul (hf.sub (locallyIntegrableOn_sum_cpow_smul _ b n)) (z - 1))
    h0 h1 hR
  simp only [Pi.sub_apply] at h
  simp_rw [← smul_sub, sub_sub_cancel] at h
  rw [intervalIntegral_cpow_smul_sum (w := fun k ↦ -β k)
    (fun k hk ↦ by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr (hz k hk)) hR] at h
  simp only [← sub_eq_add_neg] at h
  have hS : ∑ k ∈ Finset.range n, ((R : ℂ) ^ (z - β k) * (z - β k)⁻¹) • b k =
      ∑ k ∈ Finset.range n, ((z - β k)⁻¹ * ((R : ℂ) ^ (z - β k) - 1)) • b k +
        ∑ k ∈ Finset.range n, (z - β k)⁻¹ • b k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← add_smul]; ring_nf
  rw [mellinContAtTop_def, hS]
  linear_combination (norm := module) -h

/-- Rescaling the variable of the continuation at `+∞`: the continuation of `t ↦ f (x t)`, whose
expansion at `+∞` has coefficients `x^{-β_k} b_k`, is `x^{-z}` times that of `f`. -/
theorem mellinContAtTop_comp_mul_left [CompleteSpace E] (hf : LocallyIntegrableOn f (Ioi 0))
    (h0 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • f t) (Ioc 0 1))
    (h1 : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ (z - 1) • (f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • b k)) (Ioi 1))
    (hz : ∀ k < n, z ≠ β k) {x : ℝ} (hx : 0 < x) :
    mellinContAtTop (fun t ↦ f (x * t)) (fun k ↦ (x : ℂ) ^ (-β k) • b k) β n z =
      (x : ℂ) ^ (-z) • mellinContAtTop f b β n z := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hI : ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) •
      (f (x * t) - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-β k) • (x : ℂ) ^ (-β k) • b k) =
      (x : ℂ) ^ (-z) • ∫ u : ℝ in Ioi x, (u : ℂ) ^ (z - 1) •
        (f u - ∑ k ∈ Finset.range n, (u : ℂ) ^ (-β k) • b k) := by
    rw [← integral_Ioi_cpow_smul_comp_mul_left _ z hx]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
      rw [sum_cpow_smul_cpow_smul_eq_sum_mul_cpow_smul hx.le (fun k ↦ -β k)]
  rw [mellinContAtTop_def, hI, integral_Ioc_cpow_smul_comp_mul_left f z hx,
    mellinContAtTop_eq_split hf h0 h1 hz hx, smul_sub, smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, smul_smul, ← mul_assoc, ← cpow_add _ _ hx0]
  ring_nf

end AtTop

end TauCeti
