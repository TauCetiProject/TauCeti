/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.Analysis.MellinTransform.Continued
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Regularization of `∫₀^∞ f(t) h(xt) dt` (DLMF 2.6.54–2.6.62)

Let `f` be locally integrable and `h` continuous on `(0, ∞)`, and fix `n`. Assume the expansions
of order `n`: `f(t) = ∑_{s<n} a_s t^{s+α-1} + f_n(t)` with `f_n(t) = O(t^{n+α-1})` as `t → 0+`,
and `h(t) = ∑_{s<n} b_s t^{-s-β} + h_n(t)` with `h_n(t) = O(t^{-n-β})` as `t → +∞`. Asymptotic
expansions `f(t) ∼ ∑ a_s t^{s+α-1}` and `h(t) ∼ ∑ b_s t^{-s-β}`
(`Asymptotics.HasAsymptoticExpansion`) give these for every `n`, through
`Asymptotics.HasAsymptoticExpansion.isBigO`. Assume moreover
`h(t) = O(t^{-c})` as `t → 0+` with `c < α`, and `f(t) = O(t^{-ρ})` as `t → +∞` with `1 < ρ + β`,
and `0 < |α - β| < 1` (DLMF takes `0 < α, β ≤ 1` and `α ≠ β`). Then for every `x > 0`, the
remainder integral below converges absolutely and

`∫₀^∞ f(t) h(xt) dt = ∑_{j<n} a_j 𝓜h(j + α) x^{-j-α} + ∑_{k<n} b_k 𝓜f(1 - k - β) x^{-k-β}
  + ∫₀^∞ f_n(t) h_n(xt) dt`,

where `𝓜h = mellinContAtTop h b (k ↦ k + β) n` and `𝓜f = mellinContAtZero f a (k ↦ k + α - 1) n`
are the Mellin transforms continued through the expansions; and the last integral is
`O(x^{-n-min(α, β)})` as `x → +∞`. For full expansions of `f` and `h`, these give the asymptotic
expansion of
`∫₀^∞ f(t) h(xt) dt` as `x → +∞` in the two interleaved scales `x^{-j-α}` and `x^{-k-β}`,
with coefficients the continued Mellin transforms.

The identity is elementary. On `(0, 1]` the difference `f(t) h(xt) - f_n(t) h_n(xt)` is
`∑ a_j t^{j+α-1} h(xt) + ∑ b_k (xt)^{-k-β} f_n(t)`, and on `(1, ∞)` it is
`∑ a_j t^{j+α-1} h_n(xt) + ∑ b_k (xt)^{-k-β} f(t)`. Each piece is a partial Mellin integral, and the
two brackets they form are the continued transforms of `h(x ·)` and of `f` up to their principal
parts, which cancel against each other. The continued transform of `h(x ·)` is `x^{-z}` times that
of `h` (`TauCeti.mellinContAtTop_comp_mul_left`). For the bound, `(0, ∞)` is split at `x⁻¹` and at
a fixed small `δ`, and on each piece the integrand is dominated by explicit powers.

## Main results

* `TauCeti.integral_mul_comp_mul_eq_sum_mellinCont_add_integral`: the exact identity above.
* `TauCeti.integrableOn_mul_comp_mul_sub_sum`: the remainder integrand `f_n(t) h_n(xt)` is
  integrable on `(0, ∞)`; for `n = 0` this is the integrability of `t ↦ f(t) h(xt)`.
* `TauCeti.isBigO_integral_mul_comp_mul_sub_sum`: the remainder integral is
  `O(x^{-n-min(α, β)})` as `x → +∞`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.6(iv),
  <https://dlmf.nist.gov/2.6.iv>.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Dover, 1986,
  Chapter 4.
* R. Wong, *Asymptotic Approximations of Integrals*, Academic Press, 1989, Chapter VI.
-/

public section

open Filter Set Complex MeasureTheory Asymptotics
open scoped Topology

namespace TauCeti

/-! ### The algebra of regularization -/

/-- The double sum of the principal parts of the two continued transforms cancels. -/
private theorem sum_mul_add_sum_mul_sub_cancel (u v X Y : ℕ → ℂ) (d : ℕ → ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range n, u j * (X j + ∑ k ∈ Finset.range n, d j k * v k) +
        ∑ k ∈ Finset.range n, v k * (Y k - ∑ j ∈ Finset.range n, d j k * u j) =
      ∑ j ∈ Finset.range n, u j * X j + ∑ k ∈ Finset.range n, v k * Y k := by
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun k j ↦ v k * (d j k * u j))]
  have : ∀ j ∈ Finset.range n, ∑ k ∈ Finset.range n, u j * (d j k * v k) =
      ∑ k ∈ Finset.range n, v k * (d j k * u j) := fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- The algebra of regularization. If `f = ∑_{j<n} u_j P_j + F` and `g = ∑_{k<n} v_k Q_k + H`, then
on `(0, 1]` the product `f g - F H` is `∑ u_j P_j g + ∑ v_k Q_k F`, and on `(1, ∞)` it is
`∑ u_j P_j H + ∑ v_k Q_k f`. When these pieces are integrable, so are `f g` and `F H`, and the
integral of `f g` over `(0, ∞)` is the sum of the pieces plus that of `F H`. -/
private theorem integral_mul_eq_sum_add_integral {f g F H : ℝ → ℂ} {P Q : ℕ → ℝ → ℂ}
    {u v : ℕ → ℂ} {n : ℕ}
    (hf : ∀ t, f t = ∑ j ∈ Finset.range n, u j * P j t + F t)
    (hg : ∀ t, g t = ∑ k ∈ Finset.range n, v k * Q k t + H t)
    (hPg : ∀ j < n, IntegrableOn (fun t ↦ P j t * g t) (Ioc 0 1))
    (hQF : ∀ k < n, IntegrableOn (fun t ↦ Q k t * F t) (Ioc 0 1))
    (hQf : ∀ k < n, IntegrableOn (fun t ↦ Q k t * f t) (Ioi 1))
    (hPH : ∀ j < n, IntegrableOn (fun t ↦ P j t * H t) (Ioi 1))
    (hFg : IntegrableOn (fun t ↦ F t * g t) (Ioc 0 1))
    (hfH : IntegrableOn (fun t ↦ f t * H t) (Ioi 1)) :
    IntegrableOn (fun t ↦ F t * H t) (Ioi 0) ∧ ∫ t in Ioi 0, f t * g t =
      ∑ j ∈ Finset.range n, u j * ((∫ t in Ioc 0 1, P j t * g t) + ∫ t in Ioi 1, P j t * H t) +
        ∑ k ∈ Finset.range n, v k * ((∫ t in Ioc 0 1, Q k t * F t) + ∫ t in Ioi 1, Q k t * f t) +
        ∫ t in Ioi 0, F t * H t := by
  -- finite linear combinations of the pieces are integrable, with the combined integrals
  have hsum {S : Set ℝ} {R : ℕ → ℝ → ℂ} (c : ℕ → ℂ) (hR : ∀ j < n, IntegrableOn (R j) S) :
      IntegrableOn (fun t ↦ ∑ j ∈ Finset.range n, c j * R j t) S ∧
        ∫ t in S, ∑ j ∈ Finset.range n, c j * R j t =
          ∑ j ∈ Finset.range n, c j * ∫ t in S, R j t := by
    have hR' : ∀ j ∈ Finset.range n, Integrable (fun t ↦ c j * R j t) (volume.restrict S) :=
      fun j hj ↦ (hR j (Finset.mem_range.mp hj)).const_mul (c j)
    refine ⟨integrable_finsetSum _ hR', ?_⟩
    rw [integral_finsetSum _ hR']
    exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _
  obtain ⟨iPg, IPg⟩ := hsum (S := Ioc 0 1) u hPg
  obtain ⟨iQF, IQF⟩ := hsum (S := Ioc 0 1) v hQF
  obtain ⟨iQf, IQf⟩ := hsum (S := Ioi 1) v hQf
  obtain ⟨iPH, IPH⟩ := hsum (S := Ioi 1) u hPH
  -- on `(0, 1]`, `f g = ∑ u_j P_j g + ∑ v_k Q_k F + F H`, and `F H = F g - ∑ v_k Q_k F`
  have e₀ : EqOn (fun t ↦ ∑ j ∈ Finset.range n, u j * (P j t * g t) +
      ∑ k ∈ Finset.range n, v k * (Q k t * F t) + F t * H t) (fun t ↦ f t * g t) (Ioc 0 1) :=
    fun t _ ↦ by simp only [← mul_assoc, ← Finset.sum_mul, hf t, hg t]; ring
  have hFH₀ : IntegrableOn (fun t ↦ F t * H t) (Ioc 0 1) := (hFg.sub iQF).congr_fun
    (fun t _ ↦ by simp only [Pi.sub_apply, ← mul_assoc, ← Finset.sum_mul, hg t]; ring)
    measurableSet_Ioc
  have i₀ : IntegrableOn (fun t ↦ ∑ j ∈ Finset.range n, u j * (P j t * g t) +
      ∑ k ∈ Finset.range n, v k * (Q k t * F t)) (Ioc 0 1) := iPg.add iQF
  -- on `(1, ∞)`, `f g = ∑ u_j P_j H + ∑ v_k Q_k f + F H`, and `F H = f H - ∑ u_j P_j H`
  have e₁ : EqOn (fun t ↦ ∑ j ∈ Finset.range n, u j * (P j t * H t) +
      ∑ k ∈ Finset.range n, v k * (Q k t * f t) + F t * H t) (fun t ↦ f t * g t) (Ioi 1) :=
    fun t _ ↦ by simp only [← mul_assoc, ← Finset.sum_mul, hf t, hg t]; ring
  have hFH₁ : IntegrableOn (fun t ↦ F t * H t) (Ioi 1) := (hfH.sub iPH).congr_fun
    (fun t _ ↦ by simp only [Pi.sub_apply, ← mul_assoc, ← Finset.sum_mul, hf t]; ring)
    measurableSet_Ioi
  have i₁ : IntegrableOn (fun t ↦ ∑ j ∈ Finset.range n, u j * (P j t * H t) +
      ∑ k ∈ Finset.range n, v k * (Q k t * f t)) (Ioi 1) := iPH.add iQf
  have hsplit {G : ℝ → ℂ} (h₀ : IntegrableOn G (Ioc 0 1)) (h₁ : IntegrableOn G (Ioi 1)) :
      ∫ t in Ioi 0, G t = (∫ t in Ioc 0 1, G t) + ∫ t in Ioi 1, G t := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h₀ h₁]
  refine ⟨by rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]; exact hFH₀.union hFH₁, ?_⟩
  rw [hsplit ((i₀.add hFH₀).congr_fun e₀ measurableSet_Ioc)
      ((i₁.add hFH₁).congr_fun e₁ measurableSet_Ioi), hsplit hFH₀ hFH₁,
    ← setIntegral_congr_fun measurableSet_Ioc e₀, ← setIntegral_congr_fun measurableSet_Ioi e₁,
    integral_add i₀ hFH₀, integral_add iPg iQF, integral_add i₁ hFH₁, integral_add iPH iQf, IPg,
    IQF, IQf, IPH]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- The regularization identity in terms of partial Mellin integrals. If
`f = ∑_{j<n} u_j t^{z_j-1} + F` and `g = ∑_{k<n} v_k t^{w_k-1} + H`, with the power bounds below,
then `∫₀^∞ f g` is `∑ u_j (∫₀¹ t^{z_j-1} g + ∫₁^∞ t^{z_j-1} H) + ∑ v_k (∫₀¹ t^{w_k-1} F +
∫₁^∞ t^{w_k-1} f) + ∫₀^∞ F H`, every integral converging absolutely; in particular `F H` is
integrable on `(0, ∞)`. -/
private theorem integral_mul_eq_sum_partialMellin {f g F H : ℝ → ℂ} {u v z w : ℕ → ℂ} {n : ℕ}
    {b c ρ r : ℝ} (hf : ∀ t, f t = ∑ j ∈ Finset.range n, u j * (t : ℂ) ^ (z j - 1) + F t)
    (hg : ∀ t, g t = ∑ k ∈ Finset.range n, v k * (t : ℂ) ^ (w k - 1) + H t)
    (hfl : LocallyIntegrableOn f (Ioi 0)) (hFl : LocallyIntegrableOn F (Ioi 0))
    (hgc : ContinuousOn g (Ioi 0)) (hHc : ContinuousOn H (Ioi 0))
    (hF₀ : F =O[𝓝[>] 0] (· ^ (-b))) (hg₀ : g =O[𝓝[>] 0] (· ^ (-c)))
    (hf₁ : f =O[atTop] (· ^ (-ρ))) (hH₁ : H =O[atTop] (· ^ (-r)))
    (hz₀ : ∀ j < n, c < (z j).re) (hw₀ : ∀ k < n, b < (w k).re) (hw₁ : ∀ k < n, (w k).re < ρ)
    (hz₁ : ∀ j < n, (z j).re < r) (hbc : b + c < 1) (hρr : 1 < ρ + r) :
    IntegrableOn (fun t ↦ F t * H t) (Ioi 0) ∧ ∫ t in Ioi 0, f t * g t =
      ∑ j ∈ Finset.range n, u j * ((∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z j - 1) * g t) +
          ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z j - 1) * H t) +
        ∑ k ∈ Finset.range n, v k * ((∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (w k - 1) * F t) +
          ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (w k - 1) * f t) +
        ∫ t in Ioi 0, F t * H t := by
  refine integral_mul_eq_sum_add_integral hf hg
    (fun j hj ↦ by
      simpa only [smul_eq_mul] using integrableOn_Ioc_cpow_smul_of_isBigO
        (hgc.locallyIntegrableOn measurableSet_Ioi) hg₀ (hz₀ j hj))
    (fun k hk ↦ by simpa only [smul_eq_mul] using
      integrableOn_Ioc_cpow_smul_of_isBigO hFl hF₀ (hw₀ k hk))
    (fun k hk ↦ by simpa only [smul_eq_mul] using
      integrableOn_Ioi_cpow_smul_of_isBigO hfl hf₁ (hw₁ k hk))
    (fun j hj ↦ by
      simpa only [smul_eq_mul] using integrableOn_Ioi_cpow_smul_of_isBigO
        (hHc.locallyIntegrableOn measurableSet_Ioi) hH₁ (hz₁ j hj)) ?_ ?_
  · have := integrableOn_Ioc_cpow_smul_of_isBigO
      (hFl.mul_continuousOn hgc isOpen_Ioi.isLocallyClosed)
      (hF₀.mul_nhdsGT_zero_rpow_of_isBigO_rpow hg₀ (c := -(b + c)) (by linarith))
      (z := 1) (by simpa using hbc)
    simpa using this
  · have := integrableOn_Ioi_cpow_smul_of_isBigO
      (hfl.mul_continuousOn hHc isOpen_Ioi.isLocallyClosed)
      (hf₁.mul_atTop_rpow_of_isBigO_rpow _ _ (-(ρ + r)) hH₁ (by linarith)) (z := 1)
      (by simpa using hρr)
    simpa using this

/-! ### The exact identity -/

/-- For `|α - β| < 1` and `α ≠ β`, no `j + α` with `j : ℕ` equals any `k + β` with `k : ℕ`. -/
private theorem natCast_add_ne_natCast_add {α β : ℝ} (hαβ : α < β + 1) (hβα : β < α + 1)
    (hne : α ≠ β) (j k : ℕ) : (j : ℂ) + α ≠ (k : ℂ) + β := by
  intro h
  have h' : (j : ℝ) + α = k + β := by exact_mod_cast congrArg re h
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    linarith
  · exact hne (by linarith)
  · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hjk
    linarith

variable {f h : ℝ → ℂ} {a b : ℕ → ℂ} {α β c ρ : ℝ}

/-- The remainder bound of `f` at `0+` after `n` terms, with a real power. -/
private theorem isBigO_sub_sum_nhdsGT {n : ℕ}
    (hfn : (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ ((n : ℂ) + α - 1)) :
    (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j)
      =O[𝓝[>] 0] (· ^ ((n : ℝ) + α - 1)) := by
  have := hfn.trans (isBigO_ofReal_cpow_rpow eventually_mem_nhdsWithin _)
  simpa only [sub_re, add_re, natCast_re, ofReal_re, one_re] using this

/-- The remainder bound of `h` at `+∞` after `n` terms, with a real power. -/
private theorem isBigO_sub_sum_atTop {n : ℕ}
    (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β))) :
    (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k)
      =O[atTop] (· ^ (-((n : ℝ) + β))) := by
  have := hhn.trans (isBigO_ofReal_cpow_rpow (eventually_gt_atTop 0) _)
  simpa only [neg_re, add_re, natCast_re, ofReal_re] using this

/-- The partial Mellin integrals of `h (x ·)` at `z`, with the expansion of `h (x ·)` at `+∞`
subtracted on `(1, ∞)`, are `x^{-z}` times the continued transform of `h` plus the principal
parts of the continued transform of `h (x ·)`. -/
private theorem integral_Ioc_add_integral_Ioi_comp_mul_left (hh : ContinuousOn h (Ioi 0))
    {n : ℕ} (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β)))
    (hh0 : h =O[𝓝[>] 0] (· ^ (-c))) {z : ℂ} (hcz : c < z.re) (hzn : z.re < n + β)
    (hz : ∀ k < n, z ≠ (k : ℂ) + β) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) * h (x * t)) +
        (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) * (h (x * t) - ∑ k ∈ Finset.range n,
          (t : ℂ) ^ (-((k : ℂ) + β)) • ((x : ℂ) ^ (-((k : ℂ) + β)) • b k))) =
      (x : ℂ) ^ (-z) * mellinContAtTop h b (fun k ↦ (k : ℂ) + β) n z +
        ∑ k ∈ Finset.range n, (z - ((k : ℂ) + β))⁻¹ * ((x : ℂ) ^ (-((k : ℂ) + β)) * b k) := by
  have hsc := mellinContAtTop_comp_mul_left (f := h) (b := b) (β := fun k : ℕ ↦ (k : ℂ) + β)
    (hh.locallyIntegrableOn measurableSet_Ioi)
    (integrableOn_Ioc_cpow_smul_of_isBigO (hh.locallyIntegrableOn measurableSet_Ioi) hh0 hcz)
    (integrableOn_Ioi_cpow_smul_of_isBigO
      ((hh.sub (continuousOn_sum_cpow_smul _ b n)).locallyIntegrableOn measurableSet_Ioi)
      (isBigO_sub_sum_atTop hhn) hzn) hz hx
  rw [mellinContAtTop_def] at hsc
  simp only [smul_eq_mul] at hsc ⊢
  linear_combination hsc

/-- The partial Mellin integrals of `f` at `1 - (k + β)`, with the expansion of `f` at `0+`
subtracted on `(0, 1]`, are the continued transform of `f` minus its principal parts. -/
private theorem integral_Ioc_add_integral_Ioi_eq_mellinContAtZero {n : ℕ} (k : ℕ) :
    (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (1 - ((k : ℂ) + β) - 1) *
        (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j)) +
      (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (1 - ((k : ℂ) + β) - 1) * f t) =
    mellinContAtZero f a (fun j ↦ (j : ℂ) + α - 1) n (1 - ((k : ℂ) + β)) -
      ∑ j ∈ Finset.range n, ((j : ℂ) + α - ((k : ℂ) + β))⁻¹ * a j := by
  have hS : ∑ j ∈ Finset.range n, (1 - ((k : ℂ) + β) + ((j : ℂ) + α - 1))⁻¹ * a j =
      ∑ j ∈ Finset.range n, ((j : ℂ) + α - ((k : ℂ) + β))⁻¹ * a j :=
    Finset.sum_congr rfl fun j _ ↦ by ring_nf
  rw [mellinContAtZero_def]
  simp only [smul_eq_mul, hS]
  ring

/-- The common first stage of the regularization theorems: under their hypotheses, the remainder
integrand is integrable on `(0, ∞)`, and `∫₀^∞ f(t) h(xt) dt` is the sum of the partial Mellin
brackets of `h (x ·)` and of `f` plus the remainder integral. -/
private theorem integrableOn_and_integral_eq_sum_brackets
    (hf : LocallyIntegrableOn f (Ioi 0)) (hh : ContinuousOn h (Ioi 0)) {n : ℕ}
    (hfn : (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ ((n : ℂ) + α - 1))
    (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β)))
    (hh0 : h =O[𝓝[>] 0] (· ^ (-c))) (hc : c < α) (hf1 : f =O[atTop] (· ^ (-ρ)))
    (hρ : 1 < ρ + β) (hαβ : α < β + 1) (hβα : β < α + 1) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t ↦ (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) *
      (h (x * t) - ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) • b k)) (Ioi 0) ∧
    ∫ t in Ioi 0, f t * h (x * t) =
      ∑ j ∈ Finset.range n, a j * ((∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ ((j : ℂ) + α - 1) * h (x * t)) +
          ∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((j : ℂ) + α - 1) * (h (x * t) - ∑ k ∈ Finset.range n,
            (t : ℂ) ^ (-((k : ℂ) + β)) • ((x : ℂ) ^ (-((k : ℂ) + β)) • b k))) +
        ∑ k ∈ Finset.range n, (x : ℂ) ^ (-((k : ℂ) + β)) * b k *
          ((∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (1 - ((k : ℂ) + β) - 1) *
            (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j)) +
          ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (1 - ((k : ℂ) + β) - 1) * f t) +
        ∫ t in Ioi 0, (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) *
          (h (x * t) - ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) • b k) := by
  have hlt (j : ℕ) (hj : j < n) : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  -- `A`, `B`: the subtracted sums of `f` at `0+` and of `h (x ·)` at `+∞`, in the variable `t`
  set A : ℝ → ℂ := fun t ↦ ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j
  set B : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.range n,
    (t : ℂ) ^ (-((k : ℂ) + β)) • ((x : ℂ) ^ (-((k : ℂ) + β)) • b k)
  have hBx (t : ℝ) : ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) • b k = B t :=
    (sum_cpow_smul_cpow_smul_eq_sum_mul_cpow_smul hx.le (fun k ↦ -((k : ℂ) + β)) b n t).symm
  -- the subtracted sums in the shape of `integral_mul_eq_sum_partialMellin`
  have hA (t : ℝ) : ∑ j ∈ Finset.range n, a j * (t : ℂ) ^ ((j : ℂ) + α - 1) = A t :=
    Finset.sum_congr rfl fun j _ ↦ by rw [smul_eq_mul, mul_comm]
  have hB (t : ℝ) : ∑ k ∈ Finset.range n, (x : ℂ) ^ (-((k : ℂ) + β)) * b k *
      (t : ℂ) ^ (1 - ((k : ℂ) + β) - 1) = B t :=
    Finset.sum_congr rfl fun k _ ↦ by rw [smul_smul, smul_eq_mul, mul_comm]; ring_nf
  have hhx : ContinuousOn (fun t ↦ h (x * t)) (Ioi 0) :=
    hh.comp (continuousOn_const.mul continuousOn_id) fun t ht ↦ mul_pos hx ht
  have hH1 : (fun t ↦ h (x * t) - B t) =O[atTop] (· ^ (-((n : ℝ) + β))) := by
    simpa only [hBx] using (isBigO_sub_sum_atTop hhn).comp_mul_left_rpow hx
      (tendsto_id.const_mul_atTop hx) (eventually_gt_atTop 0)
  simp only [hBx]
  exact integral_mul_eq_sum_partialMellin (F := fun t ↦ f t - A t)
    (H := fun t ↦ h (x * t) - B t) (z := fun j ↦ (j : ℂ) + α) (w := fun k ↦ 1 - ((k : ℂ) + β))
    (u := a) (v := fun k ↦ (x : ℂ) ^ (-((k : ℂ) + β)) * b k) (b := 1 - (n + α)) (r := n + β)
    (fun t ↦ by rw [hA, add_sub_cancel]) (fun t ↦ by rw [hB, add_sub_cancel])
    hf (hf.sub (locallyIntegrableOn_sum_cpow_smul _ a n))
    hhx (hhx.sub (continuousOn_sum_cpow_smul _ _ n))
    (by rw [neg_sub]; exact isBigO_sub_sum_nhdsGT hfn)
    (hh0.comp_mul_left_rpow hx (tendsto_iff_comap.mpr (comap_mulLeft_nhdsGT_zero hx).ge)
      eventually_mem_nhdsWithin) hf1 hH1
    (fun j _ ↦ by simp only [add_re, natCast_re, ofReal_re]; linarith [j.cast_nonneg (α := ℝ)])
    (fun k hk ↦ by
      simp only [sub_re, one_re, add_re, natCast_re, ofReal_re]; linarith [hlt k hk])
    (fun k _ ↦ by
      simp only [sub_re, one_re, add_re, natCast_re, ofReal_re]
      linarith [k.cast_nonneg (α := ℝ)])
    (fun j hj ↦ by simp only [add_re, natCast_re, ofReal_re]; linarith [hlt j hj])
    (by linarith) (by linarith)

/-- **Absolute convergence of the regularization remainder.** Under the hypotheses of
`TauCeti.integral_mul_comp_mul_eq_sum_mellinCont_add_integral` (except `α ≠ β`), for every `x > 0`
the remainder integrand `f_n(t) h_n(xt)` is integrable on `(0, ∞)`, where `f_n` and `h_n` are the
remainders of the expansions of order `n` of `f` at `0+` and of `h` at `+∞`. For `n = 0` this is
the integrability of `t ↦ f(t) h(xt)`. -/
theorem integrableOn_mul_comp_mul_sub_sum
    (hf : LocallyIntegrableOn f (Ioi 0)) (hh : ContinuousOn h (Ioi 0)) {n : ℕ}
    (hfn : (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ ((n : ℂ) + α - 1))
    (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β)))
    (hh0 : h =O[𝓝[>] 0] (· ^ (-c))) (hc : c < α) (hf1 : f =O[atTop] (· ^ (-ρ)))
    (hρ : 1 < ρ + β) (hαβ : α < β + 1) (hβα : β < α + 1) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t ↦ (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) *
      (h (x * t) - ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) • b k)) (Ioi 0) :=
  (integrableOn_and_integral_eq_sum_brackets hf hh hfn hhn hh0 hc hf1 hρ hαβ hβα hx).1

/-- **Regularization of `∫₀^∞ f(t) h(xt) dt`** (DLMF 2.6.54–2.6.61). Let `f` be locally integrable
and `h` continuous on `(0, ∞)`, with expansions of order `n`:
`f_n(t) = f(t) - ∑_{j<n} a_j t^{j+α-1} = O(t^{n+α-1})` as `t → 0+` and
`h_n(t) = h(t) - ∑_{k<n} b_k t^{-k-β} = O(t^{-n-β})` as `t → +∞` (for asymptotic expansions `hfa`,
`hhb` of `f` and `h`, take `hfa.isBigO n` and `hhb.isBigO n`). Assume `h(t) = O(t^{-c})` as
`t → 0+` with `c < α`, and `f(t) = O(t^{-ρ})` as `t → +∞` with `1 < ρ + β`, where
`0 < |α - β| < 1`. Then for every `x > 0`,
`∫₀^∞ f(t) h(xt) dt = ∑_{j<n} x^{-j-α} a_j 𝓜h(j + α) + ∑_{k<n} x^{-k-β} b_k 𝓜f(1 - k - β)
  + ∫₀^∞ f_n(t) h_n(xt) dt`,
with `𝓜h`, `𝓜f` the continued Mellin transforms of `h` at `+∞` and of `f` at `0+`. The remainder
integrand `f_n(t) h_n(xt)` is integrable on `(0, ∞)` (`TauCeti.integrableOn_mul_comp_mul_sub_sum`);
its `n = 0` case gives the integrability of `t ↦ f(t) h(xt)` under the order-`0` bounds
`f(t) = O(t^{α-1})` as `t → 0+` and `h(t) = O(t^{-β})` as `t → +∞`. -/
theorem integral_mul_comp_mul_eq_sum_mellinCont_add_integral
    (hf : LocallyIntegrableOn f (Ioi 0)) (hh : ContinuousOn h (Ioi 0)) {n : ℕ}
    (hfn : (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ ((n : ℂ) + α - 1))
    (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β)))
    (hh0 : h =O[𝓝[>] 0] (· ^ (-c))) (hc : c < α) (hf1 : f =O[atTop] (· ^ (-ρ)))
    (hρ : 1 < ρ + β) (hαβ : α < β + 1) (hβα : β < α + 1) (hne : α ≠ β) {x : ℝ}
    (hx : 0 < x) :
    ∫ t in Ioi 0, f t * h (x * t) =
      ∑ j ∈ Finset.range n, (x : ℂ) ^ (-((j : ℂ) + α)) * a j *
          mellinContAtTop h b (fun k ↦ (k : ℂ) + β) n ((j : ℂ) + α) +
        ∑ k ∈ Finset.range n, (x : ℂ) ^ (-((k : ℂ) + β)) * b k *
          mellinContAtZero f a (fun j ↦ (j : ℂ) + α - 1) n (1 - ((k : ℂ) + β)) +
        ∫ t in Ioi 0, (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) *
          (h (x * t) - ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) • b k) := by
  have hlt (j : ℕ) (hj : j < n) : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  -- the brackets of `h` are rescaled continued transforms of `h`, those of `f` continued
  -- transforms of `f`, and their principal parts cancel
  rw [(integrableOn_and_integral_eq_sum_brackets hf hh hfn hhn hh0 hc hf1 hρ hαβ hβα hx).2,
    Finset.sum_congr rfl fun j hj ↦ congrArg (a j * ·)
      (integral_Ioc_add_integral_Ioi_comp_mul_left hh hhn hh0 (z := (j : ℂ) + α)
        (by simp only [add_re, natCast_re, ofReal_re]; linarith [j.cast_nonneg (α := ℝ)])
        (by simp only [add_re, natCast_re, ofReal_re]; linarith [hlt j (Finset.mem_range.mp hj)])
        (fun k _ ↦ natCast_add_ne_natCast_add hαβ hβα hne j k) hx),
    Finset.sum_congr rfl fun (k : ℕ) _ ↦ congrArg ((x : ℂ) ^ (-((k : ℂ) + β)) * b k * ·)
      (integral_Ioc_add_integral_Ioi_eq_mellinContAtZero (f := f) (a := a) k),
    sum_mul_add_sum_mul_sub_cancel]
  congr 2
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-! ### The remainder bound -/

/-- If `‖F t‖ ≤ C₁ t^p` and `‖H (x t)‖ ≤ C (x t)^{-s}`, then
`‖F t H (x t)‖ ≤ C₁ C x^{-s} t^{p-s}`. -/
private theorem norm_mul_comp_mul_le_rpow {F H : ℝ → ℂ} {C₁ C p s x t : ℝ}
    (hF : ‖F t‖ ≤ C₁ * t ^ p) (hH : ‖H (x * t)‖ ≤ C * (x * t) ^ (-s)) (hC₁ : 0 ≤ C₁)
    (hx : 0 < x) (ht : 0 < t) : ‖F t * H (x * t)‖ ≤ C₁ * C * x ^ (-s) * t ^ (p - s) := by
  calc ‖F t * H (x * t)‖ = ‖F t‖ * ‖H (x * t)‖ := norm_mul _ _
    _ ≤ (C₁ * t ^ p) * (C * (x * t) ^ (-s)) :=
      mul_le_mul hF hH (norm_nonneg _) (mul_nonneg hC₁ (Real.rpow_nonneg ht.le _))
    _ = C₁ * C * x ^ (-s) * t ^ (p - s) := by
      simp only [Real.mul_rpow hx.le ht.le, Real.rpow_sub ht, Real.rpow_neg ht.le]
      field_simp

/-- The three-piece estimate behind the remainder bound. Split `(0, ∞)` at `x⁻¹ ≤ δ` and at `δ`.
On `(0, x⁻¹]` use `‖F t‖ ≤ C₁ t^p` and the bound `‖H u‖ ≤ C₃ u^{-e}` on `(0, 1]`. On `(x⁻¹, δ]` use
`‖F t‖ ≤ C₁ t^p` and the bound `‖H u‖ ≤ C₂ u^{-r}` on `[1, ∞)`. On `(δ, ∞)` use that bound on
`H` and the integrability of `t^{-r} ‖F t‖`. -/
private theorem norm_integral_mul_comp_mul_le {F H : ℝ → ℂ} {C₁ C₂ C₃ δ e p r x : ℝ}
    (hF : LocallyIntegrableOn F (Ioi 0)) (hH : ContinuousOn H (Ioi 0))
    (hF₀ : ∀ t ∈ Ioc 0 δ, ‖F t‖ ≤ C₁ * t ^ p) (hH₀ : ∀ u ∈ Ioc 0 1, ‖H u‖ ≤ C₃ * u ^ (-e))
    (hH₁ : ∀ u ∈ Ici 1, ‖H u‖ ≤ C₂ * u ^ (-r))
    (hK : IntegrableOn (fun t ↦ t ^ (-r) * ‖F t‖) (Ioi δ))
    (hC₁ : 0 ≤ C₁) (hpe : -1 < p - e) (hpr : p - r ≠ -1)
    (hx : 0 < x) (hxδ : x⁻¹ ≤ δ) :
    ‖∫ t in Ioi 0, F t * H (x * t)‖ ≤
      C₁ * C₃ * x ^ (-e) * ((x⁻¹) ^ (p - e + 1) / (p - e + 1)) +
        C₁ * C₂ * x ^ (-r) * ((δ ^ (p - r + 1) - (x⁻¹) ^ (p - r + 1)) / (p - r + 1)) +
        C₂ * x ^ (-r) * ∫ t in Ioi δ, t ^ (-r) * ‖F t‖ := by
  have hxi : 0 < x⁻¹ := inv_pos.mpr hx
  have hδ : 0 < δ := hxi.trans_le hxδ
  have hxt {t : ℝ} (ht : x⁻¹ ≤ t) : x * t ∈ Ici 1 := by
    simpa [hx.ne'] using mul_le_mul_of_nonneg_left ht hx.le
  have h₂ : IntegrableOn (fun t : ℝ ↦ t ^ (p - r)) (Icc x⁻¹ δ) :=
    (ContinuousOn.rpow_const (s := Icc x⁻¹ δ) continuousOn_id fun t (ht : t ∈ Icc x⁻¹ δ) ↦
      Or.inl (hxi.trans_le ht.1).ne').integrableOn_compact isCompact_Icc
  refine (norm_integral_Ioi_le_of_three_pieces hxi.le hxδ
    (hF.mul_continuousOn (hH.comp (continuousOn_const.mul continuousOn_id)
      fun t ht ↦ mul_pos hx ht) isOpen_Ioi.isLocallyClosed).aestronglyMeasurable
    ((intervalIntegral.intervalIntegrable_rpow' hpe (a := 0) (b := x⁻¹)).1.const_mul
      (C₁ * C₃ * x ^ (-e)))
    (IntegrableOn.mono_set (h₂.const_mul (C₁ * C₂ * x ^ (-r))) Ioc_subset_Icc_self)
    (hK.const_mul (C₂ * x ^ (-r)))
    (fun t ht ↦ norm_mul_comp_mul_le_rpow (hF₀ t ⟨ht.1, ht.2.trans hxδ⟩)
      (hH₀ _ ⟨mul_pos hx ht.1, by simpa [hx.ne'] using mul_le_mul_of_nonneg_left ht.2 hx.le⟩)
      hC₁ hx ht.1)
    (fun t ht ↦ norm_mul_comp_mul_le_rpow (hF₀ t ⟨hxi.trans ht.1, ht.2⟩) (hH₁ _ (hxt ht.1.le))
      hC₁ hx (hxi.trans ht.1))
    (fun t ht ↦ ?_)).trans_eq ?_
  · rw [norm_mul]
    calc ‖F t‖ * ‖H (x * t)‖ ≤ ‖F t‖ * (C₂ * (x * t) ^ (-r)) :=
          mul_le_mul_of_nonneg_left (hH₁ _ (hxt (hxδ.trans ht.le))) (norm_nonneg _)
      _ = C₂ * x ^ (-r) * (t ^ (-r) * ‖F t‖) := by
          rw [Real.mul_rpow hx.le (hδ.trans ht).le]
          ring
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    ← intervalIntegral.integral_of_le hxi.le, integral_rpow (Or.inl hpe),
    Real.zero_rpow (by linarith), sub_zero, ← intervalIntegral.integral_of_le hxδ,
    integral_rpow (Or.inr ⟨hpr, notMem_uIcc_of_lt hxi hδ⟩)]

/-- The majorant of `norm_integral_mul_comp_mul_le`, as a function of `x`, is
`O(x^{-m})` whenever `m ≤ p + 1` and `m ≤ r`. -/
private theorem isBigO_majorant {A₁ A₂ A₃ δ e p r m : ℝ} (hm₁ : m ≤ p + 1) (hm₂ : m ≤ r) :
    (fun x : ℝ ↦ A₁ * x ^ (-e) * ((x⁻¹) ^ (p - e + 1) / (p - e + 1)) +
      A₂ * x ^ (-r) * ((δ ^ (p - r + 1) - (x⁻¹) ^ (p - r + 1)) / (p - r + 1)) +
      A₃ * x ^ (-r)) =O[atTop] (· ^ (-m)) := by
  have h₁ := (isBigO_refl (fun x : ℝ ↦ x ^ (-(p + 1))) atTop).atTop_rpow_of_le (neg_le_neg hm₁)
  have h₂ := (isBigO_refl (fun x : ℝ ↦ x ^ (-r)) atTop).atTop_rpow_of_le (neg_le_neg hm₂)
  have heq : (fun x : ℝ ↦ A₁ * x ^ (-e) * ((x⁻¹) ^ (p - e + 1) / (p - e + 1)) +
      A₂ * x ^ (-r) * ((δ ^ (p - r + 1) - (x⁻¹) ^ (p - r + 1)) / (p - r + 1)) +
      A₃ * x ^ (-r)) =ᶠ[atTop] fun x ↦ (A₁ / (p - e + 1) - A₂ / (p - r + 1)) * x ^ (-(p + 1)) +
        (A₂ * δ ^ (p - r + 1) / (p - r + 1) + A₃) * x ^ (-r) :=
    (eventually_gt_atTop 0).mono fun x hx ↦ by
      have hpow (a : ℝ) : x ^ (-a) * (x⁻¹) ^ (p - a + 1) = x ^ (-(p + 1)) := by
        rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
        congr 1
        ring
      linear_combination (A₁ / (p - e + 1)) * hpow e - (A₂ / (p - r + 1)) * hpow r
  exact (((h₁.const_mul_left _).add (h₂.const_mul_left _))).congr' heq.symm EventuallyEq.rfl

/-- Near `0+`, the remainder of `f` after `n` terms is bounded by `C t^{n+α-1}` on some `(0, δ]`. -/
private theorem exists_norm_sub_sum_le_rpow_Ioc_nhdsGT {n : ℕ}
    (hfn : (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ ((n : ℂ) + α - 1)) : ∃ C ≥ 0, ∃ δ > 0, ∀ t ∈ Ioc 0 δ,
      ‖f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j‖ ≤
        C * t ^ ((n : ℝ) + α - 1) := by
  obtain ⟨C, hC, hw⟩ := (isBigO_sub_sum_nhdsGT hfn).exists_nonneg
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hw.bound
  refine ⟨C, hC, ε / 2, half_pos hε, fun t ht ↦ ?_⟩
  have : ‖f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j‖ ≤
      C * ‖t ^ ((n : ℝ) + α - 1)‖ := hsub ⟨ht.1, ht.2.trans_lt (half_lt_self hε)⟩
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)] at this

/-- On `(0, 1]`, the remainder of `h` after `n` terms is bounded by `C u^{-e}` with
`e = max c (n - 1 + β)`. -/
private theorem exists_norm_sub_sum_le_rpow_Ioc (hh : ContinuousOn h (Ioi 0))
    (hh0 : h =O[𝓝[>] 0] (· ^ (-c))) (n : ℕ) : ∃ C ≥ 0, ∀ u ∈ Ioc 0 1,
      ‖h u - ∑ k ∈ Finset.range n, (u : ℂ) ^ (-((k : ℂ) + β)) • b k‖ ≤
        C * u ^ (-max c ((n : ℝ) - 1 + β)) := by
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := eventually_mem_nhdsWithin
  have hH0 : (fun u ↦ h u - ∑ k ∈ Finset.range n, (u : ℂ) ^ (-((k : ℂ) + β)) • b k)
      =O[𝓝[>] 0] (· ^ (-max c ((n : ℝ) - 1 + β))) := by
    refine (hh0.nhdsGT_zero_rpow_of_le (neg_le_neg (le_max_left _ _))).sub
      (IsBigO.fun_sum fun k hk ↦ ?_)
    have hk : (k : ℝ) + β ≤ max c ((n : ℝ) - 1 + β) := le_max_of_le_right (by
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
      linarith)
    have hbk : (fun u : ℝ ↦ (u : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[𝓝[>] 0]
        (· ^ (-((k : ℝ) + β))) := by
      simpa only [neg_re, add_re, natCast_re, ofReal_re] using
        (isBigO_smul_const_self (fun u : ℝ ↦ (u : ℂ) ^ (-((k : ℂ) + β))) (b k)
          fun r ↦ norm_smul_le r (b k)).trans (isBigO_ofReal_cpow_rpow hpos _)
    exact hbk.nhdsGT_zero_rpow_of_le (neg_le_neg hk)
  obtain ⟨C, hC, hw⟩ := (hH0.isBigO_principal_Ioc_of_continuousOn
    ((hh.sub (continuousOn_sum_cpow_smul _ b n)).mono Ioc_subset_Ioi_self)
    (continuousOn_id.rpow_const fun u (hu : u ∈ Ioc 0 1) ↦ Or.inl hu.1.ne')
    fun u (hu : u ∈ Ioc 0 1) ↦ norm_ne_zero_iff.mpr (Real.rpow_pos_of_pos hu.1 _).ne').exists_nonneg
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  have := isBigOWith_principal.mp hw u hu
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _)] at this

/-- On `[1, ∞)`, the remainder of `h` after `n` terms is bounded by `C u^{-n-β}`. -/
private theorem exists_norm_sub_sum_le_rpow_Ici (hh : ContinuousOn h (Ioi 0)) {n : ℕ}
    (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β))) : ∃ C ≥ 0, ∀ u ∈ Ici 1,
      ‖h u - ∑ k ∈ Finset.range n, (u : ℂ) ^ (-((k : ℂ) + β)) • b k‖ ≤
        C * u ^ (-((n : ℝ) + β)) := by
  obtain ⟨C, hC, hw⟩ := ((isBigO_sub_sum_atTop hhn).isBigO_principal_Ici_of_continuousOn
    ((hh.sub (continuousOn_sum_cpow_smul _ b n)).mono fun u (hu : 1 ≤ u) ↦
      zero_lt_one.trans_le hu)
    (continuousOn_id.rpow_const fun u (hu : 1 ≤ u) ↦ Or.inl (zero_lt_one.trans_le hu).ne')
    fun u (hu : 1 ≤ u) ↦ norm_ne_zero_iff.mpr
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hu) _).ne').exists_nonneg
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  have := isBigOWith_principal.mp hw u hu
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hu) _)] at this

/-- On `(δ, ∞)`, `t^{-n-β}` times the remainder of `f` after `n` terms is integrable. -/
private theorem integrableOn_rpow_mul_norm_sub_sum (hf : LocallyIntegrableOn f (Ioi 0))
    (hf1 : f =O[atTop] (· ^ (-ρ))) (hρ : 1 < ρ + β) (hαβ : α < β + 1) (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : IntegrableOn (fun t ↦ t ^ (-((n : ℝ) + β)) *
      ‖f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j‖) (Ioi δ) := by
  set F : ℝ → ℂ := fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j with hF
  -- on `(1, ∞)`, both `f` and each term of the subtracted sum have convergent Mellin integrals
  have h₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (1 - ((n : ℂ) + β) - 1) • F t) (Ioi 1) := by
    simp only [hF, smul_sub, Finset.smul_sum]
    refine (integrableOn_Ioi_cpow_smul_of_isBigO hf hf1 (by
      simp only [sub_re, one_re, add_re, natCast_re, ofReal_re]
      linarith [n.cast_nonneg (α := ℝ)])).sub
      (integrable_finsetSum _ fun j hj ↦ ?_)
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hj
    refine integrableOn_Ioi_cpow_smul_of_isBigO (a := 1 - (j + α))
      (g := fun t : ℝ ↦ (t : ℂ) ^ ((j : ℂ) + α - 1) • a j)
      (locallyIntegrableOn_cpow_smul (locallyIntegrableOn_const (a j)) _)
      (by simpa only [sub_re, add_re, natCast_re, ofReal_re, one_re, neg_sub] using
        (isBigO_smul_const_self (fun u : ℝ ↦ (u : ℂ) ^ ((j : ℂ) + α - 1)) (a j)
          fun r ↦ norm_smul_le r (a j)).trans (isBigO_ofReal_cpow_rpow (eventually_gt_atTop 0) _))
      (by simp only [sub_re, one_re, add_re, natCast_re, ofReal_re]; linarith)
  have h₀ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (1 - ((n : ℂ) + β) - 1) • F t) (Icc δ 1) :=
    (locallyIntegrableOn_cpow_smul (hf.sub (locallyIntegrableOn_sum_cpow_smul _ a n)) _)
      |>.integrableOn_compact_subset (fun t ht ↦ hδ.trans_le ht.1) isCompact_Icc
  have h₂ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (1 - ((n : ℂ) + β) - 1) • F t) (Ioi δ) :=
    (h₀.union h₁).mono_set fun t (ht : δ < t) ↦ by
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨le_of_lt ht, ht1⟩
      · exact Or.inr (not_le.mp ht1)
  refine IntegrableOn.congr_fun h₂.norm (fun t ht ↦ ?_) measurableSet_Ioi
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos (hδ.trans ht), sub_sub_cancel_left, neg_re, add_re,
    natCast_re, ofReal_re]

/-- **The remainder of the regularization is small** (DLMF 2.6.62). Under the hypotheses of
`TauCeti.integral_mul_comp_mul_eq_sum_mellinCont_add_integral`, the remainder integral
`∫₀^∞ f_n(t) h_n(xt) dt` is `O(x^{-n-min(α, β)})` as `x → +∞`, where `f_n` and `h_n` are the
remainders of the expansions of order `n` of `f` at `0+` and of `h` at `+∞`. -/
theorem isBigO_integral_mul_comp_mul_sub_sum
    (hf : LocallyIntegrableOn f (Ioi 0)) (hh : ContinuousOn h (Ioi 0)) {n : ℕ}
    (hfn : (fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) =O[𝓝[>] 0]
      fun t ↦ (t : ℂ) ^ ((n : ℂ) + α - 1))
    (hhn : (fun t ↦ h t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + β)) • b k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + β)))
    (hh0 : h =O[𝓝[>] 0] (· ^ (-c))) (hc : c < α) (hf1 : f =O[atTop] (· ^ (-ρ)))
    (hρ : 1 < ρ + β) (hαβ : α < β + 1) (hβα : β < α + 1) (hne : α ≠ β) :
    (fun x : ℝ ↦ ∫ t in Ioi 0, (f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j) *
      (h (x * t) - ∑ k ∈ Finset.range n, ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) • b k))
      =O[atTop] (· ^ (-(n + min α β))) := by
  set F : ℝ → ℂ := fun t ↦ f t - ∑ j ∈ Finset.range n, (t : ℂ) ^ ((j : ℂ) + α - 1) • a j
  set H : ℝ → ℂ := fun u ↦ h u - ∑ k ∈ Finset.range n, (u : ℂ) ^ (-((k : ℂ) + β)) • b k
  set e := max c ((n : ℝ) - 1 + β)
  obtain ⟨C₁, hC₁, δ, hδ, hF₀⟩ := exists_norm_sub_sum_le_rpow_Ioc_nhdsGT hfn
  obtain ⟨C₃, -, hH₀⟩ := exists_norm_sub_sum_le_rpow_Ioc (b := b) (β := β) hh hh0 n
  obtain ⟨C₂, -, hH₁⟩ := exists_norm_sub_sum_le_rpow_Ici hh hhn
  have hK := integrableOn_rpow_mul_norm_sub_sum (a := a) hf hf1 hρ hαβ n hδ
  have hpe : -1 < (n : ℝ) + α - 1 - e := by
    have : e < n + α := max_lt (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by linarith)
    linarith
  have hpr : (n : ℝ) + α - 1 - (n + β) ≠ -1 := fun h ↦ hne (by linarith)
  -- the three-piece estimate for `x ≥ δ⁻¹`, and the decay of its right side
  refine IsBigO.trans ?_ (isBigO_majorant (A₁ := C₁ * C₃) (A₂ := C₁ * C₂)
    (A₃ := C₂ * ∫ t in Ioi δ, t ^ (-((n : ℝ) + β)) * ‖F t‖) (δ := δ) (e := e)
    (p := (n : ℝ) + α - 1) (r := (n : ℝ) + β) (by linarith [min_le_left α β])
    (by linarith [min_le_right α β]))
  refine IsBigO.of_bound 1 ((eventually_ge_atTop δ⁻¹).mono fun x hx ↦ ?_)
  have hx0 : 0 < x := (inv_pos.mpr hδ).trans_le hx
  refine (norm_integral_mul_comp_mul_le (F := F) (H := H)
    (hf.sub (locallyIntegrableOn_sum_cpow_smul _ a n))
    (hh.sub (continuousOn_sum_cpow_smul _ b n)) hF₀ hH₀ hH₁ hK hC₁ hpe hpr hx0
    (inv_le_of_inv_le₀ hδ hx)).trans ?_
  rw [one_mul]
  exact le_of_eq_of_le (by ring) (Real.le_norm_self _)

end TauCeti
