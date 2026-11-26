/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.MeanInequalities
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Reverse square function inequalities by duality

Let `Bᵢ` be bounded operators on `L²(μ, F)` and let `S f = (∑ᵢ ‖Bᵢ f‖²)^{1/2}` be their square
function. Suppose that every `Bᵢ f` only sees the operators `Bₖ` with `k` in a finite window
`W i`, in the sense that `⟪Bᵢ f, g⟫ = ∑_{k ∈ W i} ⟪Bᵢ f, Bₖ g⟫`, that the windows have bounded
overlap, and that partial sums `∑_{i ∈ t N} Bᵢ f` tend to `f`. Then a square function inequality
`‖S g‖_q ≤ C ‖g‖_q` at an exponent `q` gives the reverse inequality `‖f‖_p ≤ L C ‖S f‖_p` at
the conjugate exponent `p`, where `L` bounds the window sizes and overlaps
(`TauCeti.eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow`).

The proof pairs `f` with test functions `g`: the window identity and Cauchy–Schwarz for the banded
double sum bound `|⟪∑_{i ∈ t N} Bᵢ f, g⟫|` by `L ∫ S f · S g`
(`TauCeti.enorm_inner_sum_le_mul_lintegral_tsum_enorm_sq_rpow`), and Hölder's inequality and the
square function inequality for `g` bound this by `L C ‖S f‖_p ‖g‖_q`.

This is the duality step of the Littlewood–Paley theorem, used both for Fourier multipliers on
`ℝᵈ` and for the periodic blocks on the torus.

## Main results

* `TauCeti.enorm_inner_sum_le_mul_lintegral_tsum_enorm_sq_rpow`: the pairing bound.
* `TauCeti.eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow`: the reverse square function inequality.

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 6.1 (the reverse Littlewood–Paley inequality by duality).
-/

public section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {α ι F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The pairing bound.** Let `Bᵢ` be bounded operators on `L²(μ, F)` and let `W i` be finite
windows, each with at most `L` elements, such that every index lies in at most `L` of them and
`⟪Bᵢ f, g⟫ = ∑_{k ∈ W i} ⟪Bᵢ f, Bₖ g⟫`. Then for every finite set `t` of indices,
`|⟪∑_{i ∈ t} Bᵢ f, g⟫| ≤ L ∫ S f · S g`, where `S f = (∑ᵢ ‖Bᵢ f‖²)^{1/2}`. -/
theorem enorm_inner_sum_le_mul_lintegral_tsum_enorm_sq_rpow [DecidableEq ι]
    (B : ι → Lp F 2 μ →L[ℂ] Lp F 2 μ) (W : ι → Finset ι) {L : ℕ} (hWL : ∀ i, (W i).card ≤ L)
    (hWL' : ∀ (s : Finset ι) (k : ι), (s.filter (k ∈ W ·)).card ≤ L)
    (hW : ∀ i f g, ⟪B i f, g⟫_ℂ = ∑ k ∈ W i, ⟪B i f, B k g⟫_ℂ) (t : Finset ι)
    (f g : Lp F 2 μ) :
    ‖⟪∑ i ∈ t, B i f, g⟫_ℂ‖ₑ ≤
      L * ∫⁻ x, (∑' i, ‖B i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, ‖B k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) ∂μ := by
  have hmeas : ∀ i k, AEMeasurable (fun x ↦ ‖B i f x‖ₑ * ‖B k g x‖ₑ) μ :=
    fun i k ↦ (Lp.aestronglyMeasurable _).eNorm.mul (Lp.aestronglyMeasurable _).eNorm
  calc ‖⟪∑ i ∈ t, B i f, g⟫_ℂ‖ₑ
      = ‖∑ i ∈ t, ∑ k ∈ W i, ∫ x, ⟪B i f x, B k g x⟫_ℂ ∂μ‖ₑ := by
        rw [sum_inner]
        refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
        rw [hW]
        simp only [L2.inner_def]
    _ ≤ ∑ i ∈ t, ∑ k ∈ W i, ∫⁻ x, ‖B i f x‖ₑ * ‖B k g x‖ₑ ∂μ :=
        (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (eNorm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ (eNorm_integral_le_lintegral_eNorm _).trans
            (lintegral_mono fun x ↦ eNorm_inner_le_eNorm _ _)))
    _ = ∫⁻ x, ∑ i ∈ t, ∑ k ∈ W i, ‖B i f x‖ₑ * ‖B k g x‖ₑ ∂μ := by
        rw [lintegral_finsetSum' _ fun i _ ↦ Finset.aemeasurable_fun_sum _ fun k _ ↦ hmeas i k]
        exact Finset.sum_congr rfl fun i _ ↦
          (lintegral_finsetSum' _ fun k _ ↦ hmeas i k).symm
    _ ≤ ∫⁻ x, L * ((∑' i, ‖B i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖B k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) ∂μ :=
        lintegral_mono fun x ↦ (_root_.sum_le_tsum _).trans
          (ENNReal.tsum_sum_mul_le_of_card_le W hWL hWL' _ _)
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

/-- **The reverse square function inequality by duality.** On a σ-finite measure space, let `Bᵢ`
be countably many bounded operators on `L²(μ, F)` with square function
`S f = (∑ᵢ ‖Bᵢ f‖²)^{1/2}`, and let `W i` be finite windows, each with at most `L` elements, such
that every index lies in at most `L` of them and `⟪Bᵢ f, g⟫ = ∑_{k ∈ W i} ⟪Bᵢ f, Bₖ g⟫`. Let `p`
and `q` be Hölder conjugate. If `‖S g‖_q ≤ C ‖g‖_q` for every `g ∈ L²` and the partial sums
`∑_{i ∈ t N} Bᵢ f` tend to `f`, then

`‖f‖_p ≤ L C ‖S f‖_p`.

Neither side is assumed finite. -/
theorem eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow [DecidableEq ι] [Countable ι] [SigmaFinite μ]
    (B : ι → Lp F 2 μ →L[ℂ] Lp F 2 μ) (W : ι → Finset ι) {L : ℕ} (hWL : ∀ i, (W i).card ≤ L)
    (hWL' : ∀ (s : Finset ι) (k : ι), (s.filter (k ∈ W ·)).card ≤ L)
    (hW : ∀ i f g, ⟪B i f, g⟫_ℂ = ∑ k ∈ W i, ⟪B i f, B k g⟫_ℂ) {p q : ℝ≥0∞}
    [p.HolderConjugate q] {C : ℝ≥0∞}
    (hC : ∀ g : Lp F 2 μ,
      eLpNorm (fun x ↦ (∑' i, ‖B i g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) q μ ≤ C * eLpNorm g q μ)
    {f : Lp F 2 μ} (t : ℕ → Finset ι)
    (ht : Tendsto (fun N ↦ ∑ i ∈ t N, B i f) atTop (𝓝 f)) :
    eLpNorm f p μ ≤ L * C * eLpNorm (fun x ↦ (∑' i, ‖B i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p μ := by
  set S : Lp F 2 μ → α → ℝ≥0∞ := fun f x ↦ (∑' i, ‖B i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hS : ∀ f, AEMeasurable (S f) μ := fun f ↦
    (AEMeasurable.tsum fun i ↦ (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  -- By duality, it suffices to bound the pairing of `f` with a bounded `g` of finite-measure
  -- support, which is an element `G` of `L²`.
  refine (Lp.aestronglyMeasurable f).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ)
    (q' := q) fun g s hs hgs hg ↦ ?_
  have hg2 : MemLp g 2 μ := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  set G := hg2.toLp g
  have hGg : (G : α → F) =ᵐ[μ] g := hg2.coeFn_toLp
  have hpair : ∫ x, ⟪f x, g x⟫_ℂ ∂μ = ⟪f, G⟫_ℂ := by
    rw [L2.inner_def]
    exact integral_congr_ae (hGg.mono fun x hx ↦ by simp only [hx])
  -- Hölder's inequality and the square function inequality at the exponent `q` for `G`.
  have hHolder : ∫⁻ x, S f x * S G x ∂μ ≤ eLpNorm (S f) p μ * eLpNorm (S G) q μ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (μ := μ) (p := p) (q := q)
      (r := 1) (fun a b : ℝ≥0∞ ↦ a * b) 1 (f := S f) (g := S G)
      (fun _ _ ↦ ((hS f).mul (hS G)).aestronglyMeasurable)
      (ae_of_all _ fun x ↦ by simp) zero_lt_one
    rw [eLpNorm_one_eq_lintegral_eNorm (f := fun x ↦ S f x * S G x)
      ((hS f).mul (hS G)).aestronglyMeasurable] at h
    simpa only [eNorm_eq_self, one_mul] using h
  have hSG : eLpNorm (S G) q μ ≤ C * eLpNorm g q μ := by
    rw [← eLpNorm_congr_ae hGg]
    exact hC G
  -- The pairing is the limit of the pairings of the partial sums of `f`.
  have hlim : ‖⟪f, G⟫_ℂ‖ₑ ≤ L * ∫⁻ x, S f x * S G x ∂μ :=
    le_of_tendsto' ((continuous_eNorm.tendsto _).comp (ht.inner tendsto_const_nhds))
      fun N ↦ enorm_inner_sum_le_mul_lintegral_tsum_enorm_sq_rpow B W hWL hWL' hW (t N) f G
  rw [hpair]
  calc ‖⟪f, G⟫_ℂ‖ₑ ≤ L * ∫⁻ x, S f x * S G x ∂μ := hlim
    _ ≤ L * (eLpNorm (S f) p μ * (C * eLpNorm g q μ)) := by
        gcongr
        exact hHolder.trans (by gcongr)
    _ = L * C * eLpNorm (S f) p μ * eLpNorm g q μ := by ring

end TauCeti
