/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.MeanInequalities
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# The reverse square function inequality by duality

Let `(α, μ)` be a σ-finite measure space, `F` a complex Hilbert space and `Mᵢ`, `i ∈ ι`, a
countable family of self-adjoint bounded operators on `L²(α, F)` with **square function**
`S f = (∑ᵢ ‖Mᵢ f‖²)^{1/2}`. Suppose the operators are almost orthogonal: there are windows
`W i ∋ i` with `∑_{k ∈ W i} Mₖ Mᵢ = Mᵢ`, each window has at most `L` elements and each index lies
in at most `L` windows. Then for a finite set `t` of indices

`|⟪∑_{i ∈ t} Mᵢ f, g⟫| ≤ L ∫ S f · S g`

(`TauCeti.enorm_inner_sum_apply_le_of_card_le`). If moreover `‖S g‖_q ≤ C ‖g‖_q` for the conjugate
exponent `q` of `p`, and the partial sums `∑_{i ∈ t N} Mᵢ f` converge to `f` in `L²`, then
Hölder's inequality and duality give the **reverse square function inequality**

`‖f‖_p ≤ L C ‖S f‖_p`

(`TauCeti.eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow_of_card_le`), without assuming either side
finite. This is the argument deriving the lower Littlewood–Paley bound from the upper one, on `ℝᵈ`
and on the torus.

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Theorem 6.1.2.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {α ι F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [CompleteSpace F] [DecidableEq ι]

/-- **The pairing bound for almost orthogonal operators.** Let `Mᵢ` be self-adjoint operators on
`L²` with `∑_{k ∈ W i} Mₖ Mᵢ = Mᵢ`, where every window `W i` has at most `L` elements and every
index lies in at most `L` windows. Then `|⟪∑_{i ∈ t} Mᵢ f, g⟫| ≤ L ∫ S f · S g` for every finite
set `t` of indices, where `S f = (∑ᵢ ‖Mᵢ f‖²)^{1/2}`. -/
theorem enorm_inner_sum_apply_le_of_card_le (M : ι → Lp F 2 μ →L[ℂ] Lp F 2 μ)
    (hM : ∀ i, IsSelfAdjoint (M i)) (W : ι → Finset ι) {L : ℕ} (hWL : ∀ i, (W i).card ≤ L)
    (hWL' : ∀ (s : Finset ι) (k : ι), (s.filter (k ∈ W ·)).card ≤ L)
    (hW : ∀ i f, ∑ k ∈ W i, M k (M i f) = M i f) (t : Finset ι) (f g : Lp F 2 μ) :
    ‖⟪∑ i ∈ t, M i f, g⟫_ℂ‖ₑ ≤
      L * ∫⁻ x, (∑' i, ‖M i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, ‖M k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) ∂μ := by
  have hmeas : ∀ i k, AEMeasurable (fun x ↦ ‖M i f x‖ₑ * ‖M k g x‖ₑ) μ :=
    fun i k ↦ (Lp.aestronglyMeasurable _).eNorm.mul (Lp.aestronglyMeasurable _).eNorm
  -- The block `Mᵢ f` only sees the blocks `Mₖ g` with `k ∈ W i`.
  have hpair (i : ι) : ⟪M i f, g⟫_ℂ = ∑ k ∈ W i, ⟪M i f, M k g⟫_ℂ := by
    conv_lhs => rw [← hW i f]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun k _ ↦ (hM k).isSymmetric _ _
  calc ‖⟪∑ i ∈ t, M i f, g⟫_ℂ‖ₑ
      = ‖∑ i ∈ t, ∑ k ∈ W i, ∫ x, ⟪M i f x, M k g x⟫_ℂ ∂μ‖ₑ := by
        simp only [sum_inner, hpair, L2.inner_def]
    _ ≤ ∑ i ∈ t, ∑ k ∈ W i, ∫⁻ x, ‖M i f x‖ₑ * ‖M k g x‖ₑ ∂μ :=
        (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (eNorm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ (eNorm_integral_le_lintegral_eNorm _).trans
            (lintegral_mono fun x ↦ eNorm_inner_le_eNorm _ _)))
    _ = ∫⁻ x, ∑ i ∈ t, ∑ k ∈ W i, ‖M i f x‖ₑ * ‖M k g x‖ₑ ∂μ := by
        rw [lintegral_finsetSum' _ fun i _ ↦ Finset.aemeasurable_fun_sum _ fun k _ ↦ hmeas i k]
        exact Finset.sum_congr rfl fun i _ ↦
          (lintegral_finsetSum' _ fun k _ ↦ hmeas i k).symm
    _ ≤ ∫⁻ x, L * ((∑' i, ‖M i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖M k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) ∂μ :=
        lintegral_mono fun x ↦ (_root_.sum_le_tsum _).trans
          (ENNReal.tsum_sum_mul_le_of_card_le W hWL hWL' _ _)
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

/-- **The reverse square function inequality by duality.** Let `Mᵢ` be a countable family of
self-adjoint operators on `L²` with `∑_{k ∈ W i} Mₖ Mᵢ = Mᵢ`, where every window `W i` has at most
`L` elements and every index lies in at most `L` windows, and let `p` and `q` be conjugate
exponents. If the square function `S g = (∑ᵢ ‖Mᵢ g‖²)^{1/2}` satisfies `‖S g‖_q ≤ C ‖g‖_q` for
every `g ∈ L²`, and the partial sums `∑_{i ∈ t N} Mᵢ f` converge to `f` in `L²`, then

`‖f‖_p ≤ L C ‖S f‖_p`.

Neither side is assumed finite. -/
theorem eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow_of_card_le [SigmaFinite μ] [Countable ι]
    (M : ι → Lp F 2 μ →L[ℂ] Lp F 2 μ) (hM : ∀ i, IsSelfAdjoint (M i)) (W : ι → Finset ι) {L : ℕ}
    (hWL : ∀ i, (W i).card ≤ L) (hWL' : ∀ (s : Finset ι) (k : ι), (s.filter (k ∈ W ·)).card ≤ L)
    (hW : ∀ i f, ∑ k ∈ W i, M k (M i f) = M i f) {p q : ℝ≥0∞} [p.HolderConjugate q] {C : ℝ≥0}
    (hC : ∀ g : Lp F 2 μ,
      eLpNorm (fun x ↦ (∑' i, ‖M i g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) q μ ≤ C * eLpNorm g q μ)
    {f : Lp F 2 μ} {t : ℕ → Finset ι} (ht : Tendsto (fun N ↦ ∑ i ∈ t N, M i f) atTop (𝓝 f)) :
    eLpNorm f p μ ≤
      ↑((L : ℝ≥0) * C) * eLpNorm (fun x ↦ (∑' i, ‖M i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p μ := by
  set S : Lp F 2 μ → α → ℝ≥0∞ := fun f x ↦ (∑' i, ‖M i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
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
      fun N ↦ enorm_inner_sum_apply_le_of_card_le M hM W hWL hWL' hW (t N) f G
  rw [hpair]
  calc ‖⟪f, G⟫_ℂ‖ₑ ≤ L * ∫⁻ x, S f x * S G x ∂μ := hlim
    _ ≤ L * (eLpNorm (S f) p μ * (C * eLpNorm g q μ)) := by
        gcongr
        exact hHolder.trans (by gcongr)
    _ = ↑((L : ℝ≥0) * C) * eLpNorm (S f) p μ * eLpNorm g q μ := by
        push_cast
        ring

end TauCeti
