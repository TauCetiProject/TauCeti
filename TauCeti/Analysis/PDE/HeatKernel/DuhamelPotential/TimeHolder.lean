/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder estimate in time of the Hessian of the Duhamel heat potential

For a forcing term `f : ℝ → E → F` on a finite-dimensional real inner product space `E`, the
Duhamel potential `w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` (`TauCeti.heatDuhamelPotential`) has
a Hessian `D² w(t, ·)` that is `α`-Hölder in space with constant `C H`
(`TauCeti.exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential`) whenever `f` is jointly
strongly measurable and essentially bounded on `(0, t) × E` and the time slices `f(s, ·)` are
`α`-Hölder with constant `H` for almost every `s`, `0 < α < 1`. This file proves the matching
estimate in time: under the same hypotheses on `(0, T) × E`, for every `x`, the map
`t ↦ D² w(t, x)` is `α/2`-Hölder on `[0, T]` with constant `C H`, where `C` depends only on `α`
and the dimension. Neither `T` nor the bound on `f` enters the
constant. Together, the two estimates say that `D² w` is parabolically `α`-Hölder.

## The argument

Write `A_u(r) = D² (K_{u-r} ⋆ f(r, ·))(x)`, so that `D² w(u, x) = ∫₀ᵘ A_u(r) dr`, and let
`0 < s < t` with `d = t - s`. Then

`D² w(t, x) - D² w(s, x) = ∫ₛᵗ A_t(r) dr + ∫₀ˢ (A_t(r) - A_s(r)) dr`.

Since `∫ D²K = 0`, the Hölder continuity of `f(r, ·)` gives `‖A_u(r)‖ = O(H (u - r)^((α - 2)/2))`,
which integrates over `[s, t]` to `O(H d^(α/2))`. In the second integral put `τ = s - r`. For
`τ ≥ d` the time increment of the heat kernel
(`TauCeti.exists_norm_iteratedFDeriv_heatKernel_convolution_sub_le`) gives
`‖A_t(r) - A_s(r)‖ = O(H d τ^((α - 4)/2)) ≤ O(H √d τ^((α - 3)/2))`, and for `τ < d` the bound
`O(H τ^((α - 2)/2))` on each term is again `O(H √d τ^((α - 3)/2))`. Splitting the integral at
`τ = d` (`TauCeti.norm_integral_le_of_ae_norm_le_rpow`, with `√d` in the role of the spatial
distance) bounds it by `O(H (√d)^α) = O(H d^(α/2))`; this step uses `α < 1`.

## Main declarations

* `TauCeti.exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential_Icc`: for `0 < α < 1`,
  `t ↦ D² w(t, x)` is `α/2`-Hölder on `[0, T]` with constant `C H` under the hypotheses above.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3 (Hölder
  continuity in time of the second derivatives of the volume potential).
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (Hölder estimates for the heat equation).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Set
open scoped Convolution NNReal Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Hölder estimate in time for the Hessian of the Duhamel potential.** For `0 < α < 1`
there is a constant `C`, depending only on `α` and the dimension, such that for every `x` the map
`t ↦ D² w(t, x)` is `α/2`-Hölder on `[0, T]` with constant `C H`, whenever `f` is jointly
measurable and essentially bounded on `(0, T) × E` and `f(s, ·)` is `α`-Hölder with constant `H`
for almost every `0 < s < T`. Neither the bound on `f` nor `T` enters the estimate. -/
theorem exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential_Icc {α : ℝ≥0} (hα₀ : 0 < α)
    (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ {f : ℝ → E → F} {M T : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) → ∀ x,
        HolderOnWith (C * H) (α / 2) (fun t => iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x)
          (Icc 0 T) := by
  have hα₀' : (0 : ℝ) < α := hα₀
  have hα₁' : (α : ℝ) < 1 := hα₁
  have h1α : 0 < 1 - (α : ℝ) := by linarith
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) 2 α.coe_nonneg
  obtain ⟨C₄, hC₄0, hC₄⟩ :=
    exists_norm_iteratedFDeriv_heatKernel_convolution_sub_le (E := E) (F := F) two_ne_zero α
  set K : ℝ := 2 / α * C₂ + 2 / α * (2 * C₂) + 2 / (1 - α) * (C₄ + 2 * C₂) with hK_def
  refine ⟨K.toNNReal, fun {f M T H} hf hfM hH x => ?_⟩
  -- The time integrand `A_u(r) = D² (K_{u-r} ⋆ f(r, ·))(x)` and its slice bound.
  set A : ℝ → ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F :=
    fun u r => iteratedFDeriv ℝ 2 (heatKernel (u - r) ⋆ f r) x with hA_def
  have hmeas : ∀ r, AEStronglyMeasurable (f r) := fun r =>
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  have hslice : ∀ᵐ r, r ∈ Ioo 0 T → (∀ᵐ y, ‖f r y‖ ≤ M) ∧ HolderWith H α (f r) :=
    (ae_restrict_iff' measurableSet_Ioo).1 (hfM.and hH)
  have hAle : ∀ r, (∀ᵐ y, ‖f r y‖ ≤ M) → HolderWith H α (f r) → ∀ u, r < u →
      ‖A u r‖ ≤ C₂ * H * (u - r) ^ (((α : ℝ) - 2) / 2) := by
    intro r hrM hrH u hru
    have hur : 0 < u - r := sub_pos.2 hru
    refine (norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith hur (hmeas r) hrM hrH
      two_ne_zero x).trans ?_
    have := mul_le_mul_of_nonneg_left (hC₂ (u - r) hur) H.coe_nonneg
    rw [Nat.cast_ofNat] at this
    exact this.trans_eq (by ring)
  -- The representation `D² w(u, x) = ∫₀ᵘ A_u` and integrability, for `0 < u ≤ T`.
  have hres : ∀ u ≤ T, (∀ᵐ s ∂volume.restrict (Ioo 0 u), ∀ᵐ y, ‖f s y‖ ≤ M) ∧
      ∀ᵐ s ∂volume.restrict (Ioo 0 u), HolderWith H α (f s) := fun u hu =>
    ⟨ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hu) hfM,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hu) hH⟩
  have hrep : ∀ u, 0 < u → u ≤ T →
      iteratedFDeriv ℝ 2 (heatDuhamelPotential f u) x = ∫ r in 0..u, A u r := fun u hu huT =>
    congrFun (iteratedFDeriv_heatDuhamelPotential_of_holderWith hf (hres u huT).1
      (hres u huT).2 hα₀ hu le_rfl) x
  have hint : ∀ u, 0 < u → u ≤ T → IntervalIntegrable (A u) volume 0 u := fun u hu huT =>
    intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith hf (hres u huT).1
      (hres u huT).2 hα₀ hu le_rfl x
  -- Near the diagonal, `∫ₐᵘ A_u` is `O(H (u - a)^(α/2))`.
  have hnear : ∀ a u, 0 ≤ a → a ≤ u → u ≤ T →
      ‖∫ r in a..u, A u r‖ ≤ 2 / α * (C₂ * H) * (u - a) ^ ((α : ℝ) / 2) := by
    intro a u ha hau huT
    refine norm_integral_le_of_ae_norm_le_sub_rpow hα₀' hau ?_
    filter_upwards [hslice, Measure.ae_ne volume u] with r hr hru hrI
    have hlt : r < u := lt_of_le_of_ne hrI.2 hru
    obtain ⟨hrM, hrH⟩ := hr ⟨ha.trans_lt hrI.1, hlt.trans_le huT⟩
    exact (hAle r hrM hrH u hlt).trans_eq (by ring)
  -- The increment bound for `0 ≤ s ≤ t ≤ T`.
  have hdiff : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      ‖iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x -
          iteratedFDeriv ℝ 2 (heatDuhamelPotential f s) x‖ ≤
        K * H * (t - s) ^ ((α : ℝ) / 2) := by
    intro s t hs hst htT
    rcases hst.eq_or_lt with rfl | hst
    · simp [zero_rpow (by positivity : (α : ℝ) / 2 ≠ 0)]
    have ht : 0 < t := hs.trans_lt hst
    rw [hrep t ht htT]
    rcases hs.eq_or_lt with rfl | hs
    · -- For `s = 0` the potential vanishes and only the near-diagonal term remains.
      have h0 : iteratedFDeriv ℝ 2 (heatDuhamelPotential f 0) x = 0 := by simp
      rw [h0, sub_zero]
      refine (hnear 0 t le_rfl ht.le htT).trans ?_
      rw [show 2 / (α : ℝ) * (C₂ * H) = 2 / α * C₂ * H by ring]
      gcongr
      rw [hK_def]
      have : 0 ≤ 2 / (α : ℝ) * (2 * C₂) + 2 / (1 - α) * (C₄ + 2 * C₂) := by positivity
      linarith
    have hsT : s ≤ T := hst.le.trans htT
    have hsmem : s ∈ [[0, t]] := mem_uIcc_of_le hs.le hst.le
    have hAts : IntervalIntegrable (A t) volume 0 s :=
      (hint t ht htT).mono_set (uIcc_subset_uIcc left_mem_uIcc hsmem)
    rw [hrep s hs hsT, ← intervalIntegral.integral_add_adjacent_intervals hAts
      ((hint t ht htT).mono_set (uIcc_subset_uIcc hsmem right_mem_uIcc)), add_sub_right_comm,
      ← intervalIntegral.integral_sub hAts (hint s hs hsT)]
    set d := t - s with hd_def
    have hd : 0 < d := sub_pos.2 hst
    -- Pointwise bounds on `A_t(r) - A_s(r)` for almost every `0 < r < s`.
    have hpt : ∀ᵐ r, r ∈ Ioc 0 s → ‖A t r - A s r‖ ≤ 2 * C₂ * H * (s - r) ^ (((α : ℝ) - 2) / 2) ∧
        ‖A t r - A s r‖ ≤ (C₄ + 2 * C₂) * H * (s - r) ^ (((α : ℝ) - 3) / 2) * √d := by
      filter_upwards [hslice, Measure.ae_ne volume s] with r hr hrs hrI
      have hlt : r < s := lt_of_le_of_ne hrI.2 hrs
      have hτ : 0 < s - r := sub_pos.2 hlt
      obtain ⟨hrM, hrH⟩ := hr ⟨hrI.1, hlt.trans (hst.trans_le htT)⟩
      have hA : ‖A t r - A s r‖ ≤ 2 * C₂ * H * (s - r) ^ (((α : ℝ) - 2) / 2) := by
        have hmono : (t - r) ^ (((α : ℝ) - 2) / 2) ≤ (s - r) ^ (((α : ℝ) - 2) / 2) :=
          rpow_le_rpow_of_nonpos hτ (by linarith) (by linarith)
        have h₁ := hAle r hrM hrH t (hlt.trans hst)
        have h₂ := hAle r hrM hrH s hlt
        have hCH : 0 ≤ C₂ * H := by positivity
        calc ‖A t r - A s r‖ ≤ ‖A t r‖ + ‖A s r‖ := norm_sub_le _ _
          _ ≤ C₂ * H * (s - r) ^ (((α : ℝ) - 2) / 2) +
                C₂ * H * (s - r) ^ (((α : ℝ) - 2) / 2) :=
              add_le_add (h₁.trans (mul_le_mul_of_nonneg_left hmono hCH)) h₂
          _ = _ := by ring
      refine ⟨hA, ?_⟩
      have hsq : 0 ≤ √d * (s - r) ^ (((α : ℝ) - 3) / 2) := by positivity
      rcases le_or_gt d (s - r) with hdτ | hτd
      · -- Away from the diagonal: the time increment of the heat kernel.
        have h := hC₄ (hmeas r) hrM hrH (t := s - r) (t' := t - r) hτ (by linarith) (by linarith) x
        rw [show t - r - (s - r) = d by ring, Nat.cast_ofNat] at h
        calc ‖A t r - A s r‖ ≤ C₄ * H * (d * (s - r) ^ (((α : ℝ) - 2 - 2) / 2)) :=
              h.trans_eq (by ring)
          _ ≤ C₄ * H * (√d * (s - r) ^ (((α : ℝ) - 3) / 2)) :=
              mul_le_mul_of_nonneg_left (by
                rw [show ((α : ℝ) - 2 - 2) / 2 = ((α : ℝ) - 3) / 2 - 1 / 2 by ring]
                exact mul_rpow_sub_half_le_sqrt_mul_rpow hτ hd.le hdτ _) (by positivity)
          _ ≤ (C₄ + 2 * C₂) * H * (s - r) ^ (((α : ℝ) - 3) / 2) * √d := by
              have : 0 ≤ 2 * C₂ * H * (√d * (s - r) ^ (((α : ℝ) - 3) / 2)) := by positivity
              nlinarith
      · -- Near the diagonal: the bound on each term.
        calc ‖A t r - A s r‖ ≤ 2 * C₂ * H * (s - r) ^ (((α : ℝ) - 2) / 2) := hA
          _ ≤ 2 * C₂ * H * (√d * (s - r) ^ (((α : ℝ) - 3) / 2)) :=
              mul_le_mul_of_nonneg_left (by
                rw [show ((α : ℝ) - 2) / 2 = ((α : ℝ) - 3) / 2 + 1 / 2 by ring]
                exact rpow_add_half_le_sqrt_mul_rpow hτ hτd.le _) (by positivity)
          _ ≤ (C₄ + 2 * C₂) * H * (s - r) ^ (((α : ℝ) - 3) / 2) * √d := by
              have : 0 ≤ C₄ * H * (√d * (s - r) ^ (((α : ℝ) - 3) / 2)) := by positivity
              nlinarith
    have hfar := norm_integral_le_of_ae_norm_le_rpow (Φ := fun r => A t r - A s r) hα₀' hα₁' hs
      (sqrt_pos.2 hd) (by positivity) (by positivity) (hAts.sub (hint s hs hsT))
      (hpt.mono fun r hr hrI => (hr hrI).1) (hpt.mono fun r hr hrI => (hr hrI).2)
    have hδ : √d ^ (α : ℝ) = d ^ ((α : ℝ) / 2) := by
      rw [sqrt_eq_rpow, ← rpow_mul hd.le]
      ring_nf
    calc ‖(∫ r in 0..s, A t r - A s r) + ∫ r in s..t, A t r‖
        ≤ ‖∫ r in 0..s, A t r - A s r‖ + ‖∫ r in s..t, A t r‖ := norm_add_le _ _
      _ ≤ (2 / α * (2 * C₂ * H) + 2 / (1 - α) * ((C₄ + 2 * C₂) * H)) * √d ^ (α : ℝ) +
            2 / α * (C₂ * H) * (t - s) ^ ((α : ℝ) / 2) :=
          add_le_add hfar (hnear s t hs.le hst.le htT)
      _ = K * H * d ^ ((α : ℝ) / 2) := by
          rw [hδ, hK_def]
          ring
  refine HolderOnWith.of_dist_le fun t ht s hs => ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by rw [hK_def]; positivity), NNReal.coe_div,
    NNReal.coe_ofNat]
  rcases le_total s t with hst | hts
  · rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hst)]
    exact hdiff s t hs.1 hst ht.2
  · rw [dist_comm, dist_eq_norm, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hts)]
    exact hdiff t s ht.1 hts hs.2

end TauCeti
