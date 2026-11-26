/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Fredholm
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Family
import TauCeti.MeasureTheory.Function.Lp.PathTruncation
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The trajectory operator of a path of invertible operators has index zero

Let `ι : D →L[ℝ] H` be a compact embedding of a Banach space into a real Hilbert space, and let
`A : ℝ → (D →L[ℝ] H)` be a continuous path of `ι`-symmetric operators
(`⟪A s x, ι y⟫ = ⟪ι x, A s y⟫`) with invertible limits `B₋` and `B₊` at `-∞` and `∞`, differing
from `B₊` on every bounded interval by operators bounded through `ι`. Then
`D_A u = (ι ∘ u)' + A u` is Fredholm
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`). This file shows that if
moreover every `A s` is invertible, then `D_A` has index zero
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`).

Such a path has no spectral flow (`TauCeti.domainSpectralFlow_eq_zero_of_forall_isInvertible`),
so in this case the index of `D_A` is the spectral flow of `A` over every interval
(`index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_forall_isInvertible`).
This is the case without crossings of the formula identifying the index of `∂ₛ + A(s)` with the
spectral flow of `A`, whose finite-dimensional form is
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finsum_sigPos_sub_sigNeg_crossingForm`.

The index of `D_A` depends only on the limits `B±`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`), but that alone does not
compute it. Instead we move the limit at `∞` back along the path itself. For `t ∈ ℝ`, the
truncated path `s ↦ A (min s t)` runs from `B₋` to the invertible operator `A t`, so its
operator `D_t` is Fredholm. The truncations depend continuously on `t` in `L∞`, so the index of
`D_t` does not depend on `t`. As `t → -∞` the truncations converge in `L∞` to the constant `B₋`,
whose operator is invertible, so `D_t` is invertible for `t` far to the left. As `t → ∞` they
converge in `L∞` to `A`, so `D_t` has the index of `D_A` for `t` far to the right.

Combined with the catenation law
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_add`), the limit at `∞` of a
family can be moved along any path of invertible operators without changing the index
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_forall_isInvertible`): the
index can change only when the limits pass through noninvertible operators.

## Main results

* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`:
  the operator of a path of invertible operators has index zero.
* `index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_forall_isInvertible`: for such a
  path, the index is the spectral flow of `A`.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_forall_isInvertible`: moving
  the limit at `∞` along a path of invertible operators does not change the index.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §4 (the index of `d/ds + A(s)` is the spectral flow of `A`).
-/

public section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ι : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H}

/-! ### Truncations of a path -/

/-- For a continuous path, a bound through `ι` that holds for almost every time of a bounded
interval holds for the truncation `s ↦ A (min s t)` at every time, with `A t` in place of the
reference operator. -/
private theorem truncation_sub_bound (hA : Continuous A) {B : D →L[ℝ] H}
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖) (t T : ℝ) :
    ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A (min s t) - A t) x‖ ≤ c * ‖ι x‖ := by
  set R := |T| + |t| + 1
  obtain ⟨c, hcR⟩ := hc R
  -- The almost-everywhere bound holds everywhere on `(-R, R)`, by continuity.
  have hall (u : ℝ) (hu : u ∈ Ioo (-R) R) (x : D) : ‖(A u - B) x‖ ≤ c * ‖ι x‖ :=
    ContinuousOn.le_of_ae_le (μ := volume) isOpen_Ioo
      ((hA.sub continuous_const).clm_apply continuous_const).norm.continuousOn continuousOn_const
      ((ae_restrict_iff' measurableSet_Ioo).2 (hcR.mono fun _ hu huR ↦ hu huR x)) u hu
  refine ⟨c + c, Eventually.of_forall fun s hs x ↦ ?_⟩
  have hT := le_abs_self T
  have ht := neg_abs_le t
  have ht' := le_abs_self t
  have hT₀ := abs_nonneg T
  have hmin : min s t ∈ Ioo (-R) R :=
    ⟨lt_min (by linarith [hs.1]) (by linarith), (min_le_right s t).trans_lt (by linarith)⟩
  calc ‖(A (min s t) - A t) x‖ = ‖(A (min s t) - B) x - (A t - B) x‖ := by
        simp only [sub_apply, sub_sub_sub_cancel_right]
    _ ≤ ‖(A (min s t) - B) x‖ + ‖(A t - B) x‖ := norm_sub_le _ _
    _ ≤ (c + c) * ‖ι x‖ := by
        rw [add_mul]
        exact add_le_add (hall _ hmin x) (hall t ⟨by linarith, by linarith⟩ x)

/-! ### The index -/

variable [CompleteSpace D] [CompleteSpace H]

/-- **A path of invertible operators gives index zero.** Let `ι` be compact and let `A` be a
continuous path of invertible `ι`-symmetric operators with invertible limits `B₋` at `-∞` and
`B₊` at `∞`, differing from `B₊` on every bounded interval by operators bounded through `ι`. Then
the Fredholm operator `u ↦ (ι ∘ u)' + A u` has index zero. -/
theorem index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hinv : ∀ s, (A s).IsInvertible)
    {Bbot Btop : D →L[ℝ] H} (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible)
    {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = 0 := by
  have hSymmbot (x y : D) : ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ :=
    ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hbot (.of_forall (hSymm · x y))
  have hSymmtop (x y : D) : ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ :=
    ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto htop (.of_forall (hSymm · x y))
  -- The truncations `s ↦ A (min s t)` are essentially bounded, by the `L∞` norm of `A`.
  have : (μ₀).IsOpenPosMeasure := by
    rw [Opens.coe_top, Measure.restrict_univ]
    infer_instance
  have hmem (t : ℝ) : MemLp (fun s ↦ A (min s t)) ∞ μ₀ :=
    memLp_top_of_bound (hA.comp (continuous_id.min continuous_const)).aestronglyMeasurable ‖AL‖
      (Eventually.of_forall fun s ↦
        Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hAL hA.continuousAt)
  set AT : ℝ → Lp (D →L[ℝ] H) ∞ μ₀ := fun t ↦ (hmem t).toLp _
  have hAT (t : ℝ) : AT t =ᵐ[μ₀] fun s ↦ A (min s t) := (hmem t).coeFn_toLp
  -- Each truncation runs from `Bbot` to the invertible `A t`, so its operator is Fredholm.
  have hF (t : ℝ) : (familyDomainTrajectoryOperator (p := 2) ι (AT t)).IsFredholm :=
    isFredholm_familyDomainTrajectoryOperator hι hSymmbot hBbot (hSymm t) (hinv t) (hAT t)
      (hbot.congr' ((eventually_le_atBot t).mono fun s hs ↦ by simp [min_eq_left hs]))
      (tendsto_const_nhds.congr' ((eventually_ge_atTop t).mono fun s hs ↦ by
        simp [min_eq_right hs]))
      (truncation_sub_bound hA hc t)
  have hcont := (continuous_familyDomainTrajectoryOperator (p := 2) ι).comp
    (Lp.continuous_of_forall_ae_eq_apply_min hA hAT)
  -- Far to the left the truncation is close to `Bbot`, so its operator is invertible.
  have hM : 0 < max ‖Bbot.inverse‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t₁, ht₁⟩ := ((Lp.tendsto_atBot_of_forall_ae_eq_apply_min hbot hAT).eventually
    (Metric.ball_mem_nhds _ (inv_pos.2 hM))).exists
  have hinv₁ := isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt hSymmbot hBbot
    ((lt_inv_mul_iff₀ hM).1 (by rw [mul_one, ← dist_eq_norm]; exact Metric.mem_ball.1 ht₁))
  -- Far to the right the truncation is close to `A`, so its operator has the index of `D_A`.
  have hFA := isFredholm_familyDomainTrajectoryOperator hι hSymmbot hBbot hSymmtop hBtop hAL hbot
    htop hc
  obtain ⟨t₂, ht₂⟩ := (((continuous_familyDomainTrajectoryOperator (p := 2) ι).tendsto AL).comp
    (Lp.tendsto_atTop_of_forall_ae_eq_apply_min htop hAL hAT)).eventually
      hFA.eventually_isFredholm_and_index_eq |>.exists
  exact ht₂.2.symm.trans ((hcont.index_eq_of_preconnectedSpace hF t₂ t₁).trans
    (ContinuousLinearMap.index_eq_zero_of_bijective _ hinv₁.bijective))

/-- **The index is the spectral flow, for a path of invertible operators.** Under the hypotheses
of `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`,
the index of `u ↦ (ι ∘ u)' + A u` is the spectral flow of `A` over every interval `[a, b]`; both
vanish. -/
theorem index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_forall_isInvertible
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hinv : ∀ s, (A s).IsInvertible)
    {Bbot Btop : D →L[ℝ] H} (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible)
    {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖)
    {a b : ℝ} (hab : a ≤ b) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = domainSpectralFlow ι A a b := by
  rw [index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι hA hSymm hinv hBbot
    hBtop hAL hbot htop hc, domainSpectralFlow_eq_zero_of_forall_isInvertible hι hab
    hA.continuousOn (fun t _ ↦ hSymm t) fun t _ ↦ hinv t]

/-- **Deforming the limit at `∞` through invertible operators preserves the index.** Let `ι` be
compact, and let `A` run from `B₀` at `-∞` to `B₁` at `∞` and `A'` from `B₀` to `B₂`, each
differing from its limit at `∞` on every bounded interval by an operator bounded through `ι`, with
`B₀`, `B₁`, `B₂` invertible, `B₀` symmetric through `ι` and `B₁ - B₂` bounded through `ι`. If a
continuous path `γ` of invertible `ι`-symmetric operators runs from `B₁` at `-∞` to `B₂` at `∞`,
differing from `B₂` on every bounded interval by operators bounded through `ι`, then
`u ↦ (ι ∘ u)' + A u` and `u ↦ (ι ∘ u)' + A' u` have the same index. -/
theorem index_familyDomainTrajectoryOperator_eq_of_forall_isInvertible (hι : IsCompactOperator ι)
    {B₀ B₁ B₂ : D →L[ℝ] H} (hSymm₀ : ∀ x y : D, ⟪B₀ x, ι y⟫_ℝ = ⟪ι x, B₀ y⟫_ℝ)
    (hB₀ : B₀.IsInvertible) (hB₁ : B₁.IsInvertible) (hB₂ : B₂.IsInvertible)
    (h₁₂ : ∃ c, ∀ x, ‖(B₁ - B₂) x‖ ≤ c * ‖ι x‖) {γ : ℝ → D →L[ℝ] H} (hγ : Continuous γ)
    (hγSymm : ∀ s x y, ⟪γ s x, ι y⟫_ℝ = ⟪ι x, γ s y⟫_ℝ) (hγinv : ∀ s, (γ s).IsInvertible)
    {γL : Lp (D →L[ℝ] H) ∞ μ₀} (hγL : γL =ᵐ[μ₀] γ) (hγbot : Tendsto γ atBot (𝓝 B₁))
    (hγtop : Tendsto γ atTop (𝓝 B₂))
    (hγc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(γ s - B₂) x‖ ≤ c * ‖ι x‖)
    {A A' : ℝ → D →L[ℝ] H} {AL AL' : Lp (D →L[ℝ] H) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 B₀)) (htop : Tendsto A atTop (𝓝 B₁))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B₁) x‖ ≤ c * ‖ι x‖)
    (hAL' : AL' =ᵐ[μ₀] A') (hbot' : Tendsto A' atBot (𝓝 B₀)) (htop' : Tendsto A' atTop (𝓝 B₂))
    (hc' : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A' s - B₂) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL').index =
      (familyDomainTrajectoryOperator (p := 2) ι AL).index := by
  -- Catenate `A` with `γ`; the operator of `γ` has index zero.
  rw [index_familyDomainTrajectoryOperator_eq_add hι hSymm₀ hB₀
    (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hγbot
      (.of_forall (hγSymm · x y))) hB₁
    (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hγtop
      (.of_forall (hγSymm · x y))) hB₂ h₁₂
    hAL hbot htop hc hγL hγbot hγtop hγc hAL' hbot' htop' hc',
    index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι hγ hγSymm hγinv hB₁ hB₂
      hγL hγbot hγtop hγc, add_zero]

end TauCeti.WeakDerivStep
