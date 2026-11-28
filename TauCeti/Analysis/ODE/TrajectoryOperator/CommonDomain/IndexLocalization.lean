/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Fredholm
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Bounds
import TauCeti.MeasureTheory.Function.Lp.StoppedPath
import TauCeti.Topology.Order.ProjIcc

/-!
# The index of the trajectory operator is localized at the crossings

Let `ι : D →L[ℝ] H` be a compact embedding of a Banach space `D` into a Hilbert space `H`, and let
`A : ℝ → (D →L[ℝ] H)` be a continuous path of `ι`-symmetric operators,
`⟪A(s) x, ι y⟫ = ⟪ι x, A(s) y⟫`, converging to invertible operators `B₋` and `B₊` at `-∞` and
`∞`, and differing from `B₊` on bounded windows by operators bounded through `ι`. By
`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`, the operator
`D_A u = (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is Fredholm. A typical case
is the linearized Floer operator, where `A(s) = J₀ ∂ₜ + S(s, t)` with `D = H¹` and `H = L²`.

This file shows that the index of `D_A` only sees the times `s` at which `A(s)` is not invertible,
the *crossings* of `A`, in the same way as the spectral flow `TauCeti.domainSpectralFlow` does.

* **No crossings, no index.** If every `A(s)` is invertible, then `D_A` has index zero
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`).
  Stop the path at time `t`: the path `s ↦ A (min s t)` runs from `B₋` to the invertible operator
  `A(t)`, so its trajectory operator is Fredholm for every `t`. It depends continuously on `t`,
  so its index does not depend on `t`. As `t → -∞` the stopped paths converge uniformly to the
  constant path `B₋`, whose operator is invertible, and as `t → ∞` they converge uniformly to `A`.
  Since the index is locally constant on Fredholm operators, it is `0` for very negative `t` and
  the index of `D_A` for very positive `t`. The continuity of `A` is essential: a path jumping from
  `B` to `-B` has no crossings, but its index need not vanish.
* **Localization.** If `A(s)` is invertible for every `s` outside an interval `(a, b)`, then the
  index of `D_A` is the index for the path that is constant outside `[a, b]`,
  `Set.IccExtend` of the restriction of `A` to `[a, b]`
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_ae_eq_IccExtend`). Cut `A` at
  `a` and at `b` and apply the catenation law
  `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_add` twice: the two outer pieces
  have no crossings, so they contribute nothing.

These are the counterparts for the index of the vanishing of the spectral flow of a path of
invertible operators (`TauCeti.domainSpectralFlow_eq_zero_of_forall_isInvertible`) and of its
additivity under concatenation. They reduce the identification of the index of `D_A` with the
spectral flow of `A` to paths that are constant outside a compact interval.

## Main results

* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`: a
  path of invertible operators has index zero.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_ae_eq_IccExtend`: the index
  only depends on the path over an interval outside which it is invertible.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §4 (the index of `d/ds + A(s)` satisfies the axioms of the spectral flow).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ι : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H}

/-! ### The index -/

variable [CompleteSpace D] [CompleteSpace H] {Bbot Btop : D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀}

/-- **A path of invertible operators has index zero.** Let `ι` be compact and let `A` be a
continuous path of invertible `ι`-symmetric operators, converging to invertible operators `Bbot`
and `Btop` at `-∞` and `∞`, and differing from `Btop` on every bounded interval by an operator
bounded through `ι`, as in `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`.
Then `u ↦ (ι ∘ u)' + A u` has index zero. -/
theorem index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hInv : ∀ s, (A s).IsInvertible)
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = 0 := by
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_tendsto hA hbot htop
  have hb := exists_forall_mem_Icc_norm_sub_apply_le_of_ae hA hc
  have hSymmbot (x y : D) : ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ :=
    ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hbot (.of_forall fun s ↦ hSymm s x y)
  -- The class in `L∞` of the path stopped at `t`.
  have hm (t : ℝ) : MemLp (fun s ↦ A (min s t)) ∞ μ₀ := memLp_top_of_bound
    (hA.comp (continuous_id.min continuous_const)).aestronglyMeasurable C (.of_forall fun s ↦ hC _)
  -- The path stopped at `t` runs from `Bbot` to the invertible `A t`, so its operator is Fredholm.
  have hFred (t : ℝ) : (familyDomainTrajectoryOperator (p := 2) ι ((hm t).toLp _)).IsFredholm :=
    isFredholm_familyDomainTrajectoryOperator hι hSymmbot hBbot (hSymm t) (hInv t)
      (hm t).coeFn_toLp (hbot.comp_min_atBot t) (tendsto_comp_min_atTop t)
      (exists_ae_norm_comp_sub_apply_le hb (exists_norm_sub_apply_le hb t) (by fun_prop))
  have hD := continuous_familyDomainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι
  have hFredbot : (familyDomainTrajectoryOperator (p := 2) ι
      ((memLp_top_const (μ := μ₀) Bbot).toLp _)).IsFredholm := by
    rw [familyDomainTrajectoryOperator_toLp_const]
    exact isFredholm_domainTrajectoryOperator hSymmbot hBbot
  -- The index vanishes when stopping very early, and is that of `A` when stopping very late.
  obtain ⟨t₀, -, ht₀⟩ := (((hD.tendsto _).comp (tendsto_atBot_of_ae_eq_comp_min hbot
    (fun t ↦ (hm t).coeFn_toLp) (memLp_top_const Bbot).coeFn_toLp)).eventually
    hFredbot.eventually_isFredholm_and_index_eq).exists
  have hFredA := isFredholm_familyDomainTrajectoryOperator_of_forall_symm hι hSymm hBbot hBtop hAL
    hbot htop hc
  obtain ⟨t₁, -, ht₁⟩ := (((hD.tendsto _).comp (tendsto_atTop_of_ae_eq_comp_min htop
    (fun t ↦ (hm t).coeFn_toLp) hAL)).eventually
    hFredA.eventually_isFredholm_and_index_eq).exists
  have hconst := (hD.comp (continuous_of_ae_eq_comp_min hA
    fun t ↦ (hm t).coeFn_toLp)).index_eq_of_preconnectedSpace hFred t₀ t₁
  simp only [Function.comp_apply] at ht₀ ht₁ hconst
  rw [← ht₁, ← hconst, ht₀, familyDomainTrajectoryOperator_toLp_const,
    index_domainTrajectoryOperator hSymmbot hBbot]

/-- **The index is localized on an interval containing the crossings.** Let `ι` be compact and let
`A` be a continuous path of `ι`-symmetric operators as in
`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`, with invertible limits `Bbot`
and `Btop` at `-∞` and `∞`. If `A s` is invertible for every `s` outside `(a, b)`, then
`u ↦ (ι ∘ u)' + A u` has the same index as the operator of the path `Set.IccExtend` of `A` on
`[a, b]`, which is `A a` before `a`, `A` on `[a, b]` and `A b` after `b`. -/
theorem index_familyDomainTrajectoryOperator_eq_of_ae_eq_IccExtend (hι : IsCompactOperator ι)
    (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {a b : ℝ}
    (hab : a ≤ b) (hInv : ∀ s ∉ Ioo a b, (A s).IsInvertible) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖)
    {AL' : Lp (D →L[ℝ] H) ∞ μ₀} (hAL' : AL' =ᵐ[μ₀] IccExtend hab ((Icc a b).domRestrict A)) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index =
      (familyDomainTrajectoryOperator (p := 2) ι AL').index := by
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_tendsto hA hbot htop
  have hb := exists_forall_mem_Icc_norm_sub_apply_le_of_ae hA hc
  have hpt := exists_norm_sub_apply_le hb
  have hb₀ : ∃ c, ∀ x, ‖(Btop - Btop) x‖ ≤ c * ‖ι x‖ := ⟨0, fun x ↦ by simp⟩
  have hSymmbot (x y : D) : ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ :=
    ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hbot (.of_forall fun s ↦ hSymm s x y)
  have hSymmtop (x y : D) : ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ :=
    ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto htop (.of_forall fun s ↦ hSymm s x y)
  -- The pieces: `A` up to `a`, `A` from `a` on, `A` on `[a, b]`, and `A` from `b` on.
  have hm {φ : ℝ → ℝ} (hφ : Continuous φ) : MemLp (fun s ↦ A (φ s)) ∞ μ₀ :=
    memLp_top_of_bound (hA.comp hφ).aestronglyMeasurable C (.of_forall fun s ↦ hC _)
  have hL := hm (φ := fun s ↦ min s a) (by fun_prop)
  have hM := hm (φ := fun s ↦ max s a) (by fun_prop)
  have hR := hm (φ := fun s ↦ max s b) (by fun_prop)
  -- The outer pieces have no crossings.
  have hL₀ : (familyDomainTrajectoryOperator (p := 2) ι (hL.toLp _)).index = 0 :=
    index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι (by fun_prop)
      (fun s ↦ hSymm _) (fun s ↦ hInv _ fun h ↦ (min_le_right s a).not_gt h.1) hBbot
      (hInv a left_notMem_Ioo) hL.coeFn_toLp (hbot.comp_min_atBot a) (tendsto_comp_min_atTop a)
      (exists_ae_norm_comp_sub_apply_le hb (hpt a) (by fun_prop))
  have hR₀ : (familyDomainTrajectoryOperator (p := 2) ι (hR.toLp _)).index = 0 :=
    index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι (by fun_prop)
      (fun s ↦ hSymm _) (fun s ↦ hInv _ fun h ↦ (le_max_right s b).not_gt h.2)
      (hInv b right_notMem_Ioo) hBtop hR.coeFn_toLp (tendsto_comp_max_atBot b)
      (htop.comp_max_atTop b) (exists_ae_norm_comp_sub_apply_le hb hb₀ (by fun_prop))
  -- Cut at `a`, then at `b`.
  rw [index_familyDomainTrajectoryOperator_eq_add hι hSymmbot hBbot (hSymm a)
      (hInv a left_notMem_Ioo) hSymmtop hBtop (hpt a) hL.coeFn_toLp (hbot.comp_min_atBot a)
      (tendsto_comp_min_atTop a) (exists_ae_norm_comp_sub_apply_le hb (hpt a) (by fun_prop))
      hM.coeFn_toLp (tendsto_comp_max_atBot a) (htop.comp_max_atTop a)
      (exists_ae_norm_comp_sub_apply_le hb hb₀ (by fun_prop)) hAL hbot htop hc,
    hL₀, zero_add,
    index_familyDomainTrajectoryOperator_eq_add hι (hSymm a) (hInv a left_notMem_Ioo) (hSymm b)
      (hInv b right_notMem_Ioo) hSymmtop hBtop (hpt b) hAL'
      (TauCeti.tendsto_IccExtend_atBot hab _) (TauCeti.tendsto_IccExtend_atTop hab _)
      (exists_ae_norm_IccExtend_sub_apply_le hb (hpt b) hab) hR.coeFn_toLp
      (tendsto_comp_max_atBot b) (htop.comp_max_atTop b)
      (exists_ae_norm_comp_sub_apply_le hb hb₀ (by fun_prop)) hM.coeFn_toLp
      (tendsto_comp_max_atBot a) (htop.comp_max_atTop a)
      (exists_ae_norm_comp_sub_apply_le hb hb₀ (by fun_prop)),
    hR₀, add_zero]

end TauCeti.WeakDerivStep
