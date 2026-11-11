/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Periodic curves do not lie in a segment

A differentiable periodic curve `χ : ℝ → F` in a real normed space whose derivative vanishes
nowhere is not contained in any segment (`Function.Periodic.exists_notMem_segment`). On a segment
`[a, b]` the curve is `a + (f / ‖b - a‖) • (b - a)` for a real coordinate `f`, which is periodic
and so attains its maximum, where its derivative and with it the derivative of `χ` vanish.
-/

public section

open Set

namespace Function

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : ℝ → F} {L : ℝ}

/-- A differentiable periodic curve with nowhere vanishing derivative does not lie in a segment. -/
theorem Periodic.exists_notMem_segment (hper : Periodic χ L) (hL : 0 < L)
    (hχ : Differentiable ℝ χ) (hχ' : ∀ t, deriv χ t ≠ 0) (a b : F) :
    ∃ t, χ t ∉ segment ℝ a b := by
  by_contra! h
  -- A coordinate `f` of `χ` along the segment attains its maximum at some `t₀`.
  set v := b - a
  obtain ⟨g, -, hg⟩ := exists_dual_vector'' ℝ v
  set f : ℝ → ℝ := fun t ↦ g (χ t - a)
  have hf : Differentiable ℝ f := g.differentiable.comp (hχ.sub_const a)
  have hfper : Periodic f L := fun t ↦ by simp only [f, hper t]
  obtain ⟨-, ⟨t₀, rfl⟩, ht₀⟩ :=
    (hfper.compact_of_continuous hL.ne' hf.continuous).exists_isGreatest (range_nonempty f)
  have hmax : IsLocalMax f t₀ :=
    Filter.Eventually.of_forall fun t ↦ ht₀ (mem_range_self t)
  -- On the segment `χ = a + (f / ‖v‖) • v`, so `χ'(t₀) = (f'(t₀) / ‖v‖) • v = 0`.
  have hχeq : χ = fun t ↦ a + (f t / ‖v‖) • v := by
    funext t
    obtain ⟨θ, -, hθ⟩ := (segment_eq_image' ℝ a b ▸ h t :)
    have hθ' : χ t = a + θ • v := hθ.symm
    rcases eq_or_ne v 0 with hv | hv
    · simp [hθ', hv]
    · have hfθ : f t = θ * ‖v‖ := by
        simp only [f, hθ', add_sub_cancel_left, map_smul, hg, smul_eq_mul,
          RCLike.ofReal_real_eq_id, id_eq]
      rw [hfθ, mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hv), hθ']
  apply hχ' t₀
  rw [hχeq, deriv_const_add, deriv_smul_const ((hf t₀).div_const _), deriv_div_const,
    hmax.deriv_eq_zero, zero_div, zero_smul]

end Function
