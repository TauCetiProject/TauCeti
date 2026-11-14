/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Periodic curves do not lie in a line

A periodic curve `χ : ℝ → F` in a real normed space whose derivative vanishes nowhere is not
contained in any affine line (`Function.Periodic.exists_notMem_affineSpan_pair`), and in particular
in no segment (`Function.Periodic.exists_notMem_segment`). On the line through `a` and `b` the
curve is `a + (f / ‖b - a‖) • (b - a)` for a real coordinate `f`, which is periodic and so attains
its maximum, where its derivative and with it the derivative of `χ` vanish.
-/

public section

open Set

namespace Function

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : ℝ → F} {L : ℝ}

/-- A periodic curve with nowhere vanishing derivative does not lie in an affine line. -/
theorem Periodic.exists_notMem_affineSpan_pair (hper : Periodic χ L) (hL : L ≠ 0)
    (hχ' : ∀ t, deriv χ t ≠ 0) (a b : F) : ∃ t, χ t ∉ line[ℝ, a, b] := by
  by_contra! h
  have hχ : Differentiable ℝ χ := fun t ↦ differentiableAt_of_deriv_ne_zero (hχ' t)
  -- A coordinate `f` of `χ` along the line attains its maximum at some `t₀`.
  set v := b - a
  obtain ⟨g, -, hg⟩ := exists_dual_vector'' ℝ v
  set f : ℝ → ℝ := fun t ↦ g (χ t - a)
  have hf : Differentiable ℝ f := g.differentiable.comp (hχ.sub_const a)
  have hfper : Periodic f L := fun t ↦ by simp only [f, hper t]
  obtain ⟨-, ⟨t₀, rfl⟩, ht₀⟩ :=
    (hfper.compact_of_continuous hL hf.continuous).exists_isGreatest (range_nonempty f)
  have hmax : IsLocalMax f t₀ :=
    Filter.Eventually.of_forall fun t ↦ ht₀ (mem_range_self t)
  -- On the line `χ = a + (f / ‖v‖) • v`, so `χ'(t₀) = (f'(t₀) / ‖v‖) • v = 0`.
  have hχeq : χ = fun t ↦ a + (f t / ‖v‖) • v := by
    funext t
    obtain ⟨θ, hθ⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 (h t)
    have hθ' : χ t = a + θ • v := by rw [← hθ, AffineMap.lineMap_apply_module', add_comm]
    rcases eq_or_ne v 0 with hv | hv
    · simp [hθ', hv]
    · have hfθ : f t = θ * ‖v‖ := by
        simp only [f, hθ', add_sub_cancel_left, map_smul, hg, smul_eq_mul,
          RCLike.ofReal_real_eq_id, id_eq]
      rw [hfθ, mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hv), hθ']
  apply hχ' t₀
  rw [hχeq, deriv_const_add, deriv_smul_const ((hf t₀).div_const _), deriv_div_const,
    hmax.deriv_eq_zero, zero_div, zero_smul]

/-- A periodic curve with nowhere vanishing derivative does not lie in a segment. -/
theorem Periodic.exists_notMem_segment (hper : Periodic χ L) (hL : L ≠ 0)
    (hχ' : ∀ t, deriv χ t ≠ 0) (a b : F) : ∃ t, χ t ∉ segment ℝ a b :=
  (hper.exists_notMem_affineSpan_pair hL hχ' a b).imp fun t ht hseg ↦ ht <| by
    obtain ⟨θ, -, hθ⟩ := segment_eq_image_lineMap ℝ a b ▸ hseg
    exact hθ ▸ AffineMap.lineMap_mem_affineSpan_pair θ a b

end Function
