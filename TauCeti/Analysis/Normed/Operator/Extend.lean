/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Factoring an operator through the range of a dominating operator

Let `g : E →L[𝕜] G` and `f : E →L[𝕜] F` be bounded operators with `‖f x‖ ≤ C ‖g x‖` for every
`x`. Then `f` vanishes on the kernel of `g`, so it factors as `f = S ∘ g` through the range of
`g`, with a factor `S` of norm at most `C`. When `F` is complete, `S` extends by continuity to the
closure of that range, with the same bound. Conversely, any such factorization gives the bound.

The factor on the range is Mathlib's `LinearMap.compLeftInverse` and its extension to the closure
is `LinearMap.extendOfNorm`. This file records the operator-norm bound for the former and the two
factorization criteria.

## Main results

* `LinearMap.opNorm_compLeftInverse_le`: the norm of `f.compLeftInverse g` is at most `C`.
* `ContinuousLinearMap.exists_eq_comp_rangeRestrict_iff`: `f` factors through the range of `g`
  with a factor of norm at most `C` iff `‖f x‖ ≤ C ‖g x‖` for all `x`.
* `ContinuousLinearMap.exists_eq_comp_codRestrict_topologicalClosure_iff`: the same criterion for
  factorizations through the closure of the range, when the target is complete.
-/

public section

variable {𝕜 𝕜₂ E F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂}

namespace LinearMap

variable [AddCommGroup E] [Module 𝕜 E] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- If `‖f x‖ ≤ C ‖g x‖` for all `x`, the factor `f.compLeftInverse g` of `f` through the range
of `g` has operator norm at most `C`. -/
theorem opNorm_compLeftInverse_le {f : E →ₛₗ[σ₁₂] F} {g : E →ₗ[𝕜] G} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) : ‖f.compLeftInverse g‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC fun y ↦ by
    obtain ⟨_, x, rfl⟩ := y
    rw [compLeftInverse_apply_of_bdd f g ⟨C, h⟩ x _ rfl]
    exact h x

end LinearMap

namespace ContinuousLinearMap

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂]

/-- The corestriction of an operator to the closure of its range has dense range. -/
theorem denseRange_codRestrict_topologicalClosure (g : E →L[𝕜] G) :
    DenseRange (g.codRestrict (LinearMap.range (g : E →ₗ[𝕜] G)).topologicalClosure
      fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  exact (Submodule.topologicalClosure_coe _).subset

/-- An operator `f` factors as `S ∘ g` through the range of `g`, with `‖S‖ ≤ C`, if and only if
`‖f x‖ ≤ C ‖g x‖` for all `x`. -/
theorem exists_eq_comp_rangeRestrict_iff {f : E →SL[σ₁₂] F} {g : E →L[𝕜] G} {C : ℝ}
    (hC : 0 ≤ C) :
    (∃ S : LinearMap.range (g : E →ₗ[𝕜] G) →SL[σ₁₂] F, ‖S‖ ≤ C ∧ f = S.comp g.rangeRestrict) ↔
      ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  refine ⟨fun ⟨S, hS, hf⟩ x ↦ ?_, fun h ↦ ?_⟩
  · rw [hf]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  · refine ⟨(f : E →ₛₗ[σ₁₂] F).compLeftInverse (g : E →ₗ[𝕜] G),
      LinearMap.opNorm_compLeftInverse_le hC h, ?_⟩
    ext x
    exact (LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨C, h⟩ x _ rfl).symm

/-- When `F` is complete, an operator `f` factors as `S ∘ g` through the closure of the range of
`g`, with `‖S‖ ≤ C`, if and only if `‖f x‖ ≤ C ‖g x‖` for all `x`. -/
theorem exists_eq_comp_codRestrict_topologicalClosure_iff [CompleteSpace F] {f : E →SL[σ₁₂] F}
    {g : E →L[𝕜] G} {C : ℝ} (hC : 0 ≤ C) :
    (∃ S : (LinearMap.range (g : E →ₗ[𝕜] G)).topologicalClosure →SL[σ₁₂] F,
        ‖S‖ ≤ C ∧ f = S.comp (g.codRestrict _
          fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))) ↔
      ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  refine ⟨fun ⟨S, hS, hf⟩ x ↦ ?_, fun h ↦ ?_⟩
  · rw [hf]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  · set j := g.codRestrict _
      fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (g : E →ₗ[𝕜] G) x)
    have hd : DenseRange j := g.denseRange_codRestrict_topologicalClosure
    have h' (x : E) : ‖f x‖ ≤ C * ‖j x‖ := h x
    refine ⟨(f : E →ₛₗ[σ₁₂] F).extendOfNorm j.toLinearMap,
      LinearMap.opNorm_extendOfNorm_le hd hC h', ?_⟩
    ext x
    exact (LinearMap.extendOfNorm_eq hd ⟨C, h'⟩ x).symm

end ContinuousLinearMap
