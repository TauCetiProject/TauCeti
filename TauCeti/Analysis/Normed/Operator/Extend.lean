/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Factoring an operator through the range of a dominating operator

Let `σ₁₂ : 𝕜 →+* 𝕜₂` be a ring homomorphism, let `g : E →L[𝕜] G` be a continuous linear map and
`f : E →SL[σ₁₂] F` a continuous `σ₁₂`-semilinear map (for instance a conjugate-linear map, or a map
into a space over another field), from a module `E` with any topology (no norm on `E` is needed)
to a seminormed space `G` and a normed space `F`. Let `0 ≤ C` with `‖f x‖ ≤ C ‖g x‖` for every `x`.
Then `f` vanishes on the kernel of `g`, so it factors as `f = S ∘ g` through the range of `g`, with
a `σ₁₂`-semilinear factor `S` of norm at most `C`. When `F` is complete, `S` extends by continuity
to the closure of that range, with the same bound. Conversely, when `σ₁₂` is isometric
(`RingHomIsometric σ₁₂`), any such factorization gives the bound; the two factorization criteria
assume this.

The factor on the range is Mathlib's `LinearMap.compLeftInverse` and its extension to the closure
is `LinearMap.extendOfNorm`. This file records the pointwise and operator-norm bounds for the
former and the two factorization criteria. The pointwise bound needs no norms on the scalars,
which may be any division rings; it still needs `G` to be a seminormed and `F` a normed additive
group, each a module over its scalars, while `E` is any module over `𝕜`.

## Main results

* `LinearMap.norm_compLeftInverse_apply_le`: the pointwise bound `C` for `f.compLeftInverse g`.
* `LinearMap.opNorm_compLeftInverse_le`: for `0 ≤ C`, the norm of `f.compLeftInverse g` is at
  most `C`.
* `ContinuousLinearMap.exists_eq_comp_rangeRestrict_iff`: for `0 ≤ C` and isometric `σ₁₂`, a
  `σ₁₂`-semilinear `f` factors through the range of a linear `g` with a `σ₁₂`-semilinear factor of
  norm at most `C` iff `‖f x‖ ≤ C ‖g x‖` for all `x`.
* `ContinuousLinearMap.exists_eq_comp_codRestrict_topologicalClosure_iff`: the same criterion for
  factorizations through the closure of the range, when the target is complete.
-/

public section

variable {𝕜 𝕜₂ E F G : Type*}

namespace LinearMap

section DivisionRing

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup G] [Module 𝕜 G] [NormedAddCommGroup F] [Module 𝕜₂ F]

/-- If `‖f x‖ ≤ C ‖g x‖` for all `x`, the factor `f.compLeftInverse g` of the semilinear map `f`
through the range of the linear map `g` satisfies `‖f.compLeftInverse g y‖ ≤ C ‖y‖` on that
range. -/
theorem norm_compLeftInverse_apply_le {f : E →ₛₗ[σ₁₂] F} {g : E →ₗ[𝕜] G} {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) (y : range g) : ‖f.compLeftInverse g y‖ ≤ C * ‖(y : G)‖ := by
  obtain ⟨_, x, rfl⟩ := y
  rw [compLeftInverse_apply_of_bdd f g ⟨C, h⟩ x _ rfl]
  exact h x

end DivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [Module 𝕜 E] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- If `0 ≤ C` and `‖f x‖ ≤ C ‖g x‖` for all `x`, the factor `f.compLeftInverse g` of the
semilinear map `f` through the range of the linear map `g` has operator norm at most `C`. -/
theorem opNorm_compLeftInverse_le {f : E →ₛₗ[σ₁₂] F} {g : E →ₗ[𝕜] G} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) : ‖f.compLeftInverse g‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_compLeftInverse_apply_le h)

end NormedField

end LinearMap

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂]

/-- For `0 ≤ C` and an isometric `σ₁₂`, a continuous `σ₁₂`-semilinear map `f` factors as `S ∘ g`
through the range of the continuous linear map `g`, with `S` `σ₁₂`-semilinear and `‖S‖ ≤ C`, if
and only if `‖f x‖ ≤ C ‖g x‖` for all `x`. -/
theorem exists_eq_comp_rangeRestrict_iff {f : E →SL[σ₁₂] F} {g : E →L[𝕜] G} {C : ℝ}
    (hC : 0 ≤ C) :
    (∃ S : LinearMap.range (g : E →ₗ[𝕜] G) →SL[σ₁₂] F, ‖S‖ ≤ C ∧ f = S.comp g.rangeRestrict) ↔
      ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  refine ⟨fun ⟨S, hS, hf⟩ x ↦ ?_, fun h ↦ ?_⟩
  · rw [hf]
    exact S.le_of_opNorm_le hS _
  · let := Module.addCommMonoidToAddCommGroup 𝕜 (M := E)
    refine ⟨(f : E →ₛₗ[σ₁₂] F).compLeftInverse (g : E →ₗ[𝕜] G),
      LinearMap.opNorm_compLeftInverse_le hC h, ?_⟩
    ext x
    exact (LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨C, h⟩ x _ rfl).symm

/-- When `F` is complete, `0 ≤ C` and `σ₁₂` is isometric, a continuous `σ₁₂`-semilinear map `f`
factors as `S ∘ g` through the closure of the range of the continuous linear map `g`, with `S`
`σ₁₂`-semilinear and `‖S‖ ≤ C`, if and only if `‖f x‖ ≤ C ‖g x‖` for all `x`. -/
theorem exists_eq_comp_codRestrict_topologicalClosure_iff [CompleteSpace F] {f : E →SL[σ₁₂] F}
    {g : E →L[𝕜] G} {C : ℝ} (hC : 0 ≤ C) :
    (∃ S : (LinearMap.range (g : E →ₗ[𝕜] G)).topologicalClosure →SL[σ₁₂] F,
        ‖S‖ ≤ C ∧ f = S.comp (g.codRestrict _
          fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))) ↔
      ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  refine ⟨fun ⟨S, hS, hf⟩ x ↦ ?_, fun h ↦ ?_⟩
  · rw [hf]
    exact S.le_of_opNorm_le hS _
  · let := Module.addCommMonoidToAddCommGroup 𝕜 (M := E)
    set j := g.codRestrict _
      fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (g : E →ₗ[𝕜] G) x)
    have hd : DenseRange j := g.denseRange_codRestrict_topologicalClosure
    have h' (x : E) : ‖f x‖ ≤ C * ‖j x‖ := h x
    refine ⟨(f : E →ₛₗ[σ₁₂] F).extendOfNorm j.toLinearMap,
      LinearMap.opNorm_extendOfNorm_le hd hC h', ?_⟩
    ext x
    exact (LinearMap.extendOfNorm_eq hd ⟨C, h'⟩ x).symm

end ContinuousLinearMap
