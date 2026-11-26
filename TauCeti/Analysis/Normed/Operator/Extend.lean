/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Bounded extensions and factorizations of linear maps

A semilinear map `f : V →ₛₗ[σ] F` with `‖f x‖ ≤ C * ‖e x‖` extends uniquely along a linear
map `e : V →ₗ[R] E` with dense range when `E` is seminormed and `F` is complete and normed.
The construction `LinearMap.extendOfBound` works over arbitrary rings `R`, `S` with continuous
constant scalar actions of `R` on `E` and `S` on `F`. The source `V` needs no norm or topology.
The range factor `LinearMap.rangeMapOfBound` needs neither density nor completeness nor continuous
scalar actions.
The descent follows Mathlib's `LinearMap.compLeftInverse` construction, using `Submodule.liftQ`
and `LinearMap.quotKerEquivRange` over an arbitrary ring; the extension then uses
`ContinuousLinearMap.extend`.

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

* `LinearMap.rangeMapOfBound_apply`: the range factor agrees with the original map.
* `LinearMap.rangeMapOfBound_unique`: the values on representatives determine the range factor.
* `LinearMap.norm_rangeMapOfBound_apply_le`: the range factor preserves the bound.
* `LinearMap.extendOfBound_eq_of_bound`: valid choices of the bound give the same extension.
* `LinearMap.extendOfBound_apply`: the extension agrees with the original map on dense tests.
* `LinearMap.extendOfBound_eq_zero_of_not_denseRange`: the extension is zero when the comparison
  map has non-dense range.
* `LinearMap.norm_extendOfBound_apply_le`: the extension preserves the original bound.
* `LinearMap.extendOfBound_unique`: the extension is the unique continuous semilinear extension.

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

namespace LinearMap

open Topology

variable {R S V E F : Type*} [Ring R] [Ring S] {σ : R →+* S}
  [AddCommGroup V] [Module R V] [SeminormedAddCommGroup E] [Module R E]
  [NormedAddCommGroup F] [Module S F]

private noncomputable def rangeMapOfBoundAux (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) : e.range →ₛₗ[σ] F :=
  let hk : e.ker ≤ f.ker := by
    intro x hx
    have hx' := h x
    rw [LinearMap.mem_ker.mp hx, norm_zero, mul_zero] at hx'
    exact LinearMap.mem_ker.mpr (norm_le_zero_iff.mp hx')
  (e.ker.liftQ f hk).comp e.quotKerEquivRange.symm.toLinearMap

private theorem rangeMapOfBoundAux_apply (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (x : V) :
    rangeMapOfBoundAux f e C h (e.rangeRestrict x) = f x := by
  have he : e.quotKerEquivRange (e.ker.mkQ x) = e.rangeRestrict x := by
    apply Subtype.ext
    rw [Submodule.mkQ_apply, quotKerEquivRange_apply_mk, rangeRestrict, codRestrict_apply]
  simp only [rangeMapOfBoundAux, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    ← he, LinearEquiv.symm_apply_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Factor a bounded semilinear map through the range of the linear map controlling its norm.

The bound forces `f` to vanish on the kernel of `e`. Neither density of the range nor
completeness of the target is needed, and the source `V` needs no norm or topology. -/
noncomputable def rangeMapOfBound (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) : e.range →SL[σ] F :=
  (rangeMapOfBoundAux f e C h).mkContinuous C (by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective_rangeRestrict y
    simpa only [rangeMapOfBoundAux_apply, ← Submodule.norm_coe, rangeRestrict,
      codRestrict_apply] using h x)

/-- The bounded range factor agrees with the original map on representatives. -/
@[simp] theorem rangeMapOfBound_apply (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (x : V) :
    f.rangeMapOfBound e C h (e.rangeRestrict x) = f x := by
  rw [rangeMapOfBound, LinearMap.mkContinuous_apply]
  exact rangeMapOfBoundAux_apply f e C h x

/-- A continuous semilinear map agreeing with `f` on representatives is its bounded range factor. -/
theorem rangeMapOfBound_unique (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (g : e.range →SL[σ] F)
    (H : ∀ x, g (e.rangeRestrict x) = f x) : f.rangeMapOfBound e C h = g := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective_rangeRestrict y
  rw [rangeMapOfBound_apply, H]

/-- The bounded range factor preserves the original pointwise bound. -/
theorem norm_rangeMapOfBound_apply_le (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (y : e.range) :
    ‖f.rangeMapOfBound e C h y‖ ≤ C * ‖y‖ := by
  obtain ⟨x, rfl⟩ := e.surjective_rangeRestrict y
  simpa only [rangeMapOfBound_apply, ← Submodule.norm_coe, rangeRestrict,
    codRestrict_apply] using h x

variable [ContinuousConstSMul R E] [ContinuousConstSMul S F] [CompleteSpace F]

/-- Extend a bounded semilinear map along a linear map with dense range.

The bound is measured in the ambient domain `E`, so the source `V` needs no norm or topology.
It forces `f` to vanish on the kernel of `e`, allowing descent to its range without injectivity.
When `e` has dense range, this is the unique continuous semilinear extension of `f`; otherwise it
is zero. This construction works over rings that need not be fields. -/
noncomputable def extendOfBound (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) : E →SL[σ] F :=
  (f.rangeMapOfBound e C h).extend e.range.subtypeL

/-- The bounded extension is zero when the comparison map does not have dense range. -/
@[simp] theorem extendOfBound_eq_zero_of_not_denseRange (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (hd : ¬ DenseRange e) :
    f.extendOfBound e C h = 0 := by
  have hd' : ¬ DenseRange e.range.subtypeL :=
    fun hs ↦ hd ((denseRange_range_subtypeL_iff e).mp hs)
  simp only [extendOfBound, ContinuousLinearMap.extend, hd', false_and, ↓reduceDIte]

/-- The bounded extension agrees with the original map on the dense range. -/
@[simp] theorem extendOfBound_apply (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (hd : DenseRange e) (x : V) :
    f.extendOfBound e C h (e x) = f x := by
  have hd' : DenseRange e.range.subtypeL := (denseRange_range_subtypeL_iff e).mpr hd
  have hi : IsUniformInducing e.range.subtypeL := by
    rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
    exact isUniformInducing_val _
  have hh : e.range.subtypeL (e.rangeRestrict x) = e x := by
    rw [Submodule.subtypeL_apply, rangeRestrict, codRestrict_apply]
  rw [← hh, extendOfBound, ContinuousLinearMap.extend_eq _ hd' hi]
  exact rangeMapOfBound_apply f e C h x

/-- Extending a bounded semilinear map along a dense map preserves its bound. -/
theorem norm_extendOfBound_apply_le (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖)
    (hd : DenseRange e) (x : E) : ‖f.extendOfBound e C h x‖ ≤ C * ‖x‖ := by
  refine hd.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro y
  rw [extendOfBound_apply f e C h hd]
  exact h y

/-- A continuous semilinear map agreeing with `f` on a dense range is its bounded extension. -/
theorem extendOfBound_unique (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (hd : DenseRange e)
    (g : E →SL[σ] F) (H : ∀ x, g (e x) = f x) : f.extendOfBound e C h = g := by
  apply ContinuousLinearMap.coeFn_injective
  exact hd.equalizer (f.extendOfBound e C h).continuous g.continuous
    (funext fun x ↦ (extendOfBound_apply f e C h hd x).trans (H x).symm)

/-- The bounded extension is independent of the chosen bound, including when the comparison
map does not have dense range. -/
theorem extendOfBound_eq_of_bound (f : V →ₛₗ[σ] F) (e : V →ₗ[R] E)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C * ‖e x‖) (hD : ∀ x, ‖f x‖ ≤ D * ‖e x‖) :
    f.extendOfBound e C hC = f.extendOfBound e D hD := by
  by_cases hd : DenseRange e
  · exact f.extendOfBound_unique e C hC hd (f.extendOfBound e D hD)
      (fun x ↦ f.extendOfBound_apply e D hD hd x)
  · rw [extendOfBound_eq_zero_of_not_denseRange f e C hC hd,
      extendOfBound_eq_zero_of_not_denseRange f e D hD hd]

end LinearMap

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
