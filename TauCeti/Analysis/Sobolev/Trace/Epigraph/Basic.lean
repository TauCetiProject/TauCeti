/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening
public import TauCeti.Analysis.Sobolev.Trace.Kernel
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# Sobolev functions above the graph of a `C¹` function, and their trace

Let `φ : E → ℝ` be continuous. In the Euclidean product `ℝ × E`, the region above its graph is
the open set

`TauCeti.normalEpigraph φ = {x | φ x.snd < x.fst}`, the strict epigraph of `φ`,

whose boundary is the graph `{(φ y, y) | y ∈ E}`. These regions are the local models of domains
with `C¹` (or Lipschitz) boundary: near each boundary point such a domain is, after a rotation,
the region above the graph of a function. The half-space `TauCeti.normalHalfSpace 0` is the case
`φ = 0`.

The graph-flattening homeomorphism `TauCeti.graphFlattening φ : (t, y) ↦ (t - φ y, y)` is
measure-preserving and carries the region above the graph onto the half-space `{0 < t}`; its
inverse adds `φ y` to the normal coordinate. If `φ` is of class `C¹` with `‖fderiv ℝ φ‖ ≤ L`,
both maps are `C¹` with derivative of norm at most `1 + L`, so by
`TauCeti.W1p.compMeasurePreservingL` precomposition with them is a pair of mutually inverse
bounded operators between `W^{1,p}` of the region and `W^{1,p}` of the half-space
(`TauCeti.W1p.normalEpigraphEquivL`), and for `p < ∞` both preserve zero boundary values.

Composing with the half-space trace `TauCeti.W1p.halfSpaceTrace` gives the trace on the graph,
`TauCeti.W1p.normalEpigraphTrace φ : H¹(normalEpigraph φ) →L[ℝ] L²(E)`, a bounded operator. The
graph is parametrized by `y ↦ (φ y, y)`, the image under the inverse flattening of the boundary
point `(0, y)` of the half-space, and the trace is measured by Lebesgue measure on `E` rather
than by surface measure on the graph. Its kernel is exactly `H¹₀` of the region
(`TauCeti.W1p.ker_normalEpigraphTrace`), the characterization of the homogeneous Dirichlet
condition by the trace.

## Main declarations

* `TauCeti.W1p.normalEpigraphEquivL`: `W^{1,p}` of the region is isomorphic to `W^{1,p}` of the
  half-space, with `TauCeti.W1p.normalEpigraphEquivL_mem_w1p0Submodule_iff`.
* `TauCeti.W1p.normalEpigraphTrace`: the trace on the graph, with
  `TauCeti.W1p.norm_normalEpigraphTrace_le`, `TauCeti.W1p.opNorm_normalEpigraphTrace_le` and
  `TauCeti.W1p.ker_normalEpigraphTrace`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1 (the trace theorem is
  proved by flattening the boundary locally).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.3
  (flattening `C¹` boundaries) and Lemma 9.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### Flattening `W^{1,p}` of the region above a `C¹` graph -/

section Flatten

variable {φ : C(E, ℝ)} {L : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Precomposition with inverse graph flattening, from the region above the graph to the
half-space. -/
private def flattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalEpigraph φ) p →L[ℝ] W1p volume (normalHalfSpace (E := E) 0) p :=
  W1p.compMeasurePreservingL (M := 1 + L) (measurePreserving_graphFlattening_symm φ φ.continuous)
    (by
      rw [← Homeomorph.image_eq_preimage_symm, coe_normalEpigraph, graphFlattening_image_lt]
      ext x
      exact mem_normalHalfSpace 0 x)
    (contDiff_graphFlattening_symm hφ).contDiffOn
    fun x _ => (norm_fderiv_graphFlattening_symm_le φ.continuous
      (hφ.differentiable one_ne_zero _)).trans (by linarith [hL x.snd])

/-- Precomposition with graph flattening, from the half-space to the region above the graph. -/
private def unflattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalHalfSpace (E := E) 0) p →L[ℝ] W1p volume (normalEpigraph φ) p :=
  W1p.compMeasurePreservingL (M := 1 + L) (measurePreserving_graphFlattening φ φ.continuous)
    (by
      rw [← (graphFlattening φ φ.continuous).preimage_image (normalEpigraph φ),
        coe_normalEpigraph, graphFlattening_image_lt]
      congr 1
      ext x
      exact (mem_normalHalfSpace 0 x).symm)
    (contDiff_graphFlattening hφ).contDiffOn
    fun x _ => norm_fderiv_graphFlattening_le_one_add (hφ.differentiable one_ne_zero) hL x

private theorem norm_flattenL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖(flattenL hφ hL : W1p volume (normalEpigraph φ) p →L[ℝ] _)‖ ≤ 1 + L :=
  (W1p.norm_compMeasurePreservingL_le _ _ _ _).trans_eq
    (max_eq_right (le_add_of_nonneg_right (nonneg_of_forall_norm_fderiv_le hL)))

private theorem norm_unflattenL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖(unflattenL hφ hL : W1p volume (normalHalfSpace (E := E) 0) p →L[ℝ] _)‖ ≤ 1 + L :=
  (W1p.norm_compMeasurePreservingL_le _ _ _ _).trans_eq
    (max_eq_right (le_add_of_nonneg_right (nonneg_of_forall_norm_fderiv_le hL)))

private theorem unflattenL_flattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    Function.LeftInverse (unflattenL (p := p) hφ hL) (flattenL hφ hL) := fun u =>
  W1p.compMeasurePreservingL_compMeasurePreservingL _ _ _ _ _ _ _ _
    (fun x _ => (graphFlattening φ φ.continuous).symm_apply_apply x) u

private theorem flattenL_unflattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    Function.RightInverse (unflattenL (p := p) hφ hL) (flattenL hφ hL) := fun v =>
  W1p.compMeasurePreservingL_compMeasurePreservingL _ _ _ _ _ _ _ _
    (fun x _ => (graphFlattening φ φ.continuous).apply_symm_apply x) v

/-- **Flattening the region above a `C¹` graph.** If `φ` is of class `C¹` with
`‖fderiv ℝ φ‖ ≤ L`, precomposition with inverse graph flattening is an isomorphism from
`W^{1,p}` of the region above the graph of `φ` onto `W^{1,p}` of the half-space `{0 < t}`, with
inverse the precomposition with `TauCeti.graphFlattening φ`. Both directions have norm at most
`1 + L` (`TauCeti.W1p.norm_normalEpigraphEquivL_le`). -/
def W1p.normalEpigraphEquivL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalEpigraph φ) p ≃L[ℝ] W1p volume (normalHalfSpace (E := E) 0) p :=
  ContinuousLinearEquiv.equivOfInverse (flattenL hφ hL) (unflattenL hφ hL)
    (unflattenL_flattenL hφ hL) (flattenL_unflattenL hφ hL)

private theorem normalEpigraphEquivL_apply_eq (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.normalEpigraphEquivL hφ hL u = flattenL hφ hL u :=
  ContinuousLinearEquiv.equivOfInverse_apply _ _ _ _ u

private theorem normalEpigraphEquivL_symm_apply_eq (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    (W1p.normalEpigraphEquivL hφ hL).symm v = unflattenL hφ hL v := by
  rw [W1p.normalEpigraphEquivL, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]

/-- Flattening multiplies the `W^{1,p}` norm by at most `1 + L`. -/
theorem W1p.norm_normalEpigraphEquivL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L)
    (u : W1p volume (normalEpigraph φ) p) :
    ‖W1p.normalEpigraphEquivL hφ hL u‖ ≤ (1 + L) * ‖u‖ := by
  rw [normalEpigraphEquivL_apply_eq]
  have h1 := (flattenL hφ hL).le_opNorm u
  have h2 := norm_flattenL_le (p := p) hφ hL
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- The inverse of flattening multiplies the `W^{1,p}` norm by at most `1 + L`. -/
theorem W1p.norm_normalEpigraphEquivL_symm_le (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    ‖(W1p.normalEpigraphEquivL hφ hL).symm v‖ ≤ (1 + L) * ‖v‖ := by
  rw [normalEpigraphEquivL_symm_apply_eq]
  have h1 := (unflattenL hφ hL).le_opNorm v
  have h2 := norm_unflattenL_le (p := p) hφ hL
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- Flattening has operator norm at most `1 + L`. -/
theorem W1p.opNorm_normalEpigraphEquivL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖(W1p.normalEpigraphEquivL (p := p) hφ hL : W1p volume (normalEpigraph φ) p →L[ℝ]
      W1p volume (normalHalfSpace (E := E) 0) p)‖ ≤ 1 + L :=
  ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg zero_le_one (nonneg_of_forall_norm_fderiv_le hL))
    (W1p.norm_normalEpigraphEquivL_le hφ hL)

/-- The inverse of flattening has operator norm at most `1 + L`. -/
theorem W1p.opNorm_normalEpigraphEquivL_symm_le (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖((W1p.normalEpigraphEquivL (p := p) hφ hL).symm :
      W1p volume (normalHalfSpace (E := E) 0) p →L[ℝ] W1p volume (normalEpigraph φ) p)‖ ≤
      1 + L :=
  ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg zero_le_one (nonneg_of_forall_norm_fderiv_le hL))
    (W1p.norm_normalEpigraphEquivL_symm_le hφ hL)

/-- The flattened function is `u ∘ (graphFlattening φ).symm`. -/
theorem W1p.value_normalEpigraphEquivL_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.value (W1p.normalEpigraphEquivL hφ hL u) =ᵐ[volume.restrict (normalHalfSpace (E := E) 0)]
      fun x => W1p.value u ((graphFlattening φ φ.continuous).symm x) := by
  rw [normalEpigraphEquivL_apply_eq]
  exact W1p.value_compMeasurePreservingL_ae _ _ _ _ u

/-- The weak gradient of the flattened function is given by the chain rule. -/
theorem W1p.gradient_normalEpigraphEquivL_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.gradient (W1p.normalEpigraphEquivL hφ hL u) =ᵐ[volume.restrict (normalHalfSpace (E := E) 0)]
      fun x => ContinuousLinearMap.adjoint (fderiv ℝ (graphFlattening φ φ.continuous).symm x)
        (W1p.gradient u ((graphFlattening φ φ.continuous).symm x)) := by
  rw [normalEpigraphEquivL_apply_eq]
  exact W1p.gradient_compMeasurePreservingL_ae _ _ _ _ u

/-- The inverse of flattening is `v ∘ graphFlattening φ`. -/
theorem W1p.value_normalEpigraphEquivL_symm_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    W1p.value ((W1p.normalEpigraphEquivL hφ hL).symm v) =ᵐ[volume.restrict (normalEpigraph φ)]
      fun x => W1p.value v (graphFlattening φ φ.continuous x) := by
  rw [normalEpigraphEquivL_symm_apply_eq]
  exact W1p.value_compMeasurePreservingL_ae _ _ _ _ v

/-- The weak gradient of the inverse of flattening is given by the chain rule. -/
theorem W1p.gradient_normalEpigraphEquivL_symm_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    W1p.gradient ((W1p.normalEpigraphEquivL hφ hL).symm v) =ᵐ[volume.restrict (normalEpigraph φ)]
      fun x => ContinuousLinearMap.adjoint (fderiv ℝ (graphFlattening φ φ.continuous) x)
        (W1p.gradient v (graphFlattening φ φ.continuous x)) := by
  rw [normalEpigraphEquivL_symm_apply_eq]
  exact W1p.gradient_compMeasurePreservingL_ae _ _ _ _ v

/-- Flattening and its inverse preserve zero boundary values. -/
theorem W1p.normalEpigraphEquivL_mem_w1p0Submodule_iff (hp : p ≠ ∞) (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.normalEpigraphEquivL hφ hL u ∈ w1p0Submodule volume (normalHalfSpace 0) p ↔
      u ∈ w1p0Submodule volume (normalEpigraph φ) p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (W1p.normalEpigraphEquivL hφ hL).symm_apply_apply u, normalEpigraphEquivL_symm_apply_eq]
    exact W1p.compMeasurePreservingL_mem_w1p0Submodule hp
      (Homeomorph.isProperMap _) _ _ _ _ h
  · rw [normalEpigraphEquivL_apply_eq]
    exact W1p.compMeasurePreservingL_mem_w1p0Submodule hp
      (Homeomorph.isProperMap _) _ _ _ _ h

end Flatten

/-! ### The trace on the graph -/

section Trace

variable {φ : C(E, ℝ)} {L : ℝ}

/-- **The trace on the graph of a `C¹` function.** For `φ` of class `C¹` with
`‖fderiv ℝ φ‖ ≤ L`, the trace of `u ∈ H¹` of the region `{φ y < t}` above the graph is the
half-space trace of the flattened function `u ∘ (graphFlattening φ).symm`. It is an element of
`L²(E)`: the graph is parametrized by `y ↦ (φ y, y)`, the image under inverse flattening of the
boundary point `(0, y)` of the half-space. -/
def W1p.normalEpigraphTrace (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalEpigraph φ) 2 →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (W1p.halfSpaceTrace 0).comp (W1p.normalEpigraphEquivL hφ hL).toContinuousLinearMap

theorem W1p.normalEpigraphTrace_apply (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L)
    (u : W1p volume (normalEpigraph φ) 2) :
    W1p.normalEpigraphTrace hφ hL u = W1p.halfSpaceTrace 0 (W1p.normalEpigraphEquivL hφ hL u) :=
  (rfl)

/-- **The trace inequality on a graph domain**: `‖Tu‖_{L²} ≤ (1 + L) ‖u‖_{H¹}`. -/
theorem W1p.norm_normalEpigraphTrace_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L)
    (u : W1p volume (normalEpigraph φ) 2) :
    ‖W1p.normalEpigraphTrace hφ hL u‖ ≤ (1 + L) * ‖u‖ :=
  (W1p.norm_halfSpaceTrace_le 0 _).trans (W1p.norm_normalEpigraphEquivL_le hφ hL u)

/-- The trace on a graph domain has operator norm at most `1 + L`. -/
theorem W1p.opNorm_normalEpigraphTrace_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖W1p.normalEpigraphTrace hφ hL‖ ≤ 1 + L :=
  ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg zero_le_one (nonneg_of_forall_norm_fderiv_le hL))
    (W1p.norm_normalEpigraphTrace_le hφ hL)

/-- **The functions of zero trace on a graph domain are those of `H¹₀`.** -/
theorem W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) 2) :
    u ∈ w1p0Submodule volume (normalEpigraph φ) 2 ↔ W1p.normalEpigraphTrace hφ hL u = 0 := by
  rw [W1p.normalEpigraphTrace_apply, ← W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero,
    W1p.normalEpigraphEquivL_mem_w1p0Submodule_iff (p := 2) ENNReal.ofNat_ne_top]

/-- **The kernel of the trace on a graph domain is `H¹₀`.** On the region above the graph of a
`C¹` function with bounded derivative, the trace `H¹ → L²(E)` vanishes exactly on the closure
of the test functions. -/
theorem W1p.ker_normalEpigraphTrace (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    LinearMap.ker (W1p.normalEpigraphTrace hφ hL).toLinearMap =
      (w1p0Submodule volume (normalEpigraph φ) 2).toSubmodule := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ClosedSubmodule.mem_toSubmodule_iff,
    W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero hφ hL]

end Trace

end TauCeti
