/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Calculus.GraphFlattening.Direction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Hyperplane
import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace

/-!
# Differentiability and extension up to a graph

Let `ν` be a unit vector of a real inner product space `E` and let `γ : E → ℝ` be invariant under
translation along `ν`. The closed region `{x | γ x ≤ ⟪x, ν⟫}` lies on or above the graph of `γ`
over the hyperplane `ν^⊥`, and the shear `φ = TauCeti.shearAlong γ ν`, `φ y = y + γ y ν`, maps the
closed half-space `{0 ≤ ⟪y, ν⟫}` onto it, with inverse the shear by `-γ`. This file transports two
facts about a half-space to such a region, near a point of an open set `V`.

* **Differentiability up to the graph**
  (`TauCeti.hasFDerivWithinAt_setOf_le_inner_of_hasFDerivAt`). If `γ` is `C¹`, `f` is continuous
  on `V ∩ {γ ≤ ⟪·, ν⟫}`, differentiable at the points of `V` strictly above the graph with
  derivative `f'`, and `f'` is continuous on `V ∩ {γ ≤ ⟪·, ν⟫}`, then `f` has derivative `f' x`
  within the closed region at every point `x` of `V` on or above the graph. After the shear, this
  is Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv` on a convex half-ball.
* **Extension across the graph**
  (`TauCeti.exists_contDiff_eventually_eq_of_contDiffOn_setOf_le_inner`). If `γ` is `Cᵏ` and `u`
  is `Cᵏ` on `V ∩ {γ ≤ ⟪·, ν⟫}`, then near every point `z` of `V` on the graph, `u` agrees on the
  closed region with a map that is `Cᵏ` on all of `E`. After the shear and a linear identification
  `E ≃ ℝ × ν^⊥`, this is the higher-order reflection across a hyperplane,
  `TauCeti.HalfSpaceExtension.exists_local_contDiff_extension_halfSpace`.

These are the local steps by which a function on the closure of a domain with `C^k` boundary
is shown to be `C^k` up to the boundary, and then to be the restriction of a `C^k` function on the
whole space.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 6.37 (extension of `C^{k,α}` functions from a `C^{k,α}` domain).
* M. R. Hestenes, *Extension of the range of a differentiable function*, Duke Math. J. 8 (1941),
  183–192.
-/

public section

open Set Filter Metric
open scoped Topology InnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {γ : E → ℝ} {ν : E}

/-- The shear `shearAlong γ ν` carries the closed half-space `{0 ≤ ⟪y, ν⟫}` into the closed region
on or above the graph of `γ`. -/
private theorem le_inner_shearAlong (hν : ‖ν‖ = 1) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    {y : E} (hy : 0 ≤ ⟪y, ν⟫_ℝ) : γ (shearAlong γ ν y) ≤ ⟪shearAlong γ ν y, ν⟫_ℝ := by
  have := real_inner_shearAlong_sub hν hγν y
  linarith

/-- The inverse shear `shearAlong (-γ) ν` lowers the height `⟪x, ν⟫` by `γ x`. -/
private theorem inner_shearAlong_neg (hν : ‖ν‖ = 1) (x : E) :
    ⟪shearAlong (-γ) ν x, ν⟫_ℝ = ⟪x, ν⟫_ℝ - γ x := by
  rw [real_inner_shearAlong hν, Pi.neg_apply, sub_eq_add_neg]

/-- **Differentiability up to a graph.** Let `‖ν‖ = 1`, let `γ` be `C¹` and invariant along `ν`,
and let `V` be open. Suppose that `f` and `f'` are continuous on the part
`V ∩ {γ ≤ ⟪·, ν⟫}` of `V` on or above the graph of `γ`, and that `f` has derivative `f' x` at every
point `x` of `V` strictly above the graph. Then `f` has derivative `f' x` within the closed region
`{γ ≤ ⟪·, ν⟫}` at every point `x` of `V` on or above the graph. This is the graph form of
Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv` for convex sets. -/
theorem hasFDerivWithinAt_setOf_le_inner_of_hasFDerivAt (hν : ‖ν‖ = 1) (hγ : ContDiff ℝ 1 γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {V : Set E} (hV : IsOpen V) {f : E → F}
    {f' : E → E →L[ℝ] F} (hf : ContinuousOn f (V ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}))
    (hf' : ContinuousOn f' (V ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}))
    (hd : ∀ x ∈ V, γ x < ⟪x, ν⟫_ℝ → HasFDerivAt f (f' x) x) {x : E} (hxV : x ∈ V)
    (hx : γ x ≤ ⟪x, ν⟫_ℝ) : HasFDerivWithinAt f (f' x) {x | γ x ≤ ⟪x, ν⟫_ℝ} x := by
  set φ := shearAlong γ ν
  set ψ := shearAlong (-γ) ν
  have hγd : Differentiable ℝ γ := hγ.differentiable one_ne_zero
  have hφc : Continuous φ := (contDiff_shearAlong hγ).continuous
  have hφψ (y : E) : φ (ψ y) = y := shearAlong_shearAlong_neg hγν y
  -- The derivative `S y = id + Dγ(y) ν` of the shear depends continuously on `y`.
  set S : E → E →L[ℝ] E := fun y => ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight ν
  have hφd (y : E) : HasFDerivAt φ (S y) y := hasFDerivAt_shearAlong (hγd y)
  have hS : Continuous S := by
    rw [show S = fderiv ℝ φ from funext fun y => (hφd y).fderiv.symm]
    exact (contDiff_shearAlong hγ).continuous_fderiv one_ne_zero
  -- After the shear, the region is the half-space `ℓ ≥ 0`, `ℓ y = ⟪y, ν⟫`.
  set ℓ := innerSL ℝ ν
  have hℓ (y : E) : ℓ y = ⟪y, ν⟫_ℝ := by rw [innerSL_apply_apply, real_inner_comm]
  have hℓ0 : ℓ ≠ 0 := fun h => by
    simpa [hℓ, real_inner_self_eq_norm_sq, hν] using congrArg (fun L : E →L[ℝ] ℝ => L ν) h
  have hmaps : MapsTo φ (φ ⁻¹' V ∩ {y | 0 ≤ ℓ y}) (V ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}) := fun y hy =>
    ⟨hy.1, le_inner_shearAlong hν hγν (hℓ y ▸ mem_ofPred.1 hy.2)⟩
  have hflat := hasFDerivWithinAt_setOf_nonneg_of_hasFDerivAt hℓ0 (hV.preimage hφc)
    (hf.comp hφc.continuousOn hmaps) ((hf'.comp hφc.continuousOn hmaps).clm_comp hS.continuousOn)
    (fun y hy hy0 => (hd (φ y) hy (by
      have := real_inner_shearAlong_sub hν hγν y
      rw [hℓ] at hy0
      linarith)).comp y (hφd y))
    (x := ψ x) (by rw [mem_preimage, hφψ]; exact hxV)
    (by rw [hℓ, inner_shearAlong_neg hν]; linarith)
  -- Pull back along `ψ`, whose derivative inverts `S (ψ x)`.
  have hψd : HasFDerivAt ψ (ContinuousLinearMap.id ℝ E + (fderiv ℝ (-γ) x).smulRight ν) x :=
    hasFDerivAt_shearAlong (hγd x).neg
  have hinv : (S (ψ x)).comp (ContinuousLinearMap.id ℝ E + (fderiv ℝ (-γ) x).smulRight ν) =
      ContinuousLinearMap.id ℝ E := by
    have h := (hφd (ψ x)).comp x hψd
    rw [show φ ∘ ψ = id from funext hφψ] at h
    exact h.unique (hasFDerivAt_id x)
  have hcomp := hflat.comp x hψd.hasFDerivWithinAt (s := {x | γ x ≤ ⟪x, ν⟫_ℝ}) fun y hy => by
    rw [mem_ofPred_eq, hℓ, inner_shearAlong_neg hν]
    linarith [mem_ofPred.1 hy]
  rw [Function.comp_apply, hφψ, ContinuousLinearMap.comp_assoc, hinv,
    ContinuousLinearMap.comp_id, show (f ∘ φ) ∘ ψ = f from funext fun y => by simp [hφψ]] at hcomp
  exact hcomp

/-- **Extension across a graph.** Let `‖ν‖ = 1`, let `γ` be `Cᵏ` and invariant along `ν`, and let
`u` be `Cᵏ` on the part `V ∩ {γ ≤ ⟪·, ν⟫}` of an open set `V` on or above the graph of `γ`. Then
near every point `z` of `V` on the graph, `u` agrees on the closed region `{γ ≤ ⟪·, ν⟫}` with a map
that is `Cᵏ` on all of `E`. In finite dimension this is the higher-order reflection of Hestenes,
`TauCeti.HalfSpaceExtension.exists_local_contDiff_extension_halfSpace`, read through the shear
`shearAlong γ ν` that flattens the graph. -/
theorem exists_contDiff_eventually_eq_of_contDiffOn_setOf_le_inner [FiniteDimensional ℝ E]
    {k : ℕ} (hν : ‖ν‖ = 1) (hγ : ContDiff ℝ k γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    {V : Set E} (hV : IsOpen V) {u : E → F} (hu : ContDiffOn ℝ k u (V ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ}))
    {z : E} (hzV : z ∈ V) (hz : ⟪z, ν⟫_ℝ = γ z) :
    ∃ g : E → F, ContDiff ℝ k g ∧ ∀ᶠ x in 𝓝 z, γ x ≤ ⟪x, ν⟫_ℝ → g x = u x := by
  -- The coordinates `E ≃ ℝ × ν^⊥`, `x ↦ (⟪ν, x⟫, x - ⟪ν, x⟫ ν)`.
  have hright : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℝ ν) (innerSL ℝ ν) :=
    fun t => by simp [hν]
  set T := ContinuousLinearEquiv.equivOfRightInverse _ _ hright
  have hT (x : E) : (T x).1 = ⟪x, ν⟫_ℝ := by
    rw [ContinuousLinearEquiv.fst_equivOfRightInverse, innerSL_apply_apply, real_inner_comm]
  -- `χ` maps the closed upper half-space onto the closed region, with inverse `ψ`.
  set χ := fun y => shearAlong γ ν (T.symm y)
  set ψ := fun x => T (shearAlong (-γ) ν x)
  have hχψ (x : E) : χ (ψ x) = x := by
    simp only [χ, ψ, ContinuousLinearEquiv.symm_apply_apply, shearAlong_shearAlong_neg hγν]
  have hψ1 (x : E) : (ψ x).1 = ⟪x, ν⟫_ℝ - γ x := by
    rw [hT, inner_shearAlong_neg hν]
  have hχ1 (y) : ⟪χ y, ν⟫_ℝ - γ (χ y) = y.1 := by
    rw [real_inner_shearAlong_sub hν hγν, ← hT, ContinuousLinearEquiv.apply_symm_apply]
  have hχc : ContDiff ℝ k χ := (contDiff_shearAlong hγ).comp T.symm.contDiff
  have hψc : ContDiff ℝ k ψ := T.contDiff.comp (contDiff_shearAlong hγ.neg)
  have hv : ContDiffOn ℝ k (u ∘ χ)
      (HalfSpaceExtension.upperHalfSpace _ ∩ χ ⁻¹' V) := by
    refine hu.comp hχc.contDiffOn fun y hy => ⟨hy.2, ?_⟩
    have h1 := hχ1 y
    have h2 : 0 ≤ y.1 := HalfSpaceExtension.mem_upperHalfSpace.1 hy.1
    rw [mem_ofPred_eq]
    linarith
  have hψz : ψ z = (0, (ψ z).2) := Prod.ext (by rw [hψ1, hz, sub_self]) rfl
  obtain ⟨G, hG, hGv⟩ := HalfSpaceExtension.exists_local_contDiff_extension_halfSpace k (u ∘ χ)
    (hV.preimage hχc.continuous) hv (ψ z).2 (by rw [← hψz, mem_preimage, hχψ]; exact hzV)
  refine ⟨G ∘ ψ, hG.comp hψc, ?_⟩
  have hlim : Tendsto ψ (𝓝 z) (𝓝 ((0 : ℝ), (ψ z).2)) := hψz ▸ hψc.continuous.tendsto z
  filter_upwards [hlim.eventually hGv] with x hx hxγ
  have h := hx (by rw [hψ1]; linarith)
  simpa only [Function.comp_apply, hχψ] using h

end TauCeti
