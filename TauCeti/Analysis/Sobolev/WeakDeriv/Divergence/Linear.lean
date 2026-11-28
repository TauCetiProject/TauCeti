/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
public import Mathlib.Analysis.InnerProductSpace.TwoDim
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Trace.Free

/-!
# The divergence of linear fields and of skew gradients

A linear vector field `T` has constant divergence `tr T`
(`ContinuousLinearMap.hasWeakDivergenceOn`), so it is solenoidal exactly when it is trace free;
in particular the identity field `x ↦ x` has divergence `dim E` (`TauCeti.hasWeakDivergenceOn_id`).

For a skew-adjoint `S` and a `C²` function `ψ`, the field `S ∇ψ` is solenoidal
(`ContDiffOn.isSolenoidalOn_apply_gradient`): its divergence is the trace pairing of `S` with the
Hessian of `ψ`, which is symmetric, and that pairing vanishes. In an oriented plane, with `S` the
rotation `J` by a right angle, this is the solenoidal field `∇^⊥ψ = J ∇ψ` of the stream function
`ψ` (`ContDiffOn.isSolenoidalOn_rightAngleRotation_gradient`), in coordinates `(-∂₂ψ, ∂₁ψ)`.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter
open scoped Gradient InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- A linear vector field `T` has constant weak divergence `tr T`. -/
theorem _root_.ContinuousLinearMap.hasWeakDivergenceOn (T : E →L[ℝ] E) :
    HasWeakDivergenceOn μ Ω T (fun _ ↦ LinearMap.trace ℝ E T) := by
  simpa only [ContinuousLinearMap.fderiv] using
    (T.contDiff (n := 1)).contDiffOn.hasWeakDivergenceOn (μ := μ) (Ω := Ω)

/-- A linear vector field is solenoidal on a nonempty open set exactly when it is trace free. -/
theorem _root_.ContinuousLinearMap.isSolenoidalOn_iff (T : E →L[ℝ] E)
    (hΩ : (Ω : Set E).Nonempty) :
    IsSolenoidalOn μ Ω T ↔ LinearMap.trace ℝ E T = 0 := by
  rw [(T.contDiff (n := 1)).contDiffOn.isSolenoidalOn_iff]
  simp only [ContinuousLinearMap.fderiv]
  exact ⟨fun h ↦ h _ hΩ.some_mem, fun h _ _ ↦ h⟩

/-- The identity vector field `x ↦ x` has weak divergence `dim E`. -/
theorem hasWeakDivergenceOn_id :
    HasWeakDivergenceOn μ Ω id (fun _ ↦ (Module.finrank ℝ E : ℝ)) := by
  simpa using (ContinuousLinearMap.id ℝ E).hasWeakDivergenceOn (μ := μ) (Ω := Ω)

/-- For a skew-adjoint `S`, one with `⟪S u, w⟫ = -⟪u, S w⟫`, the field `S ∇ψ` of a function `ψ`
that is `C²` on `Ω` is solenoidal on `Ω`. -/
theorem _root_.ContDiffOn.isSolenoidalOn_apply_gradient {ψ : E → ℝ} (hψ : ContDiffOn ℝ 2 ψ Ω)
    {S : E →L[ℝ] E} (hS : ∀ u w, ⟪S u, w⟫_ℝ = -⟪u, S w⟫_ℝ) :
    IsSolenoidalOn μ Ω (fun x ↦ S (∇ ψ x)) := by
  have hat (x : E) (hx : x ∈ (Ω : Set E)) : ContDiffAt ℝ 2 ψ x :=
    hψ.contDiffAt (Ω.isOpen.mem_nhds hx)
  have hgrad (x : E) (hx : x ∈ (Ω : Set E)) : ContDiffAt ℝ 1 (∇ ψ) x :=
    (hat x hx).gradient_right le_rfl
  have hfield : ContDiffOn ℝ 1 (fun x ↦ S (∇ ψ x)) Ω := fun x hx ↦
    (S.contDiff.contDiffAt.comp x (hgrad x hx)).contDiffWithinAt
  refine hfield.isSolenoidalOn_iff.2 fun x hx ↦ ?_
  have hd : HasFDerivAt (∇ ψ) (fderiv ℝ (∇ ψ) x) x :=
    ((hgrad x hx).differentiableAt one_ne_zero).hasFDerivAt
  -- The derivative of `S ∇ψ` is `S` composed with the Hessian of `ψ`, which is symmetric.
  have hψd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ψ y :=
    eventually_of_mem (Ω.isOpen.mem_nhds hx) fun y hy ↦
      (hat y hy).differentiableAt (by norm_num)
  have hcomp : HasFDerivAt (fun y ↦ S (∇ ψ y)) (S ∘L fderiv ℝ (∇ ψ) x) x :=
    S.hasFDerivAt.comp x hd
  rw [hcomp.fderiv, ContinuousLinearMap.toLinearMap_comp]
  exact LinearMap.trace_comp_eq_zero_of_inner_left_eq_neg hS
    (isSymmetric_of_hasFDerivAt_gradient hψd hd)

/-- **Stream functions.** In an oriented Euclidean plane, the field `∇^⊥ψ = J ∇ψ` of a function
`ψ` that is `C²` on `Ω`, with `J` the rotation by a right angle, is solenoidal on `Ω`. -/
theorem _root_.ContDiffOn.isSolenoidalOn_rightAngleRotation_gradient
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) {ψ : E → ℝ}
    (hψ : ContDiffOn ℝ 2 ψ Ω) : IsSolenoidalOn μ Ω (fun x ↦ o.rightAngleRotation (∇ ψ x)) :=
  hψ.isSolenoidalOn_apply_gradient (S := (o.rightAngleRotation : E →L[ℝ] E))
    o.inner_rightAngleRotation_swap'

end TauCeti
