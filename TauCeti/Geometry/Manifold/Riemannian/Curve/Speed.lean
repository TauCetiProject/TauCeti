/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# The derivative of the speed of a curve

For a `C²` curve `γ` in a Riemannian manifold, metric compatibility of the Levi-Civita connection
gives `(‖γ'‖²)' = 2 ⟪D_t γ', γ'⟫`. In particular a curve of locally constant speed, for instance
a unit-speed curve, has acceleration orthogonal to its velocity.

## Main results

* `ContMDiffAt.hasDerivAt_norm_sq_curveVelocity`: the derivative of the squared speed is twice the
  pairing of acceleration and velocity.
* `TauCeti.Manifold.inner_acceleration_curveVelocity_eq_zero`: at a parameter near which the speed
  is constant, the acceleration is orthogonal to the velocity.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {t : ℝ}

/-- **The derivative of the squared speed of a curve.** At a parameter where the curve `γ` is
`C²`, the function `r ↦ ‖γ'(r)‖²` has derivative `2 ⟪D_t γ', γ'⟫`. This is the derivative along
the curve; `TauCeti.Manifold.hasDerivAt_norm_sq_curveVelocity` is the derivative across a family
of curves. -/
theorem _root_.ContMDiffAt.hasDerivAt_norm_sq_curveVelocity
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t) :
    HasDerivAt (fun r ↦ ‖curveVelocity I γ r‖ ^ 2)
      (2 * ⟪acceleration (leviCivitaConnection I M) γ t, curveVelocity I γ t⟫_ℝ) t := by
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγ
  have hcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := γ)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hd := hm.hasDerivAt_inner_alongCurve (hγ.mdifferentiableAt two_ne_zero) hcoord hcoord
  convert hd using 1
  · ext r
    exact (real_inner_self_eq_norm_sq _).symm
  · simp only [← acceleration_def]
    rw [real_inner_comm (curveVelocity I γ t)]
    ring

/-- The acceleration of a curve is orthogonal to its velocity at a parameter near which the speed
is constant, for instance for a unit-speed curve. -/
theorem inner_acceleration_curveVelocity_eq_zero {c : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hc : ∀ᶠ r in 𝓝 t, ‖curveVelocity I γ r‖ = c) :
    ⟪acceleration (leviCivitaConnection I M) γ t, curveVelocity I γ t⟫_ℝ = 0 := by
  have hzero : HasDerivAt (fun r ↦ ‖curveVelocity I γ r‖ ^ 2) 0 t :=
    (hasDerivAt_const t (c ^ 2)).congr_of_eventuallyEq
      (hc.mono fun r hr ↦ by dsimp only; rw [hr])
  have hd := hγ.hasDerivAt_norm_sq_curveVelocity.unique hzero
  linarith

end TauCeti.Manifold
