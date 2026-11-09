/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Translation invariance from a vanishing directional derivative

A differentiable map `u` from a real normed space `E` to a manifold is invariant under every
translation along a vector `v`, `u (z + t • v) = u z`, exactly when its derivative in the direction
`v` vanishes everywhere (`MDifferentiable.forall_periodic_smul_iff`). The derivative of
`t ↦ u (z + t • v)` is the derivative of `u` in the direction `v`, and a map from `ℝ` with zero
derivative is constant.

## Main results

* `MDifferentiableAt.mfderiv_comp_add_right`: the derivative of a translate of `u` is the
  translate of the derivative of `u`.
* `MDifferentiableAt.hasMFDerivAt_comp_add_smul`,
  `MDifferentiableAt.mfderiv_comp_add_smul_apply_one`: the derivative of `u` along the line
  `t ↦ z + t • v` is the derivative of `u` in the direction `v`.
* `MDifferentiable.forall_periodic_smul_iff`: `u` is invariant under the translations along `v`
  exactly when its derivative in the direction `v` vanishes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
-/

public section

open Filter Function Topology
open scoped Manifold

namespace MDifferentiableAt

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The derivative of a translate `w ↦ u (w + c)` at `z` is the derivative of `u` at `z + c`. -/
theorem mfderiv_comp_add_right {u : E → M} {z c : E}
    (hu : MDifferentiableAt 𝓘(ℝ, E) I u (z + c)) :
    mfderiv 𝓘(ℝ, E) I (fun w ↦ u (w + c)) z = mfderiv 𝓘(ℝ, E) I u (z + c) :=
  (hu.hasMFDerivAt.comp z ((hasFDerivAt_id z).add_const c).hasMFDerivAt).mfderiv

/-- The derivative of `u` along the line `s ↦ z + s • v` is the derivative of `u` in the direction
`v`. -/
theorem hasMFDerivAt_comp_add_smul {u : E → M} {z v : E} {t : ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, E) I u (z + t • v)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ u (z + s • v)) t
      ((mfderiv 𝓘(ℝ, E) I u (z + t • v)).comp (ContinuousLinearMap.toSpanSingleton ℝ v)) := by
  have hℓ : HasFDerivAt (fun s : ℝ ↦ z + s • v) (ContinuousLinearMap.toSpanSingleton ℝ v) t := by
    simpa using (((hasDerivAt_id t).smul_const v).const_add z).hasFDerivAt
  exact hu.hasMFDerivAt.comp t hℓ.hasMFDerivAt

/-- The derivative of `s ↦ u (z + s • v)` at `t`, evaluated on `1`, is the derivative of `u` at
`z + t • v` in the direction `v`. -/
theorem mfderiv_comp_add_smul_apply_one {u : E → M} {z v : E} {t : ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, E) I u (z + t • v)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ u (z + s • v)) t (1 : ℝ) =
      mfderiv 𝓘(ℝ, E) I u (z + t • v) v := by
  rw [hu.hasMFDerivAt_comp_add_smul.mfderiv]
  exact congrArg (mfderiv 𝓘(ℝ, E) I u (z + t • v)) (one_smul ℝ v)

end MDifferentiableAt

namespace MDifferentiable

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **Translation invariance from a vanishing directional derivative.** A differentiable map `u`
from a real normed space to a manifold satisfies `u (z + t • v) = u z` for all `t` and `z` exactly
when its derivative in the direction `v` vanishes everywhere. -/
theorem forall_periodic_smul_iff {u : E → M} (hu : MDifferentiable 𝓘(ℝ, E) I u) {v : E} :
    (∀ t : ℝ, Periodic u (t • v)) ↔ ∀ z, mfderiv 𝓘(ℝ, E) I u z v = 0 := by
  constructor
  · intro h z
    have h1 := (hu (z + (0 : ℝ) • v)).mfderiv_comp_add_smul_apply_one
    rw [show (fun s : ℝ ↦ u (z + s • v)) = fun _ ↦ u z from funext fun s ↦ h s z,
      mfderiv_const, zero_smul, add_zero] at h1
    exact h1.symm.trans (zero_apply _)
  · intro h t z
    -- The map `s ↦ u (z + s • v)` has zero derivative, hence is constant on `ℝ`.
    have hzero (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ u (z + s • v)) s = 0 := by
      apply ContinuousLinearMap.ext_ring
      exact ((hu (z + s • v)).mfderiv_comp_add_smul_apply_one.trans (h _)).trans
        (zero_apply (F := TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (u (z + s • v))) _).symm
    simpa using MDifferentiable.apply_eq_of_mfderiv_eq_zero
      (fun s ↦ (hu (z + s • v)).hasMFDerivAt_comp_add_smul.mdifferentiableAt) hzero t 0

end MDifferentiable
