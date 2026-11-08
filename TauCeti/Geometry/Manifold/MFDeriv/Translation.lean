/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Dynamics.Flow.Translation
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

On the cylinder `ℝ × ℝ`, with coordinates `(s, t)`, a constant linear combination
`a ∂_s u + b ∂_t u` of the two partial derivatives is the derivative of `u` in the direction
`(a, b)`. If it vanishes identically, `u` is invariant under all translations along `(a, b)`. For
a map with a constant end, a point `x` with `u (s, t) → x` as `s → -∞` uniformly in `t`, such an
invariance with `a ≠ 0` makes `u` constant, and one with `a = 0` and `b ≠ 0` makes it invariant
under every time rotation. So for a map with a constant end which is not invariant under every time
rotation, `∂_s u` and `∂_t u` are linearly independent as global sections: no constant combination
of them vanishes except the trivial one (`MDifferentiable.eq_zero_of_forall_mfderiv_apply_eq_zero`).
This is the infinitesimal form of the computation of the stabilizer of such a map under translations
and rotations, `TauCeti.exists_periodic_iff_of_tendsto_atBot`.

## Main results

* `mfderiv_comp_add_right`: the derivative of a translate of `u` is the translate of the
  derivative of `u`.
* `MDifferentiable.forall_periodic_smul_iff`: `u` is invariant under the translations along `v`
  exactly when its derivative in the direction `v` vanishes.
* `MDifferentiable.eq_zero_of_forall_mfderiv_apply_eq_zero`: for a map on the cylinder with a
  constant end which is not invariant under every time rotation, a direction in which the
  derivative vanishes everywhere is zero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
-/

public section

open Filter Function Topology
open scoped Manifold

namespace MDifferentiable

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

omit [IsManifold I 1 M] in
/-- The derivative of a translate `w ↦ u (w + c)` at `z` is the derivative of `u` at `z + c`. -/
theorem _root_.mfderiv_comp_add_right {u : E → M} {z c : E}
    (hu : MDifferentiableAt 𝓘(ℝ, E) I u (z + c)) :
    mfderiv 𝓘(ℝ, E) I (fun w ↦ u (w + c)) z = mfderiv 𝓘(ℝ, E) I u (z + c) :=
  (hu.hasMFDerivAt.comp z ((hasFDerivAt_id z).add_const c).hasMFDerivAt).mfderiv

omit [IsManifold I 1 M] in
/-- The derivative of `u` along the line `t ↦ z + t • v` is the derivative of `u` in the direction
`v`. -/
private theorem hasMFDerivAt_comp_add_smul {u : E → M} (hu : MDifferentiable 𝓘(ℝ, E) I u)
    (z v : E) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ u (z + s • v)) t
      ((mfderiv 𝓘(ℝ, E) I u (z + t • v)).comp (ContinuousLinearMap.toSpanSingleton ℝ v)) := by
  have hℓ : HasFDerivAt (fun s : ℝ ↦ z + s • v) (ContinuousLinearMap.toSpanSingleton ℝ v) t := by
    simpa using (((hasDerivAt_id t).smul_const v).const_add z).hasFDerivAt
  exact (hu (z + t • v)).hasMFDerivAt.comp t hℓ.hasMFDerivAt

omit [IsManifold I 1 M] in
/-- The derivative of `t ↦ u (z + t • v)` at `t`, evaluated on `1`, is the derivative of `u` at
`z + t • v` in the direction `v`. -/
private theorem mfderiv_comp_add_smul_apply_one {u : E → M} (hu : MDifferentiable 𝓘(ℝ, E) I u)
    (z v : E) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ u (z + s • v)) t (1 : ℝ) =
      mfderiv 𝓘(ℝ, E) I u (z + t • v) v := by
  rw [(hasMFDerivAt_comp_add_smul hu z v t).mfderiv]
  exact congrArg (mfderiv 𝓘(ℝ, E) I u (z + t • v)) (one_smul ℝ v)

/-- **Translation invariance from a vanishing directional derivative.** A differentiable map `u`
from a real normed space to a manifold satisfies `u (z + t • v) = u z` for all `t` and `z` exactly
when its derivative in the direction `v` vanishes everywhere. -/
theorem forall_periodic_smul_iff {u : E → M} (hu : MDifferentiable 𝓘(ℝ, E) I u) {v : E} :
    (∀ t : ℝ, Periodic u (t • v)) ↔ ∀ z, mfderiv 𝓘(ℝ, E) I u z v = 0 := by
  constructor
  · intro h z
    have h1 := mfderiv_comp_add_smul_apply_one hu z v 0
    rw [show (fun s : ℝ ↦ u (z + s • v)) = fun _ ↦ u z from funext fun s ↦ h s z,
      mfderiv_const] at h1
    rw [zero_smul, add_zero] at h1
    -- `0 1` is the value of the zero map, definitionally `0`.
    exact h1.symm
  · intro h t z
    -- The map `s ↦ u (z + s • v)` has zero derivative, hence is constant on `ℝ`.
    have hzero (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ u (z + s • v)) s = 0 := by
      apply ContinuousLinearMap.ext_ring
      -- The right side `0 1` is the value of the zero map, definitionally `0`.
      exact (mfderiv_comp_add_smul_apply_one hu z v s).trans (h _)
    simpa using MDifferentiable.apply_eq_of_mfderiv_eq_zero
      (fun s ↦ (hasMFDerivAt_comp_add_smul hu z v s).mdifferentiableAt) hzero t 0

/-- **Independence of `∂_s u` and `∂_t u` for a cylinder with a constant end.** Let `u` be a
differentiable map on the cylinder `ℝ × ℝ` tending to `x` as `s → -∞` uniformly in `t`, and not
invariant under every time rotation `(s, t) ↦ (s, t + θ)`. If the derivative of `u` in the
direction `w = (a, b)`, that is `a ∂_s u + b ∂_t u`, vanishes everywhere, then `w = 0`. -/
theorem eq_zero_of_forall_mfderiv_apply_eq_zero [T2Space M] {u : ℝ × ℝ → M}
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u) {x : M} (hx : Tendsto u (atBot ×ˢ ⊤) (𝓝 x))
    (hθ : ∃ θ : ℝ, ¬Periodic u (0, θ)) {w : ℝ × ℝ}
    (hw : ∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z w = 0) : w = 0 := by
  have hper := hu.forall_periodic_smul_iff.2 hw
  obtain ⟨θ, hθ⟩ := hθ
  -- A period with nonzero `s`-component makes `u` constant, hence time-invariant.
  have hw₁ : w.1 = 0 := by
    by_contra hw₁
    have h := hper 1
    rw [one_smul] at h
    exact hθ fun z ↦ by rw [h.eq_of_tendsto_atBot hw₁ hx, h.eq_of_tendsto_atBot hw₁ hx]
  -- Then the multiples of `w` are time rotations, and all of them would be periods.
  have hw₂ : w.2 = 0 := by
    by_contra hw₂
    refine hθ ?_
    convert hper (θ / w.2) using 1
    ext <;> simp [hw₁, div_mul_cancel₀ θ hw₂]
  exact Prod.ext hw₁ hw₂

end MDifferentiable
