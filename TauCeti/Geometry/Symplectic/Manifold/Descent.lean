/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Symplectic forms descended along submersions

Let `f : M → M'` be a surjective smooth submersion from a boundaryless manifold, and let `σ` be a
smooth two-form on `M` that is basic for `f` (`TauCeti.RoughForm.IsBasic`). Then `σ` is the
pullback of a unique smooth two-form `β` on `M'`, its descent
`TauCeti.SmoothForm.descendedForm`. This file determines when `β` is symplectic.

Since `σ_x(u, w) = β_(f x)(df_x u, df_x w)` and `df_x` is surjective, a vector `u` lies in the
kernel of `σ_x` exactly when `df_x u` lies in the kernel of `β_(f x)`. So `β` is nondegenerate
exactly when the kernel of `σ_x` is the kernel of `df_x` at every point
(`TauCeti.SmoothTwoForm.isNondegenerate_descendedForm_iff`). As descent detects closedness, `β` is
symplectic exactly when `σ` is closed and has these kernels
(`TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`).

This is the final step of symplectic reduction: on a regular level `Z = μ⁻¹(c)` of a moment map
with free and proper stabilizer action, the restriction of the symplectic form is closed, basic for
the orbit projection `Z → Z / G_c`, and has kernel the tangent spaces of the orbits, which are the
kernels of the derivative of the projection; its descent is the reduced symplectic form.

## Main results

* `TauCeti.SmoothTwoForm.eval₂_descendedForm_mfderiv`: the descent evaluates on images under the
  derivative of `f` as the form.
* `TauCeti.SmoothTwoForm.isNondegenerate_descendedForm_iff`: the descent of a basic two-form is
  nondegenerate exactly when the kernel of the form is the kernel of the derivative of `f`.
* `TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`: the descent is symplectic exactly when
  the form is moreover closed.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the Marsden–Weinstein–Meyer theorem: the reduced form as the
  descent of the restricted form).
* Jerrold Marsden and Alan Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports
  on Mathematical Physics 5 (1974), 121–130.
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] [I.Boundaryless]
  {f : M → M'} {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f} {σ : SmoothTwoForm I M}
  {hσ : RoughForm.IsBasic (V := ℝ) I' f σ.1}

/-- The descent `β` of a basic two-form `σ` evaluates on images under the derivative of `f` as
`σ`: `σ_x(u, w) = β_(f x)(df_x u, df_x w)`. -/
theorem eval₂_descendedForm_mfderiv (x : M) (u w : TangentSpace I x) :
    SmoothBundleForm.eval₂ (SmoothForm.descendedForm hf hsurj σ hσ) (f x)
        (mfderiv I I' f x u) (mfderiv I I' f x w) =
      SmoothBundleForm.eval₂ σ x u w := by
  rw [← SmoothForm.eval₂_mpullback f hf.contMDiff, SmoothForm.mpullback_descendedForm]

/-- **The descended form is nondegenerate exactly when the kernels match.** The descent of a
two-form `σ` basic for a surjective smooth submersion `f` is nondegenerate exactly when, at every
point `x`, the kernel of `σ_x` is the kernel of the derivative of `f` at `x`. -/
theorem isNondegenerate_descendedForm_iff :
    IsNondegenerate (SmoothForm.descendedForm hf hsurj σ hσ) ↔
      ∀ x, LinearMap.ker (σ.bilinFormAt x) = (mfderiv I I' f x).ker := by
  have hdf (x : M) : Surjective (mfderiv I I' f x) := hf.surjective_mfderiv (by simp) x
  have key := eval₂_descendedForm_mfderiv (hf := hf) (hsurj := hsurj) (hσ := hσ)
  rw [isNondegenerate_iff_separatingLeft]
  refine ⟨fun hβ x ↦ Submodule.ext fun v ↦ ?_, fun hker y v hv ↦ ?_⟩
  · rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine ⟨fun hv ↦ hβ (f x) _ fun u ↦ ?_, fun hv ↦ LinearMap.ext fun w ↦ ?_⟩
    · obtain ⟨w, rfl⟩ := hdf x u
      rw [key, ← SmoothForm.bilinFormAt_apply, hv, LinearMap.zero_apply]
    · rw [SmoothForm.bilinFormAt_apply, ← key, hv,
        ← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  · obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨v, rfl⟩ := hdf x v
    have hvσ : v ∈ LinearMap.ker (σ.bilinFormAt x) :=
      LinearMap.ext fun w ↦ by
        rw [SmoothForm.bilinFormAt_apply, ← key, LinearMap.zero_apply]
        exact hv _
    rw [hker x, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hvσ
    exact hvσ

/-- **Symplectic descent.** The descent of a two-form `σ` basic for a surjective smooth
submersion `f` is symplectic exactly when `σ` is closed and, at every point `x`, the kernel of
`σ_x` is the kernel of the derivative of `f` at `x`. -/
theorem isSymplectic_descendedForm_iff :
    IsSymplectic (SmoothForm.descendedForm hf hsurj σ hσ) ↔
      SmoothForm.IsClosed σ ∧
        ∀ x, LinearMap.ker (σ.bilinFormAt x) = (mfderiv I I' f x).ker := by
  rw [← isNondegenerate_descendedForm_iff (hf := hf) (hsurj := hsurj) (hσ := hσ),
    ← SmoothForm.isClosed_descendedForm_iff (hf := hf) (hsurj := hsurj) (hα := hσ)]
  exact ⟨fun h ↦ ⟨h.isClosed, h.isNondegenerate⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

end TauCeti.SmoothTwoForm
