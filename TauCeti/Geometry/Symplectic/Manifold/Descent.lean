/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Descent of symplectic forms along submersions

Let `f : M → M'` be a surjective smooth submersion of a boundaryless manifold. A smooth two-form `α`
on `M` is the pullback of a symplectic form on `M'` exactly when

* `α` is closed,
* `α` is basic for `f` (`TauCeti.RoughForm.IsBasic`): its values only depend on the images of
  tangent vectors under `f` and its derivative, and
* at every point `x`, the kernel of `α_x` is exactly the kernel of the derivative of `f` at `x`

(`Manifold.IsSubmersion.exists_isSymplectic_mpullback_eq_iff`). The symplectic form is then unique,
since pullback along `f` is injective: it is the descent
`TauCeti.SmoothForm.descendAlongSubmersion` of `α`
(`TauCeti.SmoothForm.eq_descendAlongSubmersion_iff`).

This is the final step of symplectic reduction (Marsden–Weinstein–Meyer). For a level set `Z` of
a moment map on which the stabilizer of the level acts freely and properly, the restriction of the
symplectic form to `Z` is closed and basic for the orbit projection `Z → Z / G`, with kernel the
tangent spaces of the orbits; the reduced symplectic form is its descent.

The kernel condition is a statement about the pullback alone. For a surjective map with
surjective derivatives, a two-form `σ` on `M'` is nondegenerate exactly when the kernel of its
pullback at every point is the kernel of the derivative
(`TauCeti.SmoothTwoForm.isNondegenerate_iff_ker_mpullback_eq_ker_mfderiv`); closedness descends
by `Manifold.IsSubmersion.isClosed_mpullback_iff`.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_iff_ker_mpullback_eq_ker_mfderiv`: nondegeneracy of a
  two-form read off from its pullback.
* `TauCeti.SmoothForm.isSymplectic_descendAlongSubmersion_iff`: the descent of a basic two-form is
  symplectic exactly when the form is closed with kernel the kernel of the derivative.
* `Manifold.IsSubmersion.exists_isSymplectic_mpullback_eq_iff`: the two-forms which are pullbacks
  of symplectic forms along a surjective submersion.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 23 (the Marsden–Weinstein–Meyer theorem).
* Jerrold E. Marsden and Alan Weinstein, *Reduction of symplectic manifolds with symmetry*,
  Rep. Math. Phys. 5 (1974), 121–130.
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] {f : M → M'}

namespace TauCeti.SmoothTwoForm

/-- For a surjective smooth map `f` whose derivative is surjective at every point, a two-form `σ`
on `M'` is nondegenerate exactly when, at every point `x` of `M`, the vectors annihilating every
vector under the pullback `f^* σ` are exactly the kernel of the derivative of `f` at `x`. -/
theorem isNondegenerate_iff_ker_mpullback_eq_ker_mfderiv (hfs : ContMDiff I I' ∞ f)
    (hsurj : Surjective f) (hf : ∀ x, Surjective (mfderiv I I' f x)) {σ : SmoothTwoForm I' M'} :
    σ.IsNondegenerate ↔ ∀ (x : M) (v : TangentSpace I x),
      (∀ w, (SmoothForm.mpullback f hfs σ).eval₂ x v w = 0) ↔ mfderiv I I' f x v = 0 := by
  simp only [SmoothForm.eval₂_mpullback]
  rw [isNondegenerate_iff_separatingLeft]
  refine ⟨fun hσ x v ↦ ⟨fun hv ↦ hσ (f x) _ fun w ↦ ?_, fun hv w ↦ ?_⟩, fun hker y v hv ↦ ?_⟩
  · -- Every tangent vector at `f x` is the image of one at `x`.
    obtain ⟨u, rfl⟩ := hf x w
    exact hv u
  · rw [hv, ← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply]
  · -- Lift `v` to a tangent vector at a preimage of `y`; it lies in the kernel of the pullback.
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨u, rfl⟩ := hf x v
    exact (hker x u).mp fun w ↦ hv _

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothForm

variable [I.Boundaryless] {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f}
  {α : SmoothTwoForm I M} {hα : RoughForm.IsBasic (V := ℝ) I' f α.1}

/-- The descent of a basic two-form `α` along a surjective smooth submersion is symplectic exactly
when `α` is closed and, at every point, the kernel of `α` is the kernel of the derivative of the
submersion. -/
theorem isSymplectic_descendAlongSubmersion_iff :
    SmoothTwoForm.IsSymplectic (descendAlongSubmersion hf hsurj α hα) ↔
      α.IsClosed ∧ ∀ (x : M) (v : TangentSpace I x),
        (∀ w, α.eval₂ x v w = 0) ↔ mfderiv I I' f x v = 0 := by
  have hnd := SmoothTwoForm.isNondegenerate_iff_ker_mpullback_eq_ker_mfderiv
    (σ := descendAlongSubmersion hf hsurj α hα) hf.contMDiff hsurj
    fun x ↦ (hf.hasRightInverse_mfderiv (by simp) x).surjective
  rw [mpullback_descendAlongSubmersion] at hnd
  rw [← isClosed_descendAlongSubmersion_iff (hf := hf) (hsurj := hsurj) (hα := hα), ← hnd]
  exact ⟨fun h ↦ ⟨h.isClosed, h.isNondegenerate⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end TauCeti.SmoothForm

namespace Manifold.IsSubmersion

variable [I.Boundaryless]

/-- **Descent of symplectic forms along a submersion.** For a surjective smooth submersion `f` of a
boundaryless manifold, a smooth two-form `α` on `M` is the pullback of a symplectic form on `M'`
exactly when `α` is closed, basic for `f`, and at every point has kernel the kernel of the
derivative of `f`. The symplectic form is unique, by
`TauCeti.SmoothForm.eq_descendAlongSubmersion_iff`. -/
theorem exists_isSymplectic_mpullback_eq_iff (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    {α : TauCeti.SmoothTwoForm I M} :
    (∃ σ : TauCeti.SmoothTwoForm I' M', σ.IsSymplectic ∧
        TauCeti.SmoothForm.mpullback f hf.contMDiff σ = α) ↔
      α.IsClosed ∧ TauCeti.RoughForm.IsBasic (V := ℝ) I' f α.1 ∧
        ∀ (x : M) (v : TangentSpace I x), (∀ w, α.eval₂ x v w = 0) ↔ mfderiv I I' f x v = 0 := by
  refine ⟨fun ⟨σ, hσ, hσα⟩ ↦ ⟨?_, ?_, ?_⟩, fun ⟨hcl, hα, hker⟩ ↦ ?_⟩
  · exact hσα ▸ hσ.isClosed.mpullback f hf.contMDiff
  · exact (hf.exists_smoothForm_mpullback_eq_iff hsurj).mp ⟨σ, hσα⟩
  · rw [← hσα]
    exact (TauCeti.SmoothTwoForm.isNondegenerate_iff_ker_mpullback_eq_ker_mfderiv hf.contMDiff
      hsurj fun x ↦ (hf.hasRightInverse_mfderiv (by simp) x).surjective).mp hσ.isNondegenerate
  · exact ⟨_, TauCeti.SmoothForm.isSymplectic_descendAlongSubmersion_iff.mpr ⟨hcl, hker⟩,
      TauCeti.SmoothForm.mpullback_descendAlongSubmersion (hf := hf) (hsurj := hsurj) (hα := hα)⟩

end Manifold.IsSubmersion
