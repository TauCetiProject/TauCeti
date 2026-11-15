/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Fixed points of maps preserving a two-form

Let `f : M → M` be a smooth self-map of a manifold pulling a two-form `σ` back to itself,
`f^* σ = σ`. At a fixed point `x` of `f` the differential of `f` is an endomorphism of `T_x M`,
the fixed-point derivative `TauCeti.fixedPointDerivative`, and the invariance of `σ` says that it
is an isometry of the alternating bilinear form `σ_x`
(`TauCeti.SmoothTwoForm.isIsometry_fixedPointDerivative`). When `σ` is nondegenerate, an isometry
of `σ_x` has determinant one, so the fixed-point derivative has determinant one
(`TauCeti.SmoothTwoForm.det_fixedPointDerivative_eq_one`).

Applied to the iterate `f^[d]` at a periodic point of period `d`, which preserves `σ` as well
(`TauCeti.SmoothForm.mpullback_iterate_eq_self`), this says that the linearized return map of a
periodic orbit of a symplectomorphism has determinant one
(`TauCeti.SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one`). For an area-preserving
diffeomorphism of a surface the return maps are therefore `2 × 2` matrices of determinant one,
whose fixed-point indices `sgn det (1 - P)` are governed by the trace alone.

## Main results

* `TauCeti.SmoothTwoForm.isIsometry_fixedPointDerivative`: the fixed-point derivative of a map
  preserving `σ` is an isometry of `σ_x`.
* `TauCeti.SmoothTwoForm.det_fixedPointDerivative_eq_one`: for nondegenerate `σ` it has
  determinant one.
* `TauCeti.SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one`: the return map of a periodic
  orbit of a map preserving a nondegenerate `σ` has determinant one.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1.
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {f : M → M}

/-- At a fixed point `x` of a smooth map `f` with `f^* σ = σ`, the fixed-point derivative of `f`
is an isometry of the bilinear form `σ_x`. -/
theorem isIsometry_fixedPointDerivative (hf : ContMDiff I I ∞ f)
    (hσ : SmoothForm.mpullback f hf σ = σ) (x : {x // f x = x}) :
    BilinForm.IsIsometry (σ.bilinFormAt x.1) (fixedPointDerivative I f x) := by
  -- Every tangent space is the model space, so `σ` may be evaluated at `f x` and at `x` on the
  -- same pair of vectors; the two values agree because `f x = x`.
  have key : ∀ {y : M} (_ : y = x.1) (v w : E),
      SmoothBundleForm.eval₂ σ y v w = SmoothBundleForm.eval₂ σ x.1 v w := by
    rintro _ rfl v w
    rfl
  refine BilinForm.isIsometry_iff.2 fun v w ↦ ?_
  have hfx : σ.bilinFormAt x.1 (mfderiv I I f x.1 v) (mfderiv I I f x.1 w) =
      SmoothBundleForm.eval₂ σ (f x.1) (mfderiv I I f x.1 v) (mfderiv I I f x.1 w) :=
    (SmoothForm.bilinFormAt_apply σ x.1 _ _).trans (key x.2 _ _).symm
  rw [fixedPointDerivative_apply, fixedPointDerivative_apply, hfx,
    ← SmoothForm.eval₂_mpullback f hf, hσ, SmoothForm.bilinFormAt_apply]

/-- **The fixed-point derivative of a symplectomorphism has determinant one.** At a fixed point of
a smooth map preserving a nondegenerate two-form `σ`, the fixed-point derivative has determinant
`1`. -/
theorem det_fixedPointDerivative_eq_one (hσnd : σ.IsNondegenerate) (hf : ContMDiff I I ∞ f)
    (hσ : SmoothForm.mpullback f hf σ = σ) (x : {x // f x = x}) :
    LinearMap.det (fixedPointDerivative I f x) = 1 :=
  (isIsometry_fixedPointDerivative hf hσ x).det_eq_one_of_isAlt
    (SmoothForm.isAlt_bilinFormAt σ x.1) (hσnd.nondegenerate_bilinFormAt x.1)

/-- **Return maps of a symplectomorphism have determinant one.** If a smooth map `f` preserves a
nondegenerate two-form `σ` and `x` is a periodic point of `f` of period `d`, the linearized return
map of its orbit, the fixed-point derivative of `f^[d]` at `x`, has determinant `1`. -/
theorem det_fixedPointDerivative_iterate_eq_one (hσnd : σ.IsNondegenerate)
    (hf : ContMDiff I I ∞ f) (hσ : SmoothForm.mpullback f hf σ = σ) {d : ℕ} {x : M}
    (hx : IsPeriodicPt f d x) :
    LinearMap.det (fixedPointDerivative I f^[d] ⟨x, hx.eq⟩) = 1 :=
  det_fixedPointDerivative_eq_one hσnd (hf.iterate d)
    (SmoothForm.mpullback_iterate_eq_self hf hσ d) ⟨x, hx.eq⟩

end TauCeti.SmoothTwoForm
