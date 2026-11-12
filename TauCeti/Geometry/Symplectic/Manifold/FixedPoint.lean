/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
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

For a family of maps preserving both `σ` and a Riemannian metric, the common fixed points are
symplectic in the following sense. Let `Φ i` be Riemannian isometries of `M` pulling a
nondegenerate `σ` back to itself, and let `p` be a common fixed point. The polar normalization `J`
of `σ` for the metric (`TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure`) commutes with
every differential `dΦ_i` at `p`, since these are linear isometric symplectomorphisms of `T_p M`.
So `J` preserves the fixed tangent subspace `TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p`,
and since `σ(v, J v) > 0` for `v ≠ 0`, the form `σ_p` is nondegenerate on it
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`). Normal coordinates at
`p` flatten the common fixed set onto this subspace
(`TauCeti.RiemannianIsometry.mem_iInter_fixedPoints_iff_riemannianLog_mem`), so it is the
infinitesimal model of the fixed set at `p`. Averaging a metric over a finite group or a compact
group acting by symplectomorphisms (`TauCeti.averageRiemannianMetric`,
`TauCeti.measureAverageRiemannianMetric`) makes the action isometric.

## Main results

* `TauCeti.SmoothTwoForm.isIsometry_fixedPointDerivative`: the fixed-point derivative of a map
  preserving `σ` is an isometry of `σ_x`.
* `TauCeti.SmoothTwoForm.det_fixedPointDerivative_eq_one`: for nondegenerate `σ` it has
  determinant one.
* `TauCeti.SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one`: the return map of a periodic
  orbit of a map preserving a nondegenerate `σ` has determinant one.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`: the fixed tangent
  subspace of a family of symplectic isometries at a common fixed point is a symplectic subspace.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Proposition 12.6 (polar normalization) and Homework 21, exercise 2 (fixed sets
  of symplectic group actions are symplectic submanifolds).
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

section Isometry

open Bundle Set

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} {Φ : ι → RiemannianIsometry I I M M}

/-- **Fixed loci of symplectic isometries are symplectic.** Let `Φ i` be Riemannian isometries
pulling a nondegenerate two-form `σ` back to itself. At a common fixed point `p`, the fixed tangent
subspace of the `Φ i`, onto which normal coordinates at `p` flatten their common fixed set, is a
symplectic subspace of `(T_p M, σ_p)`: it is preserved by the polar normalization of `σ`, which is
tamed by `σ`. -/
theorem IsNondegenerate.isSymplectic_fixedTangentSubspace (h : σ.IsNondegenerate)
    (hΦ : ∀ i, SmoothForm.mpullback (Φ i) (Φ i).toDiffeomorph.contMDiff σ = σ) {p : M}
    (hp : p ∈ ⋂ i, fixedPoints (Φ i)) :
    (h.symplecticFormAt p).IsSymplectic (RiemannianIsometry.fixedTangentSubspace Φ p) := by
  refine (h.symplecticFormAt p).compatible_polarComplexStructure.tames
    |>.isSymplectic_of_mem_invtSubmodule <| (Module.End.mem_invtSubmodule _).2 fun v hv ↦
      RiemannianIsometry.mem_fixedTangentSubspace.2 fun i ↦ ?_
  -- `dΦ_i` is a linear isometric symplectomorphism of `T_p M`, so it commutes with the polar
  -- normalization of `σ_p`, and it fixes `v`.
  have hJ := h.mfderiv_polarComplexStructure_apply h rfl (f := Φ i) (x := p)
    ((Φ i).inner_mfderiv p) (fun u w ↦ by
      rw [← SmoothForm.eval₂_mpullback (Φ i) (Φ i).toDiffeomorph.contMDiff σ, hΦ i]) v
  rw [polarComplexStructure_apply, polarComplexStructure_apply,
    RiemannianIsometry.mem_fixedTangentSubspace.1 hv i,
    (mem_fixedPoints.1 (mem_iInter.1 hp i) : Φ i p = p)] at hJ
  exact hJ

end Isometry

end TauCeti.SmoothTwoForm
