/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.PolarCompatible

import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent

/-!
# Fixed tangent subspaces of symplectic isometries

Let `Φ i` be Riemannian isometries of `M` pulling a nondegenerate two-form `σ` back to itself, and
let `p` be a common fixed point. Each differential `dΦ_i` at `p` is a linear isometric
symplectomorphism of `(T_p M, σ_p)`, so it commutes with the polar normalization `J_p` of `σ_p` for
the inner product of `T_p M`
(`TauCeti.SymplecticForm.IsSymplectomorphism.polarComplexStructure_apply`). Hence `J_p` preserves
the fixed tangent subspace `TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p`
(`TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_mem_fixedTangentSubspace`), and since
`σ_p` tames `J_p`, the form `σ_p` is nondegenerate on it
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`). Everything is pointwise
at `p`: no smoothness of the metric is assumed.

On a finite-dimensional boundaryless Hausdorff manifold with a smooth metric, normal coordinates
at `p` flatten the common fixed set onto this subspace
(`TauCeti.RiemannianIsometry.mem_iInter_fixedPoints_iff_riemannianLog_mem`), so it is the
infinitesimal model of the fixed set at `p`. Averaging a metric over a finite group or a compact
group acting by symplectomorphisms (`TauCeti.averageRiemannianMetric`,
`TauCeti.measureAverageRiemannianMetric`) makes the action isometric.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_mem_fixedTangentSubspace`: the polar
  normalization of `σ_p` preserves the fixed tangent subspace at a common fixed point.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`: the fixed tangent
  subspace of a family of symplectic isometries at a common fixed point is a symplectic subspace.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Proposition 12.6 (polar normalization) and Homework 21, exercise 2 (fixed sets
  of symplectic group actions are symplectic submanifolds).
-/

public section

open Bundle Function Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {σ : SmoothTwoForm I M} {ι : Type*} {Φ : ι → RiemannianIsometry I I M M} {p : M}

/-- At a common fixed point `p` of Riemannian isometries `Φ i` pulling a nondegenerate two-form `σ`
back to itself, the polar normalization of `σ_p` for the inner product of `T_p M` preserves the
fixed tangent subspace of the `Φ i`. -/
theorem IsNondegenerate.polarComplexStructure_mem_fixedTangentSubspace (h : σ.IsNondegenerate)
    (hΦ : ∀ i, SmoothForm.mpullback (Φ i) (Φ i).toDiffeomorph.contMDiff σ = σ)
    (hp : p ∈ ⋂ i, fixedPoints (Φ i)) {v : TangentSpace I p}
    (hv : v ∈ RiemannianIsometry.fixedTangentSubspace Φ p) :
    (h.symplecticFormAt p).polarComplexStructure v ∈
      RiemannianIsometry.fixedTangentSubspace Φ p := by
  refine RiemannianIsometry.mem_fixedTangentSubspace.2 fun i ↦ ?_
  -- `dΦ_i` is a linear isometric symplectomorphism from `T_p M` to `T_(Φ_i p) M`, so it intertwines
  -- the polar normalizations there; it fixes `v`, and `Φ_i p = p`.
  have he : SymplecticForm.IsSymplectomorphism (h.symplecticFormAt p)
      (h.symplecticFormAt (Φ i p)) ((Φ i).mfderivToLinearIsometryEquiv p).toLinearEquiv :=
    SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ by
      rw [symplecticFormAt_apply, symplecticFormAt_apply]
      simp only [LinearIsometryEquiv.coe_toLinearEquiv,
        RiemannianIsometry.mfderivToLinearIsometryEquiv_apply]
      rw [← SmoothForm.eval₂_mpullback (Φ i) (Φ i).toDiffeomorph.contMDiff σ, hΦ i]
  have hJ := he.polarComplexStructure_apply v
  rw [RiemannianIsometry.mfderivToLinearIsometryEquiv_apply,
    RiemannianIsometry.mfderivToLinearIsometryEquiv_apply,
    RiemannianIsometry.mem_fixedTangentSubspace.1 hv i,
    (mem_fixedPoints.1 (mem_iInter.1 hp i) : Φ i p = p)] at hJ
  exact hJ.symm

/-- **The fixed tangent subspace of symplectic isometries is symplectic.** Let `Φ i` be Riemannian
isometries pulling a nondegenerate two-form `σ` back to itself. At a common fixed point `p`, the
fixed tangent subspace of the `Φ i` is a symplectic subspace of `(T_p M, σ_p)`. -/
theorem IsNondegenerate.isSymplectic_fixedTangentSubspace (h : σ.IsNondegenerate)
    (hΦ : ∀ i, SmoothForm.mpullback (Φ i) (Φ i).toDiffeomorph.contMDiff σ = σ)
    (hp : p ∈ ⋂ i, fixedPoints (Φ i)) :
    (h.symplecticFormAt p).IsSymplectic (RiemannianIsometry.fixedTangentSubspace Φ p) :=
  (h.symplecticFormAt p).compatible_polarComplexStructure.tames.isSymplectic_of_mem_invtSubmodule <|
    (Module.End.mem_invtSubmodule _).2 fun _ hv ↦
      h.polarComplexStructure_mem_fixedTangentSubspace hΦ hp hv

end TauCeti.SmoothTwoForm
