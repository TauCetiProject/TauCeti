/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Graph
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Lagrangian.TwistedProd
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Lagrangian graphs of diffeomorphisms and symplectic graphs

The graph `x ↦ (x, φ x)` of a diffeomorphism between manifolds carrying nondegenerate
smooth two-forms is Lagrangian for `pr₁*σ - pr₂*τ` exactly when `φ*τ = σ`.
In particular the diagonal is Lagrangian. These are the canonical transformations and
identity correspondences of symplectic geometry.

For the product form `pr₁*σ + pr₂*τ` instead, the graph of a differentiable map `f` has symplectic
tangent images exactly when `σ + f*τ` is nondegenerate at every point
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_graph_iff`), by
`SymplecticForm.isSymplectic_graph_iff` on the tangent fibres. For a constant map this says that
each slice `x ↦ (x, c)` of `M × N` has symplectic tangent images.

The proof uses `SymplecticForm.isLagrangian_graph_iff` on the tangent fibres through the
canonical product tangent identification. Neither finite dimensionality nor closedness is
needed for this tangent-image criterion. For symplectic factors the ambient twisted product
is symplectic by `SmoothTwoForm.IsSymplectic.twistedProd`. Graphs of smooth maps are embedded
by Mathlib's `Topology.isEmbedding_graph`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Sections 3 and 5.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}

/-- A diffeomorphism has Lagrangian graph for `σ ⊖ τ` exactly when it pulls `τ` back to `σ`. -/
@[simp]
theorem IsNondegenerate.isLagrangianMap_graph_iff
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) (φ : M ≃ₘ⟮I, J⟯ N) :
    (hσ.twistedProd hτ).IsLagrangianMap I (fun x ↦ (x, φ x)) ↔
      SmoothForm.mpullback φ φ.contMDiff τ = σ := by
  have hpoint (x : M) :
      ((hσ.symplecticFormAt x).twistedProd (hτ.symplecticFormAt (φ x))).IsLagrangian
          (LinearMap.range
            ((Manifold.tangentSpaceProdEquiv (x, φ x)).toLinearEquiv.toLinearMap ∘ₗ
              (mfderiv I (I.prod J) (fun y ↦ (y, φ y)) x).toLinearMap)) ↔
        ∀ v w, SmoothBundleForm.eval₂ τ (φ x)
          (mfderiv I J φ x v) (mfderiv I J φ x w) =
          SmoothBundleForm.eval₂ σ x v w := by
    rw [LinearMap.range_comp, Manifold.map_range_mfderiv_graph (φ.mdifferentiable (by simp) x)]
    have he : (φ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.toLinearMap =
        (mfderiv I J φ x).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap (φ.mfderivToContinuousLinearEquiv_coe (by simp))
    rw [← he, SymplecticForm.isLagrangian_graph_iff, SymplecticForm.isSymplectomorphism_iff]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
      ← ContinuousLinearEquiv.coe_coe, Diffeomorph.mfderivToContinuousLinearEquiv_coe]
    constructor
    · intro h v w
      exact (hτ.symplecticFormAt_apply _ _ _).symm.trans
        ((h v w).trans (hσ.symplecticFormAt_apply _ _ _))
    · intro h v w
      exact (hτ.symplecticFormAt_apply _ _ _).trans
        ((h v w).trans (hσ.symplecticFormAt_apply _ _ _).symm)
  rw [isLagrangianMap_twistedProd_iff_forall hσ hτ]
  constructor
  · intro h
    apply SmoothBundleForm.ext_eval₂
    intro x v w
    rw [SmoothForm.eval₂_mpullback]
    exact (hpoint x).mp (h x) v w
  · intro h x
    apply (hpoint x).mpr
    intro v w
    rw [← SmoothForm.eval₂_mpullback φ φ.contMDiff τ, h]

/-- The graph of a differentiable map `f : M → N` has symplectic tangent images for the product
form `pr₁*σ + pr₂*τ` exactly when the form `σ + f*τ` is nondegenerate at every point: a tangent
vector `v` with `σ(v, w) + τ(df v, df w) = 0` for every `w` is zero. -/
theorem IsNondegenerate.hasSymplecticTangentImages_graph_iff
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) {f : M → N} (hf : MDifferentiable I J f) :
    (hσ.prod hτ).HasSymplecticTangentImages I (fun x ↦ (x, f x)) ↔
      ∀ x (v : TangentSpace I x),
        (∀ w, SmoothBundleForm.eval₂ σ x v w +
            SmoothBundleForm.eval₂ τ (f x) (mfderiv I J f x v) (mfderiv I J f x w) = 0) →
          v = 0 := by
  rw [IsNondegenerate.hasSymplecticTangentImages_iff_forall]
  refine forall_congr' fun x ↦ ?_
  rw [← SymplecticForm.isSymplectic_map_transport_iff
      (e := (Manifold.tangentSpaceProdEquiv (x, f x)).toLinearEquiv),
    IsNondegenerate.symplecticFormAt_prod hσ hτ, Manifold.map_range_mfderiv_graph (hf x),
    SymplecticForm.isSymplectic_graph_iff]
  simp only [IsNondegenerate.symplecticFormAt_apply, ContinuousLinearMap.coe_coe]

/-- Every slice `x ↦ (x, c)` of a product has symplectic tangent images for the product form. -/
theorem IsNondegenerate.hasSymplecticTangentImages_prodMkLeft
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) (c : N) :
    (hσ.prod hτ).HasSymplecticTangentImages I (fun x : M ↦ (x, c)) := by
  refine (hσ.hasSymplecticTangentImages_graph_iff hτ mdifferentiable_const).2 fun x v hv ↦
    isNondegenerate_iff_separatingLeft.1 hσ x v fun w ↦ ?_
  simpa [mfderiv_const] using hv w

/-- The diagonal is Lagrangian for the difference of a nondegenerate form with itself. -/
@[simp]
theorem IsNondegenerate.isLagrangianMap_diagonal (hσ : σ.IsNondegenerate) :
    (hσ.twistedProd hσ).IsLagrangianMap I (fun x : M ↦ (x, x)) := by
  simpa using (hσ.isLagrangianMap_graph_iff hσ (Diffeomorph.refl I M ∞)).mpr (by simp)

end TauCeti.SmoothTwoForm
