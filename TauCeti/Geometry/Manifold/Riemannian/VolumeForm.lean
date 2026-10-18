/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Riemannian volume forms

An orientation and a Riemannian metric determine a top-degree alternating form on every tangent
space.  This file packages Mathlib's oriented inner-product-space volume form fibrewise, giving the
pointwise object for the manifold divergence and Stokes identities.

The construction is total, as are the rough forms in the differential-form API.  Its defining
characterization is that it evaluates to `1` on every positively oriented orthonormal basis.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 15.29.  The normalization on positively oriented orthonormal bases is the
  characterization stated in that proposition.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ}

/-- The Riemannian volume form determined by an orientation, defined fibrewise on tangent spaces. -/
noncomputable def riemannianVolumeForm (o : Manifold.Orientation I M (Fin m)) :
    RoughForm I M ℝ m := fun x ↦
  let := o.fact_finrank_tangentSpace x
  (Manifold.Orientation.orientationAt o x).volumeFormL

/-- Unfolding the Riemannian volume form at a point exposes its oriented fibre form. -/
theorem riemannianVolumeForm_eq
    (o : Manifold.Orientation I M (Fin m)) (x : M) :
    riemannianVolumeForm o x =
      (letI := o.fact_finrank_tangentSpace x
       (Manifold.Orientation.orientationAt o x).volumeFormL) := by
  simp only [riemannianVolumeForm]

/-- Evaluation of the Riemannian volume form is Mathlib's oriented volume form. -/
theorem riemannianVolumeForm_apply
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (v : Fin m → TangentSpace I x) :
    riemannianVolumeForm o x v =
      (letI := o.fact_finrank_tangentSpace x
       (Manifold.Orientation.orientationAt o x).volumeForm v) := by
  let := o.fact_finrank_tangentSpace x
  simp [riemannianVolumeForm]

/-- The volume form takes value `1` on a positively oriented orthonormal tangent basis. -/
theorem riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = 1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_eq]
  exact Orientation.volumeFormL_robust _ b hb

/-- The Riemannian volume form has absolute value one on every orthonormal basis. -/
theorem abs_riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x)) :
    |riemannianVolumeForm o x b| = 1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_eq]
  exact Orientation.abs_volumeFormL_apply_of_orthonormal _ b

/-- The Riemannian volume form is negative on an oppositely oriented orthonormal basis. -/
theorem riemannianVolumeForm_apply_orthonormal_of_opposite
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation ≠ Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = -1 := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_eq]
  exact Orientation.volumeFormL_robust_neg _ b hb

/-- A top form taking value one on an oriented orthonormal basis is the Riemannian volume form. -/
theorem eq_riemannianVolumeForm_of_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (ω : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x)
    (hω : ω b = 1) :
    ω = riemannianVolumeForm o x := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_eq]
  exact Orientation.eq_volumeFormL_of_apply_orthonormal _ ω b hb hω

end TauCeti
