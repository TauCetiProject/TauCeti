/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
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
    RoughForm I M ℝ m := fun x ↦ by
  let : Fact (Module.finrank ℝ (TangentSpace I x) = m) := by
    refine ⟨(finrank_tangentSpace (I := I) x).trans ?_⟩
    simpa using o.card_eq.symm
  exact AlternatingMap.mkContinuous ((Manifold.Orientation.orientationAt o x).volumeForm) 1 (by
    intro v
    have h := (Manifold.Orientation.orientationAt o x).abs_volumeForm_apply_le v
    simpa [Real.norm_eq_abs] using h)

/-- The volume form takes value `1` on a positively oriented orthonormal tangent basis. -/
theorem riemannianVolumeForm_apply_orthonormal
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x))
    (hb : b.toBasis.orientation = Manifold.Orientation.orientationAt o x) :
    riemannianVolumeForm o x b = 1 := by
  let : Fact (Module.finrank ℝ (TangentSpace I x) = m) :=
    ⟨(finrank_tangentSpace (I := I) x).trans (by simpa using o.card_eq.symm)⟩
  rw [riemannianVolumeForm, AlternatingMap.coe_mkContinuous,
    (Manifold.Orientation.orientationAt o x).volumeForm_robust b hb]
  exact b.toBasis.det_self

end TauCeti
