/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic

/-!
# The Riemannian isometry of a metric-indexed copy

The copy `TauCeti.WithMetric g` of a manifold `M` carries the metric `g` as its `RiemannianBundle`
instance, and the tautological diffeomorphism `diffeomorph g ∞ : WithMetric g ≃ₘ^∞⟮I, I⟯ M`
preserves tangent inner products when `g` is installed as the `RiemannianBundle` instance on `M`.
This file packages that identification as the smooth Riemannian isometry
`TauCeti.WithMetric.riemannianIsometry`.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))

/-- The tautological smooth Riemannian isometry from `WithMetric g` to `M` equipped with `g`. -/
def riemannianIsometry :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    RiemannianIsometry I I (WithMetric g) M :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  { toDiffeomorph := diffeomorph g ∞
    inner_mfderiv' x v w := by
      rw [coe_diffeomorph]
      exact (inner_def x v w).symm }

@[simp]
theorem toDiffeomorph_riemannianIsometry :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (riemannianIsometry g).toDiffeomorph = diffeomorph g ∞ :=
  (rfl)

@[simp]
theorem coe_riemannianIsometry :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ⇑(riemannianIsometry g) = ofWithMetric :=
  coe_diffeomorph (g := g) ∞

@[simp]
theorem coe_riemannianIsometry_symm :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ⇑(riemannianIsometry g).symm = toWithMetric g := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [RiemannianIsometry.coe_symm]
  exact coe_diffeomorph_symm (g := g) ∞

end TauCeti.WithMetric
