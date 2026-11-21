/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic

/-!
# Smooth Riemannian isometries for `WithMetric`

When a manifold `M` carries a `RiemannianBundle` whose inner product agrees pointwise with a smooth
metric `g`, the tautological diffeomorphism `WithMetric g → M` upgrades to a `RiemannianIsometry`
(`TauCeti.WithMetric.riemannianIsometry`), and two pointwise-equal smooth metrics have isometric
`WithMetric` copies (`TauCeti.WithMetric.riemannianIsometryOfInnerEq`).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.WithMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section RiemannianIsometry

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w)

include hg

/-- The tautological diffeomorphism `WithMetric g → M` upgraded to a `RiemannianIsometry` whenever
the ambient `RiemannianBundle` on `M` has inner product `g.inner`. -/
def riemannianIsometry : RiemannianIsometry I I (WithMetric g) M where
  toDiffeomorph := WithMetric.diffeomorph g ∞
  inner_mfderiv' x v w := by rw [WithMetric.coe_diffeomorph, hg, WithMetric.inner_def]

/-- Coercing `riemannianIsometry` to a function yields `ofWithMetric`. -/
@[simp] theorem coe_riemannianIsometry : ⇑(riemannianIsometry g hg) = ofWithMetric :=
  (RiemannianIsometry.coe_toDiffeomorph _).symm.trans (WithMetric.coe_diffeomorph ∞)

/-- Evaluating `riemannianIsometry` at `x` returns `x.ofWithMetric`. -/
@[simp] theorem riemannianIsometry_apply (x : WithMetric g) :
    riemannianIsometry g hg x = x.ofWithMetric := congrFun (coe_riemannianIsometry g hg) x

/-- Evaluating the inverse of `riemannianIsometry` at `x` returns `toWithMetric g x`. -/
@[simp] theorem riemannianIsometry_symm_apply (x : M) :
    (riemannianIsometry g hg).symm x = toWithMetric g x :=
  congrFun ((riemannianIsometry g hg).coe_symm.trans (WithMetric.coe_diffeomorph_symm ∞)) x

end RiemannianIsometry

section InnerEq

variable (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w)

include h

/-- Two smooth Riemannian metrics on `M` with pointwise equal inner products have isometric
`WithMetric` copies via the identity diffeomorphism. -/
def riemannianIsometryOfInnerEq : RiemannianIsometry I I (WithMetric g₁) (WithMetric g₂) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  (riemannianIsometry g₁ fun _ _ _ ↦ rfl).trans (riemannianIsometry g₂ h).symm

/-- Evaluating `riemannianIsometryOfInnerEq` at `x` returns `toWithMetric g₂ x.ofWithMetric`. -/
@[simp] theorem riemannianIsometryOfInnerEq_apply (x : WithMetric g₁) :
    riemannianIsometryOfInnerEq g₁ g₂ h x = toWithMetric g₂ x.ofWithMetric :=
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  (RiemannianIsometry.trans_apply _ _ x).trans <| (riemannianIsometry_symm_apply g₂ h _).trans
    (congrArg (toWithMetric g₂) (riemannianIsometry_apply g₁ _ x))

end InnerEq

end TauCeti.WithMetric

end
