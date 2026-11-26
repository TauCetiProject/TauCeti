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

The copy `TauCeti.WithMetric g` of a manifold `M` carries the metric `g` as its `RiemannianBundle`
instance, and the tautological diffeomorphism `diffeomorph g ∞ : WithMetric g ≃ₘ^∞⟮I, I⟯ M`
preserves tangent inner products when `g` is installed as the `RiemannianBundle` instance on `M`
(`TauCeti.WithMetric.riemannianIsometry`), or more generally whenever `M` carries an ambient
`RiemannianBundle` whose inner product agrees pointwise with `g`
(`TauCeti.WithMetric.riemannianIsometryOfInner`). Two pointwise-equal smooth metrics have
isometric `WithMetric` copies (`TauCeti.WithMetric.riemannianIsometryOfInnerEq`).
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

section Inner

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w)

include hg

/-- The tautological diffeomorphism `WithMetric g → M` upgraded to a `RiemannianIsometry` whenever
the ambient `RiemannianBundle` on `M` has inner product `g.inner`. -/
def riemannianIsometryOfInner : RiemannianIsometry I I (WithMetric g) M where
  toDiffeomorph := diffeomorph g ∞
  inner_mfderiv' x v w := by rw [coe_diffeomorph, hg, inner_def]

/-- Coercing `riemannianIsometryOfInner` to a function yields `ofWithMetric`. -/
@[simp] theorem coe_riemannianIsometryOfInner :
    ⇑(riemannianIsometryOfInner g hg) = ofWithMetric :=
  (RiemannianIsometry.coe_toDiffeomorph _).symm.trans (coe_diffeomorph (g := g) ∞)

/-- Evaluating `riemannianIsometryOfInner` at `x` returns `x.ofWithMetric`. -/
@[simp] theorem riemannianIsometryOfInner_apply (x : WithMetric g) :
    riemannianIsometryOfInner g hg x = x.ofWithMetric :=
  congrFun (coe_riemannianIsometryOfInner g hg) x

/-- Evaluating the inverse of `riemannianIsometryOfInner` at `x` returns `toWithMetric g x`. -/
@[simp] theorem riemannianIsometryOfInner_symm_apply (x : M) :
    (riemannianIsometryOfInner g hg).symm x = toWithMetric g x :=
  congrFun ((riemannianIsometryOfInner g hg).coe_symm.trans (coe_diffeomorph_symm (g := g) ∞)) x

end Inner

/-- The tautological smooth Riemannian isometry from `WithMetric g` to `M` equipped with `g`. -/
def riemannianIsometry :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    RiemannianIsometry I I (WithMetric g) M :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  riemannianIsometryOfInner g g.inner_riemannianBundle

@[simp]
theorem toDiffeomorph_riemannianIsometry :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (riemannianIsometry g).toDiffeomorph = diffeomorph g ∞ :=
  (rfl)

@[simp]
theorem coe_riemannianIsometry :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ⇑(riemannianIsometry g) = ofWithMetric :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  coe_riemannianIsometryOfInner g g.inner_riemannianBundle

@[simp]
theorem coe_riemannianIsometry_symm :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ⇑(riemannianIsometry g).symm = toWithMetric g :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  funext (riemannianIsometryOfInner_symm_apply g g.inner_riemannianBundle)

section InnerEq

variable (g₁ g₂ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w)

include h

/-- Two smooth Riemannian metrics on `M` with pointwise equal inner products have isometric
`WithMetric` copies via the identity diffeomorphism. -/
def riemannianIsometryOfInnerEq : RiemannianIsometry I I (WithMetric g₁) (WithMetric g₂) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  (riemannianIsometryOfInner g₁ g₁.inner_riemannianBundle).trans
    (riemannianIsometryOfInner g₂
      fun x v w ↦ (g₁.inner_riemannianBundle x v w).trans (h x v w)).symm

/-- Evaluating `riemannianIsometryOfInnerEq` at `x` returns `toWithMetric g₂ x.ofWithMetric`. -/
@[simp] theorem riemannianIsometryOfInnerEq_apply (x : WithMetric g₁) :
    riemannianIsometryOfInnerEq g₁ g₂ h x = toWithMetric g₂ x.ofWithMetric :=
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  (RiemannianIsometry.trans_apply _ _ x).trans <|
    (riemannianIsometryOfInner_symm_apply g₂
      (fun x v w ↦ (g₁.inner_riemannianBundle x v w).trans (h x v w)) _).trans
      (congrArg (toWithMetric g₂) (riemannianIsometryOfInner_apply g₁ g₁.inner_riemannianBundle x))

/-- Evaluating the inverse of `riemannianIsometryOfInnerEq` at `x` returns
`toWithMetric g₁ x.ofWithMetric`. -/
@[simp] theorem riemannianIsometryOfInnerEq_symm_apply (x : WithMetric g₂) :
    (riemannianIsometryOfInnerEq g₁ g₂ h).symm x = toWithMetric g₁ x.ofWithMetric :=
  (EquivLike.injective (riemannianIsometryOfInnerEq g₁ g₂ h)).eq_iff.1 <| by simp

end InnerEq

end TauCeti.WithMetric
