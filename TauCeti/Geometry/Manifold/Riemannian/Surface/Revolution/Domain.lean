/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Metric
public import TauCeti.Geometry.Manifold.Riemannian.Induced
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The induced Riemannian metric on an open revolution parameter domain

A `C^(n+1)` regular profile of nonzero radius determines a genuine `C^n` Riemannian metric
on each open coordinate domain where it is regular. No global regularity, injectivity of the
parametrization or completeness is required.

Ported from Yangyang Li's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/tree/b442a9f3077a4be3823b712ec92b2335dd34e771/ForTauCeti/Geometry/Manifold/Riemannian/Surface/Revolution).
-/

public noncomputable section

open Bundle Manifold TopologicalSpace
open scoped ContDiff

namespace TauCeti.SurfaceOfRevolution

local notation "P" => ℝ × ℝ
local notation "IP" => 𝓘(ℝ, P)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- On an open coordinate domain the differential of the immersion is the ordinary
differential composed with the canonical tangent-space identification. -/
theorem mvfderiv_parametrization_subtype {f g : ℝ → ℝ} {U : Opens P} {p : U}
    (hf : DifferentiableAt ℝ f p.val.2) (hg : DifferentiableAt ℝ g p.val.2)
    (w : TangentSpace IP p) :
    mvfderiv IP (fun q : U ↦ parametrization f g q.val) p w =
      fderiv ℝ (parametrization f g) p.val
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w)) := by
  have hd := differentiableAt_parametrization hf hg
  have hcomp := mvfderiv_comp_apply (g := parametrization f g)
    (f := (Subtype.val : U → P)) p hd.mdifferentiableAt
    ((contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp)) w
  simpa only [Manifold.mfderiv_subtype_val, mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Function.comp_def] using hcomp

/-- The restricted parametrization is smooth when the profile is smooth at its parameter
values. -/
theorem contMDiff_parametrization_subtype {f g : ℝ → ℝ} {U : Opens P} {n : ℕ∞ω}
    (hf : ∀ p : U, ContDiffAt ℝ n f p.val.2)
    (hg : ∀ p : U, ContDiffAt ℝ n g p.val.2) :
    ContMDiff IP 𝓘(ℝ, E₃) n (fun p : U ↦ parametrization f g p.val) := by
  intro p
  exact contMDiffAt_subtype_iff.mpr (contDiffAt_parametrization (hf p) (hg p)).contMDiffAt

/-- On any open regular parameter domain, the differential of the restricted parametrization
is injective. -/
theorem injective_mvfderiv_parametrization_subtype {f g : ℝ → ℝ} {U : Opens P} {p : U}
    (hf : DifferentiableAt ℝ f p.val.2) (hg : DifferentiableAt ℝ g p.val.2)
    (hr : f p.val.2 ≠ 0) (hs : 0 < profileSpeedSq f g p.val.2) :
    Function.Injective (mvfderiv IP (fun q : U ↦ parametrization f g q.val) p) := by
  intro w z hwz
  rw [mvfderiv_parametrization_subtype hf hg,
    mvfderiv_parametrization_subtype hf hg] at hwz
  exact (Manifold.tangentSpaceOpenEquiv (I := IP) p).injective
    ((NormedSpace.fromTangentSpace p.val).injective
      (injective_fderiv_parametrization hf hg hr hs hwz))

/-- The native `Cⁿ` Riemannian metric induced by a regular surface of revolution on an
arbitrary open parameter domain. -/
def riemannianMetric {n : ℕ∞ω} {f g : ℝ → ℝ} (U : Opens P)
    (hf : ∀ p : U, ContDiffAt ℝ (n + 1) f p.val.2)
    (hg : ∀ p : U, ContDiffAt ℝ (n + 1) g p.val.2)
    (hr : ∀ p : U, f p.val.2 ≠ 0)
    (hs : ∀ p : U, 0 < profileSpeedSq f g p.val.2) :
    ContMDiffRiemannianMetric IP n P (fun p : U ↦ TangentSpace IP p) :=
  inducedRiemannianMetric (fun p : U ↦ parametrization f g p.val)
    (contMDiff_parametrization_subtype hf hg)
    (fun p ↦ injective_mvfderiv_parametrization_subtype
      ((hf p).differentiableAt (by simp))
      ((hg p).differentiableAt (by simp)) (hr p) (hs p))

/-- The native induced Riemannian metric has the computed first fundamental form. -/
@[simp]
theorem riemannianMetric_inner {n : ℕ∞ω} {f g : ℝ → ℝ} (U : Opens P)
    (hf : ∀ p : U, ContDiffAt ℝ (n + 1) f p.val.2)
    (hg : ∀ p : U, ContDiffAt ℝ (n + 1) g p.val.2)
    (hr : ∀ p : U, f p.val.2 ≠ 0)
    (hs : ∀ p : U, 0 < profileSpeedSq f g p.val.2)
    (p : U) (w z : TangentSpace IP p) :
    (riemannianMetric U hf hg hr hs).inner p w z =
      metric f g p.val
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p z)) := by
  rw [riemannianMetric, inducedRiemannianMetric_inner,
    mvfderiv_parametrization_subtype ((hf p).differentiableAt (by simp))
      ((hg p).differentiableAt (by simp)),
    mvfderiv_parametrization_subtype ((hf p).differentiableAt (by simp))
      ((hg p).differentiableAt (by simp)),
    metric_eq_inner_fderiv ((hf p).differentiableAt (by simp))
      ((hg p).differentiableAt (by simp))]

end TauCeti.SurfaceOfRevolution
