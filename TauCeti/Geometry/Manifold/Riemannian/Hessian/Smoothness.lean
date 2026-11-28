/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.ModelSpace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Parametrization
import Mathlib.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Calculus.ContDiff.DifferentialEquation
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry

/-!
# Smoothness from prescribed Hessians

In linear coordinates, the Hessian equation is a first-order equation for the differential.
Regularity of its coefficients therefore improves an initially `C²` potential.
On a smooth Riemannian manifold this gives smoothness near an interior point when the Hessian
is a smooth scalar multiple of the metric.

## References

* `PoincareMT.LeviCivitaData.contDiffOn_of_C2_hessian_eq_smooth_mul_metric` and
  `PoincareMT.LeviCivitaData.contMDiff_of_C2_hessian_eq_smooth_mul_metric` in the public
  formalizations https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- A `C²` model-space function with smooth prescribed Hessian coefficients
is smooth on its open domain. The metric need not be the constant Euclidean metric. -/
theorem contDiffOn_of_hessian_eq_model_space {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    {A : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ContDiffOn ℝ 2 f U) (hA : ContDiffOn ℝ ∞ A U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace 𝓘(ℝ, E) x,
      hessian 𝓘(ℝ, E) f x v w = A x v w) :
    ContDiffOn ℝ ∞ f U := by
  have heq' (x : E) (hx : x ∈ U) (v w : TangentSpace 𝓘(ℝ, E) x) :
      hessian 𝓘(ℝ, E) f x v w =
        A x (tangentSpaceCastModel 𝓘(ℝ, E) x v) (tangentSpaceCastModel 𝓘(ℝ, E) x w) := by
    simpa only [tangentSpaceCastModel_modelWithCornersSelf_apply] using heq x hx v w
  let g : E → E →L[ℝ] E →L[ℝ] ℝ :=
    (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner
  have hg (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
      inner ℝ v w =
        g x (tangentSpaceCastModel 𝓘(ℝ, E) x v) (tangentSpaceCastModel 𝓘(ℝ, E) x w) := by
    rw [tangentSpaceCastModel_modelWithCornersSelf_apply,
      tangentSpaceCastModel_modelWithCornersSelf_apply]
    exact RiemannianMetric.inner_riemannianBundle x v w
  have hΓ := contDiff_christoffelSecondKind_riemannianMetric (E := E) (m := ∞) (n := ∞)
    (by simp)
  have hreg := TauCeti.contDiffOn_add_two_of_fderiv_fderiv_eq (n := ⊤) hU
    (hf.differentiableOn (by norm_num))
    ((hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num))
    hA hΓ.contDiffOn ?_
  · exact hreg.of_le le_self_add
  intro x hx
  ext v w
  have hh := hessian_model_space_eq_fderiv_sub_christoffelSecondKind
    (g := g) hg (hf.contDiffAt (hU.mem_nhds hx)) v w
  rw [heq' x hx] at hh
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hh
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply] using sub_eq_iff_eq_add.mp hh.symm

/-- A `C²` model-space potential with Hessian `a g`, for smooth `a`, is smooth. -/
theorem contDiffOn_of_hessian_eq_mul_inner_model_space {U : Set E} (hU : IsOpen U) {f a : E → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (ha : ContDiffOn ℝ ∞ a U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace 𝓘(ℝ, E) x,
      hessian 𝓘(ℝ, E) f x v w = a x * inner ℝ v w) :
    ContDiffOn ℝ ∞ f U := by
  have hsmul (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
      (a x • (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner x)
        v w = a x * inner ℝ v w := by
    simp only [_root_.smul_apply, smul_eq_mul, ← RiemannianMetric.inner_riemannianBundle]
  -- Fix the operator-norm scalar structure before elaborating the dependent metric coefficient.
  let bilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let A : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦
    a x • (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner x
  apply contDiffOn_of_hessian_eq_model_space (A := A) hU hf
  · exact ha.smul contDiff_riemannianMetric_inner.contDiffOn
  · intro x hx v w
    exact (heq x hx v w).trans (hsmul x v w).symm

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A `C²` potential with smooth pure-trace Hessian is smooth at interior points of its domain.
Only the selected point must lie in the interior of the manifold. -/
theorem contMDiffAt_of_hessian_eq_mul_inner {U : Set M} (hU : IsOpen U) {u a : M → ℝ}
    {x : M} (hx : x ∈ U) (hxi : I.IsInteriorPoint x)
    (hu : ContMDiffOn I 𝓘(ℝ) 2 u U) (ha : ContMDiffOn I 𝓘(ℝ) ∞ a U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      hessian I u x v w = a x * inner ℝ v w) :
    ContMDiffAt I 𝓘(ℝ) ∞ u x := by
  apply TauCeti.contMDiffAt_of_contDiffOn_localRiemannianIsometry hU hx hxi hu
  intro gE f hfiso hS hucomp
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  exact contDiffOn_of_hessian_eq_mul_inner_model_space hS hucomp (hfiso.contDiffOn_comp ha)
    (fun z hz v w ↦ by
    rw [hfiso.hessian_comp (hu.contMDiffAt (hU.mem_nhds hz)), heq _ hz,
      hfiso.inner_mfderiv]
    simp only [Function.comp_apply])

/-- A `C²` potential with smooth pure-trace Hessian on an open subset of a boundaryless
manifold is smooth on that subset. -/
theorem contMDiffOn_of_hessian_eq_mul_inner [BoundarylessManifold I M] {U : Set M}
    (hU : IsOpen U) {u a : M → ℝ} (hu : ContMDiffOn I 𝓘(ℝ) 2 u U)
    (ha : ContMDiffOn I 𝓘(ℝ) ∞ a U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      hessian I u x v w = a x * inner ℝ v w) :
    ContMDiffOn I 𝓘(ℝ) ∞ u U :=
  fun _ hx ↦ (contMDiffAt_of_hessian_eq_mul_inner hU hx
    BoundarylessManifold.isInteriorPoint hu ha heq).contMDiffWithinAt

end TauCeti.Manifold
