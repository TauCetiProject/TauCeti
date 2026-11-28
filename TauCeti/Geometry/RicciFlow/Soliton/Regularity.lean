/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Soliton.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Smoothness
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Smoothness of gradient Ricci soliton potentials

On a smooth Hausdorff Riemannian manifold, a `C²` solution of `Ric + Hess f = a g` is smooth
wherever
`a` is smooth and the manifold has no boundary. The local version requires that the
selected point is an interior point. Constant `a` gives the ordinary gradient Ricci soliton
potential in any finite dimension, with no compactness or shrinking assumption.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 9.50.
* `PoincareMT.GradientShrinkingSolitonData.potential_smooth` in the public formalizations
  https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- A `C²` model-space potential satisfying `Ric + Hess f = a g` with smooth `a` is smooth. -/
theorem contDiffOn_of_ricciTensor_add_hessian_eq_mul_inner_model_space {U : Set E} (hU : IsOpen U)
    {f a : E → ℝ} (hf : ContDiffOn ℝ 2 f U) (ha : ContDiffOn ℝ ∞ a U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace 𝓘(ℝ, E) x,
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).ricciTensor x v w +
        hessian 𝓘(ℝ, E) f x v w = a x * inner ℝ v w) :
    ContDiffOn ℝ ∞ f U := by
  have heval (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
      ((a x • (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner x -
        (LinearMap.toContinuousBilinearMap
          ((CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).ricciTensor x))) v) w =
      a x * inner ℝ v w -
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).ricciTensor x v w := by
    simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul,
      ← RiemannianMetric.inner_riemannianBundle,
      LinearMap.toContinuousBilinearMap_apply]
  -- Fix the operator-norm scalar structure before elaborating the dependent tensor coefficients.
  let bilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let g : E → E →L[ℝ] E →L[ℝ] ℝ :=
    (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner
  let Ric : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦
    ((CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).ricciTensor x).toContinuousBilinearMap
  let A : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ a x • g x - Ric x
  have hRic : ContDiffOn ℝ ∞ Ric U := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    exact (contMDiff_iff_contDiff.1 fun x ↦
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).contMDiffAt_ricciTensor_apply
        (TauCeti.contMDiff_tangentBundle_mk_const v x)
        (TauCeti.contMDiff_tangentBundle_mk_const w x)).contDiffOn
  have hA : ContDiffOn ℝ ∞ A U :=
    (ha.smul contDiff_riemannianMetric_inner.contDiffOn).sub hRic
  apply contDiffOn_of_hessian_eq_model_space hU hf hA
  intro x hx v w
  have hh := heq x hx v w
  exact (eq_sub_of_add_eq' hh).trans (heval x v w).symm

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- On a Hausdorff manifold, a `C²` solution of `Ric + Hess u = a g` is smooth at each interior
point of an open set `U` on which `a` is smooth and the equation holds. The metric and its Ricci
tensor are the native Levi-Civita constructions. -/
theorem contMDiffAt_of_ricciTensor_add_hessian_eq_mul_inner [T2Space M] {U : Set M}
    (hU : IsOpen U) {u a : M → ℝ} {x : M} (hx : x ∈ U) (hxi : I.IsInteriorPoint x)
    (hu : ContMDiffOn I 𝓘(ℝ) 2 u U) (ha : ContMDiffOn I 𝓘(ℝ) ∞ a U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w +
        hessian I u x v w = a x * inner ℝ v w) :
    ContMDiffAt I 𝓘(ℝ) ∞ u x := by
  apply TauCeti.contMDiffAt_of_contDiffOn_localRiemannianIsometry hU hx hxi hu
  intro gE f hfiso hS hucomp
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  exact contDiffOn_of_ricciTensor_add_hessian_eq_mul_inner_model_space hS hucomp
    (hfiso.contDiffOn_comp ha)
    (fun z hz v w ↦ by
    have h := heq _ hz (mfderiv 𝓘(ℝ, E) I f z v) (mfderiv 𝓘(ℝ, E) I f z w)
    rw [hfiso.ricciTensor_mfderiv, hfiso.inner_mfderiv,
      ← hfiso.hessian_comp (hu.contMDiffAt (hU.mem_nhds hz))] at h
    exact h)

/-- On a Hausdorff boundaryless manifold a `C²` solution of `Ric + Hess u = a g` is smooth on every
open domain where the scalar coefficient is smooth. -/
theorem contMDiffOn_of_ricciTensor_add_hessian_eq_mul_inner [T2Space M] [BoundarylessManifold I M]
    {U : Set M} (hU : IsOpen U) {u a : M → ℝ} (hu : ContMDiffOn I 𝓘(ℝ) 2 u U)
    (ha : ContMDiffOn I 𝓘(ℝ) ∞ a U)
    (heq : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w +
        hessian I u x v w = a x * inner ℝ v w) :
    ContMDiffOn I 𝓘(ℝ) ∞ u U :=
  fun _ hx ↦ (contMDiffAt_of_ricciTensor_add_hessian_eq_mul_inner hU hx
    BoundarylessManifold.isInteriorPoint hu ha heq).contMDiffWithinAt

/-- Every `C²` gradient Ricci soliton potential for a smooth metric on a
Hausdorff boundaryless manifold is smooth. No completeness or sign condition is required. -/
theorem SatisfiesGradientRicciSolitonEquation.contMDiff [T2Space M] [BoundarylessManifold I M]
    {f : M → ℝ} {c : ℝ} (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f c)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) : ContMDiff I 𝓘(ℝ) ∞ f := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_of_ricciTensor_add_hessian_eq_mul_inner isOpen_univ hf.contMDiffOn
    contMDiff_const.contMDiffOn fun x _ v w ↦
      satisfiesGradientRicciSolitonEquation_iff.mp hsol x v w

end TauCeti.Manifold
