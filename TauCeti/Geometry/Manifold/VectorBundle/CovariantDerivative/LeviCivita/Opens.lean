/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Levi-Civita Christoffel maps on open subsets

For a `C¹` Riemannian metric on an open subset of a finite-dimensional real normed space,
metric compatibility and torsion-freeness identify the native Levi-Civita Christoffel map
with the second-kind Christoffel map of its coordinate bilinear-form field.

Adapted from the open-domain connection bridge in Yangyang Li's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/tree/b442a9f3077a4be3823b712ec92b2335dd34e771/ForTauCeti/Geometry/Manifold/Riemannian/Surface/Revolution).
-/

public noncomputable section

open Bundle FiberBundle Manifold Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Opens E} [RiemannianBundle (fun p : U ↦ TangentSpace 𝓘(ℝ, E) p)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) 1 E (fun p : U ↦ TangentSpace 𝓘(ℝ, E) p)]

local notation "IP" => 𝓘(ℝ, E)

/-- Metric compatibility in open coordinates differentiates the coefficient field while
holding both tangent coordinates fixed. -/
theorem fderiv_metric_opens_apply {ι : Type*} [Fintype ι]
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
      G p.val
        (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p z)))
    (b : Module.Basis ι ℝ E) (p : U) (u v w : E) :
    fderiv ℝ G p.val u v w =
      G p.val (christoffelMap b
        ((CovariantDerivative.leviCivitaConnection IP U).isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace IP) p).baseSet)) p v u) w +
      G p.val v (christoffelMap b
        ((CovariantDerivative.leviCivitaConnection IP U).isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace IP) p).baseSet)) p w u) := by
  let e := trivializationAt E (TangentSpace IP) p
  let cov := CovariantDerivative.leviCivitaConnection IP U
  have hb : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace IP) p
  have hV (a : E) : MDifferentiableAt IP ((IP).prod 𝓘(ℝ, E))
      (fun y ↦ TotalSpace.mk' E y (e.symm y a)) p :=
    ((contMDiffOn_symm_baseSet (n := 1) a).mdifferentiableOn one_ne_zero)
      |>.mdifferentiableAt (e.open_baseSet.mem_nhds hb)
  have hloc (a c : E) : (fun y ↦ inner ℝ (e.symm y a) (e.symm y c)) =ᶠ[𝓝 p]
      (fun y : U ↦ G y.val a c) := by
    filter_upwards [eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := IP) p,
      e.open_baseSet.mem_nhds hb] with y hy hyb
    rw [hmetric, ← e.symmL_apply (R := ℝ) hyb, ← e.symmL_apply (R := ℝ) hyb,
      hy a, hy c]
    simp only [TangentBundle.symmL_model_space]
    -- The model-space tangent identification and identity linear map both reduce to identity.
    rfl
  have hd : DifferentiableAt ℝ G p.val := by
    refine TauCeti.differentiableAt_clm_apply₂.mpr fun a b ↦ ?_
    have h := (mdifferentiableAt_inner (hV a) (hV b)).congr_of_eventuallyEq (hloc a b).symm
    exact (mdifferentiableAt_comp_subtype_val_iff.mp h) |> mdifferentiableAt_iff_differentiableAt.mp
  have hcomp := (CovariantDerivative.isMetricCompatible_leviCivitaConnection IP)
    |>.mvfderiv_inner_eq (fun y ↦ e.symm y u) (hV v) (hV w)
  dsimp only at hcomp
  rw [covariantDerivative_symm_apply_symm b
      (cov.isCovariantDerivativeOn (s := e.baseSet)) hb,
    covariantDerivative_symm_apply_symm b
      (cov.isCovariantDerivativeOn (s := e.baseSet)) hb, hmetric, hmetric] at hcomp
  have hread (a : TangentSpace IP p) :
      NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p a) = a := by
    rw [tangentSpaceOpenEquiv_apply]
    exact NormedSpace.fromTangentSpace_apply p.val a
  have hscalar := (hd.clm_apply (differentiableAt_const v)).clm_apply
    (differentiableAt_const w)
  have hres := mvfderiv_comp_apply (f := (Subtype.val : U → E))
    (g := fun x : E ↦ G x v w) p hscalar.mdifferentiableAt
    (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero) (e.symm p u)
  have hderiv : mvfderiv IP (fun y : U ↦ G y.val v w) p (e.symm p u) =
      fderiv ℝ (fun x : E ↦ G x v w) p.val u := by
    simp only [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe] at hres
    rw [hread] at hres
    simpa only [Function.comp_def, e, TangentBundle.trivializationAt_symm_apply_self] using hres
  rw [(hloc v w).mvfderiv_eq, hderiv,
    TauCeti.fderiv_bilin_apply hd (differentiableAt_const v) (differentiableAt_const w)] at hcomp
  simp only [hread] at hcomp
  simpa only [e, TangentBundle.trivializationAt_symm_apply_self,
    fderiv_const_apply, map_zero, zero_apply, add_zero] using hcomp

/-- The native Levi-Civita Christoffel map of a `C¹` metric on an open subset agrees with
its coordinate Christoffel map, with the field argument before the direction argument. -/
theorem christoffelMap_opens_eq_christoffelSecondKind {ι : Type*} [Fintype ι]
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
      G p.val
        (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p z)))
    (b : Module.Basis ι ℝ E) (p : U) :
    christoffelMap b
      ((CovariantDerivative.leviCivitaConnection IP U).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace IP) p).baseSet)) p =
      (christoffelSecondKind G p.val).flip := by
  let e := (tangentSpaceOpenEquiv (I := IP) p).trans (NormedSpace.fromTangentSpace p.val)
  have hi (v w : E) : G p.val v w = inner ℝ (e.symm v) (e.symm w) := by
    rw [hmetric]
    exact congrArg₂ (fun a b ↦ G p.val a b) (e.apply_symm_apply v) (e.apply_symm_apply w) |>.symm
  have hs : (G p.val).toBilinForm.IsSymm :=
    ContinuousLinearMap.isSymm_toBilinForm_iff.mpr fun v w ↦ by
      rw [hi, hi, real_inner_comm]
  have hsep : (G p.val).toBilinForm.SeparatingLeft := fun v hv ↦ by
    have h := hv v
    rw [ContinuousLinearMap.toBilinForm_apply, hi, inner_self_eq_zero] at h
    exact e.symm.injective (by simpa using h)
  have hnd := (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hs.isRefl).mpr hsep
  have ht := (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero
    (CovariantDerivative.leviCivitaConnection IP U)).mpr
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection IP).torsion
  have h := eq_christoffelSecondKind_of_fderiv_apply_eq hs hnd
    (A := (christoffelMap b
      ((CovariantDerivative.leviCivitaConnection IP U).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace IP) p).baseSet)) p).flip)
    (fun u v ↦ by
      simpa only [ContinuousLinearMap.flip_apply] using
        christoffelMap_comm ht b p (mem_extChartAt_source p) v u)
    (fun u v w ↦ fderiv_metric_opens_apply hmetric b p u v w)
  simpa only [ContinuousLinearMap.flip_flip] using congrArg ContinuousLinearMap.flip h

end TauCeti.Manifold
