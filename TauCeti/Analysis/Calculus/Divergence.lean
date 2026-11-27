/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Topology.Algebra.Module.Trace

/-!
# Divergence calculus identities

This file develops pointwise, continuity, and support lemmas for the divergence
`x ↦ LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E)` of a differentiable vector field on a
finite-dimensional real normed or inner product space, without any test-function or measure-theory
dependency.

## Main results

* `TauCeti.trace_fderiv_orthogonalLine_eq`: decomposes the divergence `tr (Df)` in orthogonal line
  coordinates along a unit vector `e` into the hyperplane divergence of the transverse projection
  `(ℝ ∙ e)ᗮ.orthogonalProjectionOnto ∘ f` plus the longitudinal derivative `d/ds ⟪e, f (y + s • e)⟫`
  along `e`.
* `TauCeti.trace_fderiv_smul_comp_mul`: pointwise Leibniz-and-chain-rule identity for the
  divergence of a rescaled field `z ↦ a z • A z (a z * u)`.
* `TauCeti.continuous_trace_fderiv_comp_mul`: joint continuity on `ℝ × E` of the two pieces in
  `TauCeti.trace_fderiv_smul_comp_mul`.
* `TauCeti.trace_fderiv_comp_mul_eq_zero_of_notMem`: vanishing of both pieces off a closed set
  outside which `A` vanishes.
-/

public section

namespace TauCeti

section OrthogonalLine

open scoped RealInnerProductSpace

/-- Decompose the divergence `tr (Df)` in orthogonal line coordinates along a unit vector `e` into
the hyperplane divergence of the transverse projection `(ℝ ∙ e)ᗮ.orthogonalProjectionOnto ∘ f`
plus the longitudinal derivative `d/ds ⟪e, f (y + s • e)⟫` along `e`. -/
theorem trace_fderiv_orthogonalLine_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F) (he : ‖e‖ = 1)
    {f : F → F} {y : (ℝ ∙ e)ᗮ} {t : ℝ} (hf : DifferentiableAt ℝ f ((y : F) + t • e)) :
    LinearMap.trace ℝ F (fderiv ℝ f ((y : F) + t • e) : F →ₗ[ℝ] F) =
      LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
            (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f ((z : F) + t • e))) y :
            (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ) +
        deriv (fun s : ℝ => ⟪e, f ((y : F) + s • e)⟫) t := by
  set P : F →L[ℝ] (ℝ ∙ e)ᗮ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hproj (x : F) : (P x : F) + ⟪e, x⟫ • e = x := by
    have hmem : x - ⟪e, x⟫ • e ∈ (ℝ ∙ e)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp [inner_sub_right, inner_smul_right, he]
    have hP : P x = ⟨x - ⟪e, x⟫ • e, hmem⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_orthogonalProjectionOnto_apply]
      exact Submodule.eq_starProjection_of_mem_orthogonal' hmem
        (Submodule.le_orthogonal_orthogonal _
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
        (sub_add_cancel x (⟪e, x⟫ • e)).symm
    rw [hP, Submodule.coe_mk, sub_add_cancel]
  set g : F → (ℝ ∙ e)ᗮ := fun x => P (f x)
  have hdecomp : f = fun x => (ℝ ∙ e)ᗮ.subtypeL (g x) + ⟪e, f x⟫ • e := by
    ext x
    exact (hproj (f x)).symm
  set x₀ : F := (y : F) + t • e
  have hgd : DifferentiableAt ℝ g x₀ := P.differentiableAt.comp x₀ hf
  have h1d : DifferentiableAt ℝ (fun x => (ℝ ∙ e)ᗮ.subtypeL (g x)) x₀ :=
    (ℝ ∙ e)ᗮ.subtypeL.differentiableAt.comp x₀ hgd
  have hinner : DifferentiableAt ℝ (fun x => ⟪e, f x⟫) x₀ :=
    (innerSL ℝ e).differentiableAt.comp x₀ hf
  conv_lhs =>
    rw [hdecomp, fderiv_fun_add h1d (hinner.smul_const e), ContinuousLinearMap.toLinearMap_add,
      map_add, fderiv_smul_const hinner, ContinuousLinearMap.coe_smulRight,
      LinearMap.trace_smulRight]
  congr 1
  · have hf1 : fderiv ℝ (fun x => (ℝ ∙ e)ᗮ.subtypeL (g x)) x₀ =
        (ℝ ∙ e)ᗮ.subtypeL.comp (fderiv ℝ g x₀) :=
      ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt.comp x₀ hgd.hasFDerivAt).fderiv
    have haff : HasFDerivAt (fun z : (ℝ ∙ e)ᗮ => (z : F) + t • e) (ℝ ∙ e)ᗮ.subtypeL y :=
      ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt (x := y)).add_const (t • e)
    have hf2 : fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => P (f ((z : F) + t • e))) y =
        (fderiv ℝ g x₀).comp (ℝ ∙ e)ᗮ.subtypeL :=
      (HasFDerivAt.comp (f := fun z : (ℝ ∙ e)ᗮ => (z : F) + t • e) y
        hgd.hasFDerivAt haff).fderiv
    rw [hf1, hf2, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.trace_comp_comm' _ _
  · have hl : HasDerivAt (fun s : ℝ => (y : F) + s • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add (y : F)
    exact (hinner.hasFDerivAt.comp_hasDerivAt t hl).deriv.symm

end OrthogonalLine

section RescaledField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Pointwise Leibniz-and-chain-rule identity for the divergence of a field rescaled along a
scalar function `a`: `z ↦ a z • A z (a z * u)`. -/
theorem trace_fderiv_smul_comp_mul {A : E → ℝ → E} {a : E → ℝ} {u : ℝ} {y : E}
    (hA : DifferentiableAt ℝ (Function.uncurry A) (y, a y * u))
    (ha : DifferentiableAt ℝ a y) :
    LinearMap.trace ℝ E (fderiv ℝ (fun z : E => a z • A z (a z * u)) y : E →ₗ[ℝ] E) =
      a y * LinearMap.trace ℝ E (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) +
        deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u := by
  have hmul : HasFDerivAt (fun z : E => a z * u) (u • fderiv ℝ a y) y := by
    simpa only [mul_comm] using (ha.hasFDerivAt.const_mul u).congr_of_eventuallyEq
      (.of_forall fun z => mul_comm (a z) u)
  have hAd : DifferentiableAt ℝ (A y) (a y * u) :=
    hA.comp (a y * u) (differentiableAt_const y |>.prodMk differentiableAt_id)
  have hcomp_diff : DifferentiableAt ℝ (fun z : E => A z (a z * u)) y :=
    hA.fun_comp' y (differentiableAt_id.prodMk hmul.differentiableAt)
  have hcomp_eq : fderiv ℝ (fun z : E => A z (a z * u)) y =
      fderiv ℝ (fun z : E => A z (a y * u)) y +
        (u • fderiv ℝ a y).smulRight (deriv (A y) (a y * u)) := by
    ext v
    have hg := fderiv_comp_graph_apply (f := Function.uncurry A) hmul.differentiableAt hA v
    have hleft := congrArg (fun L => L v) (fderiv_slice_left hA)
    simp only [Function.uncurry, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      at hg hleft
    rw [hg, ← hleft, hmul.fderiv, hAd.hasDerivAt.hasFDerivAt.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  have hlin : HasDerivAt (fun s : ℝ => a y * s) (a y) u := by
    simpa using (hasDerivAt_id u).const_mul (a y)
  have hsm := (hasDerivAt_id u).smul (hAd.hasDerivAt.scomp u hlin)
  have hΦd : HasDerivAt (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s)))
      (fderiv ℝ a y (u • (a y • deriv (A y) (a y * u)) + (1 : ℝ) • A y (a y * u))) u :=
    (fderiv ℝ a y).hasFDerivAt.comp_hasDerivAt u hsm
  rw [fderiv_fun_smul ha hcomp_diff, hcomp_eq, smul_add, ContinuousLinearMap.toLinearMap_add,
    map_add, ContinuousLinearMap.toLinearMap_add, map_add, hΦd.deriv]
  simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_smulRight,
    LinearMap.trace_smulRight, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, map_add, map_smul, one_smul]
  ring

/-- Continuity on `ℝ × E` of the two pieces in `TauCeti.trace_fderiv_smul_comp_mul`. -/
theorem continuous_trace_fderiv_comp_mul {A : E → ℝ → E}
    (hA : ContDiff ℝ 1 (Function.uncurry A)) {a : E → ℝ} (ha : ContDiff ℝ 1 a) :
    Continuous (fun q : ℝ × E =>
        a q.2 * LinearMap.trace ℝ E
          (fderiv ℝ (fun z : E => A z (a q.2 * q.1)) q.2 : E →ₗ[ℝ] E)) ∧
      Continuous (fun q : ℝ × E =>
        deriv (fun s : ℝ => fderiv ℝ a q.2 (s • A q.2 (a q.2 * s))) q.1) := by
  have hFA : (fun p : E × ℝ => fderiv ℝ (fun z : E => A z p.2) p.1) =
      fun p => (fderiv ℝ (Function.uncurry A) p).comp (.inl ℝ E ℝ) :=
    funext fun p => fderiv_slice_left (hA.differentiable one_ne_zero (p.1, p.2))
  have hFA_cont : Continuous (fun p : E × ℝ => fderiv ℝ (fun z : E => A z p.2) p.1) := by
    rw [hFA]
    exact (((ContinuousLinearMap.compL ℝ E (E × ℝ) E).flip (.inl ℝ E ℝ)).continuous.comp
      (hA.continuous_fderiv one_ne_zero))
  have hP1 : Continuous (fun q : ℝ × E =>
      a q.2 * LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => A z (a q.2 * q.1)) q.2 : E →ₗ[ℝ] E)) := by
    simp_rw [← traceCLM_apply]
    exact (ha.continuous.comp continuous_snd).mul <|
      (traceCLM ℝ E).continuous.comp <| hFA_cont.comp
        (continuous_snd.prodMk ((ha.continuous.comp continuous_snd).mul continuous_fst))
  have hWu : ContDiff ℝ 1 (fun q : ℝ × E => a q.2 • A q.2 (a q.2 * q.1)) :=
    (ha.comp contDiff_snd).smul
      (hA.comp (contDiff_snd.prodMk ((ha.comp contDiff_snd).mul contDiff_fst)))
  have hdiv_eq : (fun q : ℝ × E => LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => a z • A z (a z * q.1)) q.2 : E →ₗ[ℝ] E)) =
      fun q => traceCLM ℝ E
        ((fderiv ℝ (fun p : ℝ × E => a p.2 • A p.2 (a p.2 * p.1)) q).comp (.inr ℝ ℝ E)) :=
    funext fun q => by
      rw [← traceCLM_apply]
      exact congrArg (traceCLM ℝ E)
        (fderiv_slice_right (f := fun p : ℝ × E => a p.2 • A p.2 (a p.2 * p.1))
          (hWu.differentiable one_ne_zero (q.1, q.2)))
  have hdiv : Continuous (fun q : ℝ × E => LinearMap.trace ℝ E
      (fderiv ℝ (fun z : E => a z • A z (a z * q.1)) q.2 : E →ₗ[ℝ] E)) := by
    rw [hdiv_eq]
    exact (traceCLM ℝ E).continuous.comp
      (((ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip (.inr ℝ ℝ E)).continuous.comp
        (hWu.continuous_fderiv one_ne_zero))
  refine ⟨hP1, ?_⟩
  convert hdiv.sub hP1 using 1
  ext ⟨u, y⟩
  simp only [Pi.sub_apply]
  linarith [trace_fderiv_smul_comp_mul
    (hA.differentiable one_ne_zero (y, a y * u)) (ha.differentiable one_ne_zero y)]

omit [FiniteDimensional ℝ E] in
/-- Off a closed set `K` outside which `A` vanishes, both pieces in
`TauCeti.trace_fderiv_smul_comp_mul` vanish. -/
theorem trace_fderiv_comp_mul_eq_zero_of_notMem {K : Set E} (hK : IsClosed K)
    {A : E → ℝ → E} (hA0 : ∀ {y : E}, y ∉ K → ∀ t, A y t = 0) (a : E → ℝ) (u : ℝ)
    {y : E} (hy : y ∉ K) :
    a y * LinearMap.trace ℝ E (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) = 0 ∧
      deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u = 0 := by
  refine ⟨?_, ?_⟩
  · have hloc : (fun z : E => A z (a y * u)) =ᶠ[nhds y] 0 :=
      Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hy) fun z hz => hA0 hz _
    simp [hloc.fderiv_eq]
  · have hloc : (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) = 0 :=
      funext fun s => by simp [hA0 hy]
    rw [hloc]
    simp

end RescaledField

end TauCeti
