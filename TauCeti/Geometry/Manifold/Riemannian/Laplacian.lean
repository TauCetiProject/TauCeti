/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Giada Franz, Otis Chodosh
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Topology.Algebra.Module.Trace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
import TauCeti.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Divergence, Hessian, and Laplace–Beltrami operators

This file introduces the pointwise Riemannian divergence as the trace of the Levi–Civita
covariant derivative, the scalar Hessian obtained by pairing that derivative of the gradient,
and the Laplace–Beltrami operator with the convention `Δ = div ∘ grad`.  The orthonormal-basis
trace formula makes the relationship between the Laplacian and the Hessian explicit, and
`ModelWithCorners.laplaceBeltrami_eq_metricTrace_hessianForm` identifies the Laplacian with the
metric trace of the Hessian as a continuous bilinear form `ModelWithCorners.hessianForm`, which is
symmetric and linear in the function at points of `C²` regularity. The operator
laws include the Leibniz rule and the chain rule `Δ (h ∘ f) = h'(f) Δ f + h''(f) |grad f|²` for a
real function `h`, with its special case `Δ (log f) = Δ f / f - |grad f|² / f²`. On a
finite-dimensional normed space whose metric is a field of bilinear forms `g`, the Hessian in
linear coordinates is `D²f(u, v) - Df(Γ(u, v))` with `Γ` the Christoffel symbols of `g`. On a
finite-dimensional inner-product space, the operator agrees with Mathlib's
flat Laplacian. The Hessian conventions follow Lee, *Introduction to Riemannian Manifolds*,
Chapter 3.

The Laplace–Beltrami locality lemmas are adapted from Giada Franz's locality helper.
The operator depends only on the germ of the function: locally equal functions have equal
Laplacians when the gradient is differentiable at the point, and the Laplacian vanishes off
the function's topological support without any regularity assumption.

The pointwise Hessian linearity lemmas are adapted from Otis Chodosh's formalization in
`riccardobrasca/ColdingMinicozziTheory`,
`ForTauCeti/Geometry/Manifold/Riemannian/Hessian/Contact.lean`,
revision `d540eafdb38a37ee49e7298d601131ceaa207ced`.
-/

noncomputable section
public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The Riemannian divergence of a vector field, defined as the trace of its
Levi–Civita covariant derivative. -/
noncomputable def divergence (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : (x : M) → TangentSpace I x) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x)
    (CovariantDerivative.leviCivitaConnection I M X x).toLinearMap

theorem divergence_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : (x : M) → TangentSpace I x) (x : M) :
    divergence I X x =
      LinearMap.trace ℝ (TangentSpace I x)
        (CovariantDerivative.leviCivitaConnection I M X x).toLinearMap := by
  rw [divergence]

/-- A `C^(n + 1)` vector field on a `C^m` Riemannian manifold with `C^k` metric has `C^n`
divergence when `n + 2 ≤ m` and `n + 1 ≤ k`. -/
theorem contMDiff_divergence {n m k : ℕ∞ω}
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M] [IsManifold I m M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent (n + 1)
      (fun y ↦ (⟨y, X y⟩ : TangentBundle I M))) :
    ContMDiff I 𝓘(ℝ) n (divergence I X) := by
  have hA : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        ((CovariantDerivative.leviCivitaConnection I M X y))) Set.univ := by
    exact CovariantDerivative.contMDiffOn_leviCivitaConnection (n := n) (m := m) (k := k)
      isOpen_univ hm hk hX.contMDiffOn
  intro x
  let _ : IsManifold I (n + 1) M := IsManifold.of_le (n := m)
    ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let e := trivializationAt E (TangentSpace I) x
  let eh := e.continuousLinearMap (RingHom.id ℝ) e
  have he : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        ((CovariantDerivative.leviCivitaConnection I M X y))) e.baseSet := hA.mono (by simp)
  have heh : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n
      (fun y ↦ (eh ⟨y, CovariantDerivative.leviCivitaConnection I M X y⟩).2) e.baseSet := by
    rw [← eh.contMDiffOn_section_iff e.open_baseSet (by simp [eh])]
    exact he
  have ht : ContMDiffOn I 𝓘(ℝ) n
      (fun y ↦ TauCeti.traceCLM ℝ E
        ((eh ⟨y, CovariantDerivative.leviCivitaConnection I M X y⟩).2)) e.baseSet := by
    exact ContMDiffOn.clm_apply contMDiffOn_const heh
  have hEq (y : M) (hy : y ∈ e.baseSet) :
      TauCeti.traceCLM ℝ E ((eh ⟨y, CovariantDerivative.leviCivitaConnection I M X y⟩).2) =
        divergence I X y := by
    let L := e.continuousLinearEquivAt ℝ y hy
    have hconj : (eh ⟨y, CovariantDerivative.leviCivitaConnection I M X y⟩).2 =
        L.toContinuousLinearMap.comp
          ((CovariantDerivative.leviCivitaConnection I M X y).comp
            L.symm.toContinuousLinearMap) := by
      ext v
      simp [eh, L, Bundle.Trivialization.continuousLinearMap_apply,
        Bundle.Trivialization.symm_continuousLinearEquivAt_eq',
        e.continuousLinearMapAt_apply_of_mem ℝ hy]
    rw [hconj, TauCeti.traceCLM_apply, divergence]
    have hcomp :
        (L.toContinuousLinearMap.comp
          ((CovariantDerivative.leviCivitaConnection I M X y).comp
            L.symm.toContinuousLinearMap)).toLinearMap =
          L.toLinearEquiv.conj
            (CovariantDerivative.leviCivitaConnection I M X y).toLinearMap := by
      ext v
      rfl
    rw [hcomp, LinearMap.trace_conj']
  refine (ht.congr (fun y hy ↦ (hEq y hy).symm)).contMDiffAt
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x))

/-- The divergence of a smooth vector field on a smooth Riemannian manifold with smooth metric is
smooth. -/
theorem _root_.ContMDiffSection.contMDiff_divergence {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (divergence I fun x ↦ X x) :=
  TauCeti.Manifold.contMDiff_divergence (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp)
    (by simpa using X.contMDiff)

/-- The scalar Hessian of `f` at `x` as a continuous bilinear form on the tangent space,
`(v, w) ↦ ⟪∇_v grad f, w⟫`: the metric lowering of the Levi–Civita covariant derivative of the
gradient. Its values are `TauCeti.Manifold.hessian` (`ModelWithCorners.hessianForm_apply`). -/
noncomputable def _root_.ModelWithCorners.hessianForm (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (innerSL ℝ).comp (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x)

/-- The Hessian form is the metric lowering `innerSL ℝ ∘L ∇ grad f` of the Levi–Civita covariant
derivative of the gradient. -/
theorem _root_.ModelWithCorners.hessianForm_def (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) :
    I.hessianForm f x =
      (innerSL ℝ).comp (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x) := by
  rw [ModelWithCorners.hessianForm]

/-- The scalar Hessian of `f`, pairing the covariant derivative of its gradient with a second
tangent vector: the values of `ModelWithCorners.hessianForm`. -/
noncomputable def hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  I.hessianForm f x v w

theorem hessian_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I f x v w =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x v) w := by
  rw [hessian, I.hessianForm_def, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

@[simp]
theorem _root_.ModelWithCorners.hessianForm_apply (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    I.hessianForm f x v w = hessian I f x v w := by
  rw [hessian]

section HessianGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] {f : M → ℝ}

/-- Vanishing of the Hessian in one tangent direction makes the covariant derivative of the
gradient vanish in that direction. -/
theorem leviCivitaConnection_mgradient_eq_zero_of_hessian_eq_zero
    (x : M) (v : TangentSpace I x) (hzero : ∀ w, hessian I f x v w = 0) :
    CovariantDerivative.leviCivitaConnection I M (mgradient I f) x v = 0 := by
  apply ext_inner_right ℝ
  intro w
  simpa only [hessian_def, inner_zero_left] using hzero w

end HessianGradient

section HessianSymmetry

variable {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A pure-trace Hessian identifies the covariant derivative of the gradient pointwise. -/
theorem leviCivitaConnection_mgradient_of_hessian_eq_mul_inner [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} {x : M} {a : ℝ}
    (h : ∀ u v : TangentSpace I x, hessian I f x u v = a * inner ℝ u v)
    (u : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M (mgradient I f) x u = a • u := by
  apply ext_inner_right ℝ
  intro v
  rw [← hessian_def, h, real_inner_smul_left]

/-- The Hessian applied to a vector field and a differentiable vector field is the directional
derivative of the directional derivative of `f`, minus the derivative in the covariant derivative
direction. -/
theorem hessian_apply_eq_mvfderiv_sub [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} (x : M) (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (V W : (y : M) → TangentSpace I y)
    (hW : MDiffAt (T% W) x) :
    hessian I f x (V x) (W x) =
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
        mvfderiv I f x ((CovariantDerivative.leviCivitaConnection I M W) x (V x)) := by
  let _ : IsManifold I (1 + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hG : ContMDiffAt I I.tangent 1
      (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x := by
    simpa only [one_add_one_eq_two] using
      (contMDiffAt_mgradient (I := I) (f := f) (x := x) (n := 1)
        (by simpa only [one_add_one_eq_two] using hf))
  have hG' : MDiffAt (T% (mgradient I f)) x := hG.mdifferentiableAt (by simp)
  have hinner :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      V (σ := mgradient I f) (τ := W) hG' hW
  have hinner' : (fun y ↦ inner ℝ (mgradient I f y) (W y)) =
      (fun y ↦ mvfderiv I f y (W y)) := by
    funext y
    exact inner_mgradient (I := I) (f := f) (x := y) (W y)
  rw [hinner'] at hinner
  have _ :
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) =
        inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x (V x))
            (W x) +
          inner ℝ (mgradient I f x)
            ((CovariantDerivative.leviCivitaConnection I M W) x (V x)) := by
    simpa only [Function.comp_apply] using hinner
  have hgrad := inner_mgradient (I := I) (f := f) (x := x)
    ((CovariantDerivative.leviCivitaConnection I M W) x (V x))
  rw [hessian_def]
  linarith

/-- The Hessian of a twice continuously differentiable function is symmetric for the
Levi–Civita connection. -/
theorem hessian_symm [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} (x : M) (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TangentSpace I x) :
    hessian I f x v w = hessian I f x w v := by
  let V : (y : M) → TangentSpace I y := FiberBundle.extend E v
  let W : (y : M) → TangentSpace I y := FiberBundle.extend E w
  have hV : MDiffAt (T% V) x := FiberBundle.mdifferentiableAt_extend I E v
  have hW : MDiffAt (T% W) x := FiberBundle.mdifferentiableAt_extend I E w
  have hessianVW := hessian_apply_eq_mvfderiv_sub x hf V W hW
  have hessianWV := hessian_apply_eq_mvfderiv_sub x hf W V hV
  have hmin : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := 2) hmin
  -- The mixed-derivative identity and torsion-freeness identify the remaining bracket term.
  have hbracket := mvfderiv_mlieBracket (I := I) (𝕜 := ℝ) (F := ℝ)
    (n := (2 : ℕ∞ω)) hf (by simp) hV hW
  have hzero :
      (CovariantDerivative.leviCivitaConnection I M).torsion x (V x) (W x) = 0 := by
    rw [CovariantDerivative.torsion_leviCivitaConnection_eq_zero I]
    simp
  have htw := CovariantDerivative.torsion_apply
    (CovariantDerivative.leviCivitaConnection I M) hV hW
  rw [hzero] at htw
  have htw' :
      CovariantDerivative.leviCivitaConnection I M W x (V x) -
          CovariantDerivative.leviCivitaConnection I M V x (W x) =
        VectorField.mlieBracket I V W x := by
    exact sub_eq_zero.mp htw.symm
  dsimp [V, W] at hessianVW hessianWV htw' hbracket
  simp only [FiberBundle.extend_apply_self] at hessianVW hessianWV htw' hbracket
  have htw_mvfderiv := congrArg (mvfderiv I f x) htw'
  simp only [map_sub] at htw_mvfderiv
  -- The two directional-derivative equations now differ only by the torsion equation.
  rw [hessianVW, hessianWV]
  linarith [hbracket, htw_mvfderiv]

/-- The Hessian divided by a nonvanishing function `f`: for the Levi-Civita connection `D`,
`(Y f / f) (X f / f) + X (Y f / f) - (D_X Y) f / f = Hess f(X,Y) / f` where `f` does not
vanish. -/
theorem hessian_div_eq_mvfderiv_add [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (hf₀ : f x ≠ 0) (X : Π x : M, TangentSpace I x) :
    (mvfderiv I f x (Y x) / f x) * (mvfderiv I f x (X x) / f x) +
        mvfderiv I (fun x ↦ mvfderiv I f x (Y x) / f x) x (X x) -
        mvfderiv I f x (CovariantDerivative.leviCivitaConnection I M Y x (X x)) / f x =
      hessian I f x (X x) (Y x) / f x := by
  have hfx : MDiffAt f x := hf.mdifferentiableAt (by simp)
  have hdY : MDiffAt (fun x ↦ mvfderiv I f x (Y x)) x :=
    mdifferentiableAt_mvfderiv_apply hf le_rfl hY
  rw [hessian_apply_eq_mvfderiv_sub x hf X Y hY]
  have hinv : mvfderiv I (fun x ↦ (f x)⁻¹) x (X x) =
      -(f x ^ 2)⁻¹ * mvfderiv I f x (X x) := by
    simpa only [Function.comp_def, fderiv_inv, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_comm] using
      (mvfderiv_comp_apply_of_differentiableAt
        (differentiableAt_inv hf₀) hfx (X x))
  simp only [div_eq_mul_inv]
  rw [mvfderiv_fun_mul (g := fun x ↦ (f x)⁻¹) hdY (hfx.inv hf₀)]
  simp only [add_apply, smul_apply, smul_eq_mul, hinv]
  field_simp [hf₀]
  ring

end HessianSymmetry

/-- The Laplace–Beltrami operator, with the sign convention `Δ = div ∘ grad`. -/
noncomputable def laplaceBeltrami (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) : ℝ :=
  divergence I (mgradient I f) x

theorem laplaceBeltrami_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) :
    laplaceBeltrami I f x = divergence I (mgradient I f) x := by
  rw [laplaceBeltrami]

/-- For a Laplace–Beltrami eigenfunction, the derivative of its Laplacian along its
gradient is minus the eigenvalue times the squared gradient norm. -/
theorem mvfderiv_laplaceBeltrami_mgradient_of_laplaceBeltrami_eq_neg_mul
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} {lam : ℝ} (heig : ∀ x, laplaceBeltrami I f x = -lam * f x) (x : M) :
    mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) =
      -lam * ‖mgradient I f x‖ ^ 2 := by
  have heq : laplaceBeltrami I f = -lam • f := funext heig
  rw [heq, mvfderiv_const_smul_field, smul_apply, smul_eq_mul,
    ← inner_mgradient, real_inner_self_eq_norm_sq]

/-- On a `C^m` manifold with a `C^k` Riemannian metric, the Laplace--Beltrami operator of a
`C^(n + 2)` function is `C^n` when `n + 2 ≤ m` and `n + 1 ≤ k`; like the flat Laplacian, it
loses two derivatives.  The finite-regularity statement is useful when the operator is used under
an integral, where smoothness of the resulting scalar function must be supplied explicitly. -/
theorem contMDiff_laplaceBeltrami {n m k : ℕ∞ω}
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M] [IsManifold I m M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) (n + 2) f) :
    ContMDiff I 𝓘(ℝ) n (laplaceBeltrami I f) := by
  let _ : IsManifold I (n + 1 + 1) M := IsManifold.of_le (n := m) (by
    simpa only [add_assoc, one_add_one_eq_two] using hm)
  let _ : IsContMDiffRiemannianBundle I (n + 1) E
      (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) hk
  have hgrad : ContMDiff I I.tangent (n + 1)
      (fun x ↦ (⟨x, mgradient I f x⟩ : TangentBundle I M)) := by
    simpa only [add_assoc] using
      (contMDiff_mgradient (I := I) (n := n + 1)
        (f := f) (by simpa only [add_assoc, one_add_one_eq_two] using hf))
  have hdiv := contMDiff_divergence (I := I) (n := n) (m := m) (k := k) hm hk hgrad
  have hEq : laplaceBeltrami I f = divergence I (mgradient I f) := by
    funext x
    exact laplaceBeltrami_def I f x
  rw [hEq]
  exact hdiv

/-- For a `C¹` Riemannian metric, the Laplace--Beltrami operator of a `C²` function is
continuous. -/
theorem continuous_laplaceBeltrami
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    Continuous (laplaceBeltrami I f) :=
  (contMDiff_laplaceBeltrami (n := 0) (m := 2) (k := 1) (by simp) (by simp)
    (by simpa using hf)).continuous

section OperatorLaws

variable (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The divergence of the zero vector field is zero. -/
@[simp]
theorem divergence_zero (x : M) : divergence I 0 x = 0 := by
  simp [divergence]

/-- Locally equal vector fields have equal divergence at a point where one is differentiable. -/
theorem divergence_congr_of_eventuallyEq {X Y : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
    (h : ∀ᶠ y in nhds x, X y = Y y) : divergence I X x = divergence I Y x := by
  have hT : (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) =ᶠ[nhds x]
      fun y ↦ (⟨y, X y⟩ : TangentBundle I M) :=
    h.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy.symm
  rw [divergence_def, divergence_def,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hX (hX.congr_of_eventuallyEq hT) Filter.univ_mem h]

/-- Divergence is additive at a point where both vector fields are differentiable. -/
theorem divergence_add (X Y : (x : M) → TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) :
    divergence I (X + Y) x = divergence I X x + divergence I Y x := by
  simp only [divergence,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hX hY,
    ContinuousLinearMap.toLinearMap_add, map_add]

/-- Divergence commutes with a real constant at a differentiability point of the field. -/
theorem divergence_smul (c : ℝ) (X : (x : M) → TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x) :
    divergence I (c • X) x = c * divergence I X x := by
  simp [divergence,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const c hX,
    ContinuousLinearMap.toLinearMap_smul]

/-- Product rule for the divergence at a point where `f` and `X` are differentiable:
`divergence I (f • X) x = f x * divergence I X x + mvfderiv I f x (X x)`.
This is the pointwise input for integrating the Laplace--Beltrami operator by parts. -/
theorem divergence_smul_function (f : M → ℝ) (X : (x : M) → TangentSpace I x) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x) :
    divergence I (f • X) x = f x * divergence I X x + mvfderiv I f x (X x) := by
  have h := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.leibniz
    hX hf
  rw [divergence, h]
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add,
    map_smul]
  -- Name the projection from the continuous rank-one constructor before applying the trace rule.
  have h_smulRight :
      ((d% f x).smulRight (X x)).toLinearMap = (d% f x).toLinearMap.smulRight (X x) := by
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe]
  -- The `d%` notation is `mvfderiv`; use its named coercion fact at the final application.
  have h_trace :
      LinearMap.trace ℝ (TangentSpace I x) ((d% f x).smulRight (X x)).toLinearMap =
        mvfderiv I f x (X x) := by
    rw [h_smulRight, LinearMap.trace_smulRight]
    exact congrFun (ContinuousLinearMap.coe_coe (d% f x)) (X x)
  rw [h_trace]
  simp only [smul_eq_mul, divergence]

/-- Divergence is additive over a finite family of vector fields, at a point where every field is
differentiable. -/
theorem divergence_finsetSum {ι : Type*} (s : Finset ι) (X : ι → (x : M) → TangentSpace I x)
    (x : M)
    (hX : ∀ i ∈ s, MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X i y⟩ : TangentBundle I M)) x) :
    divergence I (fun y ↦ ∑ i ∈ s, X i y) x = ∑ i ∈ s, divergence I (X i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact divergence_zero I x
  | insert i s hi h =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hX
    simp only [Finset.sum_insert hi, ← h hX.2]
    exact divergence_add I (X i) (fun y ↦ ∑ j ∈ s, X j y) x hX.1
      (MDifferentiableAt.sum_section hX.2)

/-- The divergence vanishes off the topological support of a vector field, since the field is zero
near such a point. No regularity of the field is needed. -/
theorem divergence_eq_zero_of_notMem_tsupport {X : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∉ tsupport (α := E) X) : divergence I X x = 0 := by
  have h : (fun y ↦ (X y : E)) =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have hT : (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) =ᶠ[nhds x]
      fun y ↦ (⟨y, (0 : (x : M) → TangentSpace I x) y⟩ : TangentBundle I M) :=
    h.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy
  have h0 : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, (0 : (x : M) → TangentSpace I x) y⟩ : TangentBundle I M)) x :=
    mdifferentiableAt_zeroSection ..
  have hcov := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
  rw [divergence_def, hcov.congr_of_eventuallyEq (h0.congr_of_eventuallyEq hT) h0 Filter.univ_mem h,
    hcov.zero]
  simp

/-- The divergence of a compactly supported vector field is compactly supported. -/
protected theorem _root_.HasCompactSupport.divergence {X : (x : M) → TangentSpace I x}
    (hX : HasCompactSupport (β := E) X) : HasCompactSupport (divergence I X) :=
  hX.mono' fun _ hx ↦ by_contra fun h ↦ hx (divergence_eq_zero_of_notMem_tsupport I h)

/-- The Laplace--Beltrami operator of a compactly supported function is compactly supported. -/
protected theorem _root_.HasCompactSupport.laplaceBeltrami {f : M → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (laplaceBeltrami I f) :=
  (hf.mgradient I).divergence I

/-- The Hessian of a constant function is zero. -/
@[simp]
theorem hessian_const (c : ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I (fun _ : M ↦ c) x v w = 0 := by
  simp [hessian_def]

/-- The Hessian of the zero function is zero. -/
@[simp]
theorem hessian_zero (x : M) (v w : TangentSpace I x) :
    hessian I (0 : M → ℝ) x v w = 0 :=
  hessian_const I 0 x v w

/-- The Hessian form is additive at `x` when both functions are differentiable near `x` and
their gradients are differentiable at `x`. -/
theorem _root_.ModelWithCorners.hessianForm_add_of_mdifferentiableAt_mgradient {f g : M → ℝ}
    {x : M} (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) f y)
    (hg : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) g y)
    (hf' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (hg' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I g y⟩ : TangentBundle I M)) x) :
    I.hessianForm (f + g) x = I.hessianForm f x + I.hessianForm g x := by
  have hev := mgradient_add_eventuallyEq hf hg
  have hsum := mdifferentiableAt_add_section hf' hg'
  have hcov := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
  rw [I.hessianForm_def, I.hessianForm_def, I.hessianForm_def,
    hcov.congr_of_eventuallyEq
      (hsum.congr_of_eventuallyEq (hev.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy))
      hsum Filter.univ_mem hev,
    hcov.add hf' hg', ContinuousLinearMap.comp_add]

/-- The Hessian is additive at `x` when both functions are differentiable near `x` and their
gradients are differentiable at `x`. -/
theorem hessian_add_of_mdifferentiableAt_mgradient {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) f y)
    (hg : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) g y)
    (hf' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (hg' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I g y⟩ : TangentBundle I M)) x)
    (v w : TangentSpace I x) :
    hessian I (f + g) x v w = hessian I f x v w + hessian I g x v w := by
  rw [← I.hessianForm_apply, I.hessianForm_add_of_mdifferentiableAt_mgradient hf hg hf' hg',
    add_apply, add_apply, I.hessianForm_apply, I.hessianForm_apply]

/-- The Hessian form commutes with constant scalar multiplication at a point where the gradient
is differentiable. -/
theorem _root_.ModelWithCorners.hessianForm_smul_of_mdifferentiableAt_mgradient (c : ℝ)
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x) :
    I.hessianForm (c • f) x = c • I.hessianForm f x := by
  rw [I.hessianForm_def, I.hessianForm_def, mgradient_smul,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const c hf,
    ContinuousLinearMap.comp_smul]

/-- The Hessian commutes with constant scalar multiplication at a point where the gradient is
differentiable. -/
theorem hessian_smul_of_mdifferentiableAt_mgradient (c : ℝ) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (v w : TangentSpace I x) :
    hessian I (c • f) x v w = c * hessian I f x v w := by
  rw [← I.hessianForm_apply, I.hessianForm_smul_of_mdifferentiableAt_mgradient c hf, smul_apply,
    smul_apply, I.hessianForm_apply, smul_eq_mul]

/-- Negating a function negates its Hessian form at a point where its gradient is
differentiable. -/
theorem _root_.ModelWithCorners.hessianForm_neg_of_mdifferentiableAt_mgradient {f : M → ℝ}
    {x : M}
    (hf : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x) :
    I.hessianForm (-f) x = -I.hessianForm f x := by
  rw [← neg_one_smul ℝ f, I.hessianForm_smul_of_mdifferentiableAt_mgradient (-1) hf,
    neg_one_smul ℝ (I.hessianForm f x)]

/-- Negating a function negates its Hessian at a point where its gradient is differentiable. -/
theorem hessian_neg_of_mdifferentiableAt_mgradient {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (v w : TangentSpace I x) :
    hessian I (-f) x v w = -hessian I f x v w := by
  rw [← I.hessianForm_apply, I.hessianForm_neg_of_mdifferentiableAt_mgradient hf, neg_apply,
    neg_apply, I.hessianForm_apply]

/-- The Hessian respects subtraction at `x` when both functions are differentiable near `x` and
their gradients are differentiable at `x`. -/
theorem hessian_sub_of_mdifferentiableAt_mgradient {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) f y)
    (hg : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) g y)
    (hf' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (hg' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I g y⟩ : TangentBundle I M)) x)
    (v w : TangentSpace I x) :
    hessian I (f - g) x v w = hessian I f x v w - hessian I g x v w := by
  have hneg : mgradient I (-g) = -mgradient I g := funext fun _ ↦ mgradient_neg
  have hg'' : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, mgradient I (-g) y⟩ : TangentBundle I M)) x := by
    rw [hneg]
    exact mdifferentiableAt_neg_section hg'
  rw [sub_eq_add_neg, hessian_add_of_mdifferentiableAt_mgradient I hf (hg.mono fun _ hy ↦ hy.neg)
    hf' hg'', hessian_neg_of_mdifferentiableAt_mgradient I hg', sub_eq_add_neg]

/-- The Hessian form respects subtraction at `x` when both functions are differentiable near `x`
and their gradients are differentiable at `x`. -/
theorem _root_.ModelWithCorners.hessianForm_sub_of_mdifferentiableAt_mgradient {f g : M → ℝ}
    {x : M} (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) f y)
    (hg : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) g y)
    (hf' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (hg' : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I g y⟩ : TangentBundle I M)) x) :
    I.hessianForm (f - g) x = I.hessianForm f x - I.hessianForm g x :=
  ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ by
    rw [sub_apply, sub_apply, I.hessianForm_apply, I.hessianForm_apply, I.hessianForm_apply,
      hessian_sub_of_mdifferentiableAt_mgradient I hf hg hf' hg']

/-- The Hessian form of a function that is `C²` at `x` is symmetric. -/
theorem _root_.ModelWithCorners.flip_hessianForm {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) : (I.hessianForm f x).flip = I.hessianForm f x :=
  ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ by
    rw [ContinuousLinearMap.flip_apply, I.hessianForm_apply, I.hessianForm_apply,
      hessian_symm x hf]

/-- The Hessian form of a constant function is zero. -/
@[simp]
theorem _root_.ModelWithCorners.hessianForm_const (c : ℝ) (x : M) :
    I.hessianForm (fun _ : M ↦ c) x = 0 :=
  ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ by
    rw [I.hessianForm_apply, hessian_const, zero_apply, zero_apply]

/-- The Hessian form of the zero function is zero. -/
@[simp]
theorem _root_.ModelWithCorners.hessianForm_zero (x : M) : I.hessianForm (0 : M → ℝ) x = 0 :=
  I.hessianForm_const 0 x

/-- The Hessian is additive on twice continuously differentiable functions. -/
theorem hessian_add {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) (v w : TangentSpace I x) :
    hessian I (f + g) x v w = hessian I f x v w + hessian I g x v w :=
  hessian_add_of_mdifferentiableAt_mgradient I
    (.of_forall fun y ↦ (hf y).mdifferentiableAt two_ne_zero)
    (.of_forall fun y ↦ (hg y).mdifferentiableAt two_ne_zero)
    (mdifferentiableAt_mgradient (hf x)) (mdifferentiableAt_mgradient (hg x)) v w

/-- The Hessian commutes with multiplication of a `C²` function by a real constant. -/
theorem hessian_smul (c : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (x : M) (v w : TangentSpace I x) :
    hessian I (c • f) x v w = c * hessian I f x v w :=
  hessian_smul_of_mdifferentiableAt_mgradient I c (mdifferentiableAt_mgradient (hf x)) v w

/-- The Laplace–Beltrami operator vanishes on constants. -/
@[simp]
theorem laplaceBeltrami_const (c : ℝ) (x : M) :
    laplaceBeltrami I (fun _ : M ↦ c) x = 0 := by
  simp [laplaceBeltrami]

/-- The Laplace–Beltrami operator vanishes on the zero function. -/
@[simp]
theorem laplaceBeltrami_zero (x : M) : laplaceBeltrami I (0 : M → ℝ) x = 0 :=
  laplaceBeltrami_const I 0 x

/-- Locally equal functions have equal Laplace–Beltrami operators at a point where the gradient
of one function is differentiable. -/
theorem laplaceBeltrami_congr_of_eventuallyEq_of_mdifferentiableAt_mgradient
    {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x)
    (h : f =ᶠ[nhds x] g) : laplaceBeltrami I f x = laplaceBeltrami I g x := by
  rw [laplaceBeltrami_def, laplaceBeltrami_def]
  apply divergence_congr_of_eventuallyEq I hf
  filter_upwards [h.eventuallyEq_nhds] with y hy
  apply ext_inner_right ℝ
  intro v
  rw [inner_mgradient, inner_mgradient, hy.mvfderiv_eq]

/-- Two functions which agree near a point have the same Laplace–Beltrami operator there if
one is `C²` at the point. -/
theorem laplaceBeltrami_congr_of_eventuallyEq {f g : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (h : f =ᶠ[nhds x] g) :
    laplaceBeltrami I f x = laplaceBeltrami I g x :=
  laplaceBeltrami_congr_of_eventuallyEq_of_mdifferentiableAt_mgradient I
    (mdifferentiableAt_mgradient hf) h

/-- The Laplace–Beltrami operator vanishes off the topological support of a function. -/
theorem laplaceBeltrami_eq_zero_of_notMem_tsupport {f : M → ℝ} {x : M}
    (hx : x ∉ tsupport f) : laplaceBeltrami I f x = 0 := by
  rw [← laplaceBeltrami_congr_of_eventuallyEq I contMDiffAt_zero
    (notMem_tsupport_iff_eventuallyEq.1 hx).symm, laplaceBeltrami_zero]

/-- The Laplace–Beltrami operator is additive at a point where both functions are `C²`. -/
theorem laplaceBeltrami_add_of_contMDiffAt {f g : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) :
    laplaceBeltrami I (f + g) x = laplaceBeltrami I f x + laplaceBeltrami I g x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hgradf := mdifferentiableAt_mgradient hf
  have hgradg := mdifferentiableAt_mgradient hg
  -- Both functions are `C¹`, hence differentiable, near `x`.
  have hdiff {h : M → ℝ} (hh : ContMDiffAt I 𝓘(ℝ) 2 h x) :
      ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ) h y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hh).mono fun _ hy ↦
      hy.mdifferentiableAt (by norm_num)
  have hev := mgradient_add_eventuallyEq (hdiff hf) (hdiff hg)
  have hcov := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
  rw [laplaceBeltrami_def, divergence_def,
    hcov.congr_of_eventuallyEq (mdifferentiableAt_mgradient (hf.add hg))
    (mdifferentiableAt_add_section hgradf hgradg) Filter.univ_mem hev,
    ← divergence_def, divergence_add I _ _ x hgradf hgradg, laplaceBeltrami_def,
    laplaceBeltrami_def]

/-- The Laplace–Beltrami operator is additive on `C²` functions. -/
theorem laplaceBeltrami_add {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    laplaceBeltrami I (f + g) x = laplaceBeltrami I f x + laplaceBeltrami I g x :=
  laplaceBeltrami_add_of_contMDiffAt I (hf x) (hg x)

/- The product rule below is the manifold counterpart of
`ContDiffAt.laplacian_fun_mul` for the flat Laplacian. -/
/-- **Leibniz rule for the Laplace--Beltrami operator.** For twice continuously differentiable
functions, the Laplacian of a product is the sum of the two scalar terms and twice the inner
product of their gradients. -/
theorem laplaceBeltrami_mul {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    laplaceBeltrami I (f * g) x =
      f x * laplaceBeltrami I g x +
        2 * inner ℝ (mgradient I f x) (mgradient I g x) +
          g x * laplaceBeltrami I f x := by
  have hgradf : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x :=
    mdifferentiable_mgradient (I := I) hf x
  have hgradg : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, mgradient I g y⟩ : TangentBundle I M)) x :=
    mdifferentiable_mgradient (I := I) hg x
  have hscaledg : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, f y • mgradient I g y⟩ : TangentBundle I M)) x := by
    exact (hf.mdifferentiableAt (by simp)).smul_section hgradg
  have hscaledf : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, g y • mgradient I f y⟩ : TangentBundle I M)) x := by
    exact (hg.mdifferentiableAt (by simp)).smul_section hgradf
  -- Normalize pointwise scalar multiplication so the divergence APIs match their section forms.
  rw [laplaceBeltrami, mgradient_mul (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)),
    show (fun y ↦ f y • mgradient I g y + g y • mgradient I f y) =
      (fun y ↦ f y • mgradient I g y) + (fun y ↦ g y • mgradient I f y) by rfl,
    divergence_add I _ _ x hscaledg hscaledf]
  rw [show (fun y ↦ f y • mgradient I g y) = f • mgradient I g by rfl,
    show (fun y ↦ g y • mgradient I f y) = g • mgradient I f by rfl,
    divergence_smul_function I f (mgradient I g) x
      (hf.mdifferentiableAt (by simp)) hgradg,
    divergence_smul_function I g (mgradient I f) x
      (hg.mdifferentiableAt (by simp)) hgradf]
  simp only [laplaceBeltrami_def]
  rw [← inner_mgradient (I := I) (f := f) (x := x),
    ← inner_mgradient (I := I) (f := g) (x := x), real_inner_comm]
  ring

/-- The Laplace–Beltrami operator commutes with real scalar multiplication at a point where the
function is `C²`. -/
theorem laplaceBeltrami_smul_of_contMDiffAt (c : ℝ) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    laplaceBeltrami I (c • f) x = c * laplaceBeltrami I f x := by
  simp only [laplaceBeltrami, mgradient_smul]
  exact divergence_smul I c _ x (mdifferentiableAt_mgradient hf)

/-- The Laplace–Beltrami operator commutes with real scalar multiplication on `C²` functions. -/
theorem laplaceBeltrami_smul (c : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (x : M) :
    laplaceBeltrami I (c • f) x = c * laplaceBeltrami I f x :=
  laplaceBeltrami_smul_of_contMDiffAt I c (hf x)

/-- The Laplace–Beltrami operator commutes with negation on `C²` functions. -/
theorem laplaceBeltrami_neg {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (x : M) :
    laplaceBeltrami I (-f) x = -laplaceBeltrami I f x := by
  rw [← neg_one_smul ℝ f, laplaceBeltrami_smul I _ hf, neg_one_mul]

/-- The Laplace–Beltrami operator is additive with respect to subtraction of `C²` functions. -/
theorem laplaceBeltrami_sub {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    laplaceBeltrami I (f - g) x = laplaceBeltrami I f x - laplaceBeltrami I g x := by
  rw [sub_eq_add_neg, laplaceBeltrami_add I hf (g := -g) hg.neg, laplaceBeltrami_neg I hg,
    sub_eq_add_neg]

/-- **Chain rule for the Laplace--Beltrami operator.** If `h` is `C²` on an open set of real
numbers containing all values of a `C²` function `f`, then
`Δ (h ∘ f) = h'(f) Δ f + h''(f) |grad f|²`. -/
theorem laplaceBeltrami_comp {h : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (hh : ContDiffOn ℝ 2 h s)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (hfs : ∀ y, f y ∈ s) (x : M) :
    laplaceBeltrami I (h ∘ f) x =
      deriv h (f x) * laplaceBeltrami I f x +
        deriv (deriv h) (f x) * ‖mgradient I f x‖ ^ 2 := by
  have hfd : ∀ y, MDifferentiableAt I 𝓘(ℝ) f y := fun y ↦ hf.mdifferentiableAt (by simp)
  have hh' : ContDiffOn ℝ 1 (deriv h) s := hh.deriv_of_isOpen hs (by norm_num)
  -- The gradient of `h ∘ f` is the section `h'(f) • grad f`, to which the product rule applies.
  have hgrad : mgradient I (h ∘ f) = (deriv h ∘ f) • mgradient I f := by
    funext y
    exact mgradient_comp_deriv ((hh.differentiableOn (by norm_num) _ (hfs y)).differentiableAt
      (hs.mem_nhds (hfs y))) (hfd y)
  have hd : DifferentiableAt ℝ (deriv h) (f x) :=
    (hh'.differentiableOn one_ne_zero _ (hfs x)).differentiableAt (hs.mem_nhds (hfs x))
  rw [laplaceBeltrami, hgrad, divergence_smul_function I _ _ x
      (hd.comp_mdifferentiableAt (hfd x)) (mdifferentiable_mgradient (I := I) hf x),
    ← laplaceBeltrami_def, ← inner_mgradient, mgradient_comp_deriv hd (hfd x),
    real_inner_smul_left, real_inner_self_eq_norm_sq, Function.comp_apply]

/-- The Laplace--Beltrami operator of the logarithm of a nowhere-vanishing `C²` function:
`Δ (log f) = Δ f / f - |grad f|² / f²`. -/
theorem laplaceBeltrami_log {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (hf0 : ∀ y, f y ≠ 0)
    (x : M) :
    laplaceBeltrami I (fun y ↦ Real.log (f y)) x =
      laplaceBeltrami I f x / f x - ‖mgradient I f x‖ ^ 2 / f x ^ 2 := by
  have hdd : deriv (deriv Real.log) (f x) = -(f x ^ 2)⁻¹ := by
    rw [Real.deriv_log', deriv_inv]
  rw [show (fun y ↦ Real.log (f y)) = Real.log ∘ f from rfl,
    laplaceBeltrami_comp I isOpen_compl_singleton Real.contDiffOn_log hf hf0 x,
    Real.deriv_log, hdd]
  ring

end OperatorLaws

/-- In any orthonormal basis, the divergence is the sum of the diagonal inner products of the
covariant derivative of the vector field. -/
theorem divergence_eq_sum_inner (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] (X : (x : M) → TangentSpace I x) (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    divergence I X x = ∑ i, inner ℝ
      (CovariantDerivative.leviCivitaConnection I M X x (b i)) (b i) := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ b]
  simp only [real_inner_comm]
  rfl

@[simp] theorem hessian_add_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v₁ v₂ w : TangentSpace I x) :
    hessian I f x (v₁ + v₂) w = hessian I f x v₁ w + hessian I f x v₂ w := by
  simp only [hessian_def, map_add, inner_add_left]

@[simp] theorem hessian_smul_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x (r • v) w = r * hessian I f x v w := by
  simp only [hessian_def, map_smul, real_inner_smul_left]

@[simp] theorem hessian_zero_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    hessian I f x 0 w = 0 := by
  simp only [hessian_def, map_zero, inner_zero_left]

@[simp] theorem hessian_add_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w₁ w₂ : TangentSpace I x) :
    hessian I f x v (w₁ + w₂) = hessian I f x v w₁ + hessian I f x v w₂ := by
  simp only [hessian_def, inner_add_right]

@[simp] theorem hessian_smul_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x v (r • w) = r * hessian I f x v w := by
  simp only [hessian_def, real_inner_smul_right]

@[simp] theorem hessian_zero_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    hessian I f x v 0 = 0 := by
  simp only [hessian_def, inner_zero_right]

/-- The Laplace–Beltrami operator is the metric trace of the Hessian form. -/
theorem _root_.ModelWithCorners.laplaceBeltrami_eq_metricTrace_hessianForm
    (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] (f : M → ℝ) (x : M) :
    laplaceBeltrami I f x =
      LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (I.hessianForm f x)) := by
  -- The Hessian form is the metric lowering of the covariant derivative of the gradient.
  rw [laplaceBeltrami_def, divergence_def, I.hessianForm_def,
    ContinuousLinearMap.toLinearMap₁₂_comp, toLinearMap₁₂_innerSL,
    ← LinearMap.BilinForm.trace_bilinFormToEnd, LinearMap.bilinFormToEnd_innerₗ_comp]

/-- The Laplace–Beltrami operator is the trace of the scalar Hessian in every orthonormal basis. -/
theorem laplaceBeltrami_eq_sum_hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] (f : M → ℝ) (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I f x = ∑ i, hessian I f x (b i) (b i) := by
  rw [I.laplaceBeltrami_eq_metricTrace_hessianForm, LinearMap.BilinMap.metricTrace_eq_sum _ b]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, I.hessianForm_apply]

/-- The squared trace of the Hessian is at most the dimension times its squared norm,
expressed in any orthonormal basis. This includes dimension zero. -/
theorem laplaceBeltrami_sq_le_finrank_mul_sum_hessian_sq
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I f x ^ 2 ≤ (Module.finrank ℝ E : ℝ) *
      ∑ i, ∑ j, hessian I f x (b i) (b j) ^ 2 := by
  classical
  have hcard : Fintype.card ι = Module.finrank ℝ E := by
    rw [← Module.finrank_eq_card_basis b.toBasis, finrank_tangentSpace]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i ↦ hessian I f x (b i) (b i))
  rw [Finset.card_univ, hcard] at hcs
  rw [laplaceBeltrami_eq_sum_hessian I f x b]
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact Finset.sum_le_sum fun i _ ↦ Finset.single_le_sum
    (f := fun j ↦ hessian I f x (b i) (b j) ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

/-- If the Hessian of `f` at `x` is `c` times the metric, then `Δ f x = n c`, where `n` is the
dimension. -/
theorem laplaceBeltrami_eq_finrank_mul_of_hessian_eq_mul_inner
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} {x : M} {c : ℝ}
    (h : ∀ v w : TangentSpace I x, hessian I f x v w = c * inner ℝ v w) :
    laplaceBeltrami I f x = Module.finrank ℝ E * c := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [laplaceBeltrami_eq_sum_hessian I f x b]
  simp only [h, ← Finset.mul_sum]
  rw [b.sum_inner_self, Fintype.card_fin, finrank_tangentSpace]
  ring

/-! ### Linear coordinates -/

/-- **The Hessian in linear coordinates.** On a finite-dimensional real normed space `F` whose
Riemannian metric is the field of bilinear forms `g`, the Hessian of a
function `f` that is `C²` at `x` is `Hess f(u, v) = D²f(u, v) - Df(Γ(u, v))`, where `Γ` is
`TauCeti.Manifold.christoffelSecondKind g`. Tangent vectors are read in the model space through
`tangentSpaceCastModel`. -/
theorem hessian_model_space_eq_fderiv_sub_christoffelSecondKind
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    {g : F → F →L[ℝ] F →L[ℝ] ℝ}
    (hg : ∀ y (v w : TangentSpace 𝓘(ℝ, F) y), inner ℝ v w =
      g y (tangentSpaceCastModel 𝓘(ℝ, F) y v) (tangentSpaceCastModel 𝓘(ℝ, F) y w))
    {x : F} {f : F → ℝ} (hf : ContDiffAt ℝ 2 f x) (u v : F) :
    hessian 𝓘(ℝ, F) f x ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm u)
        ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm v) =
      fderiv ℝ (fderiv ℝ f) x u v - fderiv ℝ f x (christoffelSecondKind g x u v) := by
  -- Extend `u` and `v` to constant vector fields.
  let C (a : F) (z : F) : TangentSpace 𝓘(ℝ, F) z := (tangentSpaceCastModel 𝓘(ℝ, F) z).symm a
  have hC (a : F) : MDiffAt (T% (C a)) x :=
    mdifferentiableAt_vectorSpace_iff_differentiableAt.2 (differentiableAt_const a)
  have h := hessian_apply_eq_mvfderiv_sub x (contMDiffAt_iff_contDiffAt.2 hf) (C u) (C v) (hC v)
  have hfun : (fun z ↦ mvfderiv 𝓘(ℝ, F) f z (C v z)) = fun z ↦ fderiv ℝ f z v := by
    funext z
    simp only [mvfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply, C]
    -- `NormedSpace.fromTangentSpace z` is `tangentSpaceCastModel 𝓘(ℝ, F) z` by definition.
    simp [NormedSpace.fromTangentSpace]
  -- The Levi-Civita derivative of the constant field `C v` in the direction `u` is `Γ(u, v)`.
  have hΓ := leviCivitaConnection_model_space_eq_fderiv_add_christoffelSecondKind
    (V := C v) (x := x) hg (differentiableAt_const v) u
  -- Read in the model space, the constant field `C v` is the constant map `v`.
  have h0 : fderiv ℝ (C v) x = 0 := fderiv_const_apply (x := x) v
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  rw [h0, zero_apply, zero_add, ContinuousLinearEquiv.apply_symm_apply] at hΓ
  rw [hfun] at h
  simp only [mvfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply] at h
  rw [h, fderiv_clm_apply_const_apply hD, ← hΓ]
  -- `NormedSpace.fromTangentSpace x` is `tangentSpaceCastModel 𝓘(ℝ, F) x` by definition.
  simp only [NormedSpace.fromTangentSpace, C, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-! ### The flat model -/

open scoped Gradient Laplacian

/-- On a finite-dimensional real inner-product space with its standard metric, the Riemannian
divergence is the trace of the ordinary Fréchet derivative. -/
theorem divergence_eq_trace_fderiv_model_space
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : ∀ y : F, TangentSpace (modelWithCornersSelf ℝ F) y} {x : F}
    (hV : DifferentiableAt ℝ V x) :
    let _ : RiemannianBundle (fun y : F ↦ TangentSpace (modelWithCornersSelf ℝ F) y) :=
      ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩
    divergence (modelWithCornersSelf ℝ F) V x =
      LinearMap.trace ℝ F (fderiv ℝ V x).toLinearMap := by
  intro _
  simp only [divergence]
  let e := tangentSpaceCastModel (modelWithCornersSelf ℝ F) x
  let A : TangentSpace (modelWithCornersSelf ℝ F) x →ₗ[ℝ]
      TangentSpace (modelWithCornersSelf ℝ F) x :=
    e.symm.toLinearEquiv.conj (fderiv ℝ V x).toLinearMap
  have hconn := leviCivitaConnection_eq_fderiv_model_space (V := V) hV
  have hconj (v : TangentSpace (modelWithCornersSelf ℝ F) x) :
      e (A v) = fderiv ℝ V x (e v) := by
    dsimp only [A]
    rw [LinearEquiv.conj_apply_apply]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv, ContinuousLinearMap.coe_coe,
      ContinuousLinearEquiv.symm_symm, e.apply_symm_apply]
  have hA :
      (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F V x).toLinearMap =
        A := by
    ext v
    apply e.injective
    calc
      e ((CovariantDerivative.leviCivitaConnection
          (modelWithCornersSelf ℝ F) F V x).toLinearMap v) =
          fderiv ℝ V x (e v) := by
        simpa only [e, ContinuousLinearMap.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply] using hconn (e v)
      _ = e (A v) := (hconj v).symm
  rw [hA]
  exact (LinearMap.trace_conj' _ e.toLinearEquiv).symm

/-- On a finite-dimensional real inner-product space with its standard metric, the Riemannian
Hessian is the second Fréchet derivative. -/
theorem hessian_eq_iteratedFDeriv_model_space
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → ℝ} {x : F} (hgrad : DifferentiableAt ℝ (∇ f) x)
    (v w : TangentSpace (modelWithCornersSelf ℝ F) x) :
    hessian (modelWithCornersSelf ℝ F) f x v w =
      iteratedFDeriv ℝ 2 f x
        ![NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w] := by
  rw [hessian_def]
  have hm : mgradient (modelWithCornersSelf ℝ F) f = ∇ f :=
    funext fun y ↦ mgradient_eq_gradient f y
  have hmgrad : DifferentiableAt ℝ (mgradient (modelWithCornersSelf ℝ F) f) x := by
    rw [hm]
    exact hgrad
  have hconnection := leviCivitaConnection_eq_fderiv_model_space hmgrad
    (NormedSpace.fromTangentSpace x v)
  have hconnection' :
      NormedSpace.fromTangentSpace x
          (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F
            (mgradient (modelWithCornersSelf ℝ F) f) x v) =
        fderiv ℝ (mgradient (modelWithCornersSelf ℝ F) f) x
          (NormedSpace.fromTangentSpace x v) := by
    simpa only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.symm_apply_apply] using
      hconnection
  calc
    inner ℝ
        (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F
          (mgradient (modelWithCornersSelf ℝ F) f) x v) w =
        inner ℝ
          (NormedSpace.fromTangentSpace x
            (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F
              (mgradient (modelWithCornersSelf ℝ F) f) x v))
          (NormedSpace.fromTangentSpace x w) :=
      inner_tangentSpace_vectorSpace _ _
    _ = inner ℝ
        (fderiv ℝ (mgradient (modelWithCornersSelf ℝ F) f) x
          (NormedSpace.fromTangentSpace x v))
        (NormedSpace.fromTangentSpace x w) := by rw [hconnection']
    _ = inner ℝ (fderiv ℝ (∇ f) x (NormedSpace.fromTangentSpace x v))
        (NormedSpace.fromTangentSpace x w) := by rw [hm]
    _ = _ := by
      rw [← InnerProductSpace.toDual_apply_apply]
      calc
        ((InnerProductSpace.toDual ℝ F)
            (fderiv ℝ (∇ f) x (NormedSpace.fromTangentSpace x v)))
            (NormedSpace.fromTangentSpace x w) =
            fderiv ℝ ((InnerProductSpace.toDual ℝ F) ∘ ∇ f) x
              (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := by
                rw [(InnerProductSpace.toDual ℝ F).comp_fderiv]
                rfl
        _ = fderiv ℝ (fderiv ℝ f) x (NormedSpace.fromTangentSpace x v)
            (NormedSpace.fromTangentSpace x w) := by rw [toDual_comp_gradient]
        _ = _ := (iteratedFDeriv_two_apply f x
          ![NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w]).symm

/-- At a point `x` where `∇ f` is differentiable, the Laplace–Beltrami operator of the standard
Riemannian metric equals Mathlib's flat Laplacian `Δ f`. This fixes the sign convention as
`Δ = div ∘ grad`. -/
theorem laplaceBeltrami_eq_laplacian_of_differentiableAt_gradient
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → ℝ} {x : F} (hgrad : DifferentiableAt ℝ (∇ f) x) :
    laplaceBeltrami (modelWithCornersSelf ℝ F) f x = Δ f x := by
  let e : TangentSpace (modelWithCornersSelf ℝ F) x ≃ₗᵢ[ℝ] F :=
    (NormedSpace.fromTangentSpace x).toLinearEquiv.isometryOfInner
      inner_tangentSpace_vectorSpace
  let b := (stdOrthonormalBasis ℝ F).map e.symm
  rw [laplaceBeltrami_eq_sum_hessian (modelWithCornersSelf ℝ F) f x b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ F)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have he (u : F) : NormedSpace.fromTangentSpace x (e.symm u) = u := by
    -- Expose the inverse `LinearEquiv` carried by the isometry equivalence.
    change (NormedSpace.fromTangentSpace x) (e.toLinearEquiv.symm u) = u
    rw [show e.toLinearEquiv = (NormedSpace.fromTangentSpace x).toLinearEquiv by
      dsimp [e]
      exact LinearEquiv.isometryOfInner_toLinearEquiv _ _]
    exact (NormedSpace.fromTangentSpace x).apply_symm_apply u
  simpa only [b, OrthonormalBasis.map_apply, he] using
    hessian_eq_iteratedFDeriv_model_space hgrad (b i) (b i)

/-- For a function `f` with `ContDiff ℝ 2 f` on a finite-dimensional real inner product space,
the Laplace--Beltrami operator of the standard metric equals Mathlib's flat Laplacian `Δ f` at
every point (convention `Δ = div ∘ grad`). -/
theorem laplaceBeltrami_eq_laplacian
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (x : F) :
    laplaceBeltrami (modelWithCornersSelf ℝ F) f x = Δ f x := by
  apply laplaceBeltrami_eq_laplacian_of_differentiableAt_gradient
  exact (hf.gradient_right (m := 1) (by norm_num)).differentiable (by norm_num) x

/-- If the installed fibre metric is the standard one, the Laplace–Beltrami operator is Mathlib's
flat Laplacian. This transports
`laplaceBeltrami_eq_laplacian_of_differentiableAt_gradient` along an equality of fibre metrics,
such as `toRiemannianMetric_ofLE`, which cannot be rewritten inside the instance-dependent
arguments. -/
theorem laplaceBeltrami_eq_laplacian_of_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [inst : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
    (hg : RiemannianBundle.g = (riemannianMetricVectorSpace F).toRiemannianMetric)
    {f : F → ℝ} {x : F} (hgrad : DifferentiableAt ℝ (∇ f) x) :
    laplaceBeltrami (modelWithCornersSelf ℝ F) f x = Δ f x := by
  obtain ⟨_⟩ := inst
  subst hg
  exact laplaceBeltrami_eq_laplacian_of_differentiableAt_gradient hgrad

/-- The squared norm has constant flat Laplace--Beltrami operator. -/
@[simp] theorem laplaceBeltrami_norm_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (x : F) :
    laplaceBeltrami (modelWithCornersSelf ℝ F) (fun y ↦ ‖y‖ ^ 2) x =
      2 * Module.finrank ℝ F := by
  rw [laplaceBeltrami_eq_laplacian
    (contDiff_norm_sq ℝ (E := F) (n := 2)) x]
  exact TauCeti.laplacian_norm_sq x

end TauCeti.Manifold
