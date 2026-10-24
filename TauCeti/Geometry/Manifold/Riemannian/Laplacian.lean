/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Analysis.Normed.Module.Trace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Divergence, Hessian, and Laplace–Beltrami operators

This file introduces the pointwise Riemannian divergence as the trace of the Levi–Civita
covariant derivative, the scalar Hessian obtained by pairing that derivative of the gradient,
and the Laplace–Beltrami operator with the convention `Δ = div ∘ grad`.  The orthonormal-basis
trace formula makes the relationship between the Laplacian and the Hessian explicit. The operator
laws include the Leibniz rule and the chain rule `Δ (h ∘ f) = h'(f) Δ f + h''(f) |grad f|²` for a
real function `h`, with its special case `Δ (log f) = Δ f / f - |grad f|² / f²`. On a
finite-dimensional inner-product space, the operator agrees with Mathlib's
flat Laplacian. The Hessian conventions follow Lee, *Introduction to Riemannian Manifolds*,
Chapter 3.

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

/-- The scalar Hessian of `f`, pairing the covariant derivative of its gradient with a second
tangent vector. -/
noncomputable def hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x v) w

theorem hessian_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I f x v w =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x v) w := by
  rw [hessian]

section HessianSymmetry

variable {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

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
    rcases hf.contMDiffOn' (m := (2 : ℕ∞ω)) le_rfl (by simp) with
      ⟨u, hu, hxu, hfu⟩
    have hfu' : ContMDiffOn I 𝓘(ℝ) 2 f u := by simpa using hfu
    have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
    have hG' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y : M ↦ TotalSpace.mk' E y
          ((Riemannian.Tensor.rieszDual (I := I) y) (mvfderiv I f y))) x := by
      refine Riemannian.Tensor.contMDiffAt_rieszDual (I := I) (E := E) (H := H) (M := M) x
        (mem_chart_source H x) (n := (1 : ℕ∞ω)) (Φ := fun y ↦ mvfderiv I f y) ?_
      intro j
      let s := u ∩ (chartAt H x).source
      have hs : IsOpen s := hu.inter hopen
      have hfs : ContMDiffOn I 𝓘(ℝ) 2 f s := hfu'.mono Set.inter_subset_left
      have hframe := Riemannian.Tensor.contMDiffOn_chartLocalFrame
        (I := I) (n := (1 : ℕ∞ω)) x j
      rw [TangentBundle.trivializationAt_baseSet] at hframe
      have hframes : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
          (fun y : M ↦ TotalSpace.mk' E y
            (Riemannian.Tensor.chartLocalFrame (I := I) x j y)) s :=
        hframe.mono Set.inter_subset_right
      exact (hfs.contMDiffOn_mvfderiv_apply hs hframes le_rfl).contMDiffAt
        (hs.mem_nhds ⟨hxu, mem_chart_source H x⟩)
    simpa only [mgradient_def] using hG'
  have hG' : MDiffAt (T% (mgradient I f)) x := hG.mdifferentiableAt (by simp)
  have hinner :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      V (σ := mgradient I f) (τ := W) hG' hW
  have hinner' : (fun y ↦ inner ℝ (mgradient I f y) (W y)) =
      (fun y ↦ mvfderiv I f y (W y)) := by
    funext y
    exact inner_mgradient (I := I) (f := f) (x := y) (W y)
  rw [hinner'] at hinner
  have hinner'' :
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

section OperatorLaws

variable (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The divergence of the zero vector field is zero. -/
@[simp]
theorem divergence_zero (x : M) : divergence I 0 x = 0 := by
  simp [divergence]

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

/-- The Hessian of a constant function is zero. -/
@[simp]
theorem hessian_const (c : ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I (fun _ : M ↦ c) x v w = 0 := by
  simp [hessian]

/-- The Hessian of the zero function is zero. -/
@[simp]
theorem hessian_zero (x : M) (v w : TangentSpace I x) :
    hessian I (0 : M → ℝ) x v w = 0 :=
  hessian_const I 0 x v w

/-- The Hessian is additive on twice continuously differentiable functions. -/
theorem hessian_add {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) (v w : TangentSpace I x) :
    hessian I (f + g) x v w = hessian I f x v w + hessian I g x v w := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [hessian, mgradient_add (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      (mdifferentiable_mgradient (I := I) hf x)
      (mdifferentiable_mgradient (I := I) hg x),
    add_apply, inner_add_left]

/-- The Hessian commutes with multiplication of a `C²` function by a real constant. -/
theorem hessian_smul (c : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (x : M) (v w : TangentSpace I x) :
    hessian I (c • f) x v w = c * hessian I f x v w := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [hessian, mgradient_smul c (hf.mdifferentiable (by simp)),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const c
      (mdifferentiable_mgradient (I := I) hf x),
    smul_apply, real_inner_smul_left]

/-- The Laplace–Beltrami operator vanishes on constants. -/
@[simp]
theorem laplaceBeltrami_const (c : ℝ) (x : M) :
    laplaceBeltrami I (fun _ : M ↦ c) x = 0 := by
  simp [laplaceBeltrami]

/-- The Laplace–Beltrami operator vanishes on the zero function. -/
@[simp]
theorem laplaceBeltrami_zero (x : M) : laplaceBeltrami I (0 : M → ℝ) x = 0 :=
  laplaceBeltrami_const I 0 x

/-- The Laplace–Beltrami operator is additive on `C²` functions. -/
theorem laplaceBeltrami_add {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    laplaceBeltrami I (f + g) x = laplaceBeltrami I f x + laplaceBeltrami I g x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [laplaceBeltrami,
    mgradient_add (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))]
  exact divergence_add I _ _ x
    (mdifferentiable_mgradient (I := I) hf x)
    (mdifferentiable_mgradient (I := I) hg x)

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

/-- The Laplace–Beltrami operator commutes with real scalar multiplication on `C²` functions. -/
theorem laplaceBeltrami_smul (c : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (x : M) :
    laplaceBeltrami I (c • f) x = c * laplaceBeltrami I f x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [laplaceBeltrami, mgradient_smul c (hf.mdifferentiable (by simp))]
  exact divergence_smul I c _ x
    (mdifferentiable_mgradient (I := I) hf x)

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
  simp only [hessian, map_add, inner_add_left]

@[simp] theorem hessian_smul_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x (r • v) w = r * hessian I f x v w := by
  simp only [hessian, map_smul, real_inner_smul_left]

@[simp] theorem hessian_zero_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    hessian I f x 0 w = 0 := by
  simp only [hessian, map_zero, inner_zero_left]

@[simp] theorem hessian_add_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w₁ w₂ : TangentSpace I x) :
    hessian I f x v (w₁ + w₂) = hessian I f x v w₁ + hessian I f x v w₂ := by
  simp only [hessian, inner_add_right]

@[simp] theorem hessian_smul_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x v (r • w) = r * hessian I f x v w := by
  simp only [hessian, real_inner_smul_right]

@[simp] theorem hessian_zero_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    hessian I f x v 0 = 0 := by
  simp only [hessian, inner_zero_right]

/-- The Laplace–Beltrami operator is the trace of the scalar Hessian in every orthonormal basis. -/
theorem laplaceBeltrami_eq_sum_hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] (f : M → ℝ) (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I f x = ∑ i, hessian I f x (b i) (b i) := by
  rw [laplaceBeltrami, divergence, LinearMap.trace_eq_sum_inner _ b]
  simp only [hessian, real_inner_comm]
  rfl

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
  rw [hessian]
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

/-- The Laplace–Beltrami operator of the standard Riemannian metric is Mathlib's flat Laplacian.
This fixes the sign convention as `Δ = div ∘ grad`. -/
theorem laplaceBeltrami_eq_laplacian
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

/-- The squared norm has constant flat Laplace--Beltrami operator. -/
@[simp] theorem laplaceBeltrami_norm_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (x : F) :
    laplaceBeltrami (modelWithCornersSelf ℝ F) (fun y ↦ ‖y‖ ^ 2) x =
      2 * Module.finrank ℝ F := by
  rw [laplaceBeltrami_eq_laplacian]
  · exact TauCeti.laplacian_norm_sq x
  · exact (((contDiff_norm_sq ℝ (E := F) (n := 2)).gradient_right (m := 1)
      (by norm_num)).differentiable (by norm_num)) x

end TauCeti.Manifold
