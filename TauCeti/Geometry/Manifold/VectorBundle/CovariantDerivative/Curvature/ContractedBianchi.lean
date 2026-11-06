/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.DifferentiatedSymmetries
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Contracting the covariant derivative of the curvature

Let `∇` be a smooth connection on the tangent bundle of a Riemannian manifold `M`. This file
contracts the covariant derivative of its curvature, the tensor
`CovariantDerivative.derivCurvatureTensor`, whose value on vector fields is

`(∇_v R)(Y, Z) σ = ∇_v (R(Y, Z) σ) - R(∇_v Y, Z) σ - R(Y, ∇_v Z) σ - R(Y, Z) (∇_v σ)`

(`CovariantDerivative.derivCurvatureTensor_apply`). It shows that the trace defining the Ricci
tensor commutes with covariant differentiation. For a metric-compatible torsion-free connection,
the contractions use pair symmetry of `⟪(∇_v R)(Y, Z) σ, U⟫`, from
`CovariantDerivative.IsMetricCompatible.inner_derivCurvatureTensor_swap_pairs` in
`DifferentiatedSymmetries`.

The trace is taken in a local frame at the point: the frame of a trivialization, cut off by a
bump function to globally smooth vector fields. Differentiating the frame coefficients by the
local frame formula `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum`
shows that the trace commutes with covariant differentiation. The cyclic form is the second
Bianchi identity `CovariantDerivative.derivCurvatureTensor_cyclic_eq_zero`.

On tangent vectors, `derivRicciTensor_eq_trace` identifies `∇Ric` with the trace of `∇R`.
Contracting the second Bianchi identity gives

`tr (z ↦ (∇_z R)(u, v) w) = (∇_u Ric)(v, w) - (∇_v Ric)(u, w)`.

This identity requires only a torsion-free affine connection. An orthonormal basis computes
its trace when a metric is present. For a metric-compatible connection, pair interchange
gives the Riemannian divergence formula

`∑ᵢ (∇_{eᵢ} Rm)(eᵢ, u, v, w) = (∇_w Ric)(u, v) - (∇_v Ric)(u, w)`,

with `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩`. Contracting once more, and using that the metric trace
commutes with covariant differentiation for a metric-compatible connection, gives the twice
contracted second Bianchi identity

`2 ∑ᵢ (∇_{eᵢ} Ric)(eᵢ, v) = d Scal(v)`,

that is `2 div Ric = d Scal`. These differential contractions underlie the divergence
of the Weyl tensor and the Cotton tensor. The derivative of the Ricci tensor is the covariant
derivative of a bilinear tensor; `exists_frame_sum_derivCurvatureTensor` identifies it with the
trace of `derivCurvatureTensor`.

## Main results

* `CovariantDerivative.exists_frame_sum_derivCurvatureTensor`: contracting `(∇_v R)(·, B) C`
  against the output gives `(∇_v Ric)(B, C)`.
* `CovariantDerivative.derivRicciTensor`: the covariant derivative of Ricci curvature, with
  its direction of differentiation last.
* `CovariantDerivative.derivRicciTensor_eq_trace`: covariant differentiation commutes with
  the Ricci trace, without a metric assumption.
* `CovariantDerivative.trace_derivCurvatureTensor_eq_sub`: the metric-free first contracted
  second Bianchi identity.
* `CovariantDerivative.sum_inner_derivCurvatureTensor_eq_sub`: its orthonormal-basis form.
* `CovariantDerivative.IsMetricCompatible.sum_inner_derivCurvatureTensor_self_eq_sub`: the
  Riemannian divergence formula.
* `CovariantDerivative.IsMetricCompatible.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature`:
  the trace of `∇Ric` is the derivative of scalar curvature.
* `CovariantDerivative.IsMetricCompatible.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature`:
  the twice contracted second Bianchi identity `2 div Ric = d Scal`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the contracted Bianchi identity).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace CovariantDerivative

section VectorFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Near `x`, the Ricci tensor `Ric(B, C)` is the trace `∑ₖ cₖ(R(Fₖ, B) C)` in a frame `F` of
globally smooth fields agreeing with the local frame of `e`, so its derivative at `x` is the
sum of the derivatives of the coefficient functions. -/
private theorem mvfderiv_ricciTensor_eq_sum_localFrameCoeff
    (e : Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {x : M} (hx : x ∈ e.baseSet)
    {F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y}
    (hF : ∀ k, CMDiff ∞ (T% (F k))) (hFeq : ∀ k, ∀ᶠ y in 𝓝 x, F k y = e.localFrame b k y)
    {B C : Π y : M, TangentSpace I y} (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ cov.ricciTensor y (B y) (C y)) x v =
      ∑ k, mvfderiv I (fun y ↦ e.localFrameCoeff I b k y
        (curvatureOperator cov (F k) B C y)) x v := by
  have hs (k : Fin (Module.finrank ℝ E)) :
      CMDiff ∞ (T% (curvatureOperator cov (F k) B C)) :=
    cov.contMDiff_curvatureOperator (hF k) hB hC
  -- Near `x`, the Ricci tensor is the trace in the frame.
  have hRic : (fun y ↦ cov.ricciTensor y (B y) (C y)) =ᶠ[𝓝 x]
      fun y ↦ ∑ k, e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx, Filter.eventually_all.2 hFeq] with y hy hFy
    rw [cov.ricciTensor_eq_sum y (e.basisAt b hy)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [e.localFrameCoeff_apply_of_mem_baseSet b hy (curvatureOperator cov (F k) B C) k,
      ← e.localFrame_apply_of_mem_baseSet b hy, ← hFy k]
    exact congrArg (fun w ↦ (e.basisAt b hy).repr w k) (curvatureTensor_apply cov y (hF k) hB hC)
  have hcoeff (k : Fin (Module.finrank ℝ E)) :
      MDiffAt (fun y ↦ e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y)) x :=
    mdifferentiableAt_localFrameCoeff b hx ((hs k).mdifferentiableAt (by simp)) k
  have hfun : (fun y ↦ ∑ k, e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y)) =
      ∑ k, fun y ↦ e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y) := by
    ext y; simp
  have hH : HasMFDerivAt I 𝓘(ℝ)
      (∑ k, fun y ↦ e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y)) x
      (∑ k, mvfderiv I (fun y ↦ e.localFrameCoeff I b k y
        (curvatureOperator cov (F k) B C y)) x) :=
    HasMFDerivAt.sum fun k _ ↦ (hcoeff k).hasMFDerivAt
  rw [hRic.mvfderiv_eq, hfun, mvfderiv_apply_eq_mfderiv_apply, hH.mfderiv]
  -- The tangent spaces of `ℝ` in which `mfderiv` takes values are `ℝ` itself.
  exact _root_.sum_apply ..

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The local frame formula for `∇_v (R(Fₖ, B) C)`, read in the `k`-th coordinate of a frame `F`
of globally smooth fields agreeing with the local frame of `e` near `x`. -/
private theorem localFrameCoeff_cov_curvatureOperator
    (e : Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {x : M} (hx : x ∈ e.baseSet)
    {F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y}
    (hF : ∀ k, CMDiff ∞ (T% (F k))) (hFeq : ∀ k, ∀ᶠ y in 𝓝 x, F k y = e.localFrame b k y)
    {B C : Π y : M, TangentSpace I y} (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (v : TangentSpace I x) (k : Fin (Module.finrank ℝ E)) :
    e.localFrameCoeff I b k x (cov (curvatureOperator cov (F k) B C) x v) =
      mvfderiv I (fun y ↦ e.localFrameCoeff I b k y
          (curvatureOperator cov (F k) B C y)) x v +
        ∑ j, e.localFrameCoeff I b j x (curvature x (F k x) (B x) (C x)) *
          e.localFrameCoeff I b k x (cov (F j) x v) := by
  have hs : CMDiff ∞ (T% (curvatureOperator cov (F k) B C)) :=
    cov.contMDiff_curvatureOperator (hF k) hB hC
  have hsx : curvatureOperator cov (F k) B C x = curvature x (F k x) (B x) (C x) :=
    (curvatureTensor_apply cov x (hF k) hB hC).symm
  have hcov' := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet)
  have h := congrArg (fun L ↦ e.localFrameCoeff I b k x (L v))
    (TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov' hx
      (hs.mdifferentiableAt (by simp)))
  have hloc (j : Fin (Module.finrank ℝ E)) : cov (e.localFrame b j) x = cov (F j) x :=
    hcov'.congr_of_eventuallyEq
      ((contMDiffAt_localFrame_of_mem (n := ∞) e b j hx).mdifferentiableAt (by simp))
      ((hF j).mdifferentiableAt (by simp)) (e.open_baseSet.mem_nhds hx)
      ((hFeq j).mono fun y hy ↦ hy.symm)
  simp only [TauCeti.Manifold.frameCovariantDerivative_apply, add_apply,
    _root_.sum_apply, _root_.smul_apply, map_add, map_sum,
    map_smul, smul_eq_mul, hloc] at h
  have hlf (j : Fin (Module.finrank ℝ E)) : e.localFrame b j x = F j x :=
    ((hFeq j).self_of_nhds).symm
  have hdual (i j : Fin (Module.finrank ℝ E)) :
      e.localFrameCoeff I b i x (F j x) = if i = j then 1 else 0 := by
    rw [← hlf, TauCeti.Manifold.localFrameCoeff_localFrame b hx]
  have hpi : LinearMap.piApply (e.localFrameCoeff I b k) (curvatureOperator cov (F k) B C) =
      fun y ↦ e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y) := by
    ext y
    simp
  simp only [hlf, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, hpi, hsx] at h
  exact h

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Contracting `(∇_v R)(·, B) C` against the output, in a local frame at `x`, gives the
covariant derivative `(∇_v Ric)(B, C) = v (Ric(B, C)) - Ric(∇_v B, C) - Ric(B, ∇_v C)` of the
Ricci tensor. The frame is a family of global smooth vector fields `F` forming a basis at `x`,
with dual coordinate functionals `c` at `x`. -/
theorem exists_frame_sum_derivCurvatureTensor (x : M) :
    ∃ (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
      (c : Fin (Module.finrank ℝ E) → TangentSpace I x →ₗ[ℝ] ℝ),
      (∀ i, CMDiff ∞ (T% (F i))) ∧ (∀ i j, c i (F j x) = if i = j then 1 else 0) ∧
      (∀ w, ∑ i, c i w • F i x = w) ∧
      ∀ (v : TangentSpace I x) {B C : Π y : M, TangentSpace I y}, CMDiff ∞ (T% B) →
        CMDiff ∞ (T% C) →
        ∑ i, c i (cov.derivCurvatureTensor cov x v (F i x) (B x) (C x)) =
          mvfderiv I (fun y ↦ cov.ricciTensor y (B y) (C y)) x v -
            cov.ricciTensor x (cov B x v) (C x) - cov.ricciTensor x (B x) (cov C x v) := by
  classical
  -- Write `Ric(B, C) = ∑ₖ cₖ(R(Fₖ, B) C)` near `x` and differentiate each coefficient by the local
  -- frame formula. The terms coming from `∇_v Fₖ` cancel against those of `(∇_v R)(Fₖ, B) C`,
  -- which is the statement that the trace commutes with covariant differentiation.
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  obtain ⟨F, hF, hFeq⟩ := e.exists_contMDiff_eventuallyEq_localFrame (I := I) b hx
  have hFx (k : Fin (Module.finrank ℝ E)) : F k x = e.basisAt b hx k := by
    rw [(hFeq k).self_of_nhds, e.localFrame_apply_of_mem_baseSet b hx]
  let c (k : Fin (Module.finrank ℝ E)) : TangentSpace I x →ₗ[ℝ] ℝ := e.localFrameCoeff I b k x
  have hc (k : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
      c k w = (e.basisAt b hx).repr w k := by
    obtain ⟨s, -, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ w
    exact e.localFrameCoeff_apply_of_mem_baseSet b hx s k
  have hdual (i j : Fin (Module.finrank ℝ E)) : c i (F j x) = if i = j then 1 else 0 := by
    rw [hFx]
    exact TauCeti.Manifold.localFrameCoeff_basisAt b hx i j
  have hsum (w : TangentSpace I x) : ∑ i, c i w • F i x = w := by
    simp only [hc, hFx]
    exact (e.basisAt b hx).sum_repr w
  have hRicx (u w : TangentSpace I x) :
      cov.ricciTensor x u w = ∑ k, c k (curvature x (F k x) u w) := by
    rw [cov.ricciTensor_eq_sum x (e.basisAt b hx)]
    simp only [hc, hFx]
  refine ⟨F, c, hF, hdual, hsum, fun v {B C} hB hC ↦ ?_⟩
  -- Expand `∇_v Fₖ` in the frame.
  have hexp (k : Fin (Module.finrank ℝ E)) :
      c k (curvature x (cov (F k) x v) (B x) (C x)) =
        ∑ j, c j (cov (F k) x v) * c k (curvature x (F j x) (B x) (C x)) := by
    conv_lhs => rw [← hsum (cov (F k) x v)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hframe (k : Fin (Module.finrank ℝ E)) :
      c k (cov (curvatureOperator cov (F k) B C) x v) =
        mvfderiv I (fun y ↦ e.localFrameCoeff I b k y (curvatureOperator cov (F k) B C y)) x v +
          ∑ j, c j (curvature x (F k x) (B x) (C x)) * c k (cov (F j) x v) :=
    localFrameCoeff_cov_curvatureOperator (cov := cov) e b hx hF hFeq hB hC v k
  have hT (k : Fin (Module.finrank ℝ E)) :
      cov.derivCurvatureTensor cov x v (F k x) (B x) (C x) =
        cov (curvatureOperator cov (F k) B C) x v - curvature x (cov (F k) x v) (B x) (C x) -
          curvature x (F k x) (cov B x v) (C x) - curvature x (F k x) (B x) (cov C x v) :=
    derivCurvatureTensor_apply cov cov x v (hF k) hB hC
  simp only [hT, map_sub, Finset.sum_sub_distrib, hframe, hexp, ← hRicx,
    mvfderiv_ricciTensor_eq_sum_localFrameCoeff (cov := cov) e b hx hF hFeq hB hC v,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k j ↦ c j (cov (F k) x v) * c k (curvature x (F j x) (B x) (C x)))]
  simp only [mul_comm]
  ring

end VectorFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative of Ricci curvature, with the direction of differentiation last:
`derivRicciTensor x u v w = (∇_w Ric)(u, v)`. -/
def derivRicciTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  cov.derivBilinearTensor (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x

/-- The covariant derivative of Ricci curvature uses the native bilinear-tensor derivative. -/
theorem derivRicciTensor_def (x : M) :
    cov.derivRicciTensor x =
      cov.derivBilinearTensor (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x :=
  (rfl)

/-- On vector fields differentiable at `x`, the derivative of Ricci curvature is the
directional derivative of its evaluation minus the two connection corrections. -/
theorem derivRicciTensor_apply {σ τ : Π y : M, TangentSpace I y} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (v : TangentSpace I x) :
    cov.derivRicciTensor x (σ x) (τ x) v =
      mvfderiv I (fun y ↦ cov.ricciTensor y (σ y) (τ y)) x v -
        cov.ricciTensor x (cov σ x v) (τ x) - cov.ricciTensor x (σ x) (cov τ x v) := by
  rw [derivRicciTensor_def]
  exact cov.derivBilinearTensor_apply
    (fun _ _ h₁ h₂ ↦ cov.mdifferentiableAt_ricciTensor_apply h₁ h₂) hσ hτ v

/-- Covariant differentiation commutes with the trace defining Ricci curvature:
`(∇_v Ric)(u, w) = tr (z ↦ (∇_v R)(z, u) w)`. No metric is needed. -/
theorem derivRicciTensor_eq_trace (x : M) (u w v : TangentSpace I x) :
    cov.derivRicciTensor x u w v =
      LinearMap.trace ℝ (TangentSpace I x)
        (((cov.derivCurvatureTensor cov x v).flip u).flip w) := by
  classical
  obtain ⟨F, c, hF, -, hsum, htr⟩ := exists_frame_sum_derivCurvatureTensor (cov := cov) x
  obtain ⟨B, hB, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ u
  obtain ⟨C, hC, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ w
  let D := ((cov.derivCurvatureTensor cov x v).flip (B x)).flip (C x)
  -- The local frame resolves the identity; apply `D` to this resolution and take its trace.
  have hD : D = ∑ i, (c i).smulRight (D (F i x)) := by
    ext z
    conv_lhs => rw [← hsum z]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hDi (i) : D (F i x) = cov.derivCurvatureTensor cov x v (F i x) (B x) (C x) := by
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
  have ht := htr v hB hC
  rw [derivRicciTensor_apply cov (hB.mdifferentiableAt (by simp))
    (hC.mdifferentiableAt (by simp))]
  calc
    _ = ∑ i, c i (D (F i x)) := by simpa only [hDi] using ht.symm
    _ = LinearMap.trace ℝ (TangentSpace I x) D := by
      conv_rhs => rw [hD]
      simp only [map_sum, LinearMap.trace_smulRight]

/-- The metric-free first contracted second Bianchi identity:
`tr (z ↦ (∇_z R)(u, v) w) = (∇_u Ric)(v, w) - (∇_v Ric)(u, w)`. -/
theorem trace_derivCurvatureTensor_eq_sub (ht : cov.torsion = 0) (x : M)
    (u v w : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x)
      ((((cov.derivCurvatureTensor cov x).flip u).flip v).flip w) =
      cov.derivRicciTensor x v w u - cov.derivRicciTensor x u w v := by
  have h : (((cov.derivCurvatureTensor cov x).flip u).flip v).flip w =
      ((cov.derivCurvatureTensor cov x u).flip v).flip w -
        ((cov.derivCurvatureTensor cov x v).flip u).flip w := by
    ext z
    simp only [LinearMap.flip_apply, LinearMap.sub_apply]
    have hcyc := congrArg (fun L ↦ L w)
      (cov.derivCurvatureTensor_cyclic_eq_zero cov ht x z u v)
    rw [cov.derivCurvatureTensor_antisymm cov x u v z] at hcyc
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply] at hcyc
    rw [← sub_eq_add_neg, sub_add_eq_add_sub, sub_eq_zero] at hcyc
    exact eq_sub_of_add_eq hcyc
  rw [h, map_sub, ← derivRicciTensor_eq_trace, ← derivRicciTensor_eq_trace]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- In any orthonormal basis, contracting the first curvature argument of `∇R` against the
output gives `∇Ric`. The connection need not preserve the metric. -/
theorem sum_inner_derivCurvatureTensor_eq_derivRicciTensor {ι : Type*} [Fintype ι]
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u w v : TangentSpace I x) :
    ∑ i, inner ℝ (b i) (cov.derivCurvatureTensor cov x v (b i) u w) =
      cov.derivRicciTensor x u w v := by
  rw [derivRicciTensor_eq_trace, LinearMap.trace_eq_sum_inner _ b]
  simp only [LinearMap.flip_apply]

/-- The first contracted second Bianchi identity in an arbitrary orthonormal basis. The
connection is torsion-free, but metric compatibility is not required. -/
theorem sum_inner_derivCurvatureTensor_eq_sub {ι : Type*} [Fintype ι]
    (ht : cov.torsion = 0) (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v w : TangentSpace I x) :
    ∑ i, inner ℝ (b i) (cov.derivCurvatureTensor cov x (b i) u v w) =
      cov.derivRicciTensor x v w u - cov.derivRicciTensor x u w v := by
  simpa only [LinearMap.trace_eq_sum_inner _ b, LinearMap.flip_apply] using
    cov.trace_derivCurvatureTensor_eq_sub ht x u v w

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov}

/-- For a metric-compatible torsion-free connection, the covariant derivative of Ricci is
symmetric in the two Ricci arguments. -/
theorem IsMetricCompatible.derivRicciTensor_comm
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v : TangentSpace I x) :
    cov.derivRicciTensor x u v = cov.derivRicciTensor x v u := by
  simp only [derivRicciTensor_def]
  exact cov.derivBilinearTensor_apply_comm
    (fun y a b ↦ IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht y a b) u v

/-- The divergence of the metric-lowered Riemann tensor is the antisymmetrized derivative of
Ricci curvature. The sign uses `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩`. -/
theorem IsMetricCompatible.sum_inner_derivCurvatureTensor_self_eq_sub {ι : Type*} [Fintype ι]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v w : TangentSpace I x) :
    ∑ i, inner ℝ (cov.derivCurvatureTensor cov x (b i) (b i) u v) w =
      cov.derivRicciTensor x u v w - cov.derivRicciTensor x u w v := by
  have h (i : ι) :
      inner ℝ (cov.derivCurvatureTensor cov x (b i) (b i) u v) w =
        -inner ℝ (b i) (cov.derivCurvatureTensor cov x (b i) v w u) := by
    rw [cov.derivCurvatureTensor_antisymm cov x (b i) (b i) u,
      LinearMap.neg_apply, inner_neg_left,
      hcov.inner_derivCurvatureTensor_swap_pairs ht, real_inner_comm]
  simp_rw [h]
  rw [Finset.sum_neg_distrib, cov.sum_inner_derivCurvatureTensor_eq_sub ht,
    hcov.derivRicciTensor_comm ht x w u, hcov.derivRicciTensor_comm ht x v u]
  ring

/-- For a metric-compatible connection, the metric trace of the covariant derivative of Ricci
curvature is the derivative of scalar curvature: `∑ᵢ (∇_v Ric)(eᵢ, eᵢ) = d Scal(v)` in any
orthonormal basis. -/
theorem IsMetricCompatible.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature
    {ι : Type*} [Fintype ι]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (v : TangentSpace I x) :
    ∑ i, cov.derivRicciTensor x (b i) (b i) v = mvfderiv I cov.scalarCurvature x v := by
  have hRic (y : M) :
      ContinuousLinearMap.toLinearMap₁₂ (cov.ricciTensor y).toContinuousBilinearMap =
        cov.ricciTensor y := by
    ext u w
    simp [LinearMap.toContinuousBilinearMap_apply]
  have hScal : cov.scalarCurvature = fun y ↦ TauCeti.bilinFormTrace
      (ContinuousLinearMap.toLinearMap₁₂ (cov.ricciTensor y).toContinuousBilinearMap) := by
    funext y
    rw [hRic, scalarCurvature_apply]
  simp only [derivRicciTensor_def]
  rw [hScal, hcov.mvfderiv_bilinFormTrace (fun _ _ h₁ h₂ ↦ by
    simpa only [LinearMap.toContinuousBilinearMap_apply] using
      cov.mdifferentiableAt_ricciTensor_apply h₁ h₂) b v]

/-- **The twice contracted second Bianchi identity** `2 div Ric = d Scal`: for a metric-compatible
torsion-free connection, `2 ∑ᵢ (∇_{eᵢ} Ric)(eᵢ, v) = d Scal(v)` in any orthonormal basis. -/
theorem IsMetricCompatible.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature
    {ι : Type*} [Fintype ι]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (v : TangentSpace I x) :
    2 * ∑ i, cov.derivRicciTensor x (b i) v (b i) = mvfderiv I cov.scalarCurvature x v := by
  -- Contract `∑ᵢ (∇_{bᵢ} Rm)(bᵢ, u, w, v) = (∇_v Ric)(u, w) - (∇_w Ric)(u, v)` over `u = w = bⱼ`.
  have h₁ : ∑ j, ∑ i, inner ℝ (cov.derivCurvatureTensor cov x (b i) (b i) (b j) (b j)) v =
      mvfderiv I cov.scalarCurvature x v - ∑ i, cov.derivRicciTensor x (b i) v (b i) := by
    simp only [hcov.sum_inner_derivCurvatureTensor_self_eq_sub ht, Finset.sum_sub_distrib,
      hcov.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature]
  -- After pair interchange, the left side is the divergence of Ricci curvature.
  have h₂ : ∑ j, ∑ i, inner ℝ (cov.derivCurvatureTensor cov x (b i) (b i) (b j) (b j)) v =
      ∑ i, cov.derivRicciTensor x (b i) v (b i) := by
    simp only [hcov.inner_derivCurvatureTensor_swap_pairs ht x (b _) (b _) (b _) (b _) v,
      real_inner_comm (b _)]
    rw [Finset.sum_comm]
    simp only [cov.sum_inner_derivCurvatureTensor_eq_derivRicciTensor,
      hcov.derivRicciTensor_comm ht x v]
  linarith

end CovariantDerivative
