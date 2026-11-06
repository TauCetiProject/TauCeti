/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Trace

/-!
# Contraction of the induced endomorphism connection

The connection induced on the endomorphisms of a finite-rank vector bundle commutes with
trace: `d(tr A)(v) = tr(∇_v A)`. This is contraction of a tensor's input against its output,
and requires neither a metric nor metric compatibility. In a local frame the connection is
`∇A = dA + ΓA - AΓ`; the two connection terms cancel on taking the trace.

The coordinate formula uses the native Hom connection `CovariantDerivative.hom` and the
frame coefficient functionals of a bundle trivialization. Only differentiability of `A`
at the evaluated point is needed; the connection itself need not be differentiable.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4
  (induced connections and compatibility with contraction).
-/

public section

open Bundle FiberBundle Module TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V)
  {A : Π x : M, V x →L[𝕜] V x} {x : M}

/-- In a local frame, the induced endomorphism connection is `dA + ΓA - AΓ`.
The first index is the row (output) index, and section coefficients are columns. -/
theorem localFrameCoeff_hom {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 F)
    {e : Trivialization F (π F V)} [MemTrivializationAtlas e] (hx : x ∈ e.baseSet)
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z ↦ V z →L[𝕜] V z) y (A y)) x)
    (v : TangentSpace I x) (i j : ι) :
    e.localFrameCoeff I b i x (cov.hom cov A x v (e.localFrame b j x)) =
      mvfderiv I (fun y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b j y))) x v +
        ∑ k, e.localFrameCoeff I b k x (A x (e.localFrame b j x)) *
          e.localFrameCoeff I b i x (cov (e.localFrame b k) x v) -
        ∑ k, e.localFrameCoeff I b k x (cov (e.localFrame b j) x v) *
          e.localFrameCoeff I b i x (A x (e.localFrame b k x)) := by
  classical
  have hframe (k : ι) : MDiffAt (T% (e.localFrame b k)) x :=
    (contMDiffAt_localFrame_of_mem (n := 1) e b k hx).mdifferentiableAt one_ne_zero
  have hAs := hA.clm_bundle_apply (hframe j)
  have hc := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet)
  have hcoord := congrArg (fun L ↦ e.localFrameCoeff I b i x (L v))
    (covariantDerivative_eq_frameCovariantDerivative_add_sum b hc hx hAs)
  simp only [frameCovariantDerivative_apply, add_apply, _root_.sum_apply,
    _root_.smul_apply, map_add, map_sum, map_smul, localFrameCoeff_localFrame b hx,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, LinearMap.piApply_apply] at hcoord
  have hexp := e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
    (s := fun y ↦ cov (e.localFrame b j) y (extend E v y)) hx
  simp only [extend_apply_self] at hexp
  rw [hom_apply cov cov hA (hframe j), map_sub, hcoord]
  congr 1
  conv_lhs => rw [hexp]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Covariant differentiation on the native endomorphism bundle commutes with trace.
This is the contraction of the input and output slots, without any metric hypothesis. -/
theorem mvfderiv_trace_eq_trace_hom
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z ↦ V z →L[𝕜] V z) y (A y)) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ LinearMap.trace 𝕜 (V y) (A y).toLinearMap) x v =
      LinearMap.trace 𝕜 (V x) (cov.hom cov A x v).toLinearMap := by
  classical
  let e := trivializationAt F V x
  let b := Module.finBasis 𝕜 F
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have htrace {y : M} (hy : y ∈ e.baseSet) (B : V y →L[𝕜] V y) :
      LinearMap.trace 𝕜 (V y) B.toLinearMap =
        ∑ i, e.localFrameCoeff I b i y (B (e.localFrame b i y)) := by
    rw [LinearMap.trace_eq_matrix_trace 𝕜 (e.basisAt b hy)]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hc := e.localFrameCoeff_apply_of_mem_baseSet (I := I) b hy
      (extend F (B (e.localFrame b i y))) i
    simpa only [extend_apply_self, e.localFrame_apply_of_mem_baseSet b hy,
      ContinuousLinearMap.coe_coe] using hc.symm
  have hnear : (fun y ↦ LinearMap.trace 𝕜 (V y) (A y).toLinearMap) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, e.localFrameCoeff I b i y (A y (e.localFrame b i y)) :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ htrace hy (A y)
  have hcoeff (i) : MDiffAt
      (fun y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b i y))) x :=
    mdifferentiableAt_localFrameCoeff b hx (hA.clm_bundle_apply
      ((contMDiffAt_localFrame_of_mem (n := 1) e b i hx).mdifferentiableAt one_ne_zero)) i
  have hsum : HasMFDerivAt I 𝓘(𝕜)
      (∑ i, fun y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b i y))) x
      (∑ i, mvfderiv I (fun y ↦ e.localFrameCoeff I b i y
        (A y (e.localFrame b i y))) x) :=
    HasMFDerivAt.sum fun i _ ↦ (hcoeff i).hasMFDerivAt
  have hfun : (∑ i, fun y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b i y))) =
      fun y ↦ ∑ i, e.localFrameCoeff I b i y (A y (e.localFrame b i y)) := by
    ext y
    simp
  have hderiv : mvfderiv I (fun y ↦ LinearMap.trace 𝕜 (V y) (A y).toLinearMap) x v =
      ∑ i, mvfderiv I (fun y ↦ e.localFrameCoeff I b i y
        (A y (e.localFrame b i y))) x v := by
    rw [hnear.mvfderiv_eq, ← hfun, mvfderiv_apply_eq_mfderiv_apply, hsum.mfderiv]
    exact _root_.sum_apply ..
  rw [hderiv, htrace hx]
  simp only [localFrameCoeff_hom cov b hx hA,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i k ↦
    e.localFrameCoeff I b k x (A x (e.localFrame b i x)) *
      e.localFrameCoeff I b i x (cov (e.localFrame b k) x v))]
  simp only [mul_comm]
  ring

end CovariantDerivative
