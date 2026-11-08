/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Trace

/-!
# Contraction of the induced endomorphism connection

The connection induced on the endomorphisms of a finite-rank vector bundle commutes with
trace: `d(tr A)(v) = tr(∇_v A)`. This is contraction of a tensor's input against its output,
and requires neither a metric nor metric compatibility. The proof reads the native Hom
connection `CovariantDerivative.hom` in a local frame via `localFrameCoeff_hom`, where it is
`∇A = dA + Γ A - A Γ`; the two connection terms cancel on taking the trace.
Only differentiability of `A` at the evaluated point is needed; the connection itself need not
be differentiable.

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
  {x : M}

/-- Covariant differentiation on the native endomorphism bundle commutes with trace.
This is the contraction of the input and output slots, without any metric hypothesis. -/
theorem mvfderiv_trace_eq_trace_hom (cov : CovariantDerivative I F V)
    {A : Π x : M, V x →L[𝕜] V x}
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z ↦ V z →L[𝕜] V z) y (A y)) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ LinearMap.trace 𝕜 (V y) (A y).toLinearMap) x v =
      LinearMap.trace 𝕜 (V x) (cov.hom cov A x v).toLinearMap := by
  classical
  let e := trivializationAt F V x
  let b := Module.finBasis 𝕜 F
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hnear : (fun y ↦ LinearMap.trace 𝕜 (V y) (A y).toLinearMap) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, e.localFrameCoeff I b i y (A y (e.localFrame b i y)) :=
    Filter.eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦
      trace_eq_sum_localFrameCoeff I b hy _
  have hcoeff (i) : MDiffAt
      (fun y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b i y))) x :=
    mdifferentiableAt_localFrameCoeff b hx (hA.clm_bundle_apply
      ((contMDiffAt_localFrame_of_mem (n := 1) e b i hx).mdifferentiableAt one_ne_zero)) i
  rw [hnear.mvfderiv_eq, TauCeti.mvfderiv_fun_sum fun i _ ↦ hcoeff i, _root_.sum_apply,
    trace_eq_sum_localFrameCoeff I b hx]
  simp only [ContinuousLinearMap.coe_coe, localFrameCoeff_hom cov cov b b hx hx hA,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- The `Γ A` and `A Γ` terms cancel: their diagonal sums agree after swapping the order
  -- of summation and commuting the two factors.
  have hswap (a g : Fin (finrank 𝕜 F) → Fin (finrank 𝕜 F) → 𝕜) :
      ∑ i, ∑ k, a k i * g i k = ∑ i, ∑ k, g k i * a i k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [hswap, add_sub_cancel_right]

end CovariantDerivative
