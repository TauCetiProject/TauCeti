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
and requires neither a metric nor metric compatibility. In local frames the induced connection
on `Hom(V, W)` is `∇A = dA + Γ_W A - A Γ_V`; for endomorphisms the two connection terms cancel
on taking the trace.

The coordinate formula uses the native Hom connection `CovariantDerivative.hom` and the
frame coefficient functionals of bundle trivializations. Only differentiability of `A`
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
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [ContMDiffVectorBundle 1 G W I]
  {x : M}

/-- In local frames of `V` and `W`, the induced Hom connection is `dA + Γ_W A - A Γ_V`.
The first index is the row (output, `W`) index, and the second is the column (input, `V`)
index. -/
theorem localFrameCoeff_hom (covV : CovariantDerivative I F V)
    (covW : CovariantDerivative I G W) {A : Π x : M, V x →L[𝕜] W x}
    {ι κ : Type*} [Fintype ι] [Fintype κ] (bV : Basis ι 𝕜 F) (bW : Basis κ 𝕜 G)
    {eV : Trivialization F (π F V)} [MemTrivializationAtlas eV]
    {eW : Trivialization G (π G W)} [MemTrivializationAtlas eW]
    (hxV : x ∈ eV.baseSet) (hxW : x ∈ eW.baseSet)
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] G)
      (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x)
    (v : TangentSpace I x) (i : κ) (j : ι) :
    eW.localFrameCoeff I bW i x (covV.hom covW A x v (eV.localFrame bV j x)) =
      mvfderiv I (fun y ↦ eW.localFrameCoeff I bW i y (A y (eV.localFrame bV j y))) x v +
        ∑ k, eW.localFrameCoeff I bW k x (A x (eV.localFrame bV j x)) *
          eW.localFrameCoeff I bW i x (covW (eW.localFrame bW k) x v) -
        ∑ k, eV.localFrameCoeff I bV k x (covV (eV.localFrame bV j) x v) *
          eW.localFrameCoeff I bW i x (A x (eV.localFrame bV k x)) := by
  classical
  have hframe : MDiffAt (T% (eV.localFrame bV j)) x :=
    (contMDiffAt_localFrame_of_mem (n := 1) eV bV j hxV).mdifferentiableAt one_ne_zero
  have hAs := hA.clm_bundle_apply hframe
  have hc := covW.isCovariantDerivativeOnUniv.mono (Set.subset_univ eW.baseSet)
  have hcoord := congrArg (fun L ↦ eW.localFrameCoeff I bW i x (L v))
    (covariantDerivative_eq_frameCovariantDerivative_add_sum bW hc hxW hAs)
  simp only [frameCovariantDerivative_apply, add_apply, _root_.sum_apply,
    _root_.smul_apply, map_add, map_sum, map_smul, localFrameCoeff_localFrame bW hxW,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, LinearMap.piApply_apply] at hcoord
  have hexp := eV.eq_sum_localFrameCoeff_smul (I := I) (b := bV)
    (s := fun y ↦ covV (eV.localFrame bV j) y (extend E v y)) hxV
  simp only [extend_apply_self] at hexp
  rw [hom_apply covV covW hA hframe, map_sub, hcoord]
  congr 1
  conv_lhs => rw [hexp]
  simp only [map_sum, map_smul, smul_eq_mul]

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
