/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondBianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Einstein's constancy theorem

Let `∇` be a smooth metric-compatible torsion-free connection on the tangent bundle of a
Riemannian manifold `M` of dimension `n`, such as its Levi-Civita connection, and suppose that its
Ricci tensor is pointwise proportional to the metric, `Ric = a g` for a function `a : M → ℝ`.
If `n ≠ 2`, then `da = 0`; hence `a` is constant when `M` is connected, and an Einstein metric in
dimension at least three has constant Einstein factor.

The proof contracts the second Bianchi identity twice. With
`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇_X Y, Z) σ - R(Y, ∇_X Z) σ - R(Y, Z) (∇_X σ)`, contracting
the direction `X` against the output turns the identity into
`(div R)(Y, Z) W = (∇_Y Ric)(Z, W) - (∇_Z Ric)(Y, W)`, and contracting `Z` with `W` through the
metric, using pair symmetry, turns the left side into `(div Ric)(Y)`: this is the contracted
Bianchi identity `2 div Ric = d Scal`. For `Ric = a g`, metric compatibility gives
`(∇_X Ric)(Y, Z) = da(X) ⟪Y, Z⟫`, and the twice contracted identity reads `da = n da - da`, that
is `(n - 2) da = 0`. In dimension two every metric has `Ric = K g` for its Gaussian curvature `K`,
which need not be constant.

The contractions are taken in a local frame at the point: the frame of a trivialization, cut off
by a bump function to globally smooth vector fields. Differentiating the frame coefficients by the
local frame formula `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum`
shows that the trace defining the Ricci tensor commutes with covariant differentiation. The
covariant derivative of the curvature is used only on vector fields, as in the second Bianchi
identity `CovariantDerivative.covariantDerivative_curvatureOperator_cyclic_eq_zero`.

## Main results

* `CovariantDerivative.mfderiv_eq_zero_of_ricciTensor_eq_smul_inner`: if `Ric = a g` and
  `n ≠ 2`, then `da` vanishes at every point.
* `CovariantDerivative.eq_of_ricciTensor_eq_smul_inner`: **Einstein's constancy theorem**; on a
  preconnected manifold of positive dimension other than two, `Ric = a g` forces `a` to be
  constant.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the contracted Bianchi identity and Einstein metrics).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace CovariantDerivative

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

variable (cov) in
/-- The covariant derivative of the curvature at `x` along `v`, evaluated on vector fields:
`(∇_v R)(Y, Z) σ = ∇_v (R(Y, Z) σ) - R(∇_v Y, Z) σ - R(Y, ∇_v Z) σ - R(Y, Z) (∇_v σ)`. -/
private def derivCurvature (x : M) (v : TangentSpace I x) (Y Z σ : Π y : M, TangentSpace I y) :
    TangentSpace I x :=
  cov (curvatureOperator cov Y Z σ) x v - curvature x (cov Y x v) (Z x) (σ x) -
    curvature x (Y x) (cov Z x v) (σ x) - curvature x (Y x) (Z x) (cov σ x v)

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The second Bianchi identity, written with `derivCurvature`. -/
private theorem derivCurvature_cyclic (ht : cov.torsion = 0)
    {X Y Z σ : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) (x : M) :
    derivCurvature cov x (X x) Y Z σ + derivCurvature cov x (Y x) Z X σ +
      derivCurvature cov x (Z x) X Y σ = 0 := by
  have h := covariantDerivative_curvatureOperator_cyclic_eq_zero cov cov
    ((isTorsionFree_iff_torsion_eq_zero cov).2 ht) hX hY hZ hσ x
  rw [← curvatureTensor_apply cov x (cov.contMDiff_apply hX hY) hZ hσ,
    ← curvatureTensor_apply cov x hY (cov.contMDiff_apply hX hZ) hσ,
    ← curvatureTensor_apply cov x hY hZ (cov.contMDiff_apply hX hσ),
    ← curvatureTensor_apply cov x (cov.contMDiff_apply hY hZ) hX hσ,
    ← curvatureTensor_apply cov x hZ (cov.contMDiff_apply hY hX) hσ,
    ← curvatureTensor_apply cov x hZ hX (cov.contMDiff_apply hY hσ),
    ← curvatureTensor_apply cov x (cov.contMDiff_apply hZ hX) hY hσ,
    ← curvatureTensor_apply cov x hX (cov.contMDiff_apply hZ hY) hσ,
    ← curvatureTensor_apply cov x hX hY (cov.contMDiff_apply hZ hσ)] at h
  simpa only [derivCurvature] using h

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- `derivCurvature` is antisymmetric in its two curvature slots. -/
private theorem derivCurvature_antisymm {Y Z σ : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) (x : M)
    (v : TangentSpace I x) :
    derivCurvature cov x v Z Y σ = -derivCurvature cov x v Y Z σ := by
  have hR : curvatureOperator cov Z Y σ = -curvatureOperator cov Y Z σ :=
    curvatureOperator_antisymm cov Z Y σ
  have hd := cov.isCovariantDerivativeOnUniv.neg
    ((cov.contMDiff_curvatureOperator hY hZ hσ).mdifferentiableAt (by simp) (x := x))
  simp only [derivCurvature, hR, hd, cov.curvatureTensor_antisymm x (Z x),
    cov.curvatureTensor_antisymm x (cov Z x v), LinearMap.neg_apply, neg_apply]
  abel

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Contracting `derivCurvature` in its first slot against the output, in a local frame at `x`,
gives the covariant derivative `(∇_X Ric)(B, C) = X (Ric(B, C)) - Ric(∇_X B, C) - Ric(B, ∇_X C)`
of the Ricci tensor. The frame is a family of global smooth vector fields `F` forming a basis at
`x`, with dual coordinate functionals `c` at `x`. -/
private theorem exists_frame_sum_derivCurvature (x : M) :
    ∃ (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
      (c : Fin (Module.finrank ℝ E) → TangentSpace I x →ₗ[ℝ] ℝ),
      (∀ i, CMDiff ∞ (T% (F i))) ∧ (∀ i j, c i (F j x) = if i = j then 1 else 0) ∧
      (∀ w, ∑ i, c i w • F i x = w) ∧
      ∀ {X B C : Π y : M, TangentSpace I y}, CMDiff ∞ (T% B) → CMDiff ∞ (T% C) →
        ∑ i, c i (derivCurvature cov x (X x) (F i) B C) =
          mvfderiv I (fun y ↦ cov.ricciTensor y (B y) (C y)) x (X x) -
            cov.ricciTensor x (cov B x (X x)) (C x) -
              cov.ricciTensor x (B x) (cov C x (X x)) := by
  classical
  -- Write `Ric(B, C) = ∑ₖ cₖ(R(Fₖ, B) C)` near `x` and differentiate each coefficient by the local
  -- frame formula. The terms coming from `∇_v Fₖ` cancel against those of `derivCurvature`, which
  -- is the statement that the trace commutes with covariant differentiation.
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hnhds : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds hx
  -- Cut off the trivialization frame by a bump function equal to one near `x`.
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hnhds).mem_iff.mp hnhds
  let F (k : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
    (ρ : M → ℝ) • e.localFrame b k
  have hF (k : Fin (Module.finrank ℝ E)) : CMDiff ∞ (T% (F k)) :=
    ρ.contMDiff.contMDiffOn.smul_section_of_tsupport e.open_baseSet hρ
      (e.contMDiffOn_localFrame_baseSet _ b k)
  have hFeq (k : Fin (Module.finrank ℝ E)) : ∀ᶠ y in 𝓝 x, F k y = e.localFrame b k y := by
    filter_upwards [ρ.eventuallyEq_one] with y hy
    simp [F, hy]
  have hFx (k : Fin (Module.finrank ℝ E)) : F k x = e.basisAt b hx k := by
    rw [(hFeq k).self_of_nhds, e.localFrame_apply_of_mem_baseSet b hx]
  let c (k : Fin (Module.finrank ℝ E)) : TangentSpace I x →ₗ[ℝ] ℝ := e.localFrameCoeff I b k x
  have hc (k : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
      c k w = (e.basisAt b hx).repr w k := by
    obtain ⟨s, -, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
    exact e.localFrameCoeff_apply_of_mem_baseSet b hx s k
  have hdual (i j : Fin (Module.finrank ℝ E)) : c i (F j x) = if i = j then 1 else 0 := by
    rw [hc, hFx, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  have hsum (w : TangentSpace I x) : ∑ i, c i w • F i x = w := by
    simp only [hc, hFx]
    exact (e.basisAt b hx).sum_repr w
  have hRicx (u w : TangentSpace I x) :
      cov.ricciTensor x u w = ∑ k, c k (curvature x (F k x) u w) := by
    rw [cov.ricciTensor_eq_sum x (e.basisAt b hx)]
    simp only [hc, hFx]
  refine ⟨F, c, hF, hdual, hsum, fun {X B C} hB hC ↦ ?_⟩
  set v := X x
  let s (k : Fin (Module.finrank ℝ E)) := curvatureOperator cov (F k) B C
  have hs (k : Fin (Module.finrank ℝ E)) : CMDiff ∞ (T% (s k)) :=
    cov.contMDiff_curvatureOperator (hF k) hB hC
  have hsx (k : Fin (Module.finrank ℝ E)) : s k x = curvature x (F k x) (B x) (C x) :=
    (curvatureTensor_apply cov x (hF k) hB hC).symm
  -- Near `x`, the Ricci tensor is the trace in the frame.
  have hRic : (fun y ↦ cov.ricciTensor y (B y) (C y)) =ᶠ[𝓝 x]
      fun y ↦ ∑ k, e.localFrameCoeff I b k y (s k y) := by
    filter_upwards [ρ.eventuallyEq_one, hnhds] with y hρy hy
    rw [cov.ricciTensor_eq_sum y (e.basisAt b hy)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hFy : F k y = e.basisAt b hy k := by
      simp [F, hρy, e.localFrame_apply_of_mem_baseSet b hy]
    rw [e.localFrameCoeff_apply_of_mem_baseSet b hy (s k) k, ← hFy]
    exact congrArg (fun w ↦ (e.basisAt b hy).repr w k) (curvatureTensor_apply cov y (hF k) hB hC)
  have hcoeff (k : Fin (Module.finrank ℝ E)) :
      MDiffAt (fun y ↦ e.localFrameCoeff I b k y (s k y)) x :=
    mdifferentiableAt_localFrameCoeff b hx ((hs k).mdifferentiableAt (by simp)) k
  have hd : mvfderiv I (fun y ↦ cov.ricciTensor y (B y) (C y)) x v =
      ∑ k, mvfderiv I (fun y ↦ e.localFrameCoeff I b k y (s k y)) x v := by
    have hfun : (fun y ↦ ∑ k, e.localFrameCoeff I b k y (s k y)) =
        ∑ k, fun y ↦ e.localFrameCoeff I b k y (s k y) := by
      ext y; simp
    have hH : HasMFDerivAt I 𝓘(ℝ) (∑ k, fun y ↦ e.localFrameCoeff I b k y (s k y)) x
        (∑ k, mvfderiv I (fun y ↦ e.localFrameCoeff I b k y (s k y)) x) :=
      HasMFDerivAt.sum fun k _ ↦ (hcoeff k).hasMFDerivAt
    rw [hRic.mvfderiv_eq, hfun, mvfderiv_apply_eq_mfderiv_apply, hH.mfderiv]
    -- The tangent spaces of `ℝ` in which `mfderiv` takes values are `ℝ` itself.
    exact _root_.sum_apply ..
  -- The local frame formula, read in the `k`-th coordinate.
  have hcov' := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet)
  have hframe (k : Fin (Module.finrank ℝ E)) :
      c k (cov (curvatureOperator cov (F k) B C) x v) =
        mvfderiv I (fun y ↦ e.localFrameCoeff I b k y (s k y)) x v +
          ∑ j, c j (s k x) * c k (cov (F j) x v) := by
    have h := congrArg (fun L ↦ c k (L v))
      (TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov' hx
        ((hs k).mdifferentiableAt (by simp)))
    have hloc (j : Fin (Module.finrank ℝ E)) : cov (e.localFrame b j) x = cov (F j) x :=
      hcov'.congr_of_eventuallyEq
        ((contMDiffAt_localFrame_of_mem (n := ∞) e b j hx).mdifferentiableAt (by simp))
        ((hF j).mdifferentiableAt (by simp)) hnhds ((hFeq j).mono fun y hy ↦ hy.symm)
    simp only [TauCeti.Manifold.frameCovariantDerivative_apply, add_apply,
      _root_.sum_apply, _root_.smul_apply, map_add, map_sum,
      map_smul, smul_eq_mul, hloc] at h
    have hlf (j : Fin (Module.finrank ℝ E)) : e.localFrame b j x = F j x := by
      rw [hFx, e.localFrame_apply_of_mem_baseSet b hx]
    have hpi : LinearMap.piApply (e.localFrameCoeff I b k) (s k) =
        fun y ↦ e.localFrameCoeff I b k y (s k y) := by
      ext y
      simp
    simp only [hlf, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, hpi] at h
    exact h
  -- Expand `∇_v Fₖ` in the frame.
  have hexp (k : Fin (Module.finrank ℝ E)) :
      c k (curvature x (cov (F k) x v) (B x) (C x)) =
        ∑ j, c j (cov (F k) x v) * c k (s j x) := by
    conv_lhs => rw [← hsum (cov (F k) x v)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hsx]
  simp only [derivCurvature, map_sub, Finset.sum_sub_distrib, hframe, hexp, ← hRicx, hd,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k j ↦ c j (cov (F k) x v) * c k (s j x))]
  simp only [mul_comm]
  ring

/-- For a metric-compatible connection, pairing `derivCurvature` with a vector field `U` gives the
covariant derivative of the metric-lowered curvature `⟪R(Y, Z) σ, U⟫`. -/
private theorem IsMetricCompatible.inner_derivCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (X : Π y : M, TangentSpace I y) {Y Z σ U : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ))
    (hU : CMDiff ∞ (T% U)) (x : M) :
    ⟪derivCurvature cov x (X x) Y Z σ, U x⟫_ℝ =
      mvfderiv I (fun y ↦ ⟪curvature y (Y y) (Z y) (σ y), U y⟫_ℝ) x (X x) -
        ⟪curvature x (cov Y x (X x)) (Z x) (σ x), U x⟫_ℝ -
          ⟪curvature x (Y x) (cov Z x (X x)) (σ x), U x⟫_ℝ -
            ⟪curvature x (Y x) (Z x) (cov σ x (X x)), U x⟫_ℝ -
              ⟪curvature x (Y x) (Z x) (σ x), cov U x (X x)⟫_ℝ := by
  have hfun : (fun y ↦ ⟪curvature y (Y y) (Z y) (σ y), U y⟫_ℝ) =
      fun y ↦ ⟪curvatureOperator cov Y Z σ y, U y⟫_ℝ := by
    funext y
    rw [curvatureTensor_apply cov y hY hZ hσ]
  have hd : mvfderiv I (fun y ↦ ⟪curvatureOperator cov Y Z σ y, U y⟫_ℝ) x (X x) =
      ⟪cov (curvatureOperator cov Y Z σ) x (X x), U x⟫_ℝ +
        ⟪curvatureOperator cov Y Z σ x, cov U x (X x)⟫_ℝ :=
    hcov.mvfderiv_inner_eq X
      ((cov.contMDiff_curvatureOperator hY hZ hσ).mdifferentiableAt (by simp))
      (hU.mdifferentiableAt (by simp))
  rw [hfun, hd, ← curvatureTensor_apply cov x hY hZ hσ]
  simp only [derivCurvature, inner_sub_left]
  ring

/-- Pair symmetry for `derivCurvature`: `⟪(∇_v R)(Y, Z) σ, U⟫ = ⟪(∇_v R)(σ, U) Y, Z⟫`. -/
private theorem IsMetricCompatible.inner_derivCurvature_swap_pairs
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (X : Π y : M, TangentSpace I y)
    {Y Z σ U : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hσ : CMDiff ∞ (T% σ)) (hU : CMDiff ∞ (T% U)) (x : M) :
    ⟪derivCurvature cov x (X x) Y Z σ, U x⟫_ℝ = ⟪derivCurvature cov x (X x) σ U Y, Z x⟫_ℝ := by
  have hs (y : M) (a b c d : TangentSpace I y) :
      ⟪curvature y a b c, d⟫_ℝ = ⟪curvature y c d a, b⟫_ℝ :=
    hcov.inner_curvatureTensor_swap_pairs ht y a b c d
  have hfun : (fun y ↦ ⟪curvature y (Y y) (Z y) (σ y), U y⟫_ℝ) =
      fun y ↦ ⟪curvature y (σ y) (U y) (Y y), Z y⟫_ℝ :=
    funext fun y ↦ hs y _ _ _ _
  rw [hcov.inner_derivCurvature X hY hZ hσ hU, hcov.inner_derivCurvature X hσ hU hY hZ, hfun,
    hs x (cov Y x (X x)), hs x (Y x) (cov Z x (X x)), hs x (Y x) (Z x) (cov σ x (X x)),
    hs x (Y x) (Z x) (σ x) (cov U x (X x))]
  ring

/-- For a metric-compatible connection whose Ricci tensor is `a g`, the covariant derivative of the
Ricci tensor is `(∇_X Ric)(B, C) = da(X) ⟪B, C⟫`. -/
private theorem IsMetricCompatible.covariantDerivative_ricciTensor_eq
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {a : M → ℝ} (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) {x : M}
    (hax : MDifferentiableAt I 𝓘(ℝ) a x) (X : Π y : M, TangentSpace I y)
    {B C : Π y : M, TangentSpace I y} (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) :
    mvfderiv I (fun y ↦ cov.ricciTensor y (B y) (C y)) x (X x) -
        cov.ricciTensor x (cov B x (X x)) (C x) - cov.ricciTensor x (B x) (cov C x (X x)) =
      mvfderiv I a x (X x) * ⟪B x, C x⟫_ℝ := by
  have hfun : (fun y ↦ cov.ricciTensor y (B y) (C y)) = a * fun y ↦ ⟪B y, C y⟫_ℝ := by
    funext y
    simp [ha]
  -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
  have hBC' : CMDiff ∞ fun y ↦ ⟪B y, C y⟫_ℝ :=
    ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hB hC
  have hBC : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ⟪B y, C y⟫_ℝ) x := hBC'.mdifferentiableAt (by simp)
  have hd : mvfderiv I (fun y ↦ ⟪B y, C y⟫_ℝ) x (X x) =
      ⟪cov B x (X x), C x⟫_ℝ + ⟪B x, cov C x (X x)⟫_ℝ :=
    hcov.mvfderiv_inner_eq X (hB.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp))
  rw [hfun, mvfderiv_mul hax hBC]
  simp only [add_apply, smul_apply, smul_eq_mul, hd, ha, LinearMap.smul_apply, innerₗ_apply_apply]
  ring

/-- The twice contracted second Bianchi identity for a metric-compatible torsion-free connection
with Ricci tensor `Ric = a g`: in dimension `n`, `(n - 2) da = 0` wherever `a` is differentiable,
evaluated here on the value of a smooth vector field. -/
private theorem IsMetricCompatible.finrank_sub_two_mul_mvfderiv_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) {a : M → ℝ}
    (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) {x : M}
    (hax : MDifferentiableAt I 𝓘(ℝ) a x) {Y : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) :
    ((Module.finrank ℝ E : ℝ) - 2) * mvfderiv I a x (Y x) = 0 := by
  obtain ⟨F, c, hF, hdual, hsum, htr⟩ := exists_frame_sum_derivCurvature (cov := cov) x
  -- Represent the coordinate functionals at `x` by vectors, and extend these to vector fields.
  let u (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
    (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (LinearMap.toContinuousLinearMap (c i))
  have hu' (i : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) : ⟪u i, w⟫_ℝ = c i w :=
    InnerProductSpace.toDual_symm_apply
  have hu (i : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) : ⟪w, u i⟫_ℝ = c i w := by
    rw [real_inner_comm, hu']
  choose U hU hUx using fun i ↦ FiberBundle.exists_contMDiff_section_eq I E (u i)
  have hsum' (w : TangentSpace I x) : ∑ j, ⟪w, F j x⟫_ℝ • u j = w := by
    refine ext_inner_right ℝ fun z ↦ ?_
    simp only [sum_inner, real_inner_smul_left, hu']
    conv_rhs => rw [← hsum z]
    simp only [inner_sum, real_inner_smul_right, mul_comm]
  have hnabla (X : Π y : M, TangentSpace I y) {B C : Π y : M, TangentSpace I y}
      (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) :=
    hcov.covariantDerivative_ricciTensor_eq ha hax X hB hC
  -- The second Bianchi identity for `Fᵢ, Y, Uⱼ` acting on `Fⱼ`, contracted over `i`.
  have hj (j : Fin (Module.finrank ℝ E)) :
      ∑ i, c i (derivCurvature cov x (F i x) Y (U j) (F j)) - mvfderiv I a x (Y x) +
        mvfderiv I a x (u j) * ⟪Y x, F j x⟫_ℝ = 0 := by
    have h0 : ∑ i, c i (derivCurvature cov x (F i x) Y (U j) (F j) +
        derivCurvature cov x (Y x) (U j) (F i) (F j) +
          derivCurvature cov x (U j x) (F i) Y (F j)) = 0 := by
      simp [derivCurvature_cyclic ht (hF _) hY (hU j) (hF j) x]
    have h2 : ∑ i, c i (derivCurvature cov x (Y x) (U j) (F i) (F j)) =
        -mvfderiv I a x (Y x) := by
      simp only [derivCurvature_antisymm (hF _) (hU j) (hF j), map_neg, Finset.sum_neg_distrib,
        htr (hU j) (hF j)]
      rw [hnabla Y (hU j) (hF j), hUx, hu', hdual]
      simp only [↓reduceIte, mul_one]
    have h3 : ∑ i, c i (derivCurvature cov x (U j x) (F i) Y (F j)) =
        mvfderiv I a x (u j) * ⟪Y x, F j x⟫_ℝ := by
      rw [htr hY (hF j), hnabla _ hY (hF j), hUx]
    simp only [map_add, Finset.sum_add_distrib, h2, h3] at h0
    linarith
  -- Contracting over `j` uses pair symmetry and the first contraction again.
  have hfirst : ∑ j, ∑ i, c i (derivCurvature cov x (F i x) Y (U j) (F j)) =
      mvfderiv I a x (Y x) := by
    have hswap (i j : Fin (Module.finrank ℝ E)) :
        c i (derivCurvature cov x (F i x) Y (U j) (F j)) =
          c j (derivCurvature cov x (F i x) (F j) (U i) Y) := by
      rw [← hu, ← hUx, hcov.inner_derivCurvature_swap_pairs ht (F i) hY (hU j) (hF j) (hU i),
        hUx, hu]
    simp only [hswap]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ ↦ htr (X := F i) (hU i) hY,
      Finset.sum_congr rfl fun i _ ↦ hnabla (F i) (hU i) hY]
    conv_rhs => rw [← hsum (Y x)]
    simp only [map_sum, map_smul, smul_eq_mul, hUx, hu', mul_comm]
  have hlast : ∑ j : Fin (Module.finrank ℝ E), mvfderiv I a x (u j) * ⟪Y x, F j x⟫_ℝ =
      mvfderiv I a x (Y x) := by
    conv_rhs => rw [← hsum' (Y x)]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htot := Finset.sum_eq_zero (s := Finset.univ) fun j _ ↦ hj j
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hfirst, hlast, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  linarith

/-- **Einstein's constancy theorem**, local form. Let a metric-compatible torsion-free connection
have Ricci tensor `Ric = a g` for a function `a`, in dimension other than two. Then `da`
vanishes at every point. -/
theorem mfderiv_eq_zero_of_ricciTensor_eq_smul_inner
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : Module.finrank ℝ E ≠ 2) {a : M → ℝ}
    (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) (x : M) :
    mfderiv I 𝓘(ℝ) a x = 0 := by
  by_cases hax : MDifferentiableAt I 𝓘(ℝ) a x
  swap
  · exact mfderiv_zero_of_not_mdifferentiableAt hax
  have h2 : ((Module.finrank ℝ E : ℝ) - 2) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hdim
  have hzero (v : TangentSpace I x) : mvfderiv I a x v = 0 := by
    obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
    exact (mul_eq_zero.1 (hcov.finrank_sub_two_mul_mvfderiv_eq_zero ht ha hax hY)).resolve_left h2
  ext v
  simpa [mvfderiv] using hzero v

/-- **Einstein's constancy theorem.** Let a metric-compatible torsion-free connection on a
preconnected manifold, of positive dimension other than two, have Ricci tensor `Ric = a g` for a
function `a`. Then `a` is constant. -/
theorem eq_of_ricciTensor_eq_smul_inner [PreconnectedSpace M]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hpos : Module.finrank ℝ E ≠ 0) (hdim : Module.finrank ℝ E ≠ 2)
    {a : M → ℝ} (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) (x y : M) :
    a x = a y := by
  -- `a` is the smooth scalar curvature divided by the dimension.
  have hn : (Module.finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hpos
  have haeq : a = fun y ↦ cov.scalarCurvature y / Module.finrank ℝ E := by
    funext y
    rw [cov.scalarCurvature_eq_of_ricciTensor_eq_smul_inner y (a y) (ha y), eq_div_iff hn]
    exact mul_comm _ _
  have had : MDifferentiable I 𝓘(ℝ) a := by
    rw [haeq]
    exact (cov.contMDiff_scalarCurvature.div_const _).mdifferentiable (by simp)
  exact had.apply_eq_of_mfderiv_eq_zero (fun z ↦
    mfderiv_eq_zero_of_ricciTensor_eq_smul_inner hcov ht hdim ha z) x y

end CovariantDerivative
