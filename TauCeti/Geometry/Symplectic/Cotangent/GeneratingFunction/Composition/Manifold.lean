/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Composition.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Correspondence
public import TauCeti.Geometry.Manifold.Morse.Basic
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Composition of generating functions on manifolds

Let `S(q, a)` on `M₁ × M₂` and `T(a, Q)` on `M₂ × M₃` be real functions. They generate
cotangent relations `T*M₁ ⇝ T*M₂` and `T*M₂ ⇝ T*M₃`, with `p = d_q S`, `-d_a S` at `a`, and
`d_a T`, `P = -d_Q T` (`TauCeti.CotangentBundle.generatingSource`,
`TauCeti.CotangentBundle.generatingTarget`). Composing the two relations means matching the
intermediate cotangent points:

`(a, -d_a S(q, a)) = (a, d_a T(a, Q))`.

This is exactly the statement that `a` is a critical point of `a' ↦ S(q, a') + T(a', Q)`
(`TauCeti.CotangentBundle.generatingTarget_eq_generatingSource_iff`).

When this critical point is nondegenerate at `(q₀, a₀, Q₀)`, the intermediate position can be
eliminated near `(q₀, Q₀)`: when `S` and `T` are `C^(n+2)` at the matched points, there is a
`C^(n+1)` stationary branch `b(q, Q) ∈ M₂` through `a₀`, and the function
`R(q, Q) = S(q, b) + T(b, Q)` on `M₁ × M₃` generates the composite relation. On an open
neighbourhood of `(q₀, Q₀)`,

`d_q R(q, Q) = d_q S(q, b)`,  `d_Q R(q, Q) = d_Q T(b, Q)`,

and near `((q₀, Q₀), a₀)` the matching equation holds exactly on the graph of `b`
(`TauCeti.CotangentBundle.exists_generatingComposition`). Nondegeneracy is the intrinsic notion
of `TauCeti.IsManifoldNondegenerateCriticalPoint`, and the regularity hypotheses are pointwise, so
no chart enters the hypotheses.

The proof reads `S` and `T` in the preferred charts at `q₀`, `a₀` and `Q₀` and applies the
normed-space statement `TauCeti.exists_cotangentGeneratingComposition`. The charts change the
covectors by the invertible chart derivatives, which preserves the matching equation and
transports the identities for `d_q R` and `d_Q R`.

All conclusions are local. No assertion is made about critical points of the sum outside the
chosen neighbourhood, nor about a globally defined composite relation.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition,
  Springer, 1989, §48 (composition of canonical transformations).
* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
-/

public section

noncomputable section

open Bundle Filter Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti.CotangentBundle

variable {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {S : M₁ × M₂ → ℝ} {T : M₂ × M₃ → ℝ}

section Charts

variable [I₁.Boundaryless] [I₂.Boundaryless] [I₃.Boundaryless]
  [IsManifold I₁ 1 M₁] [IsManifold I₂ 1 M₂] [IsManifold I₃ 1 M₃]

omit [I₁.Boundaryless] [I₂.Boundaryless] [I₃.Boundaryless] [IsManifold I₁ 1 M₁]
  [IsManifold I₃ 1 M₃] in
/-- The matching equation of `TauCeti.CotangentBundle.generatingTarget_eq_generatingSource_iff`
read in extended charts at arbitrary base points: where the coordinate expressions of `S` and `T`
are differentiable, it holds on the manifolds exactly when it holds for these expressions. -/
private theorem generatingTarget_eq_generatingSource_iff_extChartAt
    (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) {q : M₁} {a : M₂} {Q : M₃}
    (hq : q ∈ (extChartAt I₁ x₁).source) (ha : a ∈ (extChartAt I₂ x₂).source)
    (hQ : Q ∈ (extChartAt I₃ x₃).source)
    (hS : DifferentiableAt ℝ
      (fun z : E₁ × E₂ ↦ S ((extChartAt I₁ x₁).symm z.1, (extChartAt I₂ x₂).symm z.2))
      (extChartAt I₁ x₁ q, extChartAt I₂ x₂ a))
    (hT : DifferentiableAt ℝ
      (fun z : E₂ × E₃ ↦ T ((extChartAt I₂ x₂).symm z.1, (extChartAt I₃ x₃).symm z.2))
      (extChartAt I₂ x₂ a, extChartAt I₃ x₃ Q)) :
    generatingTarget I₂ S (q, a) = generatingSource I₂ T (a, Q) ↔
      cotangentGeneratingTarget
          (fun z : E₁ × E₂ ↦ S ((extChartAt I₁ x₁).symm z.1, (extChartAt I₂ x₂).symm z.2))
          (extChartAt I₁ x₁ q, extChartAt I₂ x₂ a) =
        cotangentGeneratingSource
          (fun z : E₂ × E₃ ↦ T ((extChartAt I₂ x₂).symm z.1, (extChartAt I₃ x₃).symm z.2))
          (extChartAt I₂ x₂ a, extChartAt I₃ x₃ Q) := by
  set e₁ := extChartAt I₁ x₁
  set e₂ := extChartAt I₂ x₂
  set e₃ := extChartAt I₃ x₃
  set S' : E₁ × E₂ → ℝ := fun z ↦ S (e₁.symm z.1, e₂.symm z.2)
  set T' : E₂ × E₃ → ℝ := fun z ↦ T (e₂.symm z.1, e₃.symm z.2)
  -- The two slices through `a`, read in the chart at `x₂`, are slices of `S'` and `T'`.
  have hSa : DifferentiableAt ℝ ((fun a' ↦ S (q, a')) ∘ e₂.symm) (e₂ a) := by
    have hfun : (fun a' ↦ S (q, a')) ∘ e₂.symm = fun w ↦ S' (e₁ q, w) := by
      funext w
      simp only [comp_apply, S', e₁.left_inv hq]
    rw [hfun]
    exact DifferentiableAt.comp (g := S') (e₂ a) hS
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hTa : DifferentiableAt ℝ ((fun a' ↦ T (a', Q)) ∘ e₂.symm) (e₂ a) := by
    have hfun : (fun a' ↦ T (a', Q)) ∘ e₂.symm = fun w ↦ T' (w, e₃ Q) := by
      funext w
      simp only [comp_apply, T', e₃.left_inv hQ]
    rw [hfun]
    exact DifferentiableAt.comp (g := T') (e₂ a) hT
      (differentiableAt_id.prodMk (differentiableAt_const _))
  -- A function on `M₂` is differentiable at `a` when its expression in the chart at `x₂` is.
  have hmd {f : M₂ → ℝ} (hf : DifferentiableAt ℝ (f ∘ e₂.symm) (e₂ a)) :
      MDifferentiableAt I₂ 𝓘(ℝ) f a := by
    have hfeq : (f ∘ e₂.symm) ∘ e₂ =ᶠ[𝓝 a] f := by
      filter_upwards [(isOpen_extChartAt_source x₂).mem_nhds ha] with a' ha'
      rw [comp_apply, comp_apply, e₂.left_inv ha']
    exact (hf.mdifferentiableAt.comp a
      (mdifferentiableAt_extChartAt (by simpa [e₂] using ha))).congr_of_eventuallyEq hfeq.symm
  have hsum : DifferentiableAt ℝ ((fun a' ↦ S (q, a') + T (a', Q)) ∘ e₂.symm) (e₂ a) :=
    hSa.add hTa
  have hcoord : (fun a' ↦ S (q, a') + T (a', Q)) ∘ e₂.symm =
      fun w ↦ S' (e₁ q, w) + T' (w, e₃ Q) := by
    funext w
    simp only [comp_apply, S', T', e₁.left_inv hq, e₃.left_inv hQ]
  rw [generatingTarget_eq_generatingSource_iff (hmd hSa) (hmd hTa),
    cotangentGeneratingTarget_eq_cotangentGeneratingSource_iff hS hT, mvfderiv_eq_zero_iff,
    mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero ha hsum, hcoord]

/-- **Composition of generating functions on manifolds by stationary elimination.**

Let `S` on `M₁ × M₂` and `T` on `M₂ × M₃` be `C^(n+2)` near `(q₀, a₀)` and `(a₀, Q₀)`, and let
`a₀` be a nondegenerate critical point of `a ↦ S(q₀, a) + T(a, Q₀)`, so that the relations they
generate match at `(q₀, a₀, Q₀)`. Then there are a stationary branch `b : M₁ × M₃ → M₂` through
`a₀`, `C^(n+1)` at `(q₀, Q₀)`, and the generating function `R(q, Q) = S(q, b) + T(b, Q)` of the
composite relation: on an open neighbourhood `D` of `(q₀, Q₀)` the intermediate cotangent points
match along `b`, and `R` has source covector `d_q S(q, b)` and target covector `-d_Q T(b, Q)`.
Near `((q₀, Q₀), a₀)`, the matching equation holds exactly on the graph of `b`.

All assertions except the value at `(q₀, Q₀)` are local; no global composite relation and no
uniqueness of critical points outside this neighbourhood is asserted. -/
theorem exists_generatingComposition [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace E₃]
    {n : WithTop ℕ∞} {q₀ : M₁} {a₀ : M₂} {Q₀ : M₃}
    (hS : ContMDiffAt (I₁.prod I₂) 𝓘(ℝ) (n + 2) S (q₀, a₀))
    (hT : ContMDiffAt (I₂.prod I₃) 𝓘(ℝ) (n + 2) T (a₀, Q₀))
    (h : IsManifoldNondegenerateCriticalPoint I₂ (fun a ↦ S (q₀, a) + T (a, Q₀)) a₀) :
    ∃ (b : M₁ × M₃ → M₂) (R : M₁ × M₃ → ℝ) (D : Set (M₁ × M₃)),
      IsOpen D ∧ (q₀, Q₀) ∈ D ∧ b (q₀, Q₀) = a₀ ∧
      (∀ y, R y = S (y.1, b y) + T (b y, y.2)) ∧
      ContMDiffAt (I₁.prod I₃) I₂ (n + 1) b (q₀, Q₀) ∧
      ContMDiffAt (I₁.prod I₃) 𝓘(ℝ) (n + 1) R (q₀, Q₀) ∧
      (∀ y ∈ D,
        generatingTarget I₂ S (y.1, b y) = generatingSource I₂ T (b y, y.2) ∧
        generatingSource I₁ R y = generatingSource I₁ S (y.1, b y) ∧
        generatingTarget I₃ R y = generatingTarget I₃ T (b y, y.2)) ∧
      (∀ᶠ x in 𝓝 ((q₀, Q₀), a₀),
        generatingTarget I₂ S (x.1.1, x.2) = generatingSource I₂ T (x.2, x.1.2) ↔
          b x.1 = x.2) := by
  set e₁ := extChartAt I₁ q₀
  set e₂ := extChartAt I₂ a₀
  set e₃ := extChartAt I₃ Q₀
  let S' : E₁ × E₂ → ℝ := fun z ↦ S (e₁.symm z.1, e₂.symm z.2)
  let T' : E₂ × E₃ → ℝ := fun z ↦ T (e₂.symm z.1, e₃.symm z.2)
  -- `S'` and `T'` are `S` and `T` read in the product charts at the base points.
  have hS' : ContDiffAt ℝ (n + 2) S' (e₁ q₀, e₂ a₀) := by
    have hfun : S ∘ (extChartAt (I₁.prod I₂) (q₀, a₀)).symm = S' := by
      rw [extChartAt_prod, PartialEquiv.prod_symm]
      rfl
    have hpt : extChartAt (I₁.prod I₂) (q₀, a₀) (q₀, a₀) = (e₁ q₀, e₂ a₀) := by
      rw [extChartAt_prod, PartialEquiv.prod_coe]
    rw [← hfun, ← hpt]
    exact hS.contDiffAt_comp_extChartAt_symm
  have hT' : ContDiffAt ℝ (n + 2) T' (e₂ a₀, e₃ Q₀) := by
    have hfun : T ∘ (extChartAt (I₂.prod I₃) (a₀, Q₀)).symm = T' := by
      rw [extChartAt_prod, PartialEquiv.prod_symm]
      rfl
    have hpt : extChartAt (I₂.prod I₃) (a₀, Q₀) (a₀, Q₀) = (e₂ a₀, e₃ Q₀) := by
      rw [extChartAt_prod, PartialEquiv.prod_coe]
    rw [← hfun, ← hpt]
    exact hT.contDiffAt_comp_extChartAt_symm
  have h1 : (1 : WithTop ℕ∞) ≤ n + 2 := le_add_left one_le_two
  have hv₀ : e₁ q₀ ∈ e₁.target := mem_extChartAt_target q₀
  have hw₀ : e₂ a₀ ∈ e₂.target := mem_extChartAt_target a₀
  have hu₀ : e₃ Q₀ ∈ e₃.target := mem_extChartAt_target Q₀
  /- Step 1: the hypotheses of the normed-space composition theorem, read in the charts. -/
  have hcoord : (fun a ↦ S (q₀, a) + T (a, Q₀)) ∘ e₂.symm =
      fun w ↦ S' (e₁ q₀, w) + T' (w, e₃ Q₀) := by
    funext w
    simp only [comp_apply, S', T', e₁, e₃, extChartAt_to_inv]
  have hslice : (fun w ↦ cotangentGeneratingSum S' T' ((e₁ q₀, e₃ Q₀), w)) =
      fun w ↦ S' (e₁ q₀, w) + T' (w, e₃ Q₀) :=
    funext fun w ↦ cotangentGeneratingSum_apply S' T' (e₁ q₀) (e₃ Q₀) w
  have hcrit : IsNondegenerateCriticalPoint (fun w ↦ S' (e₁ q₀, w) + T' (w, e₃ Q₀)) (e₂ a₀) := by
    rw [← hcoord]
    exact (isManifoldNondegenerateCriticalPoint_iff I₂).mp h
  have hsum : ContDiffAt ℝ (n + 2) (cotangentGeneratingSum S' T') ((e₁ q₀, e₃ Q₀), e₂ a₀) :=
    contDiffAt_cotangentGeneratingSum hS' hT'
  have hmatch : cotangentGeneratingTarget S' (e₁ q₀, e₂ a₀) =
      cotangentGeneratingSource T' (e₂ a₀, e₃ Q₀) :=
    (cotangentGeneratingTarget_eq_cotangentGeneratingSource_iff
      (hS'.differentiableAt (by simp)) (hT'.differentiableAt (by simp))).2
      hcrit.fderiv_eq_zero
  -- The negative intermediate Hessian is minus the Hessian of the slice through `(q₀, Q₀)`.
  have hH : (cotangentLegendreHessian (cotangentGeneratingSum S' T')
      ((e₁ q₀, e₃ Q₀), e₂ a₀)).IsInvertible := by
    have heq : cotangentLegendreHessian (cotangentGeneratingSum S' T') ((e₁ q₀, e₃ Q₀), e₂ a₀) =
        (ContinuousLinearEquiv.neg ℝ : (E₂ →L[ℝ] ℝ) ≃L[ℝ] (E₂ →L[ℝ] ℝ)) ∘L
          fderiv ℝ (fderiv ℝ (fun w ↦ S' (e₁ q₀, w) + T' (w, e₃ Q₀))) (e₂ a₀) := by
      ext v w
      rw [cotangentLegendreHessian_apply_apply,
        ← fderiv_fderiv_slice_right_apply (hsum.of_le (by simp)) v w, hslice]
      simp
    rw [heq, ContinuousLinearMap.isInvertible_equiv_comp]
    exact hcrit.isInvertible
  /- Step 2: eliminate the intermediate position in the charts. -/
  obtain ⟨b', R', D', hD'o, hD'mem, hb'₀, hR'def, hb', hR', hrel, huniq⟩ :=
    exists_cotangentGeneratingComposition hS' hT' hmatch hH
  let b : M₁ × M₃ → M₂ := fun y ↦ e₂.symm (b' (e₁ y.1, e₃ y.2))
  let R : M₁ × M₃ → ℝ := fun y ↦ S (y.1, b y) + T (b y, y.2)
  have hb₀ : b (q₀, Q₀) = a₀ := by
    simp only [b, hb'₀, e₂, extChartAt_to_inv]
  have htarget : ∀ᶠ y' in 𝓝 (e₁ q₀, e₃ Q₀), b' y' ∈ e₂.target :=
    hb'.continuousAt.preimage_mem_nhds (hb'₀ ▸ extChartAt_target_mem_nhds' hw₀)
  -- Read in the charts at `(q₀, Q₀)` and `a₀`, the branch `b` is `b'` near `(e₁ q₀, e₃ Q₀)`.
  have hb : ContMDiffAt (I₁.prod I₃) I₂ (n + 1) b (q₀, Q₀) := by
    have hcont : ContinuousAt b (q₀, Q₀) := by
      have he₂ : ContinuousAt e₂.symm (b' (e₁ q₀, e₃ Q₀)) := by
        rw [hb'₀]
        exact continuousAt_extChartAt_symm a₀
      have hinner : ContinuousAt (fun y : M₁ × M₃ ↦ (e₁ y.1, e₃ y.2)) (q₀, Q₀) :=
        ((continuousAt_extChartAt (I := I₁) q₀).comp continuousAt_fst).prodMk
          ((continuousAt_extChartAt (I := I₃) Q₀).comp continuousAt_snd)
      have hb'c : ContinuousAt (fun y : M₁ × M₃ ↦ b' (e₁ y.1, e₃ y.2)) (q₀, Q₀) :=
        ContinuousAt.comp (g := b') hb'.continuousAt hinner
      exact he₂.comp_of_eq hb'c rfl
    rw [contMDiffAt_iff, hb₀, extChartAt_prod, ModelWithCorners.range_eq_univ,
      contDiffWithinAt_univ]
    refine ⟨hcont, hb'.congr_of_eventuallyEq ?_⟩
    filter_upwards [htarget, prod_mem_nhds (extChartAt_target_mem_nhds' hv₀)
      (extChartAt_target_mem_nhds' hu₀)] with z hz hz'
    simp only [b, e₁, e₂, e₃, comp_apply, PartialEquiv.prod_symm, PartialEquiv.prod_coe] at hz hz' ⊢
    rw [PartialEquiv.right_inv _ hz'.1, PartialEquiv.right_inv _ hz'.2, Prod.mk.eta,
      PartialEquiv.right_inv _ hz]
  have hR : ContMDiffAt (I₁.prod I₃) 𝓘(ℝ) (n + 1) R (q₀, Q₀) := by
    have hle : n + 1 ≤ n + 2 := by gcongr; norm_num
    have hS₀ : ContMDiffAt (I₁.prod I₂) 𝓘(ℝ) (n + 1) S (q₀, b (q₀, Q₀)) := hb₀ ▸ hS.of_le hle
    have hT₀ : ContMDiffAt (I₂.prod I₃) 𝓘(ℝ) (n + 1) T (b (q₀, Q₀), Q₀) := hb₀ ▸ hT.of_le hle
    exact (hS₀.comp (q₀, Q₀) (contMDiffAt_fst.prodMk hb)).add
      (hT₀.comp (q₀, Q₀) (hb.prodMk contMDiffAt_snd))
  /- Step 3: shrink the coordinate domain so that the branch stays in the chart at `a₀` and the
  coordinate expressions stay differentiable. -/
  have hev : ∀ᶠ y' in 𝓝 (e₁ q₀, e₃ Q₀), y' ∈ D' ∧ b' y' ∈ e₂.target ∧
      DifferentiableAt ℝ R' y' ∧ DifferentiableAt ℝ S' (y'.1, b' y') ∧
        DifferentiableAt ℝ T' (b' y', y'.2) := by
    have hSd := hS'.eventually_differentiableAt h1
    have hTd := hT'.eventually_differentiableAt h1
    rw [← hb'₀] at hSd hTd
    filter_upwards [hD'o.mem_nhds hD'mem, htarget,
      ContDiffAt.eventually_differentiableAt hR' (by simp),
      (continuousAt_fst.prodMk hb'.continuousAt).eventually hSd,
      (hb'.continuousAt.prodMk continuousAt_snd).eventually hTd] with y' h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨U, hUsub, hUo, hUmem⟩ := mem_nhds_iff.mp hev
  let D : Set (M₁ × M₃) := (e₁.source ×ˢ e₃.source) ∩ (fun y ↦ (e₁ y.1, e₃ y.2)) ⁻¹' U
  have hDo : IsOpen D :=
    ((continuousOn_extChartAt q₀).prodMap (continuousOn_extChartAt Q₀)).isOpen_inter_preimage
      ((isOpen_extChartAt_source q₀).prod (isOpen_extChartAt_source Q₀)) hUo
  have hDmem : (q₀, Q₀) ∈ D :=
    ⟨⟨mem_extChartAt_source q₀, mem_extChartAt_source Q₀⟩, hUmem⟩
  refine ⟨b, R, D, hDo, hDmem, hb₀, fun _ ↦ rfl, hb, hR, ?_, ?_⟩
  /- Step 4: transport the three relations from the charts. -/
  · rintro ⟨q, Q⟩ ⟨⟨hq, hQ⟩, hU⟩
    set y' : E₁ × E₃ := (e₁ q, e₃ Q)
    have hy' : y' ∈ D' ∧ b' y' ∈ e₂.target ∧ DifferentiableAt ℝ R' y' ∧
        DifferentiableAt ℝ S' (y'.1, b' y') ∧ DifferentiableAt ℝ T' (b' y', y'.2) := hUsub hU
    obtain ⟨hy'D, hby', hRy', hS'y, hT'y⟩ := hy'
    obtain ⟨hr₁, hr₂, hr₃⟩ := hrel y' hy'D
    have hbs : b (q, Q) ∈ e₂.source := e₂.map_target hby'
    have hbe : e₂ (b (q, Q)) = b' y' := e₂.right_inv hby'
    have hq' : e₁ q ∈ e₁.target := e₁.map_source hq
    have hQ' : e₃ Q ∈ e₃.target := e₃.map_source hQ
    -- Near `y'`, the coordinate expressions of `R` and of its two slices are `R'` and its slices.
    have hReq : ∀ᶠ z in 𝓝 y', R (e₁.symm z.1, e₃.symm z.2) = R' z := by
      filter_upwards [hUo.mem_nhds hU, prod_mem_nhds (extChartAt_target_mem_nhds' hq')
        (extChartAt_target_mem_nhds' hQ')] with z _ hz
      simp only [R, b, hR'def, S', T', e₁.right_inv hz.1, e₃.right_inv hz.2]
    refine ⟨?_, ?_, ?_⟩
    · rw [generatingTarget_eq_generatingSource_iff_extChartAt q₀ a₀ Q₀ hq hbs hQ
        (by rwa [hbe]) (by rwa [hbe]), hbe]
      exact hr₁
    · have hslice : (fun q' ↦ R (q', Q)) ∘ e₁.symm =ᶠ[𝓝 (e₁ q)] fun v ↦ R' (v, e₃ Q) := by
        have hcont : ContinuousAt (fun v : E₁ ↦ (v, e₃ Q)) (e₁ q) := by fun_prop
        filter_upwards [hcont.eventually hReq] with v hv
        simpa only [comp_apply, e₃.left_inv hQ] using hv
      -- By definition of `b` and `S'`, the slice of `S` through `b (q, Q)` reads in the chart as
      -- the slice of `S'` through `b' y'`.
      have hmv : mvfderiv I₁ (fun q' ↦ R (q', Q)) q =
          mvfderiv I₁ (fun q' ↦ S (q', b (q, Q))) q := by
        refine mvfderiv_eq_of_fderiv_comp_extChartAt_symm_eq (g' := fun v ↦ S' (v, b' y')) hq
          hslice .rfl (hRy'.comp (e₁ q) (differentiableAt_id.prodMk (differentiableAt_const _)))
          (DifferentiableAt.comp (g := S') (e₁ q) hS'y
            (differentiableAt_id.prodMk (differentiableAt_const _))) ?_
        rw [fderiv_slice_left hRy', fderiv_slice_left hS'y]
        ext w
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          cotangentGeneratingSource_snd_apply] using congr($hr₂.2 w)
      exact CotangentBundle.ext (by simp) fun v ↦ by
        rw [generatingSource_snd, generatingSource_snd]
        exact congr($hmv v)
    · have hslice : (fun Q' ↦ R (q, Q')) ∘ e₃.symm =ᶠ[𝓝 (e₃ Q)] fun u ↦ R' (e₁ q, u) := by
        have hcont : ContinuousAt (fun u : E₃ ↦ (e₁ q, u)) (e₃ Q) := by fun_prop
        filter_upwards [hcont.eventually hReq] with u hu
        simpa only [comp_apply, e₁.left_inv hq] using hu
      -- As above, the slice of `T` through `b (q, Q)` reads in the chart as that of `T'`.
      have hmv : mvfderiv I₃ (fun Q' ↦ R (q, Q')) Q =
          mvfderiv I₃ (fun Q' ↦ T (b (q, Q), Q')) Q := by
        refine mvfderiv_eq_of_fderiv_comp_extChartAt_symm_eq (g' := fun u ↦ T' (b' y', u)) hQ
          hslice .rfl (hRy'.comp (e₃ Q) ((differentiableAt_const _).prodMk differentiableAt_id))
          (DifferentiableAt.comp (g := T') (e₃ Q) hT'y
            ((differentiableAt_const _).prodMk differentiableAt_id)) ?_
        rw [fderiv_slice_right hRy', fderiv_slice_right hT'y]
        ext w
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
          cotangentGeneratingTarget_snd_apply, neg_inj] using congr($hr₃.2 w)
      exact CotangentBundle.ext (by simp) fun v ↦ by
        rw [generatingTarget_snd, generatingTarget_snd]
        exact congr((-$hmv) v)
  /- Step 5: transport the local uniqueness of the stationary branch. -/
  · have hmap : ContinuousAt (fun x : (M₁ × M₃) × M₂ ↦ ((e₁ x.1.1, e₃ x.1.2), e₂ x.2))
        ((q₀, Q₀), a₀) :=
      (((continuousAt_extChartAt (I := I₁) q₀).comp
          (continuousAt_fst.comp continuousAt_fst)).prodMk
        ((continuousAt_extChartAt (I := I₃) Q₀).comp
          (continuousAt_snd.comp continuousAt_fst))).prodMk
        ((continuousAt_extChartAt (I := I₂) a₀).comp continuousAt_snd)
    have hsrc : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀),
        x.1.1 ∈ e₁.source ∧ x.1.2 ∈ e₃.source ∧ x.2 ∈ e₂.source := by
      have h₁ : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀), x.1.1 ∈ e₁.source :=
        (continuousAt_fst.comp continuousAt_fst).preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := I₁) q₀)
      have h₂ : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀), x.1.2 ∈ e₃.source :=
        (continuousAt_snd.comp continuousAt_fst).preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := I₃) Q₀)
      have h₃ : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀), x.2 ∈ e₂.source :=
        continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I₂) a₀)
      filter_upwards [h₁, h₂, h₃] with x hx₁ hx₂ hx₃
      exact ⟨hx₁, hx₂, hx₃⟩
    have htarget : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀),
        b' (e₁ x.1.1, e₃ x.1.2) ∈ e₂.target := by
      have hU' : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀), (e₁ x.1.1, e₃ x.1.2) ∈ U :=
        (hmap.fst).preimage_mem_nhds (hUo.mem_nhds hUmem)
      filter_upwards [hU'] with x hx
      exact (hUsub hx).2.1
    have hSd : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀),
        DifferentiableAt ℝ S' (e₁ x.1.1, e₂ x.2) :=
      (hmap.fst.fst.prodMk hmap.snd).eventually (hS'.eventually_differentiableAt h1)
    have hTd : ∀ᶠ x : (M₁ × M₃) × M₂ in 𝓝 ((q₀, Q₀), a₀),
        DifferentiableAt ℝ T' (e₂ x.2, e₃ x.1.2) :=
      (hmap.snd.prodMk hmap.fst.snd).eventually (hT'.eventually_differentiableAt h1)
    filter_upwards [hmap.eventually huniq, hsrc, htarget, hSd, hTd] with x hx hs ht hSx hTx
    rw [generatingTarget_eq_generatingSource_iff_extChartAt q₀ a₀ Q₀ hs.1 hs.2.2 hs.2.1 hSx hTx]
    exact hx.trans (e₂.symm_apply_eq hs.2.2 ht).symm

end Charts

end TauCeti.CotangentBundle
