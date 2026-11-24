/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.SymmetricPower.Transition
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Chart
import TauCeti.LinearAlgebra.TotallyReal.Finrank

/-!
# Products of curves in the symmetric power: total reality and transversality

Let `α` be a Hausdorff complex curve, so that its `n`-th symmetric power `Sym α n` is a complex
manifold for its elementary-symmetric charts (`TauCeti.isManifold_symChartedSpace`). Given real
curves `γ₁, …, γₙ` in `α`, immersed at parameters `t₁, …, tₙ` whose points `γᵢ(tᵢ)` are pairwise
distinct, the map

`Γ : ℝⁿ → Sym α n`, `(s₁, …, sₙ) ↦ {γ₁(s₁), …, γₙ(sₙ)}`

is an immersion at `(t₁, …, tₙ)` in every chart of `Sym α n`, and its tangent space there is a
*maximal totally real* subspace of the complex coordinate space: it meets its image under
multiplication by `i` only in `0`, and spans with it. When `γᵢ` locally parametrizes the `i`-th
attaching curve `αᵢ` of a Heegaard diagram, `Γ` locally parametrizes the torus `T_α = α₁ × ⋯ × αₙ`
(`Sym.pi`, `Sym.ofFn_mem_pi`), whose points are always such tuples of distinct
points because attaching curves are pairwise disjoint. Thus, after supplying those local
parametrizations, the result gives the tangent-space criterion needed for the tori in the
holomorphic-disk boundary conditions of Ozsváth–Szabó. The global statement, that the product of
pairwise disjoint embedded circles is a totally real embedding of the torus, is
`Sym.isTotallyRealEmbedding_ofFn_map`.

In every chart at a tuple `p` of distinct points, the derivative of every such product through `p`
is one complex-linear isomorphism `T`, depending only on `p` and the chart, applied to the diagonal
map `τ ↦ (τᵢ vᵢ)ᵢ` of the velocities `vᵢ`. Two products `Γ` and `Δ` through the same unordered
tuple, the second through the same points in another order, therefore have complementary tangent
spaces exactly when the two diagonal maps do, that is, exactly when at each point the two curves
through it have real-independent velocities
(`TauCeti.isCompl_range_fderiv_symChartAt_ofFn_iff`). This is the transversality of the tori
`T_α` and `T_β` at a generator, read in a chart; its global form is
`Sym.isCompl_range_mfderiv_ofFn_map_iff`.

## Main declarations

* `TauCeti.differentiableAt_symChartAt_ofFn`: the product of the curves, read in a chart of the
  symmetric power, is real-differentiable.
* `TauCeti.contDiffAt_symChartAt_ofFn`: it is as smooth as the curves.
* `TauCeti.fderiv_symChartAt_ofFn_injective`: it is an immersion.
* `TauCeti.isMaximalTotallyReal_range_fderiv_symChartAt_ofFn`: its tangent space is maximal
  totally real.
* `TauCeti.isCompl_range_fderiv_symChartAt_ofFn_iff`: two such products through the same unordered
  tuple have complementary tangent spaces exactly when the curves meet transversally at each of
  its points.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Products of curves in the symmetric power -/

section Curves

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α]
  [IsManifold 𝓘(ℂ) 1 α] {n : ℕ}

/-- The real-linear map `τ ↦ (τ i • v i)ᵢ`, the derivative of a product of curves with velocities
`v i` read in product coordinates. -/
private noncomputable def diagonalSmulRight (v : Fin n → ℂ) : (Fin n → ℝ) →L[ℝ] Fin n → ℂ :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (v i)

private theorem diagonalSmulRight_apply (v : Fin n → ℂ) (τ : Fin n → ℝ) (i : Fin n) :
    diagonalSmulRight v τ i = τ i • v i :=
  rfl

private theorem coe_diagonalSmulRight (v : Fin n → ℂ) :
    (diagonalSmulRight v : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℂ) =
      LinearMap.pi fun i => (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ).smulRight (v i) :=
  LinearMap.ext fun _ => rfl

/-- Near a tuple `p` of pairwise distinct points, every chart of the symmetric power is a function
of the product coordinates `(φᵢ(wᵢ))ᵢ`, where `φᵢ` is the chart of `α` at `p i`, and this function
is complex analytic at `p`, with injective derivative. -/
private theorem exists_injective_hasFDerivAt_symChartAt_ofFn {p : Fin n → α}
    (hinj : Function.Injective p) (s : Sym α n)
    (hs : Sym.ofFn p ∈ (symChartAt (K := ℂ) s).source) :
    ∃ (T : (Fin n → ℂ) → Fin n → ℂ) (T' : (Fin n → ℂ) →L[ℂ] Fin n → ℂ),
      AnalyticAt ℂ T (fun j => chartAt ℂ (p j) (p j)) ∧
      Function.Injective T' ∧ HasFDerivAt T T' (fun j => chartAt ℂ (p j) (p j)) ∧
      ∀ᶠ w in 𝓝 p, symChartAt (K := ℂ) s (Sym.ofFn w) = T fun j => chartAt ℂ (p j) (w j) := by
  -- disjoint coordinate patches around the distinct points `p i`
  obtain ⟨V, hVo, hVsub, hpV, hVdisj⟩ :=
    exists_pairwise_disjoint_isOpen_subset_chartAt_source (H := ℂ) hinj
  have hm : ∑ _i : Fin n, 1 = n := by simp
  set e : (Σ _i : Fin n, Fin 1) ≃ Fin n := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  have hq : Nonempty (∀ i, Sym ↥(V i) 1) := ⟨fun i => Sym.ofFn fun _ => ⟨p i, hpV i⟩⟩
  -- the chart `C` with one block per point reads a nearby tuple as its negated coordinates
  set C := symOpenPartialHomeomorph (fun i => chartAt ℂ (p i)) V (fun _ => 1) hm hVo hVsub
    hVdisj e hq
  have hC_apply : ∀ᶠ w in 𝓝 p, Sym.ofFn w ∈ C.source ∧
      C (Sym.ofFn w) = -fun j => chartAt ℂ (p j) (w j) :=
    eventually_mem_source_symOpenPartialHomeomorph_ofFn (K := ℂ) hVo hpV hVsub hVdisj hm hq
  obtain ⟨hpC, hCp⟩ := hC_apply.self_of_nhds
  -- the given chart `D` is also elementary-symmetric, so both transitions are analytic
  obtain ⟨W, r, hr, hWo, hWsub, hWdisj, e', hr', hs'⟩ := symChartAt_spec (K := ℂ) s
  set D := symChartAt (K := ℂ) s
  have hpD : Sym.ofFn p ∈ D.source := hs
  rw [hs'] at hpD
  have hT : AnalyticAt ℂ (fun c => D (C.symm c)) (C (Sym.ofFn p)) := by
    rw [hs']
    exact analyticAt_symOpenPartialHomeomorph_transition _ _ V _ hm W r hr hVo hVsub hVdisj
      hWo hWsub hWdisj e e' hq hr' hpC hpD fun i j z hz _ =>
        analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _)
          (IsManifold.chart_mem_maximalAtlas _) (hVsub i hz.1) (hWsub j hz.2)
  have hS : AnalyticAt ℂ (fun c => C (D.symm c)) (D (Sym.ofFn p)) := by
    rw [hs']
    exact analyticAt_symOpenPartialHomeomorph_transition _ _ W _ hr V _ hm hWo hWsub hWdisj
      hVo hVsub hVdisj e' e hr' hq hpD hpC fun i j z hz _ =>
        analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _)
          (IsManifold.chart_mem_maximalAtlas _) (hWsub i hz.1) (hVsub j hz.2)
  rw [← hs'] at hpD
  set T₀ := fun c => D (C.symm c) with hT₀
  have hT₀' : HasFDerivAt T₀ (fderiv ℂ T₀ (C (Sym.ofFn p))) (C (Sym.ofFn p)) :=
    hT.differentiableAt.hasFDerivAt
  -- the inverse transition is a local left inverse, so the derivative of `T₀` is injective
  have hinjT₀ : Function.Injective (fderiv ℂ T₀ (C (Sym.ofFn p))) := by
    have hST : (fun c => C (D.symm c)) ∘ T₀ =ᶠ[𝓝 (C (Sym.ofFn p))] id := by
      have h₁ : C.target ∈ 𝓝 (C (Sym.ofFn p)) := C.open_target.mem_nhds (C.map_source hpC)
      have h₂ : C.symm ⁻¹' D.source ∈ 𝓝 (C (Sym.ofFn p)) :=
        (C.continuousAt_symm (C.map_source hpC)).preimage_mem_nhds
          (D.open_source.mem_nhds (by rwa [C.left_inv hpC]))
      filter_upwards [h₁, h₂] with c hc₁ hc₂
      simp only [Function.comp_apply, hT₀, D.left_inv hc₂, C.right_inv hc₁, id]
    refine hT₀'.injective_of_eventuallyEq_id
      (g' := fderiv ℂ (fun c => C (D.symm c)) (T₀ (C (Sym.ofFn p)))) ?_ hST
    simpa only [hT₀, C.left_inv hpC] using hS.differentiableAt.hasFDerivAt
  -- compose with the negation, which turns the coordinates of `C` into the product coordinates
  refine ⟨fun c => T₀ (-c), (fderiv ℂ T₀ (C (Sym.ofFn p))).comp (-ContinuousLinearMap.id ℂ _),
    ?_, hinjT₀.comp neg_injective, ?_, ?_⟩
  · refine AnalyticAt.comp (g := T₀) ?_ analyticAt_id.neg
    simpa [hCp] using hT
  · refine HasFDerivAt.comp (g := T₀) _ ?_ (hasFDerivAt_id _).neg
    simpa [hCp] using hT₀'
  · filter_upwards [hC_apply] with w ⟨hw, hCw⟩
    simp only [hT₀, ← hCw, C.left_inv hw]

/-- The core computation: in every chart of the symmetric power at a tuple `p` of distinct points,
every product of real curves through `p` is differentiable, and its derivative is one fixed
complex-linear injection, depending only on `p` and the chart, applied to the diagonal map of the
velocity vectors. -/
private theorem exists_forall_hasFDerivAt_symChartAt_ofFn {p : Fin n → α}
    (hinj : Function.Injective p) (s : Sym α n)
    (hs : Sym.ofFn p ∈ (symChartAt (K := ℂ) s).source) :
    ∃ T' : (Fin n → ℂ) →L[ℂ] Fin n → ℂ, Function.Injective T' ∧
      ∀ {γ : Fin n → ℝ → α} {t₀ : Fin n → ℝ} {v : Fin n → ℂ}, (∀ i, γ i (t₀ i) = p i) →
        (∀ i, ContinuousAt (γ i) (t₀ i)) →
        (∀ i, HasDerivAt (fun t => chartAt ℂ (p i) (γ i t)) (v i) (t₀ i)) →
        HasFDerivAt (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i)))
          ((T'.restrictScalars ℝ).comp (diagonalSmulRight v)) t₀ := by
  obtain ⟨T, T', -, hT'inj, hT', hT⟩ := exists_injective_hasFDerivAt_symChartAt_ofFn hinj s hs
  refine ⟨T', hT'inj, fun {γ t₀ v} hp hγ hv => ?_⟩
  obtain rfl : p = fun i => γ i (t₀ i) := funext fun i => (hp i).symm
  -- the product coordinates of the curves, with the diagonal derivative of the velocities
  have hG : HasFDerivAt (fun t : Fin n → ℝ => fun j => chartAt ℂ (γ j (t₀ j)) (γ j (t j)))
      (diagonalSmulRight v) t₀ := by
    refine hasFDerivAt_pi.2 fun i => ?_
    refine (HasFDerivAt.comp (f := fun t : Fin n → ℝ => t i) t₀ (hv i).hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt)).congr_fderiv
      ?_
    ext τ
    simp
  refine ((hT'.restrictScalars ℝ).comp t₀ hG).congr_of_eventuallyEq ?_
  exact Tendsto.eventually (continuousAt_pi.2 fun i =>
    ContinuousAt.comp (f := fun t : Fin n → ℝ => t i) (hγ i) (continuous_apply i).continuousAt) hT

/-- In every chart of the symmetric power at a tuple of distinct points on immersed curves, the
product of the curves is differentiable, and its derivative is a complex-linear injection applied
to the diagonal map of the velocity vectors. -/
private theorem exists_hasFDerivAt_symChartAt_ofFn {γ : Fin n → ℝ → α} {t₀ : Fin n → ℝ}
    {v : Fin n → ℂ} (hinj : Function.Injective fun i => γ i (t₀ i))
    (hγ : ∀ i, ContinuousAt (γ i) (t₀ i))
    (hv : ∀ i, HasDerivAt (fun t => chartAt ℂ (γ i (t₀ i)) (γ i t)) (v i) (t₀ i)) (s : Sym α n)
    (hs : Sym.ofFn (fun i => γ i (t₀ i)) ∈ (symChartAt (K := ℂ) s).source) :
    ∃ T' : (Fin n → ℂ) →L[ℂ] Fin n → ℂ, Function.Injective T' ∧
      HasFDerivAt (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i)))
        ((T'.restrictScalars ℝ).comp (diagonalSmulRight v)) t₀ :=
  let ⟨T', hT', hD⟩ := exists_forall_hasFDerivAt_symChartAt_ofFn hinj s hs
  ⟨T', hT', hD (fun _ => rfl) hγ hv⟩

/-- A complex-linear injection applied to the diagonal map of nonzero vectors is injective, with
totally real range. -/
private theorem injective_and_isTotallyReal_comp_pi_smulRight
    {T' : (Fin n → ℂ) →L[ℂ] Fin n → ℂ} (hT' : Function.Injective T') {v : Fin n → ℂ}
    (hv0 : ∀ i, v i ≠ 0) :
    Function.Injective ((T'.restrictScalars ℝ).comp (diagonalSmulRight v)) ∧
      IsTotallyReal (AlmostComplexStructure.ofComplexModule (Fin n → ℂ)).toLinearMap
        (LinearMap.range ((T'.restrictScalars ℝ).comp (diagonalSmulRight v) :
          (Fin n → ℝ) →ₗ[ℝ] Fin n → ℂ)) := by
  refine ⟨hT'.comp fun τ τ' h => funext fun i => ?_, ?_⟩
  · exact smul_left_injective ℝ (hv0 i) <| (diagonalSmulRight_apply v τ i).symm.trans
      ((congrFun h i).trans (diagonalSmulRight_apply v τ' i))
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, coe_diagonalSmulRight]
    refine (isTotallyReal_range_pi_smulRight).map hT' ?_
    refine LinearMap.ext fun c => ?_
    simp

variable {γ : Fin n → ℝ → α} {t₀ : Fin n → ℝ} {v : Fin n → ℂ}

/-- The product of real curves in a complex curve, read in a chart of the symmetric power, is
real-differentiable at a parameter where the curves are differentiable and pass through pairwise
distinct points. -/
theorem differentiableAt_symChartAt_ofFn (hinj : Function.Injective fun i => γ i (t₀ i))
    (hγ : ∀ i, ContinuousAt (γ i) (t₀ i))
    (hv : ∀ i, HasDerivAt (fun t => chartAt ℂ (γ i (t₀ i)) (γ i t)) (v i) (t₀ i)) (s : Sym α n)
    (hs : Sym.ofFn (fun i => γ i (t₀ i)) ∈ (symChartAt (K := ℂ) s).source) :
    DifferentiableAt ℝ (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i))) t₀ :=
  let ⟨_, _, hD⟩ := exists_hasFDerivAt_symChartAt_ofFn hinj hγ hv s hs
  hD.differentiableAt

/-- The product of real curves in a complex curve, read in a chart of the symmetric power, is `C^k`
at a parameter where the curves, read in charts of `α`, are `C^k` and pass through pairwise
distinct points: near such a tuple the chart is an analytic function of the coordinates of the
points. -/
theorem contDiffAt_symChartAt_ofFn {k : ℕ∞ω} (hinj : Function.Injective fun i => γ i (t₀ i))
    (hγ : ∀ i, ContinuousAt (γ i) (t₀ i))
    (hk : ∀ i, ContDiffAt ℝ k (fun t => chartAt ℂ (γ i (t₀ i)) (γ i t)) (t₀ i)) (s : Sym α n)
    (hs : Sym.ofFn (fun i => γ i (t₀ i)) ∈ (symChartAt (K := ℂ) s).source) :
    ContDiffAt ℝ k (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i))) t₀ := by
  obtain ⟨T, -, hTa, -, -, hT⟩ := exists_injective_hasFDerivAt_symChartAt_ofFn hinj s hs
  -- the product coordinates of the curves are `C^k`, and the chart is analytic in them
  have hG : ContDiffAt ℝ k (fun t : Fin n → ℝ => fun j => chartAt ℂ (γ j (t₀ j)) (γ j (t j)))
      t₀ :=
    contDiffAt_pi.2 fun j => ContDiffAt.comp (g := fun t => chartAt ℂ (γ j (t₀ j)) (γ j t)) t₀
      (hk j) (contDiffAt_apply ℝ (fun _ : Fin n => ℝ) j t₀)
  refine ((hTa.contDiffAt.restrict_scalars ℝ).comp t₀ hG).congr_of_eventuallyEq ?_
  exact Tendsto.eventually (continuousAt_pi.2 fun i =>
    ContinuousAt.comp (f := fun t : Fin n → ℝ => t i) (hγ i) (continuous_apply i).continuousAt) hT

/-- **The product of immersed curves is an immersion into the symmetric power.** If real curves
`γ i` in a complex curve have nonzero velocity at `t₀ i` and pass there through pairwise distinct
points, then `t ↦ {γ₁(t₁), …, γₙ(tₙ)}`, read in any chart of the symmetric power, has injective
derivative at `t₀`. -/
theorem fderiv_symChartAt_ofFn_injective (hinj : Function.Injective fun i => γ i (t₀ i))
    (hγ : ∀ i, ContinuousAt (γ i) (t₀ i))
    (hv : ∀ i, HasDerivAt (fun t => chartAt ℂ (γ i (t₀ i)) (γ i t)) (v i) (t₀ i))
    (hv0 : ∀ i, v i ≠ 0) (s : Sym α n)
    (hs : Sym.ofFn (fun i => γ i (t₀ i)) ∈ (symChartAt (K := ℂ) s).source) :
    Function.Injective
      (fderiv ℝ (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i))) t₀) := by
  obtain ⟨T', hT', hD⟩ := exists_hasFDerivAt_symChartAt_ofFn hinj hγ hv s hs
  rw [hD.fderiv]
  exact (injective_and_isTotallyReal_comp_pi_smulRight hT' hv0).1

/-- **Products of immersed curves are maximal totally real in the symmetric power.** If real
curves `γ i` in a complex curve have nonzero velocity at `t₀ i` and pass there through pairwise
distinct points, then in every chart of the symmetric power the tangent space of
`t ↦ {γ₁(t₁), …, γₙ(tₙ)}` at `t₀` is a maximal totally real subspace of `Fin n → ℂ`: it is
complementary to its image under multiplication by `i`. Applied to local parametrizations of
pairwise disjoint attaching curves, this supplies the required tangent-space criterion for the
corresponding torus in `Sym^g(Σ)`. -/
theorem isMaximalTotallyReal_range_fderiv_symChartAt_ofFn
    (hinj : Function.Injective fun i => γ i (t₀ i))
    (hγ : ∀ i, ContinuousAt (γ i) (t₀ i))
    (hv : ∀ i, HasDerivAt (fun t => chartAt ℂ (γ i (t₀ i)) (γ i t)) (v i) (t₀ i))
    (hv0 : ∀ i, v i ≠ 0) (s : Sym α n)
    (hs : Sym.ofFn (fun i => γ i (t₀ i)) ∈ (symChartAt (K := ℂ) s).source) :
    IsMaximalTotallyReal (AlmostComplexStructure.ofComplexModule (Fin n → ℂ)).toLinearMap
      (LinearMap.range
        (fderiv ℝ (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i))) t₀ :
          (Fin n → ℝ) →ₗ[ℝ] Fin n → ℂ)) := by
  obtain ⟨T', hT', hD⟩ := exists_hasFDerivAt_symChartAt_ofFn hinj hγ hv s hs
  obtain ⟨hinjD, hreal⟩ := injective_and_isTotallyReal_comp_pi_smulRight hT' hv0
  rw [hD.fderiv]
  refine hreal.isMaximalTotallyReal ?_ ?_
  · exact (AlmostComplexStructure.ofComplexModule (Fin n → ℂ)).injective.comp Subtype.val_injective
  · rw [LinearMap.finrank_range_of_inj hinjD]
    simp [Module.finrank_pi_fintype, mul_comm]

/-! ### Transverse products of curves -/

/-- **Products of transverse curves are transverse in the symmetric power.** Let `γ i` and `δ j`
be real curves in a complex curve, such that the points `γ i (t₀ i)` are pairwise distinct and are
the points `δ j (u₀ j)` up to the permutation `σ`: `δ (σ i) (u₀ (σ i)) = γ i (t₀ i)`. In every
chart of the symmetric power, the tangent spaces at their common unordered tuple of
`t ↦ {γ₁(t₁), …, γₙ(tₙ)}` and of `u ↦ {δ₁(u₁), …, δₙ(uₙ)}` are complementary exactly when, at
every point `γ i (t₀ i)`, the velocities of `γ i` and `δ (σ i)` are linearly independent over `ℝ`.
Applied to local parametrizations of the attaching curves of a Heegaard diagram, this says that
the tori `T_α` and `T_β` meet transversally at a generator exactly when each of its points is a
transverse intersection of an `α`-curve and a `β`-curve. -/
theorem isCompl_range_fderiv_symChartAt_ofFn_iff {γ δ : Fin n → ℝ → α} {t₀ u₀ : Fin n → ℝ}
    {v w : Fin n → ℂ} {σ : Equiv.Perm (Fin n)} (hinj : Function.Injective fun i => γ i (t₀ i))
    (hσ : ∀ i, δ (σ i) (u₀ (σ i)) = γ i (t₀ i))
    (hγ : ∀ i, ContinuousAt (γ i) (t₀ i)) (hδ : ∀ j, ContinuousAt (δ j) (u₀ j))
    (hv : ∀ i, HasDerivAt (fun t => chartAt ℂ (γ i (t₀ i)) (γ i t)) (v i) (t₀ i))
    (hw : ∀ j, HasDerivAt (fun t => chartAt ℂ (δ j (u₀ j)) (δ j t)) (w j) (u₀ j)) (s : Sym α n)
    (hs : Sym.ofFn (fun i => γ i (t₀ i)) ∈ (symChartAt (K := ℂ) s).source) :
    IsCompl
        (LinearMap.range
          (fderiv ℝ (fun t => symChartAt (K := ℂ) s (Sym.ofFn fun i => γ i (t i))) t₀ :
            (Fin n → ℝ) →ₗ[ℝ] Fin n → ℂ))
        (LinearMap.range
          (fderiv ℝ (fun u => symChartAt (K := ℂ) s (Sym.ofFn fun j => δ j (u j))) u₀ :
            (Fin n → ℝ) →ₗ[ℝ] Fin n → ℂ)) ↔
      ∀ i, LinearIndependent ℝ ![v i, w (σ i)] := by
  obtain ⟨T', hT', hD⟩ := exists_forall_hasFDerivAt_symChartAt_ofFn hinj s hs
  -- reindexing by `σ`, the second family passes through the same ordered tuple as the first
  set P : (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
  have hδσ : HasFDerivAt (fun u : Fin n → ℝ => symChartAt (K := ℂ) s (Sym.ofFn fun j => δ j (u j)))
      (((T'.restrictScalars ℝ).comp (diagonalSmulRight (w ∘ σ))).comp P) u₀ := by
    have h := hD (γ := fun i => δ (σ i)) (t₀ := u₀ ∘ σ) (v := w ∘ σ) hσ (fun i => hδ (σ i))
      fun i => by
        have hwi := hw (σ i)
        rw [hσ i] at hwi
        exact hwi
    refine (h.comp u₀ P.hasFDerivAt).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    exact congrArg _ (Sym.ofFn_comp_perm σ fun j => δ j (u j)).symm
  have hP : LinearMap.range (P : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) = ⊤ :=
    LinearMap.range_eq_top.2 fun u => ⟨u ∘ σ.symm, funext fun i => by simp [P]⟩
  -- `T'` is an injective endomorphism of the finite-dimensional space `Fin n → ℂ`, so it is
  -- bijective, and so is its real restriction, which has the same underlying function
  have hsurj : Function.Surjective T' := by
    rw [← ContinuousLinearMap.coe_coe] at hT' ⊢
    exact LinearMap.injective_iff_surjective.1 hT'
  have hbij : Function.Bijective (T'.restrictScalars ℝ : (Fin n → ℂ) →ₗ[ℝ] Fin n → ℂ) := by
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars']
    exact ⟨hT', hsurj⟩
  simp only [(hD (fun _ => rfl) hγ hv).fderiv, hδσ.fderiv, ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.range_comp_of_range_eq_top _ hP, LinearMap.range_comp, LinearMap.range_comp,
    ← Submodule.orderIsoMapComapOfBijective_apply _ hbij,
    ← Submodule.orderIsoMapComapOfBijective_apply _ hbij, ← OrderIso.isCompl_iff,
    coe_diagonalSmulRight, coe_diagonalSmulRight, isCompl_range_pi_smulRight_iff]
  simp only [Function.comp_apply]

end Curves

end TauCeti
