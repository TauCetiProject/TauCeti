/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.ExtendFrom
public import TauCeti.Analysis.Holder.C2HolderBoundary.Basic
public import TauCeti.Analysis.Holder.OpenSet.Frontier
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.GraphFlattening.Extension
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Holder.LipschitzDomain
import TauCeti.Analysis.Sobolev.LipschitzDomain.GraphPatch
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Topology.ClusterSet
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.UniformSpace.Complete

/-!
# `C²` functions on a domain with `C^{2,α}` boundary extend to the whole space

Let `Ω` be a set with `C^{2,α}` boundary (`Set.HasC2HolderBoundary Ω α`) in a finite-dimensional
real inner product space `E`. This file proves that a `C²` function on `Ω` whose value and first and
second derivatives have limits at every frontier point is the restriction to `Ω` of a `C²` function
on all of `E`. In particular every element of `C^{2,α}(Ω)` is such a restriction when `Ω` is
bounded and `α > 0`. This is the qualitative form of Gilbarg–Trudinger's extension lemma for
`C^{k,α}` domains.

Its use is to apply estimates proved for functions that are `C²` on a neighbourhood of
`closure Ω`, such as the global Schauder estimate on a bounded domain with `C^{2,α}` boundary in
`TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.BoundedDomain`, to functions that are only
known on `Ω`, such as the elements of `C^{2,α}(Ω)`.

## Main declarations

* `Set.HasC2HolderBoundary.hasFDerivWithinAt_closure`: if `f` has derivative `f'` on `Ω` and both
  are continuous on `closure Ω`, then `f` has derivative `f' x` within `closure Ω` at every point
  `x` of `closure Ω`.
* `Set.HasC2HolderBoundary.exists_contDiff_eqOn_closure`: for `k ≤ 2`, a function that is `Cᵏ` on
  `closure Ω` agrees there with a function that is `Cᵏ` on `E`.
* `Set.HasC2HolderBoundary.exists_contDiff_eqOn_of_tendsto`: a function `C²` on `Ω` whose value and
  first and second derivatives have limits at every frontier point agrees on `Ω` with a function
  that is `C²` on `E`.
* `TauCeti.CkHolderSpaceOn.exists_contDiff_eq`: on a bounded `Ω` and for `α > 0`, every element of
  `C^{2,α}(Ω)` is the restriction of a function that is `C²` on `E`.
* `TauCeti.CkHolderSpaceOn.exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule`: if the element
  vanishes on the frontier of `Ω`, so does the extension, and its second derivative is `α`-Hölder on
  `closure Ω`.

## The argument

Near a frontier point, `Ω` is the region above the graph of a `C^{2,α}` function `γ` over a
hyperplane, and the shear `y ↦ y + γ y ν` flattens it to a half-space.

* **Up to the boundary.** In the half-space, Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv`
  on a convex half-ball turns limits of the derivative into a derivative within the closure
  (`TauCeti.hasFDerivWithinAt_setOf_le_inner_of_hasFDerivAt`). Applied to the continuous extensions
  `extendFrom Ω u` and `extendFrom Ω (fderiv ℝ u)`, this makes `extendFrom Ω u` a `C²` function on
  `closure Ω`.
* **Across the boundary.** In the half-space, Hestenes' higher-order reflection extends a `Cᵏ`
  function from the closed half-space
  (`TauCeti.exists_contDiff_eventually_eq_of_contDiffOn_setOf_le_inner`). On `Ω` the function
  extends itself. A smooth partition of unity glues these local extensions
  (`IsClosed.exists_contMDiffMap_eqOn`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 6.37.
* M. R. Hestenes, *Extension of the range of a differentiable function*, Duke Math. J. 8 (1941),
  183–192.
-/

public section

open Filter Metric Set
open scoped Topology InnerProductSpace NNReal Manifold

namespace Set.HasC2HolderBoundary

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Set E} {α : ℝ≥0}

/-- A frontier point of a set with `C^{2,α}` boundary has a graph patch: a ball about it in
which the closure of `Ω` is the closed region on or above the graph of `γ`, and the point lies on
the graph. -/
private theorem exists_patch (h : Ω.HasC2HolderBoundary α) {z : E} (hz : z ∈ frontier Ω) :
    ∃ (ν : E) (γ : E → ℝ) (r : ℝ), ‖ν‖ = 1 ∧ ContDiff ℝ 2 γ ∧ (∀ x (t : ℝ), γ (x + t • ν) = γ x) ∧
      0 < r ∧ ball z r ∩ Ω = ball z r ∩ {x | γ x < ⟪x, ν⟫_ℝ} ∧
      ball z r ∩ closure Ω = ball z r ∩ {x | γ x ≤ ⟪x, ν⟫_ℝ} ∧ ⟪z, ν⟫_ℝ = γ z := by
  obtain ⟨ν, γ, -, r, hν, hγ, hγν, -, -, -, hr, hpatch⟩ := hasC2HolderBoundary_iff.1 h z hz
  have hν0 : ν ≠ 0 := ne_zero_of_norm_ne_zero (hν.trans_ne one_ne_zero)
  have hΩ : ball z r ∩ Ω = ball z r ∩ {x | γ x < ⟪x, ν⟫_ℝ} := by
    rw [inter_comm, hpatch, inter_comm]
  have hfr := Set.ext_iff.1 (TauCeti.inter_frontier_eq_inter_setOf_inner_eq isOpen_ball hν0
    hγ.continuous.continuousOn hγν hΩ) z
  exact ⟨ν, γ, r, hν, hγ, hγν, hr, hΩ, TauCeti.inter_closure_eq_inter_setOf_le_inner isOpen_ball
    hν0 hγ.continuous.continuousOn hγν hΩ, (hfr.1 ⟨mem_ball_self hr, hz⟩).2⟩

/-- **Differentiability up to a `C^{2,α}` boundary.** If `f` has derivative `f' x` at every point
`x` of a set `Ω` with `C^{2,α}` boundary, and `f` and `f'` are continuous on `closure Ω`, then `f`
has derivative `f' x` within `closure Ω` at every point `x` of `closure Ω`. -/
theorem hasFDerivWithinAt_closure (h : Ω.HasC2HolderBoundary α) {f : E → F}
    {f' : E → E →L[ℝ] F} (hf : ContinuousOn f (closure Ω)) (hf' : ContinuousOn f' (closure Ω))
    (hd : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) {x : E} (hx : x ∈ closure Ω) :
    HasFDerivWithinAt f (f' x) (closure Ω) x := by
  rcases (closure_eq_self_union_frontier Ω).subset hx with hxΩ | hxf
  · exact (hd x hxΩ).hasFDerivWithinAt
  obtain ⟨ν, γ, r, hν, hγ, hγν, hr, hΩ, hcl, -⟩ := h.exists_patch hxf
  have hsub : ball x r ∩ {y | γ y ≤ ⟪y, ν⟫_ℝ} ⊆ closure Ω := fun y hy => (hcl.symm.subset hy).2
  have hR := TauCeti.hasFDerivWithinAt_setOf_le_inner_of_hasFDerivAt hν (hγ.of_le (by norm_num))
    hγν isOpen_ball (hf.mono hsub) (hf'.mono hsub)
    (fun y hy hyγ => hd y (hΩ.symm.subset ⟨hy, hyγ⟩).2)
    (mem_ball_self hr) (hcl.subset ⟨mem_ball_self hr, hx⟩).2
  rw [← hasFDerivWithinAt_inter (isOpen_ball.mem_nhds (mem_ball_self hr)), inter_comm, hcl]
  exact hR.mono inter_subset_right

/-- **Extension of `Cᵏ` functions from the closure of a domain with `C^{2,α}` boundary.** In a
finite-dimensional space, every function that is `Cᵏ` on the closure of a set with `C^{2,α}`
boundary, `k ≤ 2`, is the restriction to `closure Ω` of a function that is `Cᵏ` on the whole
space. -/
theorem exists_contDiff_eqOn_closure [FiniteDimensional ℝ E] (h : Ω.HasC2HolderBoundary α)
    {k : ℕ} (hk : k ≤ 2) {u : E → F} (hu : ContDiffOn ℝ k u (closure Ω)) :
    ∃ w : E → F, ContDiff ℝ k w ∧ EqOn w u (closure Ω) := by
  -- Near each point of `closure Ω`, `u` agrees on `closure Ω` with a `Cᵏ` function.
  have hloc : ∀ x ∈ closure Ω, ∃ V ∈ 𝓝 x, ∃ g : E → F,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) k g V ∧ EqOn g u (closure Ω ∩ V) := by
    intro x hx
    rcases (closure_eq_self_union_frontier Ω).subset hx with hxΩ | hxf
    -- On `Ω`, `u` extends itself.
    · exact ⟨Ω, h.isOpen.mem_nhds hxΩ, u, contMDiffOn_iff_contDiffOn.2 (hu.mono subset_closure),
        fun _ _ => rfl⟩
    -- At the frontier, reflect across the graph.
    obtain ⟨ν, γ, r, hν, hγ, hγν, hr, -, hcl, hxγ⟩ := h.exists_patch hxf
    obtain ⟨g, hg, hgu⟩ := TauCeti.exists_contDiff_eventually_eq_of_contDiffOn_setOf_le_inner hν
      (hγ.of_le (by exact_mod_cast hk)) hγν isOpen_ball
      (hu.mono fun y hy => (hcl.symm.subset hy).2) (mem_ball_self hr) hxγ
    refine ⟨_, inter_mem hgu (isOpen_ball.mem_nhds (mem_ball_self hr)), g,
      contMDiffOn_iff_contDiffOn.2 hg.contDiffOn, fun y hy => hy.2.1 ?_⟩
    exact (hcl.subset ⟨hy.2.2, hy.1⟩).2
  -- A smooth partition of unity glues the local extensions.
  obtain ⟨G, hG, -⟩ := isClosed_closure.exists_contMDiffMap_eqOn isOpen_univ (subset_univ _) hloc
  exact ⟨G, contMDiff_iff_contDiff.1 G.contMDiff, hG⟩

/-- The continuous extension `extendFrom Ω u` of a `C²` function on a set with `C^{2,α}` boundary,
whose value and first and second derivatives have limits at every frontier point, is `C²` on
`closure Ω`. -/
private theorem contDiffOn_extendFrom (h : Ω.HasC2HolderBoundary α) {u : E → F}
    (hu : ContDiffOn ℝ 2 u Ω) (h₀ : ∀ x ∈ frontier Ω, ∃ L, Tendsto u (𝓝[Ω] x) (𝓝 L))
    (h₁ : ∀ x ∈ frontier Ω, ∃ L, Tendsto (fderiv ℝ u) (𝓝[Ω] x) (𝓝 L))
    (h₂ : ∀ x ∈ frontier Ω, ∃ L, Tendsto (fderiv ℝ (fderiv ℝ u)) (𝓝[Ω] x) (𝓝 L)) :
    ContDiffOn ℝ 2 (extendFrom Ω u) (closure Ω) := by
  have hΩ := h.isOpen
  have hu₁ : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hu₂ : ContinuousOn (fderiv ℝ (fderiv ℝ u)) Ω :=
    (hu₁.fderiv_of_isOpen hΩ (by norm_num) : ContDiffOn ℝ 0 _ Ω).continuousOn
  have hc₀ := hu.continuousOn.continuousOn_extendFrom_closure h₀
  have hc₁ := hu₁.continuousOn.continuousOn_extendFrom_closure h₁
  have hc₂ := hu₂.continuousOn_extendFrom_closure h₂
  have he₀ (x : E) (hx : x ∈ Ω) : extendFrom Ω u =ᶠ[𝓝 x] u :=
    eventually_of_mem (hΩ.mem_nhds hx) (extendFrom_extends hu.continuousOn)
  have he₁ (x : E) (hx : x ∈ Ω) : extendFrom Ω (fderiv ℝ u) =ᶠ[𝓝 x] fderiv ℝ u :=
    eventually_of_mem (hΩ.mem_nhds hx) (extendFrom_extends hu₁.continuousOn)
  have he₂ (x : E) (hx : x ∈ Ω) :
      extendFrom Ω (fderiv ℝ (fderiv ℝ u)) =ᶠ[𝓝 x] fderiv ℝ (fderiv ℝ u) :=
    eventually_of_mem (hΩ.mem_nhds hx) (extendFrom_extends hu₂)
  -- Inside `Ω` the extensions have the derivatives of `u`.
  have hd₀ (x : E) (hx : x ∈ Ω) : HasFDerivAt (extendFrom Ω u) (extendFrom Ω (fderiv ℝ u) x) x := by
    rw [(he₁ x hx).eq_of_nhds]
    exact ((hu.differentiableOn (by norm_num) x hx).differentiableAt
      (hΩ.mem_nhds hx)).hasFDerivAt.congr_of_eventuallyEq (he₀ x hx)
  have hd₁ (x : E) (hx : x ∈ Ω) :
      HasFDerivAt (extendFrom Ω (fderiv ℝ u)) (extendFrom Ω (fderiv ℝ (fderiv ℝ u)) x) x := by
    rw [(he₂ x hx).eq_of_nhds]
    exact ((hu₁.differentiableOn one_ne_zero x hx).differentiableAt
      (hΩ.mem_nhds hx)).hasFDerivAt.congr_of_eventuallyEq (he₁ x hx)
  -- Up to the boundary, by the graph patches.
  rw [← one_add_one_eq_two, contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
  refine fun x hx => ⟨closure Ω, by rw [insert_eq_of_mem hx]; exact self_mem_nhdsWithin,
    by simp, _, fun y hy => h.hasFDerivWithinAt_closure hc₀ hc₁ hd₀ hy, ?_⟩
  rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
  refine fun x hx => ⟨closure Ω, by rw [insert_eq_of_mem hx]; exact self_mem_nhdsWithin,
    by simp, _, fun y hy => h.hasFDerivWithinAt_closure hc₁ hc₂ hd₁ hy, ?_⟩
  exact contDiffOn_zero.2 hc₂

/-- **Extension of `C²` functions from a domain with `C^{2,α}` boundary.** In a finite-dimensional
space, let `u` be `C²` on a set `Ω` with `C^{2,α}` boundary, and suppose that `u`, its derivative
and its second derivative have limits at every point of the frontier of `Ω`. Then `u` is the
restriction to `Ω` of a function that is `C²` on the whole space. This is the qualitative form of
the extension lemma for `C^{2,α}` domains (Gilbarg–Trudinger, Lemma 6.37). -/
theorem exists_contDiff_eqOn_of_tendsto [FiniteDimensional ℝ E] (h : Ω.HasC2HolderBoundary α)
    {u : E → F} (hu : ContDiffOn ℝ 2 u Ω) (h₀ : ∀ x ∈ frontier Ω, ∃ L, Tendsto u (𝓝[Ω] x) (𝓝 L))
    (h₁ : ∀ x ∈ frontier Ω, ∃ L, Tendsto (fderiv ℝ u) (𝓝[Ω] x) (𝓝 L))
    (h₂ : ∀ x ∈ frontier Ω, ∃ L, Tendsto (fderiv ℝ (fderiv ℝ u)) (𝓝[Ω] x) (𝓝 L)) :
    ∃ w : E → F, ContDiff ℝ 2 w ∧ EqOn w u Ω := by
  obtain ⟨w, hw, hwu⟩ := h.exists_contDiff_eqOn_closure le_rfl (h.contDiffOn_extendFrom hu h₀ h₁ h₂)
  exact ⟨w, hw, fun x hx => (hwu (subset_closure hx)).trans
    (extendFrom_extends hu.continuousOn x hx)⟩

end Set.HasC2HolderBoundary

namespace TauCeti.CkHolderSpaceOn

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Elements of `C^{2,α}(Ω)` extend to the whole space.** Let `Ω` be a bounded open set with
`C^{2,β}` boundary in a finite-dimensional real inner product space and let `0 < α`. Every element
of `C^{2,α}(Ω)` with values in a Banach space is the restriction to `Ω` of a function that is `C²`
on the whole space. -/
theorem exists_contDiff_eq [FiniteDimensional ℝ E] [CompleteSpace F] {α β : ℝ≥0}
    {Ω : TopologicalSpace.Opens E}
    (hΩ : (Ω : Set E).HasC2HolderBoundary β) (hb : Bornology.IsBounded (Ω : Set E)) (hα : 0 < α)
    (f : CkHolderSpaceOn 2 α Ω F) : ∃ w : E → F, ContDiff ℝ 2 w ∧ ∀ x : Ω, w x = f x := by
  have hg : ContDiffOn ℝ 2 f.extend Ω := f.contDiffOn_extend
  -- The value and the first two derivatives are bounded by the norm of `f`.
  have hbd (i : ℕ) (hi : i ≤ 2) (x : E) (hx : x ∈ (Ω : Set E)) :
      ‖_root_.iteratedFDeriv ℝ i f.extend x‖ ≤ ‖f‖₊ := f.norm_iteratedFDeriv_extend_le hi ⟨x, hx⟩
  have hΩo := hΩ.isOpen
  have hg₁ : ContDiffOn ℝ 1 (fderiv ℝ f.extend) Ω := hg.fderiv_of_isOpen hΩo (by norm_num)
  -- The value and the first derivative are uniformly continuous: nearby points of the Lipschitz
  -- domain `Ω` are joined inside it by short chains of segments.
  have huc : UniformContinuousOn f.extend Ω ∧ UniformContinuousOn (fderiv ℝ f.extend) Ω := by
    rcases Nat.eq_zero_or_eq_succ_pred (Module.finrank ℝ E) with hE | hE
    -- In dimension zero, every function is constant.
    · have : Subsingleton E := Module.finrank_zero_iff.1 hE
      exact ⟨(uniformContinuous_of_const fun a b =>
          congrArg f.extend (Subsingleton.elim a b)).uniformContinuousOn,
        (uniformContinuous_of_const fun a b =>
          congrArg (fderiv ℝ f.extend) (Subsingleton.elim a b)).uniformContinuousOn⟩
    have hL := hΩ.hasLipschitzGraphBoundary.isLipschitzDomain hE
    -- The constant quantifies over codomains in one universe, so it is obtained once for `F` and
    -- once for `E →L[ℝ] F`.
    obtain ⟨C₀, hC₀⟩ := hL.exists_holderOnWith_of_norm_fderiv_le hb (α := 1) le_rfl
    obtain ⟨C₁, hC₁⟩ := hL.exists_holderOnWith_of_norm_fderiv_le hb (α := 1) le_rfl
    exact ⟨(hC₀ (g := f.extend) (M := ‖f‖₊) (L := ‖f‖₊)
        (fun x hx => (hg.differentiableOn (by norm_num) x hx).differentiableAt (hΩo.mem_nhds hx))
        (fun x hx => by simpa using hbd 0 (by norm_num) x hx)
        (fun x hx => by simpa using hbd 1 (by norm_num) x hx)).uniformContinuousOn one_pos,
      (hC₁ (g := fderiv ℝ f.extend) (M := ‖f‖₊) (L := ‖f‖₊)
        (fun x hx => (hg₁.differentiableOn one_ne_zero x hx).differentiableAt (hΩo.mem_nhds hx))
        (fun x hx => by simpa using hbd 1 (by norm_num) x hx)
        (fun x hx => by simpa [norm_fderiv_fderiv] using hbd 2 le_rfl x hx)).uniformContinuousOn
        one_pos⟩
  obtain ⟨huc₀, huc₁⟩ := huc
  -- The second derivative is `α`-Hölder.
  have huc₂ : UniformContinuousOn (fderiv ℝ (fderiv ℝ f.extend)) Ω :=
    ((holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two _).2
      f.holderOnWith_iteratedFDeriv_extend).uniformContinuousOn hα
  obtain ⟨w, hw, hwf⟩ := hΩ.exists_contDiff_eqOn_of_tendsto hg
    (fun x hx => huc₀.exists_tendsto_nhdsWithin (frontier_subset_closure hx))
    (fun x hx => huc₁.exists_tendsto_nhdsWithin (frontier_subset_closure hx))
    (fun x hx => huc₂.exists_tendsto_nhdsWithin (frontier_subset_closure hx))
  exact ⟨w, hw, fun x => (hwf x.property).trans (f.extend_apply x)⟩

/-- **Elements of `C^{2,α}(Ω)` vanishing on `∂Ω` extend to the whole space.** Let `Ω` be a bounded
open set with `C^{2,β}` boundary in a finite-dimensional real inner product space and let `0 < α`.
Every element `f` of `C^{2,α}(Ω)` vanishing on the frontier of `Ω` is the restriction to `Ω` of a
function `w` that is `C²` on the whole space, vanishes on the frontier of `Ω`, and whose second
derivative is `α`-Hölder on `closure Ω` with constant the Hölder seminorm of the second derivative
field of `f`. These are the hypotheses of global estimates for the Dirichlet problem stated for
functions `C²` near `closure Ω`. -/
theorem exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule [FiniteDimensional ℝ E]
    [CompleteSpace F] {α β : ℝ≥0} {Ω : TopologicalSpace.Opens E}
    (hΩ : (Ω : Set E).HasC2HolderBoundary β) (hb : Bornology.IsBounded (Ω : Set E)) (hα : 0 < α)
    {f : CkHolderSpaceOn 2 α Ω F} (hf : f ∈ vanishingOnFrontierSubmodule 2 α Ω F) :
    ∃ w : E → F, ContDiff ℝ 2 w ∧ (∀ x : Ω, w x = f x) ∧ (∀ z ∈ frontier (Ω : Set E), w z = 0) ∧
      HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last 2) : Ω → E [×2]→L[ℝ] F)) α
        (_root_.iteratedFDeriv ℝ 2 w) (closure Ω) := by
  obtain ⟨w, hw, hwf⟩ := exists_contDiff_eq hΩ hb hα f
  refine ⟨w, hw, hwf, fun z hz => ?_, ?_⟩
  · -- `w` and the extension by zero of `f` agree on `Ω` and are continuous on `closure Ω`.
    have hEq : Set.EqOn w f.extend (closure Ω) :=
      Set.EqOn.of_subset_closure (fun y hy => by rw [hwf ⟨y, hy⟩, f.extend_apply_of_mem hy])
        hw.continuous.continuousOn (continuousOn_extend_closure hf) subset_closure le_rfl
    exact (hEq (frontier_subset_closure hz)).trans (f.extend_apply_of_mem_frontier hz)
  · exact (f.holderOnWith_iteratedFDeriv hwf).of_subset_closure le_rfl fun z _ =>
      (hw.continuous_iteratedFDeriv le_rfl).continuousWithinAt

end TauCeti.CkHolderSpaceOn
