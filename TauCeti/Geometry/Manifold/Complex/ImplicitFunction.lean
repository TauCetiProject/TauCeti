/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ImplicitFunction
public import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# The joint holomorphic implicit function theorem on manifolds

For a holomorphic equation `G (z, v) = w` between complex manifolds, an invertible partial
Jacobian in the unknown `v` gives a jointly holomorphic solution `v = ψ (z, w)` near a specified
solution. Both the parameter and the level may vary. The theorem is stated in arbitrary charts
of the maximal holomorphic atlases, so it applies directly to local defining equations of
holomorphic submanifolds. Its conclusion is intrinsic: it gives a manifold-valued solution and
a local equivalence between the equation and its solved form, including local uniqueness.

`TauCeti.exists_jointImplicitFunction_of_eventually_mdifferentiableAt` transports
`TauCeti.exists_jointImplicitFunction_of_eventually_differentiableAt` through these charts;
the latter uses the native joint analytic implicit-function theorem.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] [NormedAddCommGroup K] [NormedSpace ℂ K]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace K P]

/-- **The joint holomorphic implicit function theorem in charts.** Suppose `G : M × N → P` is
holomorphic near `u`, and the partial derivative in the `N` coordinate of its representative in
holomorphic charts `e`, `d`, `c` is invertible at `u`. There is a solution `ψ : M × P → N`,
holomorphic near `(u.1, G u)`, taking that point to `u.2`. Near `(u, G u)`, the equation
`G (z, v) = w` is equivalent to `ψ (z, w) = v`. In particular solutions sufficiently near `u.2`
are unique. Only the parameter and unknown model spaces need be assumed finite-dimensional;
invertibility of the partial derivative forces the level model to have the same dimension as
the unknown model. No separation or global countability assumptions are needed. -/
theorem exists_jointImplicitFunction_of_eventually_mdifferentiableAt
    {G : M × N → P} {u : M × N}
    {e : OpenPartialHomeomorph M E} {d : OpenPartialHomeomorph N F}
    {c : OpenPartialHomeomorph P K}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ, F) 1 N)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, K) 1 P)
    (hu : u.1 ∈ e.source) (hv : u.2 ∈ d.source) (hw : G u ∈ c.source)
    (hG : ∀ᶠ q in 𝓝 u, MDifferentiableAt (𝓘(ℂ, E).prod 𝓘(ℂ, F)) 𝓘(ℂ, K) G q)
    (hinv : (fderiv ℂ (fun q : E × F ↦ c (G (e.symm q.1, d.symm q.2)))
      (e u.1, d u.2) ∘L .inr ℂ E F).IsInvertible) :
    ∃ ψ : M × P → N,
      (∀ᶠ p in 𝓝 (u.1, G u),
        MDifferentiableAt (𝓘(ℂ, E).prod 𝓘(ℂ, K)) 𝓘(ℂ, F) ψ p) ∧
      ψ (u.1, G u) = u.2 ∧
      (∀ᶠ p in 𝓝 (u.1, G u), G (p.1, ψ p) = p.2) ∧
      ∀ᶠ q in 𝓝 (u, G u), G q.1 = q.2 ↔ ψ (q.1.1, q.2) = q.1.2 := by
  -- Apply the model-space theorem to the equation in the specified holomorphic charts.
  let g : E × F → K := fun q ↦ c (G (e.symm q.1, d.symm q.2))
  let a : E × F := (e u.1, d u.2)
  have hga : g a = c (G u) := by simp [g, a, e.left_inv hu, d.left_inv hv]
  have hgc : ContinuousAt G u := hG.self_of_nhds.continuousAt
  have hg : ∀ᶠ q in 𝓝 a, DifferentiableAt ℂ g q :=
    eventually_differentiableAt_chart_comp_of_eventually_mdifferentiableAt he hd hc hu hv hw hG
  obtain ⟨φ, hφ, hφa, -, hφeq⟩ :=
    exists_jointImplicitFunction_of_eventually_differentiableAt hg hinv
  rw [hga] at hφ hφa hφeq
  -- The model solution stays in the unknown chart, so transport it back holomorphically.
  let ψ : M × P → N := fun p ↦ d.symm (φ (e p.1, c p.2))
  have hψa : ψ (u.1, G u) = u.2 := by
    simp only [ψ, a, hφa, d.left_inv hv]
  have hfront : Tendsto (fun p : M × P ↦ (e p.1, c p.2))
      (𝓝 (u.1, G u)) (𝓝 (a.1, c (G u))) :=
    (e.continuousAt hu).prodMap_nhds (c.continuousAt hw)
  have hφcont : ContinuousAt φ (a.1, c (G u)) := hφ.self_of_nhds.continuousAt
  have hout : Tendsto (fun p : M × P ↦ φ (e p.1, c p.2))
      (𝓝 (u.1, G u)) (𝓝 (d u.2)) := by
    simpa only [hφa, a, Function.comp_def] using hφcont.tendsto.comp hfront
  have htarget : ∀ᶠ p : M × P in 𝓝 (u.1, G u), φ (e p.1, c p.2) ∈ d.target :=
    hout.eventually (d.open_target.mem_nhds (d.map_source hv))
  have hψ : ∀ᶠ p in 𝓝 (u.1, G u),
      MDifferentiableAt (𝓘(ℂ, E).prod 𝓘(ℂ, K)) 𝓘(ℂ, F) ψ p :=
    eventually_mdifferentiableAt_chart_symm_comp_of_eventually_differentiableAt
      he hd hc hu hw (hφ.mono fun _ hp ↦ hp.differentiableAt)
      (by rw [hφa]; exact d.map_source hv)
  -- Transport the solved-form equivalence before specializing it to the solution graph.
  have hcoords : Tendsto (fun q : (M × N) × P ↦ ((e q.1.1, d q.1.2), c q.2))
      (𝓝 (u, G u)) (𝓝 (a, c (G u))) :=
    ((e.continuousAt hu).prodMap_nhds (d.continuousAt hv)).prodMap_nhds (c.continuousAt hw)
  have hpair : Tendsto (fun q : (M × N) × P ↦ (q.1.1, q.2))
      (𝓝 (u, G u)) (𝓝 (u.1, G u)) :=
    (continuous_fst.fst.prodMk continuous_snd).continuousAt
  have hiff : ∀ᶠ q in 𝓝 (u, G u), G q.1 = q.2 ↔ ψ (q.1.1, q.2) = q.1.2 := by
    filter_upwards [hcoords.eventually hφeq, hpair.eventually htarget,
      (continuous_fst.fst.tendsto (u, G u)).eventually (e.open_source.mem_nhds hu),
      (continuous_fst.snd.tendsto (u, G u)).eventually (d.open_source.mem_nhds hv),
      (continuous_snd.tendsto (u, G u)).eventually (c.open_source.mem_nhds hw),
      (hgc.tendsto.comp (continuous_fst.tendsto (u, G u))).eventually
        (c.open_source.mem_nhds hw)] with q hq ht hqe hqd hqc hqGc
    simp only [g, e.left_inv hqe, d.left_inv hqd, Prod.mk.eta] at hq
    constructor
    · intro h
      have hval := hq.1 (congrArg c h)
      simpa only [ψ, d.left_inv hqd] using congrArg d.symm hval
    · intro h
      have hval : φ (e q.1.1, c q.2) = d q.1.2 := by
        simpa only [ψ, d.right_inv ht] using congrArg d h
      exact c.injOn hqGc hqc (hq.2 hval)
  have hψcont : ContinuousAt ψ (u.1, G u) := hψ.self_of_nhds.continuousAt
  have hgraph : Tendsto (fun p : M × P ↦ ((p.1, ψ p), p.2))
      (𝓝 (u.1, G u)) (𝓝 (u, G u)) := by
    simpa only [hψa, Prod.mk.eta] using
      ((continuous_fst.continuousAt.prodMk hψcont).prodMk continuous_snd.continuousAt).tendsto
  exact ⟨ψ, hψ, hψa, by
    filter_upwards [hgraph.eventually hiff] with p hp
    exact hp.2 rfl, hiff⟩

end TauCeti
