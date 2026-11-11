/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Graph

import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Distributions transverse to the vertical subspace

Let `D` be a `C^n` distribution on `E × F` whose rank is `finrank 𝕜 E`, and suppose that at a point
`p₀` the subspace `D p₀` contains no nonzero vertical vector, that is, meets the kernel `0 × F` of
the first projection only in `0`. Then near `p₀` the distribution is the graph distribution
`TauCeti.graphDistribution f` of a `C^n` family `f : E × F → (E →L[𝕜] F)`
(`TauCeti.IsContMDiffDistribution.exists_eventually_eq_graphDistribution`). This is the local
normal form in which the Frobenius theorem is proved: in the graph form, involutivity of `D` is
the Frobenius integrability condition on `f`, and the graphs of solutions of the total
differential equation `D u x = f (x, u x)` are integral manifolds.

The family `f` is written down from a local frame `X₁, …, Xₖ` of `D` near `p₀`. Let `Φ p` be the
linear map `c ↦ ∑ᵢ cᵢ • Xᵢ p` from `𝕜ᵏ` to `E × F`, which is injective with range `D p`. Its first
component `A p` is injective at `p₀`, since `D p₀` has no vertical vector, hence invertible because
`k = finrank 𝕜 E`; invertibility persists near `p₀`, and there `D p` is the graph of
`f p = (snd ∘ Φ p) ∘ (A p)⁻¹`. Smoothness of `f` is smoothness of inversion of continuous linear
equivalences (`contDiffAt_map_inverse`).

Combined with the Frobenius theorem in coordinates
(`TauCeti.exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt`), this gives the Frobenius
theorem for a distribution transverse to the vertical subspace at one point
(`TauCeti.IsInvolutiveDistribution.exists_eventually_eq_graph_fderiv`): over finite-dimensional
real spaces, a `C^(n+1)` involutive distribution of rank `finrank ℝ E` with `D (x₀, y₀)`
transverse to `0 × F` has an integral manifold through `(x₀, y₀)`, the graph of a function
`u : E → F` whose graph has tangent space `D (x, u x)` at every point `(x, u x)` near `(x₀, y₀)`.

## Main results

* `TauCeti.IsContMDiffDistribution.exists_eventually_eq_graphDistribution`: a `C^n` distribution
  of rank `finrank 𝕜 E` on `E × F`, transverse to `0 × F` at `p₀`, is the graph distribution of a
  family `f` near `p₀`, and `f` is `C^n` near `p₀`.
* `TauCeti.IsInvolutiveDistribution.exists_eventually_eq_graph_fderiv`: **the Frobenius theorem
  for transverse distributions.** A `C^(n+1)` involutive distribution of rank `finrank ℝ E` on
  `E × F`, transverse to `0 × F` at `(x₀, y₀)`, is tangent to the graph of a function `u` with
  `u x₀ = y₀`, `C^(n+1)` at `x₀`: `D (x, u x)` is the graph of `fderiv ℝ u x` for `x` near `x₀`.
* `TauCeti.IsDistributionFrameOn.exists_openPartialHomeomorph_map_fderiv_eq_ker_snd`: **the local
  Frobenius theorem in product coordinates.** A `C^(n+1)` change of coordinates carries `D` onto the
  horizontal subspace at each point of its domain.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19,
  proof of Theorem 19.12.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter VI, §1.
-/

public section

open Set Filter Function Module
open scoped Topology Manifold ContDiff

namespace TauCeti

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F : Type*} [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A transverse distribution with a local frame is locally a graph distribution.** Let `D` be
a family of subspaces of `E × F` with a `C^n` local frame of `finrank 𝕜 E` vector fields on an open
neighbourhood `U` of `p₀`, such that `D p₀` meets the vertical subspace `0 × F`, the kernel of the
first projection, only in `0`. Then near `p₀` the distribution is the graph distribution of a
family `f : E × F → (E →L[𝕜] F)` that is `C^n` near `p₀`. -/
theorem IsDistributionFrameOn.exists_eventually_eq_graphDistribution {n : ℕ∞ω}
    {D : E × F → Submodule 𝕜 (E × F)} {U : Set (E × F)} (hU : IsOpen U)
    {X : Fin (finrank 𝕜 E) → Π p : E × F, TangentSpace 𝓘(𝕜, E × F) p}
    (hX : IsDistributionFrameOn 𝓘(𝕜, E × F) n D X U) {p₀ : E × F} (hp₀U : p₀ ∈ U)
    (hp₀ : Disjoint (D p₀) (LinearMap.ker (LinearMap.fst 𝕜 E F))) :
    ∃ f : E × F → E →L[𝕜] F,
      ∀ᶠ p in 𝓝 p₀, ContDiffAt 𝕜 n f p ∧ D p = graphDistribution f p := by
  obtain ⟨Φ, hΦ, hΦU⟩ := hX.exists_contDiffOn_clm
  -- `A p` is the first component of `Φ p`, the projection of the frame to `E`.
  set A : E × F → (Fin (finrank 𝕜 E) → 𝕜) →L[𝕜] E :=
    fun p ↦ (ContinuousLinearMap.fst 𝕜 E F).comp (Φ p)
  have hA (p : E × F) (hp : p ∈ U) : ContDiffAt 𝕜 n A p :=
    contDiffAt_const.clm_comp (hΦ.contDiffAt (hU.mem_nhds hp))
  -- At `p₀`, `A p₀` is injective because `D p₀` has no vertical vector, hence invertible.
  have hA₀ : A p₀ ∈ range ((↑) : ((Fin (finrank 𝕜 E) → 𝕜) ≃L[𝕜] E) → _) := by
    have hinj : Injective (A p₀) := by
      refine (injective_iff_map_eq_zero (A p₀)).2 fun c hc ↦ (hΦU p₀ hp₀U).1 ?_
      have hmem : Φ p₀ c ∈ D p₀ := (hΦU p₀ hp₀U).2 ▸ LinearMap.mem_range_self _ c
      rw [map_zero]
      exact (Submodule.disjoint_def.1 hp₀) _ hmem hc
    have hsurj : Surjective (A p₀ : (Fin (finrank 𝕜 E) → 𝕜) →ₗ[𝕜] E) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
    exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩
  -- Invertibility of `A p` persists near `p₀`.
  have hnhds : ∀ᶠ p in 𝓝 p₀,
      p ∈ U ∧ A p ∈ range ((↑) : ((Fin (finrank 𝕜 E) → 𝕜) ≃L[𝕜] E) → _) :=
    (hU.eventually_mem hp₀U).and <| ((hA p₀ hp₀U).continuousAt).preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds hA₀)
  refine ⟨fun p ↦ ((ContinuousLinearMap.snd 𝕜 E F).comp (Φ p)).comp (A p).inverse,
    hnhds.mono fun p ⟨hpU, e, he⟩ ↦ ⟨?_, ?_⟩⟩
  · exact (contDiffAt_const.clm_comp (hΦ.contDiffAt (hU.mem_nhds hpU))).clm_comp
      ((he ▸ contDiffAt_map_inverse e).comp p (hA p hpU))
  · -- `Φ p` is `id.prod (f p)` precomposed with the invertible `A p`, so both have range `D p`.
    have hinv (c : Fin (finrank 𝕜 E) → 𝕜) : (A p).inverse (A p c) = c := by
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact e.symm_apply_apply c
    have hcomp : (Φ p : (Fin (finrank 𝕜 E) → 𝕜) →ₗ[𝕜] E × F) =
        (LinearMap.id.prod ((((ContinuousLinearMap.snd 𝕜 E F).comp (Φ p)).comp
          (A p).inverse : E →L[𝕜] F) : E →ₗ[𝕜] F)) ∘ₗ (e : (Fin (finrank 𝕜 E) → 𝕜) →ₗ[𝕜] E) := by
      have hec (c : Fin (finrank 𝕜 E) → 𝕜) : e c = A p c := by
        rw [← he, ContinuousLinearEquiv.coe_coe]
      refine LinearMap.ext fun c ↦ Prod.ext ?_ ?_
      · simp [hec, A]
      · simpa [hec] using (congrArg (fun c ↦ (Φ p c).2) (hinv c)).symm
    rw [graphDistribution_def, LinearMap.graph_eq_range_prod, ← (hΦU p hpU).2, hcomp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 e.surjective)]

/-- **A transverse distribution is locally a graph distribution.** Let `D` be a `C^n` distribution
on `E × F` of rank `finrank 𝕜 E` such that `D p₀` meets the vertical subspace `0 × F`, the kernel
of the first projection, only in `0`. Then near `p₀` the distribution is the graph distribution of
a family `f : E × F → (E →L[𝕜] F)` that is `C^n` near `p₀`. -/
theorem IsContMDiffDistribution.exists_eventually_eq_graphDistribution {n : ℕ∞ω}
    {D : E × F → Submodule 𝕜 (E × F)}
    (hD : IsContMDiffDistribution 𝓘(𝕜, E × F) n (finrank 𝕜 E) D) {p₀ : E × F}
    (hp₀ : Disjoint (D p₀) (LinearMap.ker (LinearMap.fst 𝕜 E F))) :
    ∃ f : E × F → E →L[𝕜] F,
      ∀ᶠ p in 𝓝 p₀, ContDiffAt 𝕜 n f p ∧ D p = graphDistribution f p := by
  obtain ⟨U, hU, hp₀U, X, hX⟩ := isContMDiffDistribution_iff.1 hD p₀
  exact hX.exists_eventually_eq_graphDistribution hU hp₀U hp₀

end Field

section Real

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The Frobenius theorem for transverse distributions.** Let `D` be an involutive `C^(n+1)`
distribution of rank `finrank ℝ E` on `E × F` such that `D (x₀, y₀)` meets the vertical subspace
`0 × F` only in `0`. Then `D` has an integral manifold through `(x₀, y₀)`: the graph of a function
`u`, of class `C^(n+1)` at `x₀`, with `u x₀ = y₀`, whose tangent space at `(x, u x)`, the graph of
`fderiv ℝ u x`, is `D (x, u x)` for every `x` near `x₀`. -/
theorem IsInvolutiveDistribution.exists_eventually_eq_graph_fderiv {n : ℕ∞}
    {D : E × F → Submodule ℝ (E × F)} (hinv : IsInvolutiveDistribution 𝓘(ℝ, E × F) D)
    (hD : IsContMDiffDistribution 𝓘(ℝ, E × F) (n + 1) (finrank ℝ E) D) {x₀ : E} {y₀ : F}
    (h₀ : Disjoint (D (x₀, y₀)) (LinearMap.ker (LinearMap.fst ℝ E F))) :
    ∃ u : E → F, u x₀ = y₀ ∧ ContDiffAt ℝ (n + 1) u x₀ ∧
      ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ u x ∧
        D (x, u x) = (fderiv ℝ u x : E →ₗ[ℝ] F).graph := by
  obtain ⟨f, hf⟩ := hD.exists_eventually_eq_graphDistribution h₀
  have hfs : ContDiffOn ℝ (n + 1) f {p | ContDiffAt ℝ (n + 1) f p} :=
    fun p (hp : ContDiffAt ℝ (n + 1) f p) ↦ hp.contDiffWithinAt
  obtain ⟨u, hu₀, hu, hderiv⟩ := exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt hfs
    (hf.mono fun _ hp ↦ hp.1) <| by
      filter_upwards [eventually_eventually_nhds.2 hf] with p hp
      exact hinv.isFrobeniusIntegrableAt (hp.mono fun _ hq ↦ hq.2)
        (hp.mono fun _ hq ↦ hq.1.differentiableAt (by simp))
  refine ⟨u, hu₀, hu, ?_⟩
  -- The graph map `x ↦ (x, u x)` tends to `(x₀, y₀)`, where `D` is the graph distribution of `f`.
  have hgraph : Tendsto (fun x ↦ (x, u x)) (𝓝 x₀) (𝓝 (x₀, y₀)) := by
    simpa [hu₀] using (continuousAt_id.prodMk hu.continuousAt).tendsto
  filter_upwards [hderiv, hgraph.eventually hf] with x hx hxD
  rw [hxD.2, graphDistribution_def, hx.fderiv]
  exact ⟨hx.differentiableAt, rfl⟩

/-- Coordinates carrying the horizontal subspace onto a transverse involutive distribution: the
change of coordinates `e` is the graph map of the smooth family of Frobenius solutions, restricted
to the points that it sends where the distribution is a graph distribution. -/
private theorem IsDistributionFrameOn.exists_map_fderiv_ker_snd_eq {n : ℕ∞}
    {D : E × F → Submodule ℝ (E × F)} {U : Set (E × F)} (hU : IsOpen U)
    {X : Fin (finrank ℝ E) → Π p : E × F, TangentSpace 𝓘(ℝ, E × F) p}
    (hX : IsDistributionFrameOn 𝓘(ℝ, E × F) (n + 1) D X U)
    (hinv : IsInvolutiveDistributionOn 𝓘(ℝ, E × F) D U) {p₀ : E × F} (hp₀U : p₀ ∈ U)
    (hp₀ : Disjoint (D p₀) (LinearMap.ker (LinearMap.fst ℝ E F))) :
    ∃ e : OpenPartialHomeomorph (E × F) (E × F), p₀ ∈ e.source ∧ e p₀ = p₀ ∧
      ContDiffOn ℝ (n + 1) e e.source ∧ ContDiffOn ℝ (n + 1) e.symm e.target ∧
      ∀ p ∈ e.source, (LinearMap.ker (LinearMap.snd ℝ E F)).map
        (fderiv ℝ e p : E × F →ₗ[ℝ] E × F) = D (e p) := by
  obtain ⟨f, hf⟩ := hX.exists_eventually_eq_graphDistribution hU hp₀U hp₀
  have hfs : ContDiffOn ℝ (n + 1) f {p | ContDiffAt ℝ (n + 1) f p} :=
    fun p (hp : ContDiffAt ℝ (n + 1) f p) ↦ hp.contDiffWithinAt
  obtain ⟨u, e₀, hu₀, -, he₀fun, he₀src, he₀, he₀symm, he₀slice⟩ :=
    exists_frobenius_flat_coordinate (x₀ := p₀.1) (y₀ := p₀.2) hfs
      (hf.mono fun _ hp ↦ hp.1) <| by
        filter_upwards [eventually_eventually_nhds.2 hf, hU.mem_nhds hp₀U] with p hp hpU
        exact hinv.isFrobeniusIntegrableAt (hU.mem_nhds hpU) (hp.mono fun _ hq ↦ hq.2)
          (hp.mono fun _ hq ↦ hq.1.differentiableAt (by simp))
  have he₀p₀ : e₀ p₀ = p₀ := by
    rw [he₀fun]
    exact Prod.ext rfl hu₀
  obtain ⟨V, hVf, hV, hp₀V⟩ := eventually_nhds_iff.1 hf
  let e := e₀.restrOpen (e₀.source ∩ e₀ ⁻¹' V) (e₀.isOpen_inter_preimage hV)
  have hecoe : (e : E × F → E × F) = e₀ := e₀.coe_restrOpen _
  have hesource : e.source ⊆ e₀.source ∩ e₀ ⁻¹' V := fun p hp ↦ by
    rw [e₀.restrOpen_source] at hp
    exact hp.2
  have hetarget : e.target ⊆ e₀.target := fun p hp ↦ by
    have h := e₀.map_source (hesource (e.map_target hp)).1
    rwa [← hecoe, e.right_inv hp] at h
  refine ⟨e, ?_, he₀p₀, he₀.mono fun p hp ↦ (hesource hp).1,
    he₀symm.mono hetarget, fun p hp ↦ ?_⟩
  · rw [e₀.restrOpen_source]
    exact ⟨he₀src, he₀src, by rwa [mem_preimage, he₀p₀]⟩
  have hp' := hesource hp
  have hd : DifferentiableAt ℝ e₀ p :=
    (he₀.contDiffAt (e₀.open_source.mem_nhds hp'.1)).differentiableAt (by simp)
  -- The derivative of `e₀` on the horizontal subspace is the derivative of the horizontal slice.
  have hslice : (fderiv ℝ e₀ p).comp (ContinuousLinearMap.inl ℝ E F) =
      (ContinuousLinearMap.id ℝ E).prod (f (e₀ p)) := by
    have hinl : HasFDerivAt (fun x ↦ ((x, p.2) : E × F)) (ContinuousLinearMap.inl ℝ E F) p.1 :=
      hasFDerivAt_prodMk_left p.1 p.2
    exact ((hd.hasFDerivAt (x := p)).comp p.1 hinl).unique (he₀slice p hp'.1)
  rw [hecoe, (hVf _ hp'.2).2, graphDistribution_def, LinearMap.graph_eq_range_prod,
    ← LinearMap.range_inl, ← LinearMap.range_comp]
  exact congrArg LinearMap.range (LinearMap.ext fun v ↦ DFunLike.congr_fun hslice v)

/-- **The local Frobenius theorem in product coordinates.** Let `D` be a family of subspaces of
`E × F` with a `C^(n+1)` local frame of `finrank ℝ E` vector fields on an open neighbourhood `U` of
`p₀`, involutive on `U`, such that `D p₀` meets the vertical subspace `0 × F` only in `0`. Then some
`C^(n+1)` change of coordinates `φ`, with `C^(n+1)` inverse and fixing `p₀`, carries `D` onto the
horizontal subspace `E × 0`, the kernel of the second projection, at each point of its domain. So
`φ` is a flat chart of `D`, and the preimages under `φ` of the horizontal slices are integral
manifolds of `D`. -/
theorem IsDistributionFrameOn.exists_openPartialHomeomorph_map_fderiv_eq_ker_snd {n : ℕ∞}
    {D : E × F → Submodule ℝ (E × F)} {U : Set (E × F)} (hU : IsOpen U)
    {X : Fin (finrank ℝ E) → Π p : E × F, TangentSpace 𝓘(ℝ, E × F) p}
    (hX : IsDistributionFrameOn 𝓘(ℝ, E × F) (n + 1) D X U)
    (hinv : IsInvolutiveDistributionOn 𝓘(ℝ, E × F) D U) {p₀ : E × F} (hp₀U : p₀ ∈ U)
    (hp₀ : Disjoint (D p₀) (LinearMap.ker (LinearMap.fst ℝ E F))) :
    ∃ φ : OpenPartialHomeomorph (E × F) (E × F), p₀ ∈ φ.source ∧ φ p₀ = p₀ ∧
      ContDiffOn ℝ (n + 1) φ φ.source ∧ ContDiffOn ℝ (n + 1) φ.symm φ.target ∧
      ∀ p ∈ φ.source, (D p).map (fderiv ℝ φ p : E × F →ₗ[ℝ] E × F) =
        LinearMap.ker (LinearMap.snd ℝ E F) := by
  obtain ⟨e, hsrc, hfix, he, he', hmap⟩ :=
    hX.exists_map_fderiv_ker_snd_eq hU hinv hp₀U hp₀
  refine ⟨e.symm, hfix ▸ e.map_source hsrc, ?_, he', he, fun p hp ↦ ?_⟩
  · conv_lhs => rw [← hfix]
    exact e.left_inv hsrc
  have hq : e.symm p ∈ e.source := e.map_target hp
  have heq : e (e.symm p) = p := e.right_inv hp
  have hd : DifferentiableAt ℝ e (e.symm p) :=
    (he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt (by simp)
  have hds : DifferentiableAt ℝ e.symm p :=
    (he'.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hL := e.fderiv_symm_comp_fderiv hp hd hds
  have hmp := hmap _ hq
  rw [heq] at hmp
  rw [← hmp, ← Submodule.map_comp]
  convert Submodule.map_id _
  exact congrArg ContinuousLinearMap.toLinearMap hL

end Real

end TauCeti
