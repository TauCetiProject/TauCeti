/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Frobenius
public import TauCeti.Geometry.Manifold.Distribution
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Graph distributions and the Frobenius theorem in coordinates

A family `f : E × F → (E →L[𝕜] F)` of linear maps defines a distribution on `E × F`, its *graph
distribution* `TauCeti.graphDistribution f`: at `p` it is the graph `{(v, f p v) | v : E}` of
`f p`. A smooth distribution on `E × F` whose subspace at a point `p₀` is a complement of `0 × F`
is, near `p₀`, the graph distribution of a smooth family `f`, so graph distributions are the local
normal form in which the Frobenius theorem is proved; that reduction is not carried out here.

This file identifies involutivity of a graph distribution with the Frobenius integrability
condition `TauCeti.IsFrobeniusIntegrableAt` of the total differential equation `D u x = f (x, u x)`,
whose solutions are the functions `u : E → F` with graphs tangent to the distribution. The
computation behind it is `TauCeti.snd_lieBracket_eq_of_eventually_mem_graphDistribution`: if `V`
and `W` are vector fields tangent to the graph distribution near `p`, their Lie bracket `[V, W]` at
`p` fails to lie in the graph of `f p` exactly by

`fderiv 𝕜 f p (V p) (W p).1 - fderiv 𝕜 f p (W p) (V p).1`,

which vanishes when the integrability condition holds at `p`. Conversely, the vector fields
`q ↦ (v, f q v)` are tangent to the distribution, and their brackets recover the integrability
condition. Combined with the local Frobenius theorem for total differential equations
(`TauCeti.exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt`), this proves the Frobenius
theorem for graph distributions: over finite-dimensional real spaces, a `C¹` graph distribution is
involutive exactly when through every point there passes the graph of a local solution, an integral
manifold of the distribution.

## Main definitions

* `TauCeti.graphDistribution f`: the distribution `p ↦ {(v, f p v) | v : E}` on `E × F`.

## Main results

* `TauCeti.isContMDiffDistribution_graphDistribution`: for a `C^n` family `f` with
  finite-dimensional source, the graph distribution is a `C^n` distribution of rank `dim E`.
* `TauCeti.lieBracket_mem_graphDistribution_iff`: the Lie bracket at `p` of two vector fields
  tangent to the graph distribution near `p` is tangent to it exactly when
  `fderiv 𝕜 f p (V p) (W p).1 = fderiv 𝕜 f p (W p) (V p).1`.
* `TauCeti.isInvolutiveDistribution_graphDistribution_iff`: for differentiable `f`, the graph
  distribution is involutive exactly when the Frobenius integrability condition holds everywhere.
* `TauCeti.IsInvolutiveDistribution.exists_eventually_hasFDerivAt`: **the Frobenius theorem in
  coordinates.** Over finite-dimensional real spaces, an involutive graph distribution of a map
  `f` of class `C^(n+1)` near `(x₀, y₀)` has an integral manifold through `(x₀, y₀)`: the graph of
  a local solution `u` with `u x₀ = y₀`.
* `TauCeti.isInvolutiveDistribution_graphDistribution_iff_forall_exists`: for `C¹` maps `f`
  between finite-dimensional real spaces, the graph distribution is involutive exactly when the
  graph of a local solution passes through every point.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter VI, §1.
* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press (1960), Section 10.9.
-/

public section

open Filter Set VectorField
open scoped Topology Manifold ContDiff

namespace TauCeti

section Field

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The graph distribution of a family `f` of linear maps `E →L[𝕜] F` indexed by `E × F`: at `p`
it is the graph `{(v, f p v) | v : E}` of `f p`, a subspace of `E × F`. -/
def graphDistribution (f : E × F → E →L[𝕜] F) (p : E × F) : Submodule 𝕜 (E × F) :=
  (f p : E →ₗ[𝕜] F).graph

@[simp]
theorem mem_graphDistribution {f : E × F → E →L[𝕜] F} {p v : E × F} :
    v ∈ graphDistribution f p ↔ v.2 = f p v.1 :=
  LinearMap.mem_graph_iff _ _

/-- For a `C^n` family `f` with finite-dimensional source `E`, the graph distribution of `f` is a
`C^n` distribution of rank `finrank 𝕜 E`. A basis `b` of `E` gives the global frame
`q ↦ (b i, f q (b i))`. -/
theorem isContMDiffDistribution_graphDistribution [FiniteDimensional 𝕜 E] {n : ℕ∞ω}
    {f : E × F → E →L[𝕜] F} (hf : ContDiff 𝕜 n f) :
    IsContMDiffDistribution 𝓘(𝕜, E × F) n (Module.finrank 𝕜 E) (graphDistribution f) := by
  -- An opaque basis, so that elaboration does not unfold `Module.finBasis`.
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E) := ⟨Module.finBasis 𝕜 E⟩
  refine IsDistributionFrameOn.isContMDiffDistribution
    (X := fun i q ↦ ((b i, f q (b i)) : E × F)) ⟨fun i ↦ ?_, fun {q} _ ↦ ?_, fun {q} _ ↦ ?_⟩
  · exact contMDiffOn_vectorSpace_iff_contDiffOn.2
      (contDiff_const.prodMk (hf.clm_apply contDiff_const)).contDiffOn
  · have hker : LinearMap.ker (LinearMap.id.prod (f q : E →ₗ[𝕜] F)) = ⊥ := by
      simp [LinearMap.ker_prod]
    have hli : LinearIndependent 𝕜 fun i ↦ ((b i, f q (b i)) : E × F) :=
      b.linearIndependent.map' _ hker
    -- The tangent spaces of the model space `E × F` are `E × F` itself, by definition.
    exact hli
  · have hspan : Submodule.span 𝕜 (range fun i ↦ ((b i, f q (b i)) : E × F)) =
        graphDistribution f q := by
      rw [graphDistribution, LinearMap.graph_eq_range_prod, LinearMap.range_eq_map, ← b.span_eq,
        Submodule.map_span, ← range_comp]
      -- `LinearMap.id.prod (f q)` sends `b i` to `(b i, f q (b i))` by definition.
      rfl
    -- The tangent spaces of the model space `E × F` are `E × F` itself, by definition.
    exact hspan

/-- The derivative of a vector field tangent to the graph distribution near `p`: its second
component is determined by its first, up to the derivative of `f`. -/
private theorem snd_fderiv_eq_of_eventually_mem_graphDistribution {f : E × F → E →L[𝕜] F}
    {V : E × F → E × F} {p : E × F} (hf : DifferentiableAt 𝕜 f p) (hV : DifferentiableAt 𝕜 V p)
    (hVD : ∀ᶠ q in 𝓝 p, V q ∈ graphDistribution f q) (h : E × F) :
    (fderiv 𝕜 V p h).2 = f p (fderiv 𝕜 V p h).1 + fderiv 𝕜 f p h (V p).1 := by
  -- The map `q ↦ (V q).2 - f q (V q).1` vanishes near `p`, so its derivative there is zero.
  have h₁ := hV.hasFDerivAt.snd.sub (hf.hasFDerivAt.clm_apply hV.hasFDerivAt.fst)
  have h₂ : HasFDerivAt (fun q ↦ (V q).2 - f q (V q).1) (0 : E × F →L[𝕜] F) p :=
    (hasFDerivAt_const 0 p).congr_of_eventuallyEq <| hVD.mono fun q hq ↦ by
      simpa [sub_eq_zero] using hq
  simpa [sub_eq_zero] using congrArg (· h) (h₁.unique h₂)

/-- **The Lie bracket of two vector fields tangent to a graph distribution.** If `V` and `W` are
differentiable at `p` and tangent to the graph distribution of `f` near `p`, and `f` is
differentiable at `p`, then the second component of `[V, W]` at `p` is `f p` applied to its first
component, plus the defect `fderiv 𝕜 f p (V p) (W p).1 - fderiv 𝕜 f p (W p) (V p).1`. -/
theorem snd_lieBracket_eq_of_eventually_mem_graphDistribution {f : E × F → E →L[𝕜] F}
    {V W : E × F → E × F} {p : E × F} (hf : DifferentiableAt 𝕜 f p)
    (hV : DifferentiableAt 𝕜 V p) (hW : DifferentiableAt 𝕜 W p)
    (hVD : ∀ᶠ q in 𝓝 p, V q ∈ graphDistribution f q)
    (hWD : ∀ᶠ q in 𝓝 p, W q ∈ graphDistribution f q) :
    (lieBracket 𝕜 V W p).2 = f p (lieBracket 𝕜 V W p).1 +
      (fderiv 𝕜 f p (V p) (W p).1 - fderiv 𝕜 f p (W p) (V p).1) := by
  simp only [lieBracket_eq, Prod.snd_sub, Prod.fst_sub, map_sub,
    snd_fderiv_eq_of_eventually_mem_graphDistribution hf hW hWD,
    snd_fderiv_eq_of_eventually_mem_graphDistribution hf hV hVD]
  abel

/-- The Lie bracket at `p` of two vector fields tangent to the graph distribution of `f` near `p`
is tangent to it at `p` exactly when `fderiv 𝕜 f p (V p) (W p).1 = fderiv 𝕜 f p (W p) (V p).1`. -/
theorem lieBracket_mem_graphDistribution_iff {f : E × F → E →L[𝕜] F}
    {V W : E × F → E × F} {p : E × F} (hf : DifferentiableAt 𝕜 f p)
    (hV : DifferentiableAt 𝕜 V p) (hW : DifferentiableAt 𝕜 W p)
    (hVD : ∀ᶠ q in 𝓝 p, V q ∈ graphDistribution f q)
    (hWD : ∀ᶠ q in 𝓝 p, W q ∈ graphDistribution f q) :
    lieBracket 𝕜 V W p ∈ graphDistribution f p ↔
      fderiv 𝕜 f p (V p) (W p).1 = fderiv 𝕜 f p (W p) (V p).1 := by
  rw [mem_graphDistribution, snd_lieBracket_eq_of_eventually_mem_graphDistribution hf hV hW hVD hWD,
    add_eq_left, sub_eq_zero]

/-- Where the Frobenius integrability condition holds, the Lie bracket of two vector fields tangent
to the graph distribution is tangent to it. -/
theorem lieBracket_mem_graphDistribution {f : E × F → E →L[𝕜] F}
    {V W : E × F → E × F} {p : E × F} (hf : DifferentiableAt 𝕜 f p)
    (hV : DifferentiableAt 𝕜 V p) (hW : DifferentiableAt 𝕜 W p)
    (hVD : ∀ᶠ q in 𝓝 p, V q ∈ graphDistribution f q)
    (hWD : ∀ᶠ q in 𝓝 p, W q ∈ graphDistribution f q) (hint : IsFrobeniusIntegrableAt f p) :
    lieBracket 𝕜 V W p ∈ graphDistribution f p := by
  have hVp : ((V p).1, f p (V p).1) = V p :=
    Prod.ext rfl (mem_graphDistribution.1 hVD.self_of_nhds).symm
  have hWp : ((W p).1, f p (W p).1) = W p :=
    Prod.ext rfl (mem_graphDistribution.1 hWD.self_of_nhds).symm
  rw [lieBracket_mem_graphDistribution_iff hf hV hW hVD hWD, ← hVp, ← hWp]
  exact isFrobeniusIntegrableAt_iff.1 hint _ _

/-- An involutive graph distribution satisfies the Frobenius integrability condition at every point
near which `f` is differentiable. The condition is the tangency of the brackets of the vector
fields `q ↦ (v, f q v)`, which are tangent to the distribution. -/
theorem IsInvolutiveDistribution.isFrobeniusIntegrableAt {f : E × F → E →L[𝕜] F} {p : E × F}
    (hD : IsInvolutiveDistribution 𝓘(𝕜, E × F) (graphDistribution f))
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt 𝕜 f q) : IsFrobeniusIntegrableAt f p := by
  obtain ⟨U, hUf, hU, hpU⟩ := eventually_nhds_iff.1 hf
  refine isFrobeniusIntegrableAt_iff.2 fun v w ↦ ?_
  -- The vector field `q ↦ (v, f q v)`, tangent to the graph distribution everywhere.
  let V (v : E) : Π q : E × F, TangentSpace 𝓘(𝕜, E × F) q := fun q ↦ (v, f q v)
  have hVdiff (v : E) {q : E × F} (hq : q ∈ U) : DifferentiableAt 𝕜 (V v) q :=
    (differentiableAt_const v).prodMk ((hUf q hq).clm_apply (differentiableAt_const v))
  have hVD (v : E) (q : E × F) : V v q ∈ graphDistribution f q := mem_graphDistribution.2 rfl
  have hmem := hD.mlieBracket_mem hU
    (mdifferentiableOn_vectorSpace_iff_differentiableOn.2 fun q hq ↦
      (hVdiff v hq).differentiableWithinAt)
    (mdifferentiableOn_vectorSpace_iff_differentiableOn.2 fun q hq ↦
      (hVdiff w hq).differentiableWithinAt)
    (fun q _ ↦ hVD v q) (fun q _ ↦ hVD w q) hpU
  rw [mlieBracket_eq_lieBracket] at hmem
  -- The tangent spaces of the model space `E × F` are `E × F` itself, by definition.
  exact (lieBracket_mem_graphDistribution_iff (hUf p hpU) (hVdiff v hpU) (hVdiff w hpU)
    (Eventually.of_forall (hVD v)) (Eventually.of_forall (hVD w))).1 hmem

/-- **Involutivity of a graph distribution is the Frobenius integrability condition.** For a
differentiable family `f`, the graph distribution of `f` is involutive exactly when `f` satisfies
the Frobenius integrability condition at every point. -/
theorem isInvolutiveDistribution_graphDistribution_iff {f : E × F → E →L[𝕜] F}
    (hf : Differentiable 𝕜 f) :
    IsInvolutiveDistribution 𝓘(𝕜, E × F) (graphDistribution f) ↔
      ∀ p, IsFrobeniusIntegrableAt f p := by
  refine ⟨fun hD p ↦ hD.isFrobeniusIntegrableAt (Eventually.of_forall hf), fun hint ↦ ?_⟩
  refine isInvolutiveDistribution_iff.2 fun U hU V W hV hW hVD hWD x hx ↦ ?_
  rw [mlieBracket_eq_lieBracket]
  have hV' := mdifferentiableOn_vectorSpace_iff_differentiableOn.1 hV
  have hW' := mdifferentiableOn_vectorSpace_iff_differentiableOn.1 hW
  exact lieBracket_mem_graphDistribution (hf x) (hV'.differentiableAt (hU.mem_nhds hx))
    (hW'.differentiableAt (hU.mem_nhds hx)) (eventually_of_mem (hU.mem_nhds hx) hVD)
    (eventually_of_mem (hU.mem_nhds hx) hWD) (hint x)

end Field

section Real

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The Frobenius theorem in coordinates.** Let `f` be of class `C^(n+1)` near `(x₀, y₀)`, with
an involutive graph distribution. Then the distribution has an integral manifold through
`(x₀, y₀)`: the graph of a function `u`, of class `C^(n+1)` at `x₀`, with `u x₀ = y₀` and
`D u x = f (x, u x)` near `x₀`, so that the tangent space of the graph at `(x, u x)` is the graph
of `f (x, u x)`. -/
theorem IsInvolutiveDistribution.exists_eventually_hasFDerivAt {n : ℕ∞}
    {f : E × F → E →L[ℝ] F} {s : Set (E × F)} {x₀ : E} {y₀ : F}
    (hD : IsInvolutiveDistribution 𝓘(ℝ, E × F) (graphDistribution f))
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ 𝓝 (x₀, y₀)) :
    ∃ u : E → F, u x₀ = y₀ ∧ ContDiffAt ℝ (n + 1) u x₀ ∧
      ∀ᶠ x in 𝓝 x₀, HasFDerivAt u (f (x, u x)) x := by
  refine exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt hf hs ?_
  filter_upwards [eventually_eventually_nhds.2 (eventually_mem_nhds_iff.2 hs)] with p hp
  exact hD.isFrobeniusIntegrableAt <| hp.mono fun q hq ↦
    (hf.contDiffAt hq).differentiableAt (by simp)

/-- **The Frobenius theorem for graph distributions.** For a `C¹` family `f` over
finite-dimensional real spaces, the graph distribution of `f` is involutive exactly when through
every point `p` there passes an integral manifold, the graph of a local solution `u` of
`D u x = f (x, u x)` with `u p.1 = p.2`. -/
theorem isInvolutiveDistribution_graphDistribution_iff_forall_exists
    {f : E × F → E →L[ℝ] F} (hf : ContDiff ℝ 1 f) :
    IsInvolutiveDistribution 𝓘(ℝ, E × F) (graphDistribution f) ↔
      ∀ p : E × F, ∃ u : E → F, u p.1 = p.2 ∧ ∀ᶠ x in 𝓝 p.1, HasFDerivAt u (f (x, u x)) x := by
  have hf' : ContDiffOn ℝ ((0 : ℕ∞) + 1) f univ := by simpa using hf.contDiffOn
  have key (p₀ : E × F) :=
    eventually_exists_hasFDerivAt_iff_eventually_isFrobeniusIntegrableAt hf' (p₀ := p₀) univ_mem
  rw [isInvolutiveDistribution_graphDistribution_iff (hf.differentiable one_ne_zero)]
  exact ⟨fun h p ↦ ((key p).2 (Eventually.of_forall h)).self_of_nhds,
    fun h p ↦ ((key p).1 (Eventually.of_forall h)).self_of_nhds⟩

end Real

end TauCeti
