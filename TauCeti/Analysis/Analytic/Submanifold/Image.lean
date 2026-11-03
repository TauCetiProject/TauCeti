/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Immersion
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Images of analytic submanifolds under analytic embeddings

An analytic map with an analytic left inverse takes an analytic submanifold to an analytic
submanifold of the same dimension. Both maps may be analytic only in submanifold charts;
ambient analyticity is not required. In particular, an analytic isomorphism transports smaller
analytic submanifolds, and its restrictions in both directions remain analytic.

The left inverse is essential: it supplies both injectivity of the differential and the
relative openness of the local parametrizations. An immersion alone does not ensure that its
image is an embedded submanifold. The ambient flattening charts are constructed by
`exists_isAnalyticChart_of_injective_fderiv`, using local ambient analytic extensions of the
inverse.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 (real analytic submanifolds).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
  di Pisa (3) 18 (1964), 449–474, §4 (analytic simplex maps and their restrictions).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {n m k d : ℕ} {S : Set (Fin n → 𝕜)} {T : Set (Fin m → 𝕜)}
  {f : (Fin n → 𝕜) → Fin m → 𝕜} {g : (Fin m → 𝕜) → Fin n → 𝕜}

/-- An analytic map on an analytic submanifold, with an analytic left inverse on a
submanifold containing its image, has an embedded analytic image of the same dimension.
The inverse need only be defined and analytic on that containing submanifold. -/
theorem IsAnalyticSubmanifold.image_of_leftInvOn (hS : IsAnalyticSubmanifold k S)
    (hf : AnalyticOnSubmanifold k f S) (hg : AnalyticOnSubmanifold d g T)
    (hfT : MapsTo f S T) (hgf : LeftInvOn g f S) :
    IsAnalyticSubmanifold k (f '' S) := by
  have hlocal (x : Fin n → 𝕜) (hx : x ∈ S) :
      k ≤ m ∧ ∃ e, f x ∈ e.source ∧ IsAnalyticChart k (f '' S) e := by
    obtain ⟨c, hxc, hc⟩ := hS.exists_isAnalyticChart x hx
    let u₀ := firstCoords 𝕜 n k (c x)
    let φ := fun u ↦ c.symm (firstCoords 𝕜 k n u)
    let p := f ∘ φ
    have hφ₀ : φ u₀ = x := hc.symm_firstCoords_firstCoords_apply hxc hx
    have hφ : AnalyticAt 𝕜 φ u₀ := hc.analyticAt_symm_firstCoords hxc hx
    have hφS : ∀ᶠ u in 𝓝 u₀, φ u ∈ c.source ∩ S :=
      hc.eventually_symm_firstCoords_mem hxc hx
    have hp : AnalyticAt 𝕜 p u₀ := hf.analyticAt_chart hx hc hxc
    have hp₀ : p u₀ = f x := congrArg f hφ₀
    -- Extend the inverse near `f x`. Composing it with `p` recovers the source immersion.
    obtain ⟨V, hV, hxV, G, hG, hgG⟩ := hg.exists_analyticAt_eqOn (hfT hx)
    have hGp : (G ∘ p) =ᶠ[𝓝 u₀] φ := by
      filter_upwards [hφS, hp.continuousAt.preimage_mem_nhds
        (hp₀ ▸ hV.mem_nhds hxV)] with u hu huV
      exact (hgG ⟨hfT hu.2, huV⟩).symm.trans (hgf hu.2)
    have hD : (fderiv 𝕜 G (p u₀)).comp (fderiv 𝕜 p u₀) = fderiv 𝕜 φ u₀ := by
      rw [← fderiv_comp u₀ (hp₀ ▸ hG.differentiableAt) hp.differentiableAt]
      exact hGp.fderiv_eq
    have hinj : Function.Injective (fderiv 𝕜 p u₀) := by
      intro v w hvw
      apply hc.injective_fderiv_symm_firstCoords hxc hx hS.le
      simpa only [← ContinuousLinearMap.comp_apply, hD] using
        congrArg (fderiv 𝕜 G (p u₀)) hvw
    -- The continuous inverse returns nearby image points to any chosen parameter neighborhood.
    have himage : ∀ W ∈ 𝓝 u₀, p '' W ∈ 𝓝[f '' S] (p u₀) := by
      intro W hW
      have hgcont : ContinuousWithinAt g (f '' S) (p u₀) := by
        rw [hp₀]
        exact (hg.continuousOn (f x) (hfT hx)).mono (image_subset_iff.2 hfT)
      have hcx : ContinuousAt c x := c.continuousAt hxc
      have hq : ContinuousWithinAt (fun y ↦ firstCoords 𝕜 n k (c (g y)))
          (f '' S) (p u₀) :=
        (firstCoords 𝕜 n k).continuous.continuousAt.comp_continuousWithinAt
          (hcx.comp_continuousWithinAt_of_eq hgcont (by rw [hp₀, hgf hx]))
      have hqW : ∀ᶠ y in 𝓝[f '' S] (p u₀), firstCoords 𝕜 n k (c (g y)) ∈ W :=
        hq.preimage_mem_nhdsWithin (by rw [hp₀, hgf hx]; exact hW)
      have hgc : ∀ᶠ y in 𝓝[f '' S] (p u₀), g y ∈ c.source :=
        hgcont.preimage_mem_nhdsWithin (by rw [hp₀, hgf hx]; exact c.open_source.mem_nhds hxc)
      filter_upwards [self_mem_nhdsWithin, hqW, hgc] with y hy hyW hyc
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨firstCoords 𝕜 n k (c (g (f z))), hyW, ?_⟩
      dsimp only [p, φ, Function.comp_apply]
      have hgz : g (f z) ∈ S := by rwa [hgf hz]
      rw [hc.symm_firstCoords_firstCoords_apply hyc hgz, hgf hz]
    obtain ⟨e, hpe, he, -, -⟩ := exists_isAnalyticChart_of_injective_fderiv hp hinj
      (hφS.mono fun u hu ↦ mem_image_of_mem f hu.2) himage
    refine ⟨?_, e, hp₀ ▸ hpe, he⟩
    simpa using LinearMap.finrank_le_finrank_of_injective
      (f := (fderiv 𝕜 p u₀).toLinearMap) hinj
  obtain ⟨x, hx⟩ := hS.nonempty
  refine ⟨hS.nonempty.image f, (hlocal x hx).1, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hlocal z hz).2

end TauCeti
