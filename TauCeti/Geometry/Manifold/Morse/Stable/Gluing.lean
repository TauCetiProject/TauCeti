/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.TransverseDisc
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
public import TauCeti.Geometry.Manifold.TransverseDisc

/-!
# Model-flow gluing of broken pseudo-gradient trajectories in a Morse box

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `x`, `r` critical points with
`ind p = ind x + 1 = ind r + 2`. In the split coordinates `(u, v)` (contracting and expanding) of a
Morse chart `φ` at `x`, the model flow is the split hyperbolic flow `(u, v) ↦ (e^{-t} u, e^t v)`.
It is the flow of `X` only in a Morse chart in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, such
as the chart given by the definition of an adapted pseudo-gradient; the results here hold for an
arbitrary Morse chart and are stated for the model flow. A broken trajectory from `p` to `r` through
`x` enters the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` along the stable manifold of `x` and leaves it along the
unstable manifold.

The gluing theorem in the split model,
`TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`, takes as input a disc
through the entrance point whose expanding component has invertible derivative, and a disc through
the exit point whose contracting component has invertible derivative. This file supplies them:

* the level cut `W^u(p) ∩ {f = c}` through the entrance point is such a disc. Its tangent space
  meets the stable subspace only in `0`, because `W^u(p)` and `W^s(x)` are transverse, their
  intersection is one-dimensional and spanned by `X`, and `X` is not tangent to the level;
* dually, the level cut `W^s(r) ∩ {f = c}` through the exit point is a disc of the second kind.

These are instances of `TauCeti.exists_param_inter_preimage_of_span_mtangentConeAt_sup_eq_top`.
Feeding both discs to the model gluing theorem shows that, in the split coordinates, the model-flow
orbits from `W^u(p)` to `W^s(r)` near the broken one form a half-open arc whose closure adds exactly
the broken trajectory and is homeomorphic to a closed interval. Such arcs are the local models at
the broken trajectories of the compactified space of index-two trajectories; assembling that space
into a compact one-manifold, whose boundary points then come in pairs, is not done here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_unstableSet_level_param`: the entrance disc in `W^u(p)`.
* `IsMorseSmale.exists_stableSet_level_param`: the exit disc in `W^s(r)`.
* `IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`: the closed interval chart of
  model-flow glued trajectories near a broken trajectory, in the split coordinates of a Morse
  chart.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x y : M}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-- **The entrance disc of an unstable manifold.** Let `x` be a critical point with Morse chart
`φ`, and `p` a critical point of index `ind x + 1`, for a Morse–Smale adapted pseudo-gradient. Let
`y` be a point of a trajectory from `p` to `x` in the chart, near which the stable manifold of `x`
lies in the contracting coordinates of `φ` (the second split coordinate vanishes). Then the level
cut `W^u(p) ∩ {f = f y}` is, near `y`, a disc transverse to the stable set of the model flow: there
is a parametrization `ι` of it with `ι 0 = y`, reaching every point of the cut near `y` from small
parameters, whose split coordinates are strictly differentiable at `0` with derivative `ψ'`
such that the expanding component of `ψ'` is invertible. -/
theorem IsMorseSmale.exists_unstableSet_level_param {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1)
    (φ : MorseChart E f x) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x)
    (hyφ : y ∈ φ.toChart.source)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.stableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) :
    ∃ (F : Submodule ℝ E) (ι : F → M)
      (ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ hX.flow.unstableSet p ∧ f (ι z) = f y) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) ψ' 0 ∧
      (WithLp.sndL 2 ℝ _ _ ∘L ψ').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet p → f w = f y →
        ∃ z ∈ V, ι z = w := by
  have hpx : p ≠ x := by rintro rfl; omega
  obtain ⟨L, q, -, hyq, hq, hs⟩ := hX.exists_isSliceChart_unstableSet hf hp hy.1
  set P := WithLp.sndL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    (φ.splitCoordL : E →L[ℝ] _)
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (0, b))
    exact ⟨u, by simp [P, hu]⟩
  have hX0 : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet p)
      hy.1)
  have hX0' : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet x) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet x)
      hy.2)
  obtain ⟨F, ι, ι', hι0, hι, hιs, hd, hinv, hexh⟩ :=
    exists_param_inter_preimage_of_span_mtangentConeAt_sup_eq_top (by simp) hq hs hyq hy.1 hy.2
      isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn (h.span_mtangentConeAt_sup_eq_top hp hx hy)
      (by rw [hX.finrank_span_mtangentConeAt_unstableSet hf hy.1, φ.finrank_snd_splitCoord,
        hind]) hX0 hX0'
      (hX.mvfderiv_apply_lt_zero y
        (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hpx hy)).ne
      φ.mem_maximalAtlas hyφ hPs (by simpa [P] using hloc)
  refine ⟨F, ι, (φ.splitCoordL : E →L[ℝ] _) ∘L ι', hι0, hι, hιs, ?_, ?_, hexh⟩
  · simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd
  · rwa [← ContinuousLinearMap.comp_assoc]

/-- **The exit disc of a stable manifold.** Let `x` be a critical point with Morse chart `φ`, and
`r` a critical point of index `ind x - 1`, for a Morse–Smale adapted pseudo-gradient. Let `y` be a
point of a trajectory from `x` to `r` in the chart, near which the unstable manifold of `x` lies in
the expanding coordinates of `φ` (the first split coordinate vanishes). Then the level cut
`W^s(r) ∩ {f = f y}` is, near `y`, a disc transverse to the unstable set of the model flow: there is
a parametrization `ι` of it with `ι 0 = y`, reaching every point of the cut near `y` from small
parameters, whose split coordinates are strictly differentiable at `0` with derivative `ψ'`
such that the contracting component of `ψ'` is invertible. -/
theorem IsMorseSmale.exists_stableSet_level_param {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {r : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (φ : MorseChart E f x) (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet r)
    (hyφ : y ∈ φ.toChart.source)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0) :
    ∃ (F : Submodule ℝ E) (ι : F → M)
      (ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ hX.flow.stableSet r ∧ f (ι z) = f y) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) ψ' 0 ∧
      (WithLp.fstL 2 ℝ _ _ ∘L ψ').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ hX.flow.stableSet r → f w = f y →
        ∃ z ∈ V, ι z = w := by
  have hxr : x ≠ r := by rintro rfl; omega
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨L, q, -, hyq, hq, hs⟩ := hX.exists_isSliceChart_stableSet hfd hr hy.2
  set P := WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    (φ.splitCoordL : E →L[ℝ] _)
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (b, 0))
    exact ⟨u, by simp [P, hu]⟩
  have hX0 : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet r) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet r)
      hy.2)
  have hX0' : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant
      (hX.flow.isInvariant_unstableSet x) hy.1)
  have hdim := hX.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hfd hr hy.2
  have hdimφ := φ.finrank_fst_splitCoord_add_manifoldMorseIndex
  obtain ⟨F, ι, ι', hι0, hι, hιs, hd, hinv, hexh⟩ :=
    exists_param_inter_preimage_of_span_mtangentConeAt_sup_eq_top (by simp) hq hs hyq hy.2 hy.1
      isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn
      (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top hx hr hy) (by omega) hX0 hX0'
      (hX.mvfderiv_apply_lt_zero y
        (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hxr hy)).ne
      φ.mem_maximalAtlas hyφ hPs (by simpa [P] using hloc)
  refine ⟨F, ι, (φ.splitCoordL : E →L[ℝ] _) ∘L ι', hι0, hι, hιs, ?_, ?_, hexh⟩
  · simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd
  · rwa [← ContinuousLinearMap.comp_assoc]

/-- **Gluing a broken trajectory in a Morse box.** Let `p`, `x`, `r` be critical points of
consecutive indices `ind p = ind x + 1 = ind r + 2` of a Morse function, with a Morse–Smale adapted
pseudo-gradient and a Morse chart `φ` at `x`. Consider a broken trajectory from `p` to `r` through
`x`, entering the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of the split coordinates `(u, v)` of `φ` at a point `y₁`
of `W^u(p) ∩ W^s(x)` on the entrance face `‖u‖ = ε`, and leaving it at a point `y₂` of
`W^u(x) ∩ W^s(r)` on the exit face `‖v‖ = ε`, where the stable and unstable manifolds of `x` lie in
the corresponding coordinate subspaces.

Read in the split coordinates, the pairs formed by the entrance point, under the model flow, of the
orbit of a point of `W^u(p) ∩ {f = f y₁}` near `y₁`, and the exit point of the orbit of a point of
`W^s(r) ∩ {f = f y₂}` near `y₂`, when the model passage map joins them, form a half-open arc
`TauCeti.splitGluingPairs`. Its closure is homeomorphic to a closed interval, with the
broken pair of coordinates of `y₁` and `y₂` as the endpoint `0`, and adds no other point; the
inverse coordinate is the norm of the expanding entrance coordinate divided by `ε`. Every point of
the arc comes from points of the two level cuts in prescribed neighbourhoods `U` of `y₁` and `V` of
`y₂`, and conversely every such pair of points near `(y₁, y₂)` whose model orbits are joined by the
passage map lies on the arc.

The chart `φ` is arbitrary, so this is a statement about the model flow. When `X` is the linear
field `z ↦ (-wᵢ zᵢ)ᵢ` in `φ`, model orbits that stay in a box inside the chart are the orbits of the
pseudo-gradient (`TauCeti.IsAdaptedPseudoGradient.flow_splitExitTime`). -/
theorem IsMorseSmale.exists_homeomorph_closure_splitGluingPairs {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p r y₁ y₂ : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hpx : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1)
    (hxr : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (φ : MorseChart E f x)
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x) (hy₁φ : y₁ ∈ φ.toChart.source)
    (hy₂ : y₂ ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet r) (hy₂φ : y₂ ∈ φ.toChart.source)
    (hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0)
    (hloc₂ : ∀ᶠ w in 𝓝 y₂, w ∈ hX.flow.unstableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)
    {ε : ℝ} (hε : 0 < ε) (hy₁ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε)
    (hy₂ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε)
    {U V : Set M} (hU : U ∈ 𝓝 y₁) (hV : V ∈ 𝓝 y₂) :
    ∃ (r₀ : ℝ) (hr₀ : 0 < r₀) (g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ)
      (k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ),
      (∃ e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitGluingPairs ε r₀ g k),
        (∀ q, (e.symm q : ℝ) = ‖q.val.1.snd‖ / ε) ∧
        (e ⟨0, left_mem_Icc.2 hr₀.le⟩).val = (φ.splitCoord (φ.coord (φ.toChart y₁)),
          φ.splitCoord (φ.coord (φ.toChart y₂)))) ∧
      closure (splitGluingPairs ε r₀ g k) = insert (φ.splitCoord (φ.coord (φ.toChart y₁)),
        φ.splitCoord (φ.coord (φ.toChart y₂))) (splitGluingPairs ε r₀ g k) ∧
      (∀ q ∈ splitGluingPairs ε r₀ g k,
        (∃ w ∈ U, w ∈ hX.flow.unstableSet p ∧ f w = f y₁ ∧
          splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = q.1) ∧
        ∃ w ∈ V, w ∈ hX.flow.stableSet r ∧ f w = f y₂ ∧
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = q.2) ∧
      ∀ᶠ w : M × M in 𝓝 (y₁, y₂), w.1 ∈ hX.flow.unstableSet p → f w.1 = f y₁ →
        w.2 ∈ hX.flow.stableSet r → f w.2 = f y₂ →
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
          (φ.splitCoord (φ.coord (φ.toChart w.1)))).snd ≠ 0 →
        splitPassage ε (splitQuadraticFlow
            (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
            (φ.splitCoord (φ.coord (φ.toChart w.1)))) =
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
            (φ.splitCoord (φ.coord (φ.toChart w.2))) →
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
            (φ.splitCoord (φ.coord (φ.toChart w.1))),
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
            (φ.splitCoord (φ.coord (φ.toChart w.2)))) ∈ splitGluingPairs ε r₀ g k := by
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w))
  obtain ⟨F₁, ι₁, ψ', hι₁0, hι₁, hι₁s, hψ, hψ', hexh₁⟩ :=
    h.exists_unstableSet_level_param hf hp hx hpx φ hy₁ hy₁φ hloc₁
  obtain ⟨F₂, ι₂, χ', hι₂0, hι₂, hι₂s, hχ, hχ', hexh₂⟩ :=
    h.exists_stableSet_level_param hf hx hr hxr φ hy₂ hy₂φ hloc₂
  -- The broken pair: `y₁` lies on the stable set of `x` and `y₂` on its unstable set.
  have hψ₀ : Φ (ι₁ 0) = WithLp.toLp 2 ((Φ y₁).fst, 0) := by
    rw [hι₁0, ← hloc₁.self_of_nhds hy₁.2]
    rfl
  have hχ₀ : Φ (ι₂ 0) = WithLp.toLp 2 (0, (Φ y₂).snd) := by
    rw [hι₂0, ← hloc₂.self_of_nhds hy₂.1]
    rfl
  -- Parameters near `0` whose points lie in the prescribed neighbourhoods and level cuts.
  set U' : Set F₁ := {z | ι₁ z ∈ U ∧ ι₁ z ∈ hX.flow.unstableSet p ∧ f (ι₁ z) = f y₁}
  set V' : Set F₂ := {z | ι₂ z ∈ V ∧ ι₂ z ∈ hX.flow.stableSet r ∧ f (ι₂ z) = f y₂}
  have hU'0 : U' ∈ 𝓝 0 := by
    have hU₁ : ∀ᶠ z in 𝓝 (0 : F₁), ι₁ z ∈ U := hι₁.preimage_mem_nhds (by rwa [hι₁0])
    exact hU₁.and hι₁s
  have hV'0 : V' ∈ 𝓝 0 := by
    have hV₂ : ∀ᶠ z in 𝓝 (0 : F₂), ι₂ z ∈ V := hι₂.preimage_mem_nhds (by rwa [hι₂0])
    exact hV₂.and hι₂s
  obtain ⟨r₀, hr₀, g, k, ⟨e, he, he₀⟩, hcl, hpairs, hexh⟩ :=
    exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt hψ hψ' hψ₀ hy₁ε hχ hχ' hχ₀
      hy₂ε hε hU'0 hV'0
  refine ⟨r₀, hr₀, g, k, ⟨e, he, by rw [he₀, ← hψ₀, ← hχ₀, hι₁0, hι₂0]⟩,
    by rw [hcl, ← hψ₀, ← hχ₀, hι₁0, hι₂0], ?_, ?_⟩
  · intro q hq
    obtain ⟨⟨z₁, ⟨hz₁U, hz₁s, hz₁f⟩, hz₁⟩, z₂, ⟨hz₂V, hz₂s, hz₂f⟩, hz₂⟩ := hpairs q hq
    exact ⟨⟨ι₁ z₁, hz₁U, hz₁s, hz₁f, hz₁⟩, ι₂ z₂, hz₂V, hz₂s, hz₂f, hz₂⟩
  · -- Points of the level cuts near `y₁` and `y₂` are reached from small parameters.
    obtain ⟨A₁, hA₁, A₂, hA₂, hA⟩ := mem_nhds_prod_iff.1 hexh
    filter_upwards [(hexh₁ A₁ hA₁).prodMk_nhds (hexh₂ A₂ hA₂)] with w hw hw₁s hw₁f hw₂s hw₂f
    obtain ⟨z₁, hz₁, hz₁w⟩ := hw.1 hw₁s hw₁f
    obtain ⟨z₂, hz₂, hz₂w⟩ := hw.2 hw₂s hw₂f
    rw [← hz₁w, ← hz₂w]
    have hq := hA (mk_mem_prod hz₁ hz₂)
    rw [mem_ofPred_eq] at hq
    exact hq

end IsAdaptedPseudoGradient

end TauCeti
