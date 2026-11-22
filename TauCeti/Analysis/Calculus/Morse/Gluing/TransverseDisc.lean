/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.Compactification
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.Analysis.Calculus.RadialRescaleGraph
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Traces of transverse discs on the faces of the split hyperbolic box

The gluing theorems for the split hyperbolic flow `φ t (x, y) = (e^{-t} x, e^t y)`
(`TauCeti.splitQuadraticFlow`) on the box `‖x‖ ≤ ε, ‖y‖ ≤ ε`, such as
`TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image`, take as input a Lipschitz graph
`y ↦ (g y, y)` in the entrance face `‖x‖ = ε` and a Lipschitz graph `x ↦ (x, k x)` in the exit
face `‖y‖ = ε`. In Morse homology these graphs are the traces on the faces of the unstable
manifold of the starting critical point and of the stable manifold of the final one. Those are
known only as differentiable discs through the broken entrance point `(x₀, 0)` and exit point
`(0, y₀)`, transverse there to the stable set `y = 0` and to the unstable set `x = 0`
respectively, and they need not lie in the faces.

This file produces the graphs. Let `ψ : F → WithLp 2 (Eₛ × Eᵤ)` be strictly differentiable at
`0`, with `ψ 0 = (x₀, 0)`, `‖x₀‖ = ε`, and with the derivative of its expanding component `y` an
isomorphism. Flowing each point `ψ z` to its entry time `log (‖x‖ / ε)` moves it onto the entrance
face, to the point `((ε / ‖x‖) • x, (‖x‖ / ε) • y)`. The expanding component of this point is
again strictly differentiable at `0`, with the same derivative
(`TauCeti.hasStrictFDerivAt_norm_div_smul`), although the faces are not smooth for a
general norm. By the inverse function theorem, near the broken entrance point the entry points
of the orbits through the disc form a Lipschitz graph `y ↦ (g y, y)` in the entrance face
(`TauCeti.exists_lipschitzOnWith_rescale_graph_prod`, with a trivial parameter). The exit face is
treated in the same way, using exit times.

Transversality to the stable set in the usual sense, that the tangent space of the disc and the
stable set together span, means that the derivative of the expanding component of `ψ` is
surjective. A complement of its kernel is then a disc on which it is an isomorphism; for the
unstable manifold of a critical point whose index exceeds by one that of the critical point at the
centre of the box, the kernel is the flow direction.

Feeding both graphs to the local compactification
`TauCeti.exists_homeomorph_closure_splitGluingPairs` shows that, near a broken orbit, the orbits
running from a disc transverse to the stable set to a disc transverse to the unstable set form a
half-open arc whose closure adds exactly the broken orbit.

The same holds for families of discs. When the broken orbit is a once-broken trajectory whose
middle critical point has index less by more than one than the first critical point, the
trajectories from the first critical point to the middle one form a family of positive dimension,
and the trace of the unstable manifold of the first critical point on the entrance face is a family
of discs transverse to the stable set, parametrized by these trajectories; likewise on the exit
face. A parameter `c` on the domain of `ψ`,
with the derivative of `z ↦ (c z, y(ψ z))` invertible, cuts it into the slices `c = s`, and the
entrance traces of all slices are the graphs `y ↦ (g (s, y), y)` of one map `g`, Lipschitz jointly
in `s` and `y`. Through the local compactification of jointly Lipschitz families of graphs
(`TauCeti.exists_homeomorph_closure_biUnion_splitGluingPairs_prod`), the orbits running from the
first family of discs to the second, together with the broken ones, form a product of `[0, r₀]`
with a ball of parameters. This is the local model of a collar along the once-broken
trajectories of a compactified space of trajectories. The single-disc traces and gluing are the
case of the trivial parameter in `Unit`.

## Main results

* `TauCeti.exists_splitQuadraticFlow_splitEntryTime_eq_graph_prod`: the entry points of the
  orbits through the slices of a family of discs transverse to the stable set form, near the broken
  entrance point, graphs over the expanding factor in the entrance face, of a map Lipschitz jointly
  in the parameter and the point, and every entry point of an orbit through a nearby point of the
  disc lies on the graph of its parameter.
* `TauCeti.exists_splitQuadraticFlow_splitExitTime_eq_graph_prod`: the same for exit points of
  the orbits through a family of discs transverse to the unstable set, as graphs over the
  contracting factor in the exit face.
* `TauCeti.exists_homeomorph_closure_biUnion_splitGluingPairs_of_hasStrictFDerivAt`: the orbits
  through the box from one family of transverse discs to the other, near the broken orbit, form a
  product of `[0, r₀]` with a ball of parameters once the broken orbits are added, and these are
  all such orbits.
* `TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`: for single discs,
  they form a closed interval once the broken orbit is added.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {F Eₛ Eᵤ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ] [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {ε : ℝ} {ψ : F → WithLp 2 (Eₛ × Eᵤ)} {ψ' : F →L[ℝ] WithLp 2 (Eₛ × Eᵤ)} {U : Set F}

/-- **Entrance traces of a family of transverse discs.** Let `ψ` be a disc through the point
`(x₀, 0)` of the stable set on the entrance face `‖x‖ = ε`, strictly differentiable at `0`, and
let `c` be a parameter on its domain, strictly differentiable at `0` with `c 0 = 0`, such that the
derivative of `z ↦ (c z, y(ψ z))` is invertible: the slices `c = s` are discs transverse to the
stable set. Near `(x₀, 0)`, the points where the orbits through the slice `c = s` enter the box
form a graph `y ↦ (g (s, y), y)` in the entrance face, for one map `g` Lipschitz on a closed ball
of `P × Eᵤ`, with `g 0 = x₀`: every point of the graph of `g (s, ·)` is the entry point of the
orbit through `ψ z` for some `z` in a prescribed neighbourhood `U` of `0` with `c z = s`, and
conversely, for `z` near `0`, the entry point of the orbit through `ψ z` lies on the graph of
`g (c z, ·)`. -/
theorem exists_splitQuadraticFlow_splitEntryTime_eq_graph_prod {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {c : F → P} {c' : F →L[ℝ] P} {x₀ : Eₛ}
    (hψ : HasStrictFDerivAt ψ ψ' 0) (hc : HasStrictFDerivAt c c' 0)
    (hψ' : (c'.prod (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ')).IsInvertible)
    (hψ₀ : ψ 0 = WithLp.toLp 2 (x₀, 0)) (hc₀ : c 0 = 0) (hx₀ : ‖x₀‖ = ε) (hε : 0 < ε)
    (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (g : P × Eᵤ → Eₛ), LipschitzOnWith K g (closedBall 0 δ) ∧ g 0 = x₀ ∧
      (∀ q ∈ closedBall (0 : P × Eᵤ) δ, ‖g q‖ = ε ∧ ∃ z ∈ U, c z = q.1 ∧
        splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = WithLp.toLp 2 (g q, q.2)) ∧
      ∀ᶠ z in 𝓝 0, (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).fst =
        g (c z, (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).snd) := by
  have ha := (WithLp.fstL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  have hb := (WithLp.sndL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  obtain ⟨δ, hδ, K, g, hg, hg₀, hpts, hexh⟩ := exists_lipschitzOnWith_rescale_graph_prod ha hb hc
    hψ' (by simpa [hψ₀] using hx₀) (by simp [hψ₀]) hc₀ hε hU
  have hfst : ∀ᶠ z in 𝓝 0, (ψ z).fst ≠ 0 :=
    ha.continuousAt.eventually_ne (by simpa [hψ₀, ← norm_pos_iff, hx₀] using hε)
  refine ⟨δ, hδ, K, g, hg, by simpa [hψ₀] using hg₀, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨z, hzU, hz₀, hzg, hzc, hzy⟩ := hpts q hq
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz₀ hzg hzy
    have hflow := splitQuadraticFlow_splitEntryTime hε hz₀
    refine ⟨?_, z, hzU, hzc, by rw [hflow, hzg, hzy]⟩
    rw [← hzg, norm_smul, Real.norm_of_nonneg (div_pos hε (norm_pos_iff.2 hz₀)).le,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hz₀)]
  · filter_upwards [hexh, hfst] with z hz hz₀
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz
    rw [splitQuadraticFlow_splitEntryTime hε hz₀]
    exact hz

/-- **Exit traces of a family of transverse discs.** Let `ψ` be a disc through the point
`(0, y₀)` of the unstable set on the exit face `‖y‖ = ε`, strictly differentiable at `0`, and let
`c` be a parameter on its domain, strictly differentiable at `0` with `c 0 = 0`, such that the
derivative of `z ↦ (c z, x(ψ z))` is invertible: the slices `c = s` are discs transverse to the
unstable set. Near `(0, y₀)`, the points where the orbits through the slice `c = s` leave the box
form a graph `x ↦ (x, k (s, x))` in the exit face, for one map `k` Lipschitz on a closed ball of
`P × Eₛ`, with `k 0 = y₀`: every point of the graph of `k (s, ·)` is the exit point of the orbit
through `ψ z` for some `z` in a prescribed neighbourhood `U` of `0` with `c z = s`, and
conversely, for `z` near `0`, the exit point of the orbit through `ψ z` lies on the graph of
`k (c z, ·)`. -/
theorem exists_splitQuadraticFlow_splitExitTime_eq_graph_prod {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {c : F → P} {c' : F →L[ℝ] P} {y₀ : Eᵤ}
    (hψ : HasStrictFDerivAt ψ ψ' 0) (hc : HasStrictFDerivAt c c' 0)
    (hψ' : (c'.prod (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L ψ')).IsInvertible)
    (hψ₀ : ψ 0 = WithLp.toLp 2 (0, y₀)) (hc₀ : c 0 = 0) (hy₀ : ‖y₀‖ = ε) (hε : 0 < ε)
    (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (k : P × Eₛ → Eᵤ), LipschitzOnWith K k (closedBall 0 δ) ∧ k 0 = y₀ ∧
      (∀ q ∈ closedBall (0 : P × Eₛ) δ, ‖k q‖ = ε ∧ ∃ z ∈ U, c z = q.1 ∧
        splitQuadraticFlow (splitExitTime ε (ψ z)) (ψ z) = WithLp.toLp 2 (q.2, k q)) ∧
      ∀ᶠ z in 𝓝 0, (splitQuadraticFlow (splitExitTime ε (ψ z)) (ψ z)).snd =
        k (c z, (splitQuadraticFlow (splitExitTime ε (ψ z)) (ψ z)).fst) := by
  have ha := (WithLp.sndL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  have hb := (WithLp.fstL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  obtain ⟨δ, hδ, K, k, hk, hk₀, hpts, hexh⟩ := exists_lipschitzOnWith_rescale_graph_prod ha hb hc
    hψ' (by simpa [hψ₀] using hy₀) (by simp [hψ₀]) hc₀ hε hU
  have hsnd : ∀ᶠ z in 𝓝 0, (ψ z).snd ≠ 0 :=
    ha.continuousAt.eventually_ne (by simpa [hψ₀, ← norm_pos_iff, hy₀] using hε)
  refine ⟨δ, hδ, K, k, hk, by simpa [hψ₀] using hk₀, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨z, hzU, hz₀, hzk, hzc, hzx⟩ := hpts q hq
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz₀ hzk hzx
    have hflow := splitQuadraticFlow_splitExitTime hε hz₀
    refine ⟨?_, z, hzU, hzc, by rw [hflow, hzk, hzx]⟩
    rw [← hzk, norm_smul, Real.norm_of_nonneg (div_pos hε (norm_pos_iff.2 hz₀)).le,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hz₀)]
  · filter_upwards [hexh, hsnd] with z hz hz₀
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz
    rw [splitQuadraticFlow_splitExitTime hε hz₀]
    exact hz

/-- **Gluing through families of transverse discs.** Let `ψ` be a disc through the broken entrance
point `(x₀, 0)` with a parameter `c`, whose slices `c = s` are transverse to the stable set, and
`χ` a disc through the broken exit point `(0, y₀)` with a parameter `d`, whose slices `d = t` are
transverse to the unstable set, as in
`TauCeti.exists_splitQuadraticFlow_splitEntryTime_eq_graph_prod` and
`TauCeti.exists_splitQuadraticFlow_splitExitTime_eq_graph_prod`. Suppose that the parameter spaces
are proper and that, on `U` and `V`, the entry points of the orbits through `ψ` determine the
parameter `c` and the exit points of the orbits through `χ` determine the parameter `d`. Then
there are radii `r₀, ρ > 0` and maps `g`, `k` whose partial maps `g (s, ·)` and `k (t, ·)` are
the entrance and exit traces of the slices `c = s` and `d = t`, such that, with `S` the closed
ball of radius `ρ` in `P × Q`:

* the closure of the union, over `(s, t) ∈ S`, of the entrance/exit pairs
  `splitGluingPairs ε r₀ (g (s, ·)) (k (t, ·))` of unbroken orbits is homeomorphic to
  `[0, r₀] × S`, with the gluing coordinate `‖y‖ / ε` of the entrance point as first inverse
  coordinate, a positive gluing coordinate paired with `(s, t)` giving a pair of the member
  `(s, t)`, and the broken pairs `((g (s, 0), 0), (0, k (t, 0)))` at gluing coordinate zero;
* these broken pairs are the entry point of the orbit through a point of the slice `c = s` of `ψ`
  on the stable set and the exit point of the orbit through a point of the slice `d = t` of `χ`
  on the unstable set;
* every pair of the member `(s, t)` consists of the entry point of the orbit through `ψ z` for
  some `z ∈ U` with `c z = s` and the exit point of the orbit through `χ z'` for some `z' ∈ V`
  with `d z' = t`;
* conversely, for `z` and `z'` near `0`, the parameter `(c z, d z')` lies in `S`, and if the orbit
  through `ψ z` enters the box off the stable set and leaves it at the exit point of the orbit
  through `χ z'`, then this pair of entry and exit points is a pair of the member `(c z, d z')`.

So, near a broken orbit, the orbits running from the first family of discs to the second form,
once the broken orbits are added, a product of `[0, r₀]` with the parameter ball. This is the
local model of a collar along the once-broken trajectories of a compactified space of trajectories,
in which `s` and `t` parametrize the trajectories into and out of the middle critical point. -/
theorem exists_homeomorph_closure_biUnion_splitGluingPairs_of_hasStrictFDerivAt
    {G P Q : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [ProperSpace Q]
    {χ : G → WithLp 2 (Eₛ × Eᵤ)} {χ' : G →L[ℝ] WithLp 2 (Eₛ × Eᵤ)} {V : Set G}
    {c : F → P} {c' : F →L[ℝ] P} {d : G → Q} {d' : G →L[ℝ] Q} {x₀ : Eₛ} {y₀ : Eᵤ}
    (hψ : HasStrictFDerivAt ψ ψ' 0) (hc : HasStrictFDerivAt c c' 0)
    (hψ' : (c'.prod (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ')).IsInvertible)
    (hψ₀ : ψ 0 = WithLp.toLp 2 (x₀, 0)) (hc₀ : c 0 = 0) (hx₀ : ‖x₀‖ = ε)
    (hχ : HasStrictFDerivAt χ χ' 0) (hd : HasStrictFDerivAt d d' 0)
    (hχ' : (d'.prod (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L χ')).IsInvertible)
    (hχ₀ : χ 0 = WithLp.toLp 2 (0, y₀)) (hd₀ : d 0 = 0) (hy₀ : ‖y₀‖ = ε)
    (hε : 0 < ε) (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0)
    (hψU : ∀ z ∈ U, ∀ z' ∈ U, splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) =
      splitQuadraticFlow (splitEntryTime ε (ψ z')) (ψ z') → c z = c z')
    (hχV : ∀ z ∈ V, ∀ z' ∈ V, splitQuadraticFlow (splitExitTime ε (χ z)) (χ z) =
      splitQuadraticFlow (splitExitTime ε (χ z')) (χ z') → d z = d z') :
    ∃ (r₀ ρ : ℝ) (hr₀ : 0 < r₀) (_ : 0 < ρ) (g : P × Eᵤ → Eₛ) (k : Q × Eₛ → Eᵤ),
      g 0 = x₀ ∧ k 0 = y₀ ∧
      (∃ e : (Icc 0 r₀ ×ˢ closedBall (0 : P × Q) ρ : Set (ℝ × (P × Q))) ≃ₜ
          closure (⋃ p ∈ closedBall (0 : P × Q) ρ,
            splitGluingPairs ε r₀ (fun y ↦ g (p.1, y)) (fun x ↦ k (p.2, x))),
        (∀ w, (e.symm w : ℝ × (P × Q)).1 = ‖w.val.1.snd‖ / ε) ∧
        (∀ q : (Icc 0 r₀ ×ˢ closedBall (0 : P × Q) ρ : Set (ℝ × (P × Q))),
          0 < (q : ℝ × (P × Q)).1 → (e q).val ∈ splitGluingPairs ε r₀
            (fun y ↦ g ((q : ℝ × (P × Q)).2.1, y)) (fun x ↦ k ((q : ℝ × (P × Q)).2.2, x))) ∧
        ∀ p (hp : p ∈ closedBall (0 : P × Q) ρ), (e ⟨(0, p), left_mem_Icc.2 hr₀.le, hp⟩).val =
          (WithLp.toLp 2 (g (p.1, 0), 0), WithLp.toLp 2 (0, k (p.2, 0)))) ∧
      closure (⋃ p ∈ closedBall (0 : P × Q) ρ,
          splitGluingPairs ε r₀ (fun y ↦ g (p.1, y)) (fun x ↦ k (p.2, x))) =
        (⋃ p ∈ closedBall (0 : P × Q) ρ,
          splitGluingPairs ε r₀ (fun y ↦ g (p.1, y)) (fun x ↦ k (p.2, x))) ∪
        (fun p ↦ (WithLp.toLp 2 (g (p.1, 0), 0), WithLp.toLp 2 (0, k (p.2, 0)))) ''
          closedBall (0 : P × Q) ρ ∧
      (∀ p ∈ closedBall (0 : P × Q) ρ,
        (∃ z ∈ U, c z = p.1 ∧
          splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = WithLp.toLp 2 (g (p.1, 0), 0)) ∧
        ∃ z ∈ V, d z = p.2 ∧
          splitQuadraticFlow (splitExitTime ε (χ z)) (χ z) = WithLp.toLp 2 (0, k (p.2, 0))) ∧
      (∀ p ∈ closedBall (0 : P × Q) ρ,
        ∀ w ∈ splitGluingPairs ε r₀ (fun y ↦ g (p.1, y)) (fun x ↦ k (p.2, x)),
        (∃ z ∈ U, c z = p.1 ∧ splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = w.1) ∧
        ∃ z ∈ V, d z = p.2 ∧ splitQuadraticFlow (splitExitTime ε (χ z)) (χ z) = w.2) ∧
      ∀ᶠ q : F × G in 𝓝 (0, 0), (c q.1, d q.2) ∈ closedBall (0 : P × Q) ρ ∧
        ((splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)).snd ≠ 0 →
          splitPassage ε (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)) =
            splitQuadraticFlow (splitExitTime ε (χ q.2)) (χ q.2) →
          (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1),
            splitQuadraticFlow (splitExitTime ε (χ q.2)) (χ q.2)) ∈
            splitGluingPairs ε r₀ (fun y ↦ g (c q.1, y)) (fun x ↦ k (d q.2, x))) := by
  -- The expanding factor is a factor of `P × Eᵤ`, which is isomorphic to the complete space `F`.
  have : CompleteSpace Eᵤ := by
    obtain ⟨L, -⟩ := hψ'
    have : CompleteSpace (P × Eᵤ) :=
      (completeSpace_congr (e := L.toEquiv.symm) L.symm.isUniformEmbedding).2 inferInstance
    exact .snd_of_prod (α := P)
  obtain ⟨δ₁, hδ₁, K₁, g, hg, hg₀, hgpts, hgexh⟩ :=
    exists_splitQuadraticFlow_splitEntryTime_eq_graph_prod hψ hc hψ' hψ₀ hc₀ hx₀ hε hU
  obtain ⟨δ₂, hδ₂, K₂, k, hk, hk₀, hkpts, hkexh⟩ :=
    exists_splitQuadraticFlow_splitExitTime_eq_graph_prod hχ hd hχ' hχ₀ hd₀ hy₀ hε hV
  -- Entry and exit points determine the parameter, so distinct parameters have disjoint traces.
  obtain ⟨r₀, ρ, hr₀, hr₀₁, hρ, hmem₁, hmem₂, he, hcl⟩ :=
    exists_homeomorph_closure_biUnion_splitGluingPairs_prod hg (fun q hq ↦ (hgpts q hq).1) hk
      (fun q hq ↦ (hkpts q hq).1)
      (fun s s' y hs hs' hgy ↦ by
        obtain ⟨-, z, hzU, rfl, hz⟩ := hgpts _ hs
        obtain ⟨-, z', hz'U, rfl, hz'⟩ := hgpts _ hs'
        exact hψU z hzU z' hz'U (by rw [hz, hz', hgy]))
      (fun t t' x ht ht' hkx ↦ by
        obtain ⟨-, z, hzV, rfl, hz⟩ := hkpts _ ht
        obtain ⟨-, z', hz'V, rfl, hz'⟩ := hkpts _ ht'
        exact hχV z hzV z' hz'V (by rw [hz, hz', hkx]))
      hδ₁ hδ₂ hε
  refine ⟨r₀, ρ, hr₀, hρ, g, k, hg₀, hk₀, he, hcl, fun p hp ↦ ?_, fun p hp w hw ↦ ?_, ?_⟩
  · -- The broken pairs are the traces at the origin of the expanding and contracting factors.
    obtain ⟨-, z, hzU, hzc, hz⟩ := hgpts _ (hmem₁ p hp (mem_closedBall_self (by positivity)))
    obtain ⟨-, z', hz'V, hz'd, hz'⟩ := hkpts _ (hmem₂ p hp (mem_closedBall_self (by positivity)))
    exact ⟨⟨z, hzU, hzc, hz⟩, z', hz'V, hz'd, hz'⟩
  · obtain ⟨hsrc, hsnd, hfst, hpass, hexit⟩ := mem_splitGluingPairs.1 hw
    have hx : w.2.fst ∈ closedBall (0 : Eₛ) (r₀ * ε) := by
      rwa [mem_closedBall_zero_iff, hpass, norm_fst_splitPassage hsrc]
    obtain ⟨-, z, hzU, hzc, hz⟩ := hgpts _ (hmem₁ p hp (mem_closedBall_zero_iff.2 hsnd))
    obtain ⟨-, z', hz'V, hz'd, hz'⟩ := hkpts _ (hmem₂ p hp hx)
    refine ⟨⟨z, hzU, hzc, hz.trans ?_⟩, z', hz'V, hz'd, hz'.trans ?_⟩ <;>
      apply WithLp.ofLp_injective <;> ext <;> simp [hfst, hexit]
  · -- The entry points of orbits through `ψ z` approach `(x₀, 0)`, and the parameters approach `0`.
    obtain ⟨hfst, hsmall⟩ := eventually_ne_zero_and_norm_rescale_smul_le
      ((WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt)
      ((WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt)
      (by simpa [hψ₀] using hx₀) (by simp [hψ₀]) hε hr₀
    have hcd : ∀ᶠ q : F × G in 𝓝 (0, 0), (c q.1, d q.2) ∈ closedBall (0 : P × Q) ρ := by
      have h := (hc.continuousAt.tendsto.comp (continuous_fst.tendsto (0, 0))).prodMk_nhds
        (hd.continuousAt.tendsto.comp (continuous_snd.tendsto ((0 : F), (0 : G))))
      rw [hc₀, hd₀, Prod.mk_zero_zero] at h
      exact h (closedBall_mem_nhds _ hρ)
    refine (hcd.and ((hgexh.and (hfst.and hsmall)).prod_nhds hkexh)).mono ?_
    rintro ⟨z, z'⟩ ⟨hS, ⟨hzg, hz₀, hzs⟩, hz'k⟩
    refine ⟨hS, fun hne hpass ↦ mem_splitGluingPairs_splitQuadraticFlow_splitEntryTime hε hr₀₁
      hz₀ hne (by rwa [splitQuadraticFlow_splitEntryTime hε hz₀]) hzg hpass.symm hz'k⟩

/-- **Gluing through transverse discs.** Let `ψ` be a disc through the broken entrance point
`(x₀, 0)` transverse to the stable set, and `χ` a disc through the broken exit point `(0, y₀)`
transverse to the unstable set, as in the trivial-parameter case of
`TauCeti.exists_splitQuadraticFlow_splitEntryTime_eq_graph_prod` and
`TauCeti.exists_splitQuadraticFlow_splitExitTime_eq_graph_prod`. Then there are a radius `r₀ > 0`
and graphs `g`, `k` in the entrance and exit faces such that:

* the closure of the entrance/exit pairs `splitGluingPairs ε r₀ g k` of unbroken orbits is a
  closed interval, with the gluing coordinate `‖y‖ / ε` of the entrance point as inverse
  coordinate and the broken pair `((x₀, 0), (0, y₀))` at parameter zero, and this broken pair is
  the only point the closure adds;
* every such pair consists of the entry point of the orbit through `ψ z` for some `z ∈ U` and the
  exit point of the orbit through `χ z'` for some `z' ∈ V`;
* conversely, for `z` and `z'` near `0`, if the orbit through `ψ z` enters the box off the stable
  set and leaves it at the exit point of the orbit through `χ z'`, then this pair of entry and
  exit points is one of these pairs.

So, near the broken orbit, the orbits running from the first disc to the second form a half-open
arc whose closure adds exactly the broken orbit. This is the case of trivial parameters in
`TauCeti.exists_homeomorph_closure_biUnion_splitGluingPairs_of_hasStrictFDerivAt`. -/
theorem exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {χ : G → WithLp 2 (Eₛ × Eᵤ)} {χ' : G →L[ℝ] WithLp 2 (Eₛ × Eᵤ)} {V : Set G}
    {x₀ : Eₛ} {y₀ : Eᵤ}
    (hψ : HasStrictFDerivAt ψ ψ' 0) (hψ' : (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ').IsInvertible)
    (hψ₀ : ψ 0 = WithLp.toLp 2 (x₀, 0)) (hx₀ : ‖x₀‖ = ε)
    (hχ : HasStrictFDerivAt χ χ' 0) (hχ' : (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L χ').IsInvertible)
    (hχ₀ : χ 0 = WithLp.toLp 2 (0, y₀)) (hy₀ : ‖y₀‖ = ε)
    (hε : 0 < ε) (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) :
    ∃ (r₀ : ℝ) (hr₀ : 0 < r₀) (g : Eᵤ → Eₛ) (k : Eₛ → Eᵤ),
      (∃ e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitGluingPairs ε r₀ g k),
        (∀ p, (e.symm p : ℝ) = ‖p.val.1.snd‖ / ε) ∧
        (e ⟨0, left_mem_Icc.2 hr₀.le⟩).val =
          (WithLp.toLp 2 (x₀, 0), WithLp.toLp 2 (0, y₀))) ∧
      closure (splitGluingPairs ε r₀ g k) =
        insert (WithLp.toLp 2 (x₀, 0), WithLp.toLp 2 (0, y₀)) (splitGluingPairs ε r₀ g k) ∧
      (∀ p ∈ splitGluingPairs ε r₀ g k,
        (∃ z ∈ U, splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = p.1) ∧
        ∃ z ∈ V, splitQuadraticFlow (splitExitTime ε (χ z)) (χ z) = p.2) ∧
      ∀ᶠ q : F × G in 𝓝 (0, 0),
        (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)).snd ≠ 0 →
        splitPassage ε (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)) =
          splitQuadraticFlow (splitExitTime ε (χ q.2)) (χ q.2) →
        (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1),
          splitQuadraticFlow (splitExitTime ε (χ q.2)) (χ q.2)) ∈ splitGluingPairs ε r₀ g k := by
  -- Take the trivial parameters in `Unit`, for which the parameter ball is a point.
  obtain ⟨r₀, ρ, hr₀, hρ, g, k, hg₀, hk₀, ⟨e, hcoord, -, he₀⟩, hcl, -, hpairs, hev⟩ :=
    exists_homeomorph_closure_biUnion_splitGluingPairs_of_hasStrictFDerivAt
      (P := Unit) (Q := Unit) (c := fun _ ↦ 0) (d := fun _ ↦ 0) hψ (hasStrictFDerivAt_const _ _)
      (ContinuousLinearMap.isInvertible_zero_prod_iff.2 hψ') hψ₀ rfl hx₀ hχ
      (hasStrictFDerivAt_const _ _) (ContinuousLinearMap.isInvertible_zero_prod_iff.2 hχ') hχ₀ rfl
      hy₀ hε hU hV (fun _ _ _ _ _ ↦ rfl) fun _ _ _ _ _ ↦ rfl
  have hbr : ((WithLp.toLp 2 (g ((0 : Unit × Unit).1, 0), 0),
      WithLp.toLp 2 (0, k ((0 : Unit × Unit).2, 0))) : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)) =
      (WithLp.toLp 2 (x₀, 0), WithLp.toLp 2 (0, y₀)) := by
    simp only [Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero, hg₀, hk₀]
  have hS : closedBall (0 : Unit × Unit) ρ = {0} :=
    subsingleton_of_subsingleton.eq_singleton_of_mem (mem_closedBall_self hρ.le)
  have hset : (⋃ p ∈ closedBall (0 : Unit × Unit) ρ,
      splitGluingPairs ε r₀ (fun y ↦ g (p.1, y)) (fun x ↦ k (p.2, x))) =
      splitGluingPairs ε r₀ (fun y ↦ g (0, y)) (fun x ↦ k (0, x)) := by
    rw [hS, biUnion_singleton, Prod.fst_zero, Prod.snd_zero]
  -- Identify `[0, r₀]` with `[0, r₀]` times the one-point parameter ball.
  let i : Icc (0 : ℝ) r₀ ≃ₜ
      (Icc 0 r₀ ×ˢ closedBall (0 : Unit × Unit) ρ : Set (ℝ × (Unit × Unit))) :=
    { toFun r := ⟨(r, 0), r.property, mem_closedBall_self hρ.le⟩
      invFun q := ⟨q.val.1, q.property.1⟩
      left_inv _ := rfl
      right_inv _ := Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨r₀, hr₀, fun y ↦ g (0, y), fun x ↦ k (0, x),
    ⟨(i.trans e).trans (Homeomorph.setCongr (congrArg closure hset)), fun w ↦ hcoord _, ?_⟩,
    ?_, fun w hw ↦ ?_, hev.mono fun q hq ↦ hq.2⟩
  · exact (he₀ 0 (mem_closedBall_self hρ.le)).trans hbr
  · rw [← hset, hcl, hset]
    simp only [hS, image_singleton, hbr, union_singleton]
  · obtain ⟨⟨z, hzU, -, hz⟩, z', hz'V, -, hz'⟩ := hpairs 0 (mem_closedBall_self hρ.le) w hw
    exact ⟨⟨z, hzU, hz⟩, z', hz'V, hz'⟩

end TauCeti
