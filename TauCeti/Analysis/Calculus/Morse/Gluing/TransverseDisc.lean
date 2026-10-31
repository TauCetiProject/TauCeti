/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.Compactification
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.Analysis.Calculus.RadialRescaleGraph

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
(`TauCeti.hasStrictFDerivAt_smul_of_isBigO_sub`), although the faces are not smooth for a
general norm. By the inverse function theorem, near the broken entrance point the entry points
of the orbits through the disc form a Lipschitz graph `y ↦ (g y, y)` in the entrance face
(`TauCeti.exists_lipschitzOnWith_rescale_graph`). The exit face is treated in the same way,
using exit times.

Transversality to the stable set in the usual sense, that the tangent space of the disc and the
stable set together span, means that the derivative of the expanding component of `ψ` is
surjective. A complement of its kernel is then a disc on which it is an isomorphism; for the
unstable manifold of a critical point whose index exceeds by one that of the critical point at the
centre of the box, the kernel is the flow direction.

Feeding both graphs to the local compactification
`TauCeti.exists_homeomorph_closure_splitGluingPairs` shows that, near a broken orbit, the orbits
running from a disc transverse to the stable set to a disc transverse to the unstable set form a
half-open arc whose closure adds exactly the broken orbit.

## Main results

* `TauCeti.exists_splitQuadraticFlow_splitEntryTime_eq_graph`: the entry points of the orbits
  through a disc transverse to the stable set form, near the broken entrance point, a Lipschitz
  graph over the expanding factor in the entrance face, and every entry point of an orbit through
  a nearby point of the disc lies on it.
* `TauCeti.exists_splitQuadraticFlow_splitExitTime_eq_graph`: the same for exit points of the
  orbits through a disc transverse to the unstable set, as a graph over the contracting factor in
  the exit face.
* `TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`: the orbits through
  the box from one transverse disc to the other, near the broken orbit, form a closed interval
  once the broken orbit is added, and these are all such orbits.

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

/-- **Entrance trace of a transverse disc.** Let `ψ` be a disc through the point `(x₀, 0)` of the
stable set on the entrance face `‖x‖ = ε`, strictly differentiable at `0` with the derivative of
its expanding component invertible. Near `(x₀, 0)`, the points where the orbits through the disc
enter the box form a Lipschitz graph `y ↦ (g y, y)` in the entrance face over a closed ball of
the expanding factor, with `g 0 = x₀`: every point of the graph is the entry point of the orbit
through `ψ z` for some `z` in a prescribed neighbourhood `U` of `0`, and conversely, for `z`
near `0`, the entry point of the orbit through `ψ z` lies on the graph.

This is the input `y ↦ (g y, y)` of the gluing theorem
`TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image`. -/
theorem exists_splitQuadraticFlow_splitEntryTime_eq_graph {x₀ : Eₛ}
    (hψ : HasStrictFDerivAt ψ ψ' 0) (hψ' : (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ').IsInvertible)
    (hψ₀ : ψ 0 = WithLp.toLp 2 (x₀, 0)) (hx₀ : ‖x₀‖ = ε) (hε : 0 < ε) (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (g : Eᵤ → Eₛ), LipschitzOnWith K g (closedBall 0 δ) ∧ g 0 = x₀ ∧
      (∀ y ∈ closedBall 0 δ, ‖g y‖ = ε ∧ ∃ z ∈ U,
        splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = WithLp.toLp 2 (g y, y)) ∧
      ∀ᶠ z in 𝓝 0, (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).fst =
        g (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).snd := by
  obtain ⟨L, hL⟩ := hψ'
  have ha := (WithLp.fstL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  have hb := (WithLp.sndL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  rw [← hL] at hb
  obtain ⟨δ, hδ, K, g, hg, hg₀, hpts, hexh⟩ :=
    exists_lipschitzOnWith_rescale_graph ha hb (by simpa [hψ₀] using hx₀) (by simp [hψ₀]) hε hU
  have hfst : ∀ᶠ z in 𝓝 0, (ψ z).fst ≠ 0 :=
    ha.continuousAt.eventually_ne (by simpa [hψ₀, ← norm_pos_iff, hx₀] using hε)
  refine ⟨δ, hδ, K, g, hg, by simpa [hψ₀] using hg₀, fun y hy ↦ ?_, ?_⟩
  · obtain ⟨z, hzU, hz₀, hzg, hzy⟩ := hpts y hy
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz₀ hzg hzy
    have hflow := splitQuadraticFlow_splitEntryTime hε hz₀
    refine ⟨?_, z, hzU, by rw [hflow, hzg, hzy]⟩
    rw [← hzg, norm_smul, Real.norm_of_nonneg (div_pos hε (norm_pos_iff.2 hz₀)).le,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hz₀)]
  · filter_upwards [hexh, hfst] with z hz hz₀
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz
    rw [splitQuadraticFlow_splitEntryTime hε hz₀]
    exact hz

/-- **Exit trace of a transverse disc.** Let `ψ` be a disc through the point `(0, y₀)` of the
unstable set on the exit face `‖y‖ = ε`, strictly differentiable at `0` with the derivative of
its contracting component invertible. Near `(0, y₀)`, the points where the orbits through the
disc leave the box form a Lipschitz graph `x ↦ (x, k x)` in the exit face over a closed ball of
the contracting factor, with `k 0 = y₀`: every point of the graph is the exit point of the orbit
through `ψ z` for some `z` in a prescribed neighbourhood `U` of `0`, and conversely, for `z` near
`0`, the exit point of the orbit through `ψ z` lies on the graph.

This is the input `x ↦ (x, k x)` of the gluing theorem
`TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image`. -/
theorem exists_splitQuadraticFlow_splitExitTime_eq_graph {y₀ : Eᵤ}
    (hψ : HasStrictFDerivAt ψ ψ' 0) (hψ' : (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L ψ').IsInvertible)
    (hψ₀ : ψ 0 = WithLp.toLp 2 (0, y₀)) (hy₀ : ‖y₀‖ = ε) (hε : 0 < ε) (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (k : Eₛ → Eᵤ), LipschitzOnWith K k (closedBall 0 δ) ∧ k 0 = y₀ ∧
      (∀ x ∈ closedBall 0 δ, ‖k x‖ = ε ∧ ∃ z ∈ U,
        splitQuadraticFlow (splitExitTime ε (ψ z)) (ψ z) = WithLp.toLp 2 (x, k x)) ∧
      ∀ᶠ z in 𝓝 0, (splitQuadraticFlow (splitExitTime ε (ψ z)) (ψ z)).snd =
        k (splitQuadraticFlow (splitExitTime ε (ψ z)) (ψ z)).fst := by
  obtain ⟨L, hL⟩ := hψ'
  have ha := (WithLp.sndL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  have hb := (WithLp.fstL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hψ
  rw [← hL] at hb
  obtain ⟨δ, hδ, K, k, hk, hk₀, hpts, hexh⟩ :=
    exists_lipschitzOnWith_rescale_graph ha hb (by simpa [hψ₀] using hy₀) (by simp [hψ₀]) hε hU
  have hsnd : ∀ᶠ z in 𝓝 0, (ψ z).snd ≠ 0 :=
    ha.continuousAt.eventually_ne (by simpa [hψ₀, ← norm_pos_iff, hy₀] using hε)
  refine ⟨δ, hδ, K, k, hk, by simpa [hψ₀] using hk₀, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨z, hzU, hz₀, hzk, hzx⟩ := hpts x hx
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz₀ hzk hzx
    have hflow := splitQuadraticFlow_splitExitTime hε hz₀
    refine ⟨?_, z, hzU, by rw [hflow, hzk, hzx]⟩
    rw [← hzk, norm_smul, Real.norm_of_nonneg (div_pos hε (norm_pos_iff.2 hz₀)).le,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hz₀)]
  · filter_upwards [hexh, hsnd] with z hz hz₀
    simp only [WithLp.fstL_apply, WithLp.sndL_apply] at hz
    rw [splitQuadraticFlow_splitExitTime hε hz₀]
    exact hz

/-- **Gluing through transverse discs.** Let `ψ` be a disc through the broken entrance point
`(x₀, 0)` transverse to the stable set, and `χ` a disc through the broken exit point `(0, y₀)`
transverse to the unstable set, as in `TauCeti.exists_splitQuadraticFlow_splitEntryTime_eq_graph`
and `TauCeti.exists_splitQuadraticFlow_splitExitTime_eq_graph`. Then there are a radius `r₀ > 0`
and graphs `g`, `k` in the entrance and exit faces such that:

* the closure of the entrance/exit pairs `splitGluingPairs ε r₀ g k` of unbroken orbits is a
  closed interval, with the gluing coordinate `‖y‖ / ε` of the entrance point as inverse
  coordinate and the broken pair `((x₀, 0), (0, y₀))` at parameter zero;
* every such pair consists of the entry point of the orbit through `ψ z` for some `z ∈ U` and the
  exit point of the orbit through `χ z'` for some `z' ∈ V`;
* conversely, for `z` and `z'` near `0`, if the orbit through `ψ z` enters the box off the stable
  set and leaves it at the exit point of the orbit through `χ z'`, then this pair of entry and
  exit points is one of these pairs.

So, near the broken orbit, the orbits running from the first disc to the second form a half-open
arc whose closure adds exactly the broken orbit. -/
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
      (∀ p ∈ splitGluingPairs ε r₀ g k,
        (∃ z ∈ U, splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = p.1) ∧
        ∃ z ∈ V, splitQuadraticFlow (splitExitTime ε (χ z)) (χ z) = p.2) ∧
      ∀ᶠ q : F × G in 𝓝 (0, 0),
        (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)).snd ≠ 0 →
        splitPassage ε (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)) =
          splitQuadraticFlow (splitExitTime ε (χ q.2)) (χ q.2) →
        (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1),
          splitQuadraticFlow (splitExitTime ε (χ q.2)) (χ q.2)) ∈ splitGluingPairs ε r₀ g k := by
  -- The expanding factor is isomorphic to the complete parameter space `F`.
  have : CompleteSpace Eᵤ := by
    obtain ⟨L, -⟩ := hψ'
    have hL : IsUniformEmbedding L.toEquiv.symm := L.symm.isUniformEmbedding
    exact (completeSpace_congr hL).2 inferInstance
  obtain ⟨δ₁, hδ₁, K₁, g, hg, hg₀, hgpts, hgexh⟩ :=
    exists_splitQuadraticFlow_splitEntryTime_eq_graph hψ hψ' hψ₀ hx₀ hε hU
  obtain ⟨δ₂, hδ₂, K₂, k, hk, hk₀, hkpts, hkexh⟩ :=
    exists_splitQuadraticFlow_splitExitTime_eq_graph hχ hχ' hχ₀ hy₀ hε hV
  -- Choose the gluing radius inside both graph domains and below the contraction threshold.
  set r₀ : ℝ := min 1 (min (min δ₁ δ₂ / ε) (1 / ((K₂ : ℝ) * K₁ + 1))) with hr₀def
  have hK₀ : (0 : ℝ) ≤ K₂ * K₁ := by positivity
  have hr₀ : 0 < r₀ := lt_min one_pos (lt_min (div_pos (lt_min hδ₁ hδ₂) hε) (by positivity))
  have hr₀₁ : r₀ ≤ 1 := min_le_left _ _
  have hr₀δ : r₀ * ε ≤ min δ₁ δ₂ :=
    (le_div_iff₀ hε).1 ((min_le_right _ _).trans (min_le_left _ _))
  have hball₁ : closedBall (0 : Eᵤ) (r₀ * ε) ⊆ closedBall 0 δ₁ :=
    closedBall_subset_closedBall (hr₀δ.trans (min_le_left _ _))
  have hball₂ : closedBall (0 : Eₛ) (r₀ * ε) ⊆ closedBall 0 δ₂ :=
    closedBall_subset_closedBall (hr₀δ.trans (min_le_right _ _))
  have hK : (K₂ : ℝ) * K₁ * r₀ ^ 2 < 1 := by
    have hr₀K : r₀ ≤ 1 / ((K₂ : ℝ) * K₁ + 1) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hr₀K
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_of_le_one hr₀.le hr₀₁ two_ne_zero) hK₀]
  have hgε : ∀ y ∈ closedBall (0 : Eᵤ) (r₀ * ε), ‖g y‖ = ε := fun y hy ↦ (hgpts y (hball₁ hy)).1
  have hkε : ∀ x ∈ closedBall (0 : Eₛ) (r₀ * ε), ‖k x‖ = ε := fun x hx ↦ (hkpts x (hball₂ hx)).1
  obtain ⟨e, he, he₀⟩ := exists_homeomorph_closure_splitGluingPairs (hg.mono hball₁) hgε
    (hk.mono hball₂) hkε hε hr₀ hr₀₁ hK
  refine ⟨r₀, hr₀, g, k, ⟨e, he, by rw [he₀, hg₀, hk₀]⟩, ?_, ?_⟩
  · intro p hp
    obtain ⟨hsrc, hsnd, hfst, hpass, hexit⟩ := mem_splitGluingPairs.1 hp
    have hy : p.1.snd ∈ closedBall (0 : Eᵤ) δ₁ := hball₁ (mem_closedBall_zero_iff.2 hsnd)
    have hx : p.2.fst ∈ closedBall (0 : Eₛ) δ₂ := by
      refine hball₂ (mem_closedBall_zero_iff.2 ?_)
      rw [hpass, norm_fst_splitPassage hsrc]
      exact hsnd
    obtain ⟨-, z, hzU, hz⟩ := hgpts _ hy
    obtain ⟨-, z', hz'V, hz'⟩ := hkpts _ hx
    refine ⟨⟨z, hzU, hz.trans ?_⟩, z', hz'V, hz'.trans ?_⟩ <;>
      apply WithLp.ofLp_injective <;> ext <;> simp [hfst, hexit]
  · -- The entry points of orbits through `ψ z` approach `(x₀, 0)`, hence eventually lie in the
    -- part of the entrance graph used by the gluing pairs.
    have hfst : ∀ᶠ z in 𝓝 (0 : F), (ψ z).fst ≠ 0 :=
      ((WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt).eventually_ne
        (by simpa [hψ₀, ← norm_pos_iff, hx₀] using hε)
    have hcont : ContinuousAt (fun z ↦ (‖(ψ z).fst‖ / ε) • (ψ z).snd) 0 :=
      ((((WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt).norm.div_const
        ε).smul ((WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt))
    have hsmall : ∀ᶠ z in 𝓝 (0 : F), ‖(‖(ψ z).fst‖ / ε) • (ψ z).snd‖ ≤ r₀ * ε := by
      have h := hcont.tendsto
      simp only [hψ₀] at h
      simp at h
      simpa [dist_zero_right] using
        h.eventually (closedBall_mem_nhds 0 (by positivity : 0 < r₀ * ε))
    refine ((hgexh.and (hfst.and hsmall)).prod_nhds hkexh).mono ?_
    rintro ⟨z, z'⟩ ⟨⟨hzg, hz₀, hzs⟩, hz'k⟩ hne hpass
    have hflow := splitQuadraticFlow_splitEntryTime hε hz₀
    have hsnd : ‖(splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).snd‖ ≤ r₀ * ε := by
      rw [hflow]
      exact hzs
    exact mem_splitGluingPairs.2 ⟨mem_splitPassage_source.2
      ⟨norm_fst_splitQuadraticFlow_splitEntryTime hε hz₀, hne,
        hsnd.trans (mul_le_of_le_one_left hε.le hr₀₁)⟩, hsnd, hzg, hpass.symm, hz'k⟩

end TauCeti
