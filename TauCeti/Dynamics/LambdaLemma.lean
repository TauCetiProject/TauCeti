/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The λ-lemma for linear hyperbolic maps

Let `L = S × T` be a block-diagonal linear map of a product `Eₛ × Eᵤ`, contracting on the stable
factor `Eₛ` and expanding on the unstable factor `Eᵤ`. The **λ-lemma** (inclination lemma) says
that iterating `L` on a disc which crosses the stable factor transversally produces discs that
converge in `C¹`, and in fact in `C^n`, to the unstable factor.

This file proves it for any family `S t × T t` along a filter `l`, where `S t : Eₛ →L Eₛ` and
`T t : Eᵤ ≃L Eᵤ` satisfy `‖S t‖ → 0` and `‖(T t)⁻¹‖ → 0`. This covers the iterates of a hyperbolic
linear map (`l = atTop` on `ℕ`) and linear hyperbolic flows such as the split model
`(x, y) ↦ (e^{-t} x, e^t y)` of a nondegenerate critical point (`l = atTop` on `ℝ`), as well as
their time reversals with the roles of the two factors exchanged.

* **Graph transform.** The map `L` sends the graph `{(g w, w)}` of a map `g : Eᵤ → Eₛ` to the graph
  of `v ↦ S (g (T⁻¹ v))`. The `i`-th derivative of this map at `v` is bounded by
  `‖S‖ ‖T⁻¹‖ ^ i` times the `i`-th derivative of `g` at `T⁻¹ v`. If `g` is `C^n` at `0`, then on
  any ball `‖v‖ < R` the points `T⁻¹ v` eventually stay near `0`, where the derivatives of `g` of
  order at most `n` are bounded; so the transformed maps and their derivatives up to order `n`
  tend to zero uniformly on that ball
  (`TauCeti.tendstoUniformlyOn_iteratedFDeriv_comp_comp_symm`).
* **Transverse discs are graphs.** A disc `z ↦ (a z, b z)`, `C^n` at `z₀`, whose unstable
  component `b` has invertible derivative at `z₀` is, near `z₀`, the graph of the map `a ∘ b⁻¹`,
  which is `C^n` at `b z₀`, by the inverse function theorem
  (`TauCeti.exists_contDiffAt_graph_of_isInvertible`). Transversality to the stable factor at a
  point of the disc with `b z₀ = 0` means exactly that the derivative of `b` at `z₀` is onto; for a
  disc of the dimension of `Eᵤ` it is then invertible.
* **The λ-lemma.** Combining the two, for every neighbourhood `U` of `z₀` in the source of the
  disc and every radius `R`, the image under `S t × T t` of the part of the disc over `U` eventually
  contains the graph of a map on the ball `‖v‖ < R` of the unstable factor, and these maps tend to
  zero in `C^n` uniformly on the ball
  (`TauCeti.exists_graph_tendstoUniformlyOn_iteratedFDeriv`).

For a vector field that is linear in a chart near a hyperbolic zero this is the λ-lemma in that
chart. In Morse theory an adapted pseudo-gradient is linear in Morse charts near its critical
points, so this is the form in which the λ-lemma applies to it. The λ-lemma for a general
nonlinear field at a hyperbolic zero is not proved here; it needs nonlinear graph-transform
estimates, since such a field need not be `C¹`-linearizable.

## Main results

* `TauCeti.eventually_contDiffOn_comp_comp_symm`: the transformed graph maps are eventually `C^k`
  on any ball, for `k ≤ n`.
* `TauCeti.tendstoUniformlyOn_iteratedFDeriv_comp_comp_symm`: their derivatives of order at most
  `n` tend to zero uniformly on any ball.
* `TauCeti.tendstoUniformlyOn_comp_comp_symm` and
  `TauCeti.tendstoUniformlyOn_fderiv_comp_comp_symm`: the values and the first derivatives, in the
  `C⁰` and `C¹` forms.
* `TauCeti.exists_contDiffAt_graph_of_isInvertible`: a transverse disc is locally a graph over the
  unstable factor.
* `TauCeti.exists_graph_tendstoUniformlyOn_iteratedFDeriv`: **the λ-lemma**.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the λ-lemma).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (pseudo-gradients that are linear near the critical points).
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {ι F Eₛ Eᵤ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ] [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {l : Filter ι} {S : ι → Eₛ →L[ℝ] Eₛ} {T : ι → Eᵤ ≃L[ℝ] Eᵤ} {g : Eᵤ → Eₛ} {n : ℕ∞ω}

/-- **Smoothness of the transformed graphs.** If `g` is `C^n` at `0` and `‖(T t)⁻¹‖ → 0`, then for
every `k ≤ n` the maps `v ↦ S t (g ((T t)⁻¹ v))`, whose graphs are the images of the graph of `g`
under `S t × T t`, are eventually `C^k` on the ball of radius `R`. -/
theorem eventually_contDiffOn_comp_comp_symm
    (hT : Tendsto (fun t ↦ ‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖) l (𝓝 0)) (hg : ContDiffAt ℝ n g 0)
    {k : ℕ} (hk : k ≤ n) (R : ℝ) :
    ∀ᶠ t in l, ContDiffOn ℝ k (fun v ↦ S t (g ((T t).symm v))) (ball 0 R) := by
  filter_upwards [ContinuousLinearMap.eventually_mapsTo_ball_of_tendsto_opNorm hT
    ((hg.of_le hk).eventually (by simp)) R] with t ht v hv
  exact ((S t).contDiff.contDiffAt.comp v
    ((ht hv).comp v (T t).symm.contDiff.contDiffAt)).contDiffWithinAt

/-- **The graph transform converges to zero in `C^n`.** Let `‖S t‖ → 0` and `‖(T t)⁻¹‖ → 0`
along `l`, and let `g` be `C^n` at `0`. For every `i ≤ n`, the `i`-th derivatives of the maps
`v ↦ S t (g ((T t)⁻¹ v))`, whose graphs are the images of the graph of `g` under `S t × T t`,
tend to zero uniformly on the ball of radius `R`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_comp_comp_symm
    (hS : Tendsto (fun t ↦ ‖S t‖) l (𝓝 0))
    (hT : Tendsto (fun t ↦ ‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖) l (𝓝 0)) (hg : ContDiffAt ℝ n g 0)
    {i : ℕ} (hi : i ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun t v ↦ iteratedFDeriv ℝ i (fun v ↦ S t (g ((T t).symm v))) v) 0 l
      (ball 0 R) := by
  have hgi : ContDiffAt ℝ i g 0 := hg.of_le hi
  -- The `i`-th derivative at `v` is bounded by `‖S t‖ ‖(T t)⁻¹‖ ^ i` times the `i`-th derivative
  -- of `g` at `(T t)⁻¹ v`, which eventually lies in a neighbourhood of `0` where that derivative
  -- is bounded.
  -- Near `0`, `g` is `C^i` and its `i`-th derivative is bounded by `C`.
  set C := ‖iteratedFDeriv ℝ i g 0‖ + 1
  have hnear : ∀ᶠ w in 𝓝 (0 : Eᵤ), ContDiffAt ℝ i g w ∧ ‖iteratedFDeriv ℝ i g w‖ < C :=
    (hgi.eventually (by simp)).and
      ((hgi.continuousAt_iteratedFDeriv le_rfl).norm.eventually (gt_mem_nhds (lt_add_one _)))
  have hbound : Tendsto (fun t ↦ ‖S t‖ * ‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖ ^ i * C) l (𝓝 0) := by
    simpa using (hS.mul (hT.pow i)).mul_const C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ContinuousLinearMap.eventually_mapsTo_ball_of_tendsto_opNorm hT hnear R,
    hbound.eventually (gt_mem_nhds hε)] with t ht htε v hv
  obtain ⟨hgv, hgvC⟩ := ht hv
  rw [ContinuousLinearEquiv.coe_coe] at hgv hgvC
  rw [Pi.zero_apply, dist_zero_left]
  calc ‖iteratedFDeriv ℝ i (fun v ↦ S t (g ((T t).symm v))) v‖
      ≤ ‖S t‖ * ‖iteratedFDeriv ℝ i (g ∘ (T t).symm) v‖ :=
        (S t).norm_iteratedFDeriv_comp_left (hgv.comp v (T t).symm.contDiff.contDiffAt) le_rfl
    _ ≤ ‖S t‖ * (‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖ ^ i * ‖iteratedFDeriv ℝ i g ((T t).symm v)‖) := by
        gcongr
        exact (T t).symm.norm_iteratedFDeriv_comp_right_le g v i
    _ ≤ ‖S t‖ * (‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖ ^ i * C) := by gcongr
    _ < ε := by rwa [← mul_assoc]

/-- **The graph transform converges to zero uniformly.** If `‖S t‖ → 0`, `‖(T t)⁻¹‖ → 0` and `g`
is continuous at `0`, the maps `v ↦ S t (g ((T t)⁻¹ v))` tend to zero uniformly on the ball of
radius `R`. This is the `C⁰` part of the λ-lemma. -/
theorem tendstoUniformlyOn_comp_comp_symm
    (hS : Tendsto (fun t ↦ ‖S t‖) l (𝓝 0))
    (hT : Tendsto (fun t ↦ ‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖) l (𝓝 0)) (hg : ContinuousAt g 0)
    (R : ℝ) :
    TendstoUniformlyOn (fun t v ↦ S t (g ((T t).symm v))) 0 l (ball 0 R) := by
  -- Near `0`, `g` is bounded by `C`.
  set C := ‖g 0‖ + 1
  have hbound : Tendsto (fun t ↦ ‖S t‖ * C) l (𝓝 0) := by simpa using hS.mul_const C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ContinuousLinearMap.eventually_mapsTo_ball_of_tendsto_opNorm hT
    (hg.norm.eventually (gt_mem_nhds (lt_add_one _))) R,
    hbound.eventually (gt_mem_nhds hε)] with t ht htε v hv
  rw [Pi.zero_apply, dist_zero_left]
  calc ‖S t (g ((T t).symm v))‖ ≤ ‖S t‖ * ‖g ((T t).symm v)‖ := (S t).le_opNorm _
    _ ≤ ‖S t‖ * C := by gcongr; exact (ht hv).le
    _ < ε := htε

/-- **The derivatives of the graph transform converge to zero uniformly.** If `‖S t‖ → 0`,
`‖(T t)⁻¹‖ → 0` and `g` is `C¹` at `0`, the derivatives of the maps `v ↦ S t (g ((T t)⁻¹ v))`
tend to zero uniformly on the ball of radius `R`. This is the `C¹` part of the λ-lemma. -/
theorem tendstoUniformlyOn_fderiv_comp_comp_symm
    (hS : Tendsto (fun t ↦ ‖S t‖) l (𝓝 0))
    (hT : Tendsto (fun t ↦ ‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖) l (𝓝 0)) (hg : ContDiffAt ℝ 1 g 0)
    (R : ℝ) :
    TendstoUniformlyOn (fun t v ↦ fderiv ℝ (fun v ↦ S t (g ((T t).symm v))) v) 0 l
      (ball 0 R) := by
  have h := tendstoUniformlyOn_iteratedFDeriv_comp_comp_symm hS hT hg (i := 1) le_rfl R
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with t ht v hv
  simpa [dist_zero_left, norm_iteratedFDeriv_one] using ht v hv

/-- **A transverse disc is a graph over the unstable factor.** Let `z ↦ (a z, b z)` be a disc,
`C^n` at `z₀` with `n ≥ 1`, whose second component `b` has invertible derivative at `z₀`. Then
there is a map `g`, `C^n` at `b z₀`, with `g (b z₀) = a z₀` whose graph near `b z₀` is covered
by the part of the disc over any prescribed neighbourhood `U` of `z₀`: every `w` near `b z₀` is
`b z` for some `z ∈ U` with `a z = g w`.

The map `g` is `a ∘ b⁻¹` for the local inverse of `b` given by the inverse function theorem. -/
theorem exists_contDiffAt_graph_of_isInvertible [CompleteSpace F] {a : F → Eₛ} {b : F → Eᵤ}
    {b' : F →L[ℝ] Eᵤ} {z₀ : F} (ha : ContDiffAt ℝ n a z₀) (hb : ContDiffAt ℝ n b z₀)
    (hb' : HasFDerivAt b b' z₀) (hb'i : b'.IsInvertible) (hn : n ≠ 0) {U : Set F}
    (hU : U ∈ 𝓝 z₀) :
    ∃ g : Eᵤ → Eₛ, ContDiffAt ℝ n g (b z₀) ∧ g (b z₀) = a z₀ ∧
      ∀ᶠ w in 𝓝 (b z₀), ∃ z ∈ U, a z = g w ∧ b z = w := by
  obtain ⟨e, rfl⟩ := hb'i
  have hσ₀ := hb.localInverse_apply_image hb' hn
  have hσ := hb.to_localInverse hb' hn
  refine ⟨a ∘ hb.localInverse hb' hn, (hσ₀ ▸ ha).comp _ hσ, by simp [hσ₀], ?_⟩
  filter_upwards [(hb.hasStrictFDerivAt hb' hn).eventually_right_inverse,
    hσ.continuousAt.preimage_mem_nhds (hσ₀ ▸ hU)] with w hw hwU
  exact ⟨_, hwU, rfl, hw⟩

/-- **The λ-lemma for linear hyperbolic maps.** Let `‖S t‖ → 0` and `‖(T t)⁻¹‖ → 0` along `l`,
and let `z ↦ (a z, b z)` be a disc, `C^n` at `z₀` with `n ≥ 1`, through the point `(a z₀, 0)` of
the stable factor, transverse to it in the sense that the derivative of `b` at `z₀` is invertible.
Fix a neighbourhood `U` of `z₀` and a radius `R`. Then there is a map `g`, `C^n` at `0`, with
`g 0 = a z₀` such that:

* eventually along `l`, the image of the part of the disc over `U` under `S t × T t` contains the
  graph of `v ↦ S t (g ((T t)⁻¹ v))` over the ball `‖v‖ < R` of the unstable factor;
* these maps tend to zero in `C^n` uniformly on that ball: their derivatives of each order
  `i ≤ n` tend to zero uniformly.

So the images of the disc contain discs converging in `C^n` to the ball of radius `R` of the
unstable factor. -/
theorem exists_graph_tendstoUniformlyOn_iteratedFDeriv [CompleteSpace F]
    (hS : Tendsto (fun t ↦ ‖S t‖) l (𝓝 0))
    (hT : Tendsto (fun t ↦ ‖((T t).symm : Eᵤ →L[ℝ] Eᵤ)‖) l (𝓝 0)) {a : F → Eₛ} {b : F → Eᵤ}
    {b' : F →L[ℝ] Eᵤ} {z₀ : F} (ha : ContDiffAt ℝ n a z₀) (hb : ContDiffAt ℝ n b z₀)
    (hb' : HasFDerivAt b b' z₀) (hb'i : b'.IsInvertible) (hb₀ : b z₀ = 0) (hn : n ≠ 0)
    {U : Set F} (hU : U ∈ 𝓝 z₀) (R : ℝ) :
    ∃ g : Eᵤ → Eₛ, ContDiffAt ℝ n g 0 ∧ g 0 = a z₀ ∧
      (∀ᶠ t in l, ∀ v ∈ ball (0 : Eᵤ) R, ∃ z ∈ U,
        S t (a z) = S t (g ((T t).symm v)) ∧ T t (b z) = v) ∧
      ∀ i : ℕ, i ≤ n → TendstoUniformlyOn
        (fun t v ↦ iteratedFDeriv ℝ i (fun v ↦ S t (g ((T t).symm v))) v) 0 l (ball 0 R) := by
  obtain ⟨g, hg, hg₀, hgraph⟩ := exists_contDiffAt_graph_of_isInvertible ha hb hb' hb'i hn hU
  rw [hb₀] at hg hg₀ hgraph
  refine ⟨g, hg, hg₀, ?_, fun i hi ↦ tendstoUniformlyOn_iteratedFDeriv_comp_comp_symm hS hT hg hi R⟩
  filter_upwards [ContinuousLinearMap.eventually_mapsTo_ball_of_tendsto_opNorm hT hgraph R]
    with t ht v hv
  obtain ⟨z, hzU, haz, hbz⟩ := ht hv
  rw [ContinuousLinearEquiv.coe_coe] at haz hbz
  exact ⟨z, hzU, by rw [haz], by rw [hbz, ContinuousLinearEquiv.apply_symm_apply]⟩

end TauCeti
