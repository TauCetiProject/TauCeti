/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Locally uniform convergence of metric-valued functions on compact sets

A complement to Mathlib's `TendstoLocallyUniformlyOn`: if functions `F k` with values in a
pseudo-metric space converge to `u` locally uniformly on `s`, then for every compact `K ⊆ s` and
every `ε > 0`, eventually `dist (F k x) (u x) < ε` for all `x ∈ K`. For real-valued functions,
`Real.dist_eq` turns this into the bound `|F k x - u x| < ε`.

On a product, locally uniform convergence on `U` gives uniform convergence of the slices
`t ↦ F k (a, t)` on every compact set `K` with `{a} × K ⊆ U`
(`TendstoLocallyUniformlyOn.tendstoUniformlyOn_slice_right`).

Conversely, if the values of `F m` at one point of `s` have norms tending to infinity, then no
subsequence of `F` converges locally uniformly on `s`
(`TauCeti.not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop`), while dividing a fixed
continuous function by `m` gives a sequence tending to `0` locally uniformly
(`TauCeti.tendstoLocallyUniformly_div_natCast`).

On an open set on which the limit is continuous, locally uniform convergence is the same as
continuous convergence at every point of the set
(`IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto_of_continuousOn`).

A family `Φ : α → δ → γ` that is jointly continuous at every point of `α × {q}` converges locally
uniformly in its first argument as the second tends to `q`
(`TauCeti.tendstoLocallyUniformly_of_forall_continuousAt`), with no local compactness assumption
on `α` or `δ`. For a flow, this gives locally uniform convergence of orbits from convergent
initial points.

Locally uniform limits on open sets glue: if `F` converges locally uniformly on each open set
`G i` of a family, with values in a Hausdorff space, the limits agree on the overlaps and `F`
converges locally uniformly on the union to the glued limit
(`TauCeti.exists_tendstoLocallyUniformlyOn_iUnion`). This assembles a limit on a whole domain from
limits on the windows of an exhaustion.
-/

public section

open Filter Set Topology Uniformity

/-- **Locally uniform convergence to a continuous limit is continuous convergence.** On an open
set on which the limit is continuous, `F i → f` locally uniformly exactly when `F i y → f x` as
`i → l` and `y → x` jointly, for every `x` in the set. -/
theorem IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto_of_continuousOn {ι α β : Type*}
    [TopologicalSpace α] [UniformSpace β] {F : ι → α → β} {f : α → β} {l : Filter ι}
    {s : Set α} (hs : IsOpen s) (hf : ContinuousOn f s) :
    TendstoLocallyUniformlyOn F f l s ↔
      ∀ x ∈ s, Tendsto (fun p : ι × α ↦ F p.1 p.2) (l ×ˢ 𝓝 x) (𝓝 (f x)) := by
  rw [hs.tendstoLocallyUniformlyOn_iff_forall_tendsto]
  refine forall₂_congr fun x hx ↦ ?_
  have hfx : Tendsto (fun p : ι × α ↦ f p.2) (l ×ˢ 𝓝 x) (𝓝 (f x)) :=
    ((hf.continuousAt (hs.mem_nhds hx)).tendsto).comp tendsto_snd
  refine ⟨fun h ↦ hfx.congr_uniformity h, fun h ↦ ?_⟩
  exact (hfx.prodMk_nhds h).mono_right (nhds_le_uniformity (f x))

variable {α β ι : Type*} [TopologicalSpace α] [PseudoMetricSpace β] {l : Filter ι}
  {F : ι → α → β} {u : α → β} {s : Set α}

/-- If functions `F k` converge to `u` locally uniformly on `s`, then for every compact `K ⊆ s`
and every `ε > 0`, eventually `dist (F k x) (u x) < ε` for all `x ∈ K`. -/
theorem TendstoLocallyUniformlyOn.eventually_forall_dist_lt
    (hFu : TendstoLocallyUniformlyOn F u l s) {K : Set α} (hK : IsCompact K) (hKs : K ⊆ s)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in l, ∀ x ∈ K, dist (F k x) (u x) < ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hFu.mono hKs)) ε hε]
    with k hk x hx
  rw [dist_comm]
  exact hk x hx

/-- If functions `F k` on a product converge to `u` locally uniformly on `U`, then their slices
`t ↦ F k (a, t)` converge uniformly on every compact set `K` with `{a} × K ⊆ U`. -/
theorem TendstoLocallyUniformlyOn.tendstoUniformlyOn_slice_right {δ γ : Type*}
    [TopologicalSpace δ] [UniformSpace γ] {F : ι → α × δ → γ} {u : α × δ → γ}
    {U : Set (α × δ)} (hFu : TendstoLocallyUniformlyOn F u l U) {a : α} {K : Set δ}
    (hK : IsCompact K) (hKU : ∀ t ∈ K, (a, t) ∈ U) :
    TendstoUniformlyOn (fun k t ↦ F k (a, t)) (fun t ↦ u (a, t)) l K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    (hFu.comp (fun t ↦ (a, t)) hKU (by fun_prop))

namespace TauCeti

/-- If the values of `F m` at a point `z ∈ s` have norms tending to infinity, then no
subsequence of `F` converges locally uniformly on `s`, since it would converge at `z`. -/
theorem not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop {E : Type*}
    [SeminormedAddCommGroup E] {F : ℕ → α → E} {z : α} (hz : z ∈ s)
    (hF : Tendsto (fun m ↦ ‖F m z‖) atTop atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : α → E) :
    ¬ TendstoLocallyUniformlyOn (fun m ↦ F (φ m)) g atTop s := by
  intro h
  exact not_tendsto_nhds_of_tendsto_atTop (hF.comp hφ.tendsto_atTop) ‖g z‖
    ((h.tendsto_at hz).norm)

/-- For a continuous `g` with values in `ℝ` or `ℂ`, the maps `z ↦ g z / m` tend to `0` locally
uniformly. -/
theorem tendstoLocallyUniformly_div_natCast {𝕜 : Type*} [RCLike 𝕜] {g : α → 𝕜}
    (hg : Continuous g) :
    TendstoLocallyUniformly (fun (m : ℕ) z ↦ g z / m) (fun _ ↦ 0) atTop := by
  have hinv : Tendsto (fun m : ℕ ↦ (m : 𝕜)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hg' : TendstoLocallyUniformly (fun (_ : ℕ) z ↦ g z) g atTop :=
    (tendstoUniformly_iff_tendsto.2
      (tendsto_diag_uniformity (fun q : ℕ × α ↦ g q.2) _)).tendstoLocallyUniformly
  simpa [div_eq_mul_inv] using
    hg'.fun_mul₀ hinv.tendstoUniformly_const.tendstoLocallyUniformly hg continuous_const

/-- A family `Φ` jointly continuous at every point of `α × {q}` converges locally uniformly to
`fun x ↦ Φ x q` along any parameter family `p` tending to `q`. -/
theorem tendstoLocallyUniformly_of_forall_continuousAt {δ γ : Type*} [TopologicalSpace δ]
    [UniformSpace γ] {Φ : α → δ → γ} {q : δ} (hΦ : ∀ x, ContinuousAt (Function.uncurry Φ) (x, q))
    {p : ι → δ} (hp : Tendsto p l (𝓝 q)) :
    TendstoLocallyUniformly (fun i x ↦ Φ x (p i)) (fun x ↦ Φ x q) l := by
  refine tendstoLocallyUniformly_iff_forall_tendsto.mpr fun x ↦ ?_
  have hx : Tendsto (fun y : ι × α ↦ y.2) (l ×ˢ 𝓝 x) (𝓝 x) := tendsto_snd
  have hlim := (hΦ x).tendsto.comp (hx.prodMk_nhds tendsto_const_nhds)
  have hfam := (hΦ x).tendsto.comp (hx.prodMk_nhds (hp.comp tendsto_fst))
  exact (hlim.prodMk_nhds hfam).mono_right (nhds_le_uniformity _)

omit [PseudoMetricSpace β] in
/-- **Gluing locally uniform limits.** If `F` converges locally uniformly to `v i` on each of the
open sets `G i`, with values in a Hausdorff uniform space, then it converges locally uniformly on
their union to one function, which agrees with every `v i` on `G i`. -/
theorem exists_tendstoLocallyUniformlyOn_iUnion [UniformSpace β] [T2Space β] [l.NeBot]
    {ι' : Type*} [Nonempty ι'] {G : ι' → Set α} (hG : ∀ i, IsOpen (G i)) {v : ι' → α → β}
    (h : ∀ i, TendstoLocallyUniformlyOn F (v i) l (G i)) :
    ∃ w : α → β, (∀ i, EqOn w (v i) (G i)) ∧ TendstoLocallyUniformlyOn F w l (⋃ i, G i) := by
  classical
  -- Limits are unique, so the `v i` agree on the overlaps of the `G i`.
  set w : α → β := fun x ↦ if hx : ∃ i, x ∈ G i then v hx.choose x else v (Classical.arbitrary ι') x
  have hw (i : ι') : EqOn w (v i) (G i) := fun x hx ↦ by
    have hx' : ∃ i, x ∈ G i := ⟨i, hx⟩
    simp only [w, hx', dite_true]
    exact tendsto_nhds_unique ((h _).tendsto_at hx'.choose_spec) ((h i).tendsto_at hx)
  exact ⟨w, hw, tendstoLocallyUniformlyOn_iUnion hG fun i ↦ (h i).congr_right (hw i).symm⟩

end TauCeti
