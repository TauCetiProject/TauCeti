/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
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

Locally uniform convergence along a filter `l` passes to any family of indices tending to `l`,
for instance to a subsequence (`TendstoLocallyUniformlyOn.comp_tendsto`,
`TendstoLocallyUniformly.comp_tendsto`), and a family that does not depend on its index
converges locally uniformly to its constant value (`TauCeti.tendstoLocallyUniformly_const`).
Locally uniform convergence on the whole space gives pointwise convergence
(`TendstoLocallyUniformly.tendsto_at`).

On an open set on which the limit is continuous, locally uniform convergence is the same as
continuous convergence at every point of the set
(`IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto_of_continuousOn`).

A locally uniform limit `w` of maps `e ∘ uᵢ`, for an open partial homeomorphism `e` and maps `uᵢ`
with values in a subset `K` of its source, is read back through `e.symm` when `w` takes values in
`e '' K`: the maps `uᵢ` converge pointwise to the continuous map `e.symm ∘ w`
(`OpenPartialHomeomorph.tendsto_symm_of_tendstoLocallyUniformlyOn`).

A family `Φ : α → δ → γ` that is jointly continuous at every point of `α × {q}` converges locally
uniformly in its first argument as the second tends to `q`
(`TauCeti.tendstoLocallyUniformly_of_forall_continuousAt`), with no local compactness assumption
on `α` or `δ`. For a flow, this gives locally uniform convergence of orbits from convergent
initial points.
-/

public section

open Filter Set Topology Uniformity

/-- Locally uniform convergence along `p` passes to any filter `q` that `g` maps into `p`; for
instance, from a sequence to a subsequence. -/
theorem TendstoLocallyUniformlyOn.comp_tendsto {ι ι' α β : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι} {s : Set α} {g : ι' → ι}
    {q : Filter ι'} (h : TendstoLocallyUniformlyOn F f p s) (hg : Tendsto g q p) :
    TendstoLocallyUniformlyOn (F ∘ g) f q s :=
  fun u hu x hx ↦ (h u hu x hx).imp fun _ ⟨ht, hev⟩ ↦ ⟨ht, hg.eventually hev⟩

/-- A locally uniform limit is a pointwise limit: if `F i → f` locally uniformly along `p`, then
`F i a → f a` for every `a`. -/
theorem TendstoLocallyUniformly.tendsto_at {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} (h : TendstoLocallyUniformly F f p) (a : α) :
    Tendsto (fun i ↦ F i a) p (𝓝 (f a)) :=
  (tendstoLocallyUniformlyOn_univ.2 h).tendsto_at (mem_univ a)

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

/-- A locally uniform limit `w` of maps `e ∘ uᵢ`, where the `uᵢ` take values in a set
`K ⊆ e.source` and `w` takes values in `e '' K`, is read back through the inverse of `e`:
`e.symm ∘ w` is continuous with values in `K`, the maps `e ∘ uᵢ` converge to `e ∘ e.symm ∘ w`,
and `uᵢ → e.symm ∘ w` pointwise. -/
theorem OpenPartialHomeomorph.tendsto_symm_of_tendstoLocallyUniformlyOn {M N : Type*}
    [TopologicalSpace M] [UniformSpace N] (e : OpenPartialHomeomorph M N) {K : Set M}
    (hKe : K ⊆ e.source) {ι X : Type*} [TopologicalSpace X] {l : Filter ι} {S : Set X}
    {w : X → N} {u : ι → X → M} (hwc : ContinuousOn w S) (hwK : MapsTo w S (e '' K))
    (huK : ∀ i, MapsTo (u i) S K) (hlim : TendstoLocallyUniformlyOn (fun i ↦ e ∘ u i) w l S) :
    ContinuousOn (e.symm ∘ w) S ∧ MapsTo (e.symm ∘ w) S K ∧
      TendstoLocallyUniformlyOn (fun i ↦ e ∘ u i) (e ∘ e.symm ∘ w) l S ∧
      ∀ y ∈ S, Tendsto (fun i ↦ u i y) l (𝓝 ((e.symm ∘ w) y)) := by
  have hwt : ∀ y ∈ S, w y ∈ e.target ∧ e (e.symm (w y)) = w y ∧ e.symm (w y) ∈ K := by
    intro y hy
    obtain ⟨x, hx, hxw⟩ := hwK hy
    rw [← hxw]
    exact ⟨e.map_source (hKe hx), by rw [e.left_inv (hKe hx)], by rwa [e.left_inv (hKe hx)]⟩
  refine ⟨e.continuousOn_symm.comp hwc fun y hy ↦ (hwt y hy).1, fun y hy ↦ (hwt y hy).2.2,
    hlim.congr_right fun y hy ↦ (hwt y hy).2.1.symm, fun y hy ↦ ?_⟩
  have hcont := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (hwt y hy).1)
  refine (hcont.tendsto.comp (hlim.tendsto_at hy)).congr fun i ↦ ?_
  exact e.left_inv (hKe (huK i hy))

/-- Reindexing a locally uniformly convergent family along `ψ` with `ψ → p` gives a locally
uniformly convergent family. -/
theorem TendstoLocallyUniformly.comp_tendsto {ι ι' α β : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter ι'} {ψ : ι' → ι}
    (h : TendstoLocallyUniformly F f p) (hψ : Tendsto ψ q p) :
    TendstoLocallyUniformly (fun i ↦ F (ψ i)) f q :=
  tendstoLocallyUniformlyOn_univ.1 ((tendstoLocallyUniformlyOn_univ.2 h).comp_tendsto hψ)

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

/-- A family that does not depend on its index converges locally uniformly to its constant
value. -/
theorem tendstoLocallyUniformly_const {γ : Type*} [UniformSpace γ] (g : α → γ) :
    TendstoLocallyUniformly (fun (_ : ι) ↦ g) g l :=
  (tendstoUniformly_iff_tendsto.2
    (tendsto_diag_uniformity (fun q : ι × α ↦ g q.2) _)).tendstoLocallyUniformly

/-- For a continuous `g` with values in `ℝ` or `ℂ`, the maps `z ↦ g z / m` tend to `0` locally
uniformly. -/
theorem tendstoLocallyUniformly_div_natCast {𝕜 : Type*} [RCLike 𝕜] {g : α → 𝕜}
    (hg : Continuous g) :
    TendstoLocallyUniformly (fun (m : ℕ) z ↦ g z / m) (fun _ ↦ 0) atTop := by
  have hinv : Tendsto (fun m : ℕ ↦ (m : 𝕜)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  simpa [div_eq_mul_inv] using
    (tendstoLocallyUniformly_const g).fun_mul₀
      hinv.tendstoUniformly_const.tendstoLocallyUniformly hg continuous_const

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

end TauCeti
