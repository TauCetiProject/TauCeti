/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Localization

import TauCeti.Topology.MetricSpace.Closeds

/-!
# Hausdorff limits of the zero sets and the vacuum away from them

Consider solutions of the Seiberg–Witten equations on a symplectic four-manifold `X` at
parameters `rᵢ → ∞`, with length scales `hᵢ → 0` (for instance `hᵢ = (2 rᵢ)^(-1/2)`), normalized
spinors `χᵢ = αᵢ u₀ + βᵢ`, `sᵢ = |αᵢ|²` and zero sets `Zᵢ = αᵢ⁻¹(0)`. The zero sets are closed, and
the closed subsets of `X` form an extended metric space for the Hausdorff distance,
`TopologicalSpace.Closeds X`, which is compact when `X` is. So, when `X` is compact, a
subsequence of the zero sets converges to a closed set `Z` (`IsCompact.tendsto_subseq`). This
file shows that, when the off-zero bound of
`TauCeti.SeibergWitten.exists_forall_exists_dist_le_of_le`

`w₊ ≤ (C / r) w₊ + C / r + C exp (-c R / h)`,  `w₊ = max (1 - |α|²) 0`,

holds with constants independent of `i`, the solutions approach the vacuum `|α| = 1` uniformly
on compact sets away from `Z`, and the regions where `|α|` is small concentrate at `Z`.

* **Compact-set vacuum.** If `K` is compact and disjoint from `Z`, then for every `σ < 1`,
  eventually `σ < |αᵢ|²` on all of `K`
  (`TauCeti.SeibergWitten.eventually_forall_lt_of_tendsto`). With the upper bound
  `|αᵢ|² ≤ |αᵢ|² + |βᵢ|² ≤ 1 + C' / rᵢ` this means `|αᵢ|² → 1` uniformly on `K`
  (`TauCeti.SeibergWitten.tendstoUniformlyOn_of_tendsto`).
* **Support convergence.** For `0 ≤ σ < 1`, the closures of the sublevel sets `{|αᵢ|² ≤ σ}`,
  which contain the zero sets, converge to the same limit `Z` in the Hausdorff distance
  (`TauCeti.SeibergWitten.tendsto_closure_setOf_le_of_tendsto`): every point where
  `|αᵢ|² ≤ σ` lies within a fixed multiple of `hᵢ` of `Zᵢ`. When the cutoff `χ` equals one above
  `σ`, these sets contain the supports of the cutoff currents `Θᵢ = i F_{aᵢ} + d(χ(|αᵢ|²) τᵢ)`,
  which therefore eventually miss every compact set disjoint from `Z`
  (`TauCeti.SeibergWitten.eventually_disjoint_tsupport_cutoffCurrent`). This is what places the
  support of a weak limit of the currents `Θᵢ / 2π` inside `Z`.

The statements are for an arbitrary metric space and an arbitrary filter, so they apply to the
manifold with a distance inducing its topology, along any subsequence. The analytic input is the
off-zero bound, taken as a hypothesis as in
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Localization`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

open Filter Metric Real Set TopologicalSpace Topology

namespace TauCeti.SeibergWitten

variable {X : Type*} [MetricSpace X] {ι : Type*} {l : Filter ι} {s : ι → X → ℝ}
  {Z : ι → Closeds X} {Z₀ : Closeds X} {r h : ι → ℝ}

/-- **The compact-set vacuum.** Let `σ < 1` and `c > 0`, and let closed sets `Z i` converge in the
Hausdorff distance to `Z₀` along `l`, while `r i → ∞` and `h i → 0⁺`. Let `K` be compact and
disjoint from `Z₀`. If eventually the off-zero bound
`max (1 - s i x) 0 ≤ (C / r i) max (1 - s i x) 0 + C / r i + C exp (-c R / h i)` holds at every
point `x` of `K`, for every radius `R ≥ c₀ h i` of an open ball about `x` missing `Z i`, then
eventually `σ < s i x` for every `x ∈ K`. -/
theorem eventually_forall_lt_of_tendsto (C c c₀ : ℝ) (hc : 0 < c) {σ : ℝ} (hσ : σ < 1)
    (hr : Tendsto r l atTop) (hh : Tendsto h l (𝓝 0)) (hZ : Tendsto Z l (𝓝 Z₀))
    {K : Set X} (hK : IsCompact K) (hKZ : Disjoint K Z₀) (hh₀ : ∀ᶠ i in l, 0 < h i)
    (hbound : ∀ᶠ i in l, ∀ x ∈ K, ∀ R, c₀ * h i ≤ R → (∀ z ∈ Z i, R ≤ dist x z) →
      max (1 - s i x) 0 ≤ C / r i * max (1 - s i x) 0 + C / r i + C * exp (-(c * R / h i))) :
    ∀ᶠ i in l, ∀ x ∈ K, σ < s i x := by
  obtain ⟨K₀, r₀, -, hK₀⟩ := exists_forall_exists_dist_le_of_le C c c₀ hc hσ
  obtain ⟨δ, hδ, hsep⟩ := hK.exists_pos_eventually_le_dist_of_tendsto hZ hKZ
  have hsmall : ∀ᶠ i in l, K₀ * h i < δ := by
    have := hh.const_mul K₀
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [hr.eventually_ge_atTop r₀, hh₀, hbound, hsep, hsmall]
    with i hri hhi hbi hsepi hsmalli x hx
  by_contra! hle
  -- A point with `s i x ≤ σ` lies within `K₀ h i < δ` of `Z i`, but `K` is `δ`-far from `Z i`.
  obtain ⟨z, hz, hxz⟩ := hK₀ (s i) (Z i) (r i) (h i) hri hhi x (hbi x hx) hle
  linarith [hsepi x hx z hz]

/-- **Uniform convergence to the vacuum on compact sets.** Under the hypotheses of
`TauCeti.SeibergWitten.eventually_forall_lt_of_tendsto`, if moreover eventually
`s i x ≤ 1 + C' / r i` on `K` (as for `s = |α|² ≤ |α|² + |β|² ≤ 1 + C' / r`), then `s i → 1`
uniformly on `K`. -/
theorem tendstoUniformlyOn_of_tendsto (C c c₀ C' : ℝ) (hc : 0 < c)
    (hr : Tendsto r l atTop) (hh : Tendsto h l (𝓝 0)) (hZ : Tendsto Z l (𝓝 Z₀))
    {K : Set X} (hK : IsCompact K) (hKZ : Disjoint K Z₀) (hh₀ : ∀ᶠ i in l, 0 < h i)
    (hbound : ∀ᶠ i in l, ∀ x ∈ K, ∀ R, c₀ * h i ≤ R → (∀ z ∈ Z i, R ≤ dist x z) →
      max (1 - s i x) 0 ≤ C / r i * max (1 - s i x) 0 + C / r i + C * exp (-(c * R / h i)))
    (hupper : ∀ᶠ i in l, ∀ x ∈ K, s i x ≤ 1 + C' / r i) :
    TendstoUniformlyOn s (fun _ ↦ 1) l K := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  have hC' : Tendsto (fun i ↦ C' / r i) l (𝓝 0) := tendsto_const_nhds.div_atTop hr
  filter_upwards [eventually_forall_lt_of_tendsto C c c₀ hc (σ := 1 - ε / 2) (by linarith) hr hh
    hZ hK hKZ hh₀ hbound, hupper, hC'.eventually (gt_mem_nhds (half_pos hε))]
    with i hlow hupp hCi x hx
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [hlow x hx, hupp x hx]

/-- **The sublevel sets converge to the limit of the zero sets.** Let `σ < 1` and `c > 0`, and
let closed sets `Z i` converge in the Hausdorff distance to `Z₀` along `l`, while `r i → ∞` and
`h i → 0⁺`. Suppose that eventually `s i ≤ σ` on `Z i` (as for `s = |α|²` vanishing on the zero
set `Z` of `α`, when `σ ≥ 0`), and the off-zero bound holds at every point of these sublevel
sets. Then the closures of the sublevel sets `{x | s i x ≤ σ}` also converge to `Z₀`. -/
theorem tendsto_closure_setOf_le_of_tendsto (C c c₀ : ℝ) (hc : 0 < c) {σ : ℝ} (hσ : σ < 1)
    (hr : Tendsto r l atTop) (hh : Tendsto h l (𝓝 0)) (hZ : Tendsto Z l (𝓝 Z₀))
    (hh₀ : ∀ᶠ i in l, 0 < h i) (hZs : ∀ᶠ i in l, ∀ z ∈ Z i, s i z ≤ σ)
    (hbound : ∀ᶠ i in l, ∀ x, s i x ≤ σ → ∀ R, c₀ * h i ≤ R → (∀ z ∈ Z i, R ≤ dist x z) →
      max (1 - s i x) 0 ≤ C / r i * max (1 - s i x) 0 + C / r i + C * exp (-(c * R / h i))) :
    Tendsto (fun i ↦ Closeds.closure {x | s i x ≤ σ}) l (𝓝 Z₀) := by
  obtain ⟨K₀, r₀, -, hK₀⟩ := exists_forall_exists_dist_le_of_le C c c₀ hc hσ
  have hK₀h : Tendsto (fun i ↦ ENNReal.ofReal (K₀ * h i)) l (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hh.const_mul K₀)
  refine EMetric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hε₂ : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  filter_upwards [hr.eventually_ge_atTop r₀, hh₀, hZs, hbound,
    hK₀h.eventually (gt_mem_nhds hε₂), EMetric.tendsto_nhds.1 hZ _ hε₂]
    with i hri hhi hZsi hbi hsmall hZi
  -- The sublevel set and `Z i` are within Hausdorff distance `K₀ h i` of each other.
  have hsub : hausdorffEDist {x | s i x ≤ σ} (Z i : Set X) ≤ ENNReal.ofReal (K₀ * h i) := by
    refine hausdorffEDist_le_of_mem_edist (fun x hx ↦ ?_) fun z hz ↦ ⟨z, hZsi z hz, by simp⟩
    obtain ⟨z, hz, hxz⟩ := hK₀ (s i) (Z i) (r i) (h i) hri hhi x (hbi x hx) hx
    exact ⟨z, hz, by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hxz⟩
  rw [Closeds.edist_eq, Closeds.coe_closure, hausdorffEDist_closure_left]
  calc hausdorffEDist {x | s i x ≤ σ} (Z₀ : Set X)
      ≤ hausdorffEDist {x | s i x ≤ σ} (Z i : Set X) + hausdorffEDist (Z i : Set X) Z₀ :=
        hausdorffEDist_triangle
    _ < ε / 2 + ε / 2 := by
        rw [Closeds.edist_eq] at hZi
        exact ENNReal.add_lt_add_of_le_of_lt (hsub.trans_lt hsmall).ne_top
          (hsub.trans hsmall.le) hZi
    _ = ε := ENNReal.add_halves ε

/-- **The supports of the cutoff currents concentrate at the limit of the zero sets.** Let
`Θ i = i F_{a i} + d(χ(|α i|²) τ i)` be cutoff currents in a chart `E`, built with a cutoff `χ`
equal to one above a threshold `0 ≤ σ < 1`, let closed sets `Z i` converge in the Hausdorff
distance to `Z₀` along `l`, while `r i → ∞` and `h i → 0⁺`, and let `K` be compact and
disjoint from `Z₀`. If eventually the off-zero bound for `s = |α i|²` holds at every point of `K`,
then eventually the support of `Θ i` is disjoint from `K`. -/
theorem eventually_disjoint_tsupport_cutoffCurrent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {χ : ℝ → ℝ} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → E → ℂ}
    {Z : ι → Closeds E} {Z₀ : Closeds E} (C c c₀ : ℝ) (hc : 0 < c)
    (hα : ∀ i, ContDiff ℝ 2 (α i)) (hb : ∀ i, Differentiable ℝ (b i))
    {σ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ < 1) (hχ : EqOn χ 1 (Ioi σ))
    (hr : Tendsto r l atTop) (hh : Tendsto h l (𝓝 0)) (hZ : Tendsto Z l (𝓝 Z₀))
    {K : Set E} (hK : IsCompact K) (hKZ : Disjoint K Z₀) (hh₀ : ∀ᶠ i in l, 0 < h i)
    (hbound : ∀ᶠ i in l, ∀ x ∈ K, ∀ R, c₀ * h i ≤ R → (∀ z ∈ Z i, R ≤ dist x z) →
      max (1 - Complex.normSq (α i x)) 0 ≤
        C / r i * max (1 - Complex.normSq (α i x)) 0 + C / r i + C * exp (-(c * R / h i))) :
    ∀ᶠ i in l, Disjoint K (tsupport (cutoffCurrent χ (b i) (α i))) := by
  filter_upwards [eventually_forall_lt_of_tendsto (s := fun i x ↦ Complex.normSq (α i x)) C c c₀
    hc hσ₁ hr hh hZ hK hKZ hh₀ hbound] with i hi
  refine Set.disjoint_left.2 fun x hx hxΘ ↦ ?_
  have := tsupport_cutoffCurrent_subset hσ₀ (hα i) (hb i) hχ hxΘ
  exact (hi x hx).not_ge this

end TauCeti.SeibergWitten
