/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Truncation

/-!
# Sobolev functions vanishing continuously on the boundary

Let `Ω` be a bounded open set and `1 ≤ p < ∞`. A function `u ∈ W^{1,p}(Ω)` that agrees almost
everywhere on `Ω` with a function `g` continuous on the closure of `Ω` and zero on its frontier
lies in `W^{1,p}_0(Ω)`. So for a function continuous up to the boundary, the classical boundary
condition `u = 0` on `∂Ω` implies the Sobolev one, with no regularity of `∂Ω` assumed.

The proof truncates. For `k > 0` the truncation `(u - k)⁺` vanishes outside the compact set
`{x ∈ closure Ω | g x ≥ k}`, which lies inside `Ω` because `g` vanishes on the frontier, so it
belongs to `W^{1,p}_0(Ω)`. As `k → 0` it tends to `u⁺` in `W^{1,p}(Ω)`: on a domain of finite
measure `(u - k)⁺` is the positive part of `u - k`, and taking positive parts is continuous on
`W^{1,p}(Ω)` (`TauCeti.W1p.continuous_posPart`). The same argument applied to `-u` handles `u⁻`.

## Main declarations

* `TauCeti.exists_isCompact_inter_preimage_Ici_subset_subset`: the superlevel sets
  `{x ∈ Ω | k ≤ g x}`, `k > 0`, of a function vanishing on the frontier lie in a compact subset
  of `Ω`.
* `TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure`: a Sobolev function on a bounded
  domain that agrees with a function continuous on the closure and vanishing on the frontier
  lies in `W^{1,p}_0(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 7.4 (truncations of Sobolev functions) and Section 7.5 (the spaces `W^{k,p}_0`).
-/

public section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Superlevel sets stay away from the boundary.** Let `g` be continuous on the closure of a
bounded open set `U` of a proper metric space and zero on its frontier. For every `k > 0` the
points of `U` where `k ≤ g` lie in a compact subset of `U`, namely `closure U ∩ g ⁻¹' Ici k`. -/
theorem exists_isCompact_inter_preimage_Ici_subset_subset {X : Type*} [MetricSpace X]
    [ProperSpace X] {U : Set X} (hU : IsOpen U) (hb : Bornology.IsBounded U) {g : X → ℝ}
    (hg : ContinuousOn g (closure U)) (hg0 : ∀ x ∈ frontier U, g x = 0) {k : ℝ} (hk : 0 < k) :
    ∃ K, IsCompact K ∧ U ∩ g ⁻¹' Ici k ⊆ K ∧ K ⊆ U := by
  refine ⟨closure U ∩ g ⁻¹' Ici k, hb.isCompact_closure.of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici) inter_subset_left,
    inter_subset_inter_left _ subset_closure, fun x ⟨hxc, hxk⟩ => ?_⟩
  -- `g ≥ k > 0` there, so the point is not on the frontier, where `g` vanishes.
  by_contra hxU
  have hx0 := hg0 x (hU.frontier_eq ▸ ⟨hxc, hxU⟩)
  simp only [mem_preimage, mem_Ici, hx0] at hxk
  linarith

/-- A truncation `(u - k)⁺` at a positive level of a Sobolev function that vanishes continuously
on the frontier of a bounded domain has compact support in the domain. -/
private theorem posPartAbove_mem_w1p0Submodule_of_continuousOn_closure (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ}
    (hg : ContinuousOn g (closure (Omega : Set E)))
    (hg0 : ∀ x ∈ frontier (Omega : Set E), g x = 0) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] g) {k : ℝ} (hk : 0 < k) :
    W1p.posPartAbove hp hk.le u ∈ w1p0Submodule mu Omega p := by
  obtain ⟨K, hK, hUK, hKO⟩ :=
    exists_isCompact_inter_preimage_Ici_subset_subset Omega.isOpen hb hg hg0 hk
  refine W1p.mem_w1p0Submodule_of_isCompact hp hK hKO ?_
  filter_upwards [W1p.value_posPartAbove_ae hp hk.le u, hu,
    ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxg hxO hxK
  have hlt : g x < k := not_le.1 fun h => hxK (hUK ⟨hxO, h⟩)
  rw [hx, hxg, max_eq_right (by linarith)]

/-- The positive part `u⁺` of a Sobolev function that vanishes continuously on the frontier of a
bounded domain lies in `W^{1,p}_0(Ω)`: it is the limit of the truncations `(u - k)⁺` as `k → 0⁺`. -/
private theorem posPart_mem_w1p0Submodule_of_continuousOn_closure (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ}
    (hg : ContinuousOn g (closure (Omega : Set E)))
    (hg0 : ∀ x ∈ frontier (Omega : Set E), g x = 0) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] g) : W1p.posPart hp u ∈ w1p0Submodule mu Omega p := by
  have : IsFiniteMeasure (mu.restrict Omega) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  -- The constant function `1`, an element of `W^{1,p}(Ω)` because `Ω` has finite measure.
  set one : W1p mu Omega p := W1p.const 1
  -- For `k ≥ 0`, `(u - k)⁺` is the positive part of `u - k • 1`.
  have hshift {k : ℝ} (hk : 0 ≤ k) :
      W1p.posPart hp (u - k • one) = W1p.posPartAbove hp hk u := by
    refine W1p.ext_value (Lp.ext ?_)
    rw [W1p.value_posPart]
    have hsub : W1p.value (u - k • one) = W1p.value u - k • Lp.const p (mu.restrict Omega) 1 := by
      rw [← W1p.valueL_apply, map_sub, map_smul, W1p.valueL_apply, W1p.valueL_apply,
        W1p.value_const]
    filter_upwards [Lp.coeFn_posPart (W1p.value (u - k • one)), W1p.value_posPartAbove_ae hp hk u,
      Lp.coeFn_sub (W1p.value u) (k • Lp.const p (mu.restrict Omega) (1 : ℝ)),
      Lp.coeFn_smul k (Lp.const p (mu.restrict Omega) (1 : ℝ)),
      Lp.coeFn_const p (mu.restrict Omega) (1 : ℝ)] with x h1 h2 h3 h4 h5
    rw [h1, h2, hsub, h3, Pi.sub_apply, h4, Pi.smul_apply, h5, Function.const_apply, smul_eq_mul,
      mul_one]
  -- Taking positive parts is continuous, so `(u - k)⁺ → u⁺` as `k → 0⁺`.
  have hc : Continuous fun k : ℝ => W1p.posPart hp (u - k • one) :=
    (W1p.continuous_posPart hp).comp (continuous_const.sub (continuous_id.smul continuous_const))
  have hlim : Tendsto (fun k : ℝ => W1p.posPart hp (u - k • one)) (𝓝[>] 0)
      (𝓝 (W1p.posPart hp u)) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine (w1p0Submodule mu Omega p).isClosed.mem_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with k (hk : 0 < k)
  rw [hshift hk.le]
  exact posPartAbove_mem_w1p0Submodule_of_continuousOn_closure hp hb hg hg0 hu hk

/-- **A Sobolev function vanishing continuously on the boundary lies in `W^{1,p}_0(Ω)`.** Let `Ω`
be bounded and `1 ≤ p < ∞`. If `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function
`g` that is continuous on `closure Ω` and zero on `frontier Ω`, then `u ∈ W^{1,p}_0(Ω)`. No
regularity of the boundary is assumed. -/
theorem W1p.mem_w1p0Submodule_of_continuousOn_closure (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ}
    (hg : ContinuousOn g (closure (Omega : Set E)))
    (hg0 : ∀ x ∈ frontier (Omega : Set E), g x = 0) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] g) : u ∈ w1p0Submodule mu Omega p := by
  have hnegv := W1p.value_neg_ae u
  have hneg : W1p.value (-u) =ᵐ[mu.restrict Omega] -g := by
    filter_upwards [hu, hnegv] with x hx hnx
    rw [hnx, Pi.neg_apply, hx, Pi.neg_apply]
  -- `u = u⁺ - (-u)⁺`.
  have hsplit : u = W1p.posPart hp u - W1p.posPart hp (-u) := by
    refine W1p.ext_value (Lp.ext ?_)
    have hsubv : ⇑(W1p.value (W1p.posPart hp u - W1p.posPart hp (-u))) =ᵐ[mu.restrict Omega]
        ⇑(W1p.value (W1p.posPart hp u)) - ⇑(W1p.value (W1p.posPart hp (-u))) := by
      simpa only [← W1p.valueL_apply, map_sub] using
        Lp.coeFn_sub (W1p.value (W1p.posPart hp u)) (W1p.value (W1p.posPart hp (-u)))
    filter_upwards [hsubv, Lp.coeFn_posPart (W1p.value u), Lp.coeFn_posPart (W1p.value (-u)),
      hnegv] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, W1p.value_posPart, W1p.value_posPart, h2, h3, h4, Pi.neg_apply,
      max_zero_sub_eq_self]
  rw [hsplit]
  exact (w1p0Submodule mu Omega p).toSubmodule.sub_mem
    (posPart_mem_w1p0Submodule_of_continuousOn_closure hp hb hg hg0 hu)
    (posPart_mem_w1p0Submodule_of_continuousOn_closure hp hb hg.neg
      (fun x hx => by simp [hg0 x hx]) hneg)

end TauCeti
