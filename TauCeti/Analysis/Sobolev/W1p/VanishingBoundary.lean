/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
public import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

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

The same truncation shows that a function vanishing on a set `Γ` lies in the space `W^{1,p}_Γ(Ω)`
of Sobolev functions vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`), when it agrees with a
locally Lipschitz function on the whole space that is zero on `Γ`, hence on `closure Γ`: its
truncations at positive levels vanish near `closure Γ`.

## Main declarations

* `TauCeti.exists_isCompact_inter_preimage_Ici_subset_subset`: the superlevel sets
  `{x ∈ Ω | k ≤ g x}`, `k > 0`, of a function vanishing on the frontier lie in a compact subset
  of `Ω`.
* `TauCeti.W1p.posPart_sub_posPart_neg`: `u = u⁺ - (-u)⁺` in `W^{1,p}(Ω)`.
* `TauCeti.W1p.posPart_mem_of_forall_posPartAbove_mem`: on a domain of finite measure, `u⁺` lies
  in every closed set containing the truncations `(u - k)⁺`, `k > 0`.
* `TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure`: a Sobolev function on a bounded
  domain that agrees with a function continuous on the closure and vanishing on the frontier
  lies in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.exists_mem_w1p0Submodule_value_ae_eq_of_contDiff`: on a bounded domain, a `C¹`
  function vanishing on the frontier is the value of an element of `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.posPart_add_mem_w1p0Submodule`: the positive part of `ψ + G`, for `ψ ∈ W^{1,p}_0(Ω)`
  and `G` continuous up to the boundary and nonpositive there, lies in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz_of_eqOn_zero`: a Sobolev function
  on a bounded domain that agrees with a locally Lipschitz function vanishing on `Γ` lies in
  `W^{1,p}_Γ(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 7.4 (truncations of Sobolev functions) and Section 7.5 (the spaces `W^{k,p}_0`).
-/

public section

namespace TauCeti

open Filter Function _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Superlevel sets stay away from the boundary.** Let `g` be continuous on the closure of a
bounded set `U` of a proper metric space and zero on its frontier. For every `k > 0` the
points of `U` where `k ≤ g` lie in a compact subset of `U`, namely `closure U ∩ g ⁻¹' Ici k`. -/
theorem exists_isCompact_inter_preimage_Ici_subset_subset {X : Type*} [MetricSpace X]
    [ProperSpace X] {U : Set X} (hb : Bornology.IsBounded U) {g : X → ℝ}
    (hg : ContinuousOn g (closure U)) (hg0 : ∀ x ∈ frontier U, g x = 0) {k : ℝ} (hk : 0 < k) :
    ∃ K, IsCompact K ∧ U ∩ g ⁻¹' Ici k ⊆ K ∧ K ⊆ U := by
  refine ⟨closure U ∩ g ⁻¹' Ici k, hb.isCompact_closure.of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici) inter_subset_left,
    inter_subset_inter_left _ subset_closure, fun x ⟨hxc, hxk⟩ => ?_⟩
  -- `g ≥ k > 0` there, so the point is not on the frontier, where `g` vanishes.
  by_contra hxU
  have hx0 := hg0 x ⟨hxc, fun hxi => hxU (interior_subset hxi)⟩
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
    exists_isCompact_inter_preimage_Ici_subset_subset hb hg hg0 hk
  refine W1p.mem_w1p0Submodule_of_isCompact hp hK hKO ?_
  filter_upwards [W1p.value_posPartAbove_ae hp hk.le u, hu,
    ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxg hxO hxK
  have hlt : g x < k := not_le.1 fun h => hxK (hUK ⟨hxO, h⟩)
  rw [hx, hxg, max_eq_right (by linarith)]

/-- **A Sobolev function is the difference of its positive and negative parts**:
`u = u⁺ - (-u)⁺` in `W^{1,p}(Ω)`, for `1 ≤ p < ∞`. -/
theorem W1p.posPart_sub_posPart_neg (hp : p ≠ ∞) (u : W1p mu Omega p) :
    W1p.posPart hp u - W1p.posPart hp (-u) = u := by
  refine W1p.ext_value (Lp.ext ?_)
  have hsubv : ⇑(W1p.value (W1p.posPart hp u - W1p.posPart hp (-u))) =ᵐ[mu.restrict Omega]
      ⇑(W1p.value (W1p.posPart hp u)) - ⇑(W1p.value (W1p.posPart hp (-u))) := by
    simpa only [← W1p.valueL_apply, map_sub] using
      Lp.coeFn_sub (W1p.value (W1p.posPart hp u)) (W1p.value (W1p.posPart hp (-u)))
  filter_upwards [hsubv, Lp.coeFn_posPart (W1p.value u), Lp.coeFn_posPart (W1p.value (-u)),
    W1p.value_neg_ae u] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, W1p.value_posPart, W1p.value_posPart, h2, h3, h4, Pi.neg_apply,
    max_zero_sub_eq_self]

/-- **The positive part is the limit of the truncations.** On a domain of finite measure and for
`1 ≤ p < ∞`, if every truncation `(u - k)⁺` at a positive level `k` of `u ∈ W^{1,p}(Ω)` lies in a
closed set `s`, then so does `u⁺`: on such a domain `(u - k)⁺` is the positive part of `u - k`,
and taking positive parts is continuous on `W^{1,p}(Ω)`, so `(u - k)⁺ → u⁺` as `k → 0⁺`. -/
theorem W1p.posPart_mem_of_forall_posPartAbove_mem (hp : p ≠ ∞) (hΩ : mu Omega ≠ ∞)
    {s : Set (W1p mu Omega p)} (hs : IsClosed s) {u : W1p mu Omega p}
    (h : ∀ k (hk : 0 < k), W1p.posPartAbove hp hk.le u ∈ s) : W1p.posPart hp u ∈ s := by
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hΩ
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
  refine hs.mem_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with k (hk : 0 < k)
  rw [hshift hk.le]
  exact h k hk

/-- **A Sobolev function vanishing continuously on the boundary lies in `W^{1,p}_0(Ω)`.** Let `Ω`
be bounded and `1 ≤ p < ∞`. If `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function
`g` that is continuous on `closure Ω` and zero on `frontier Ω`, then `u ∈ W^{1,p}_0(Ω)`. No
regularity of the boundary is assumed. -/
theorem W1p.mem_w1p0Submodule_of_continuousOn_closure (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ}
    (hg : ContinuousOn g (closure (Omega : Set E)))
    (hg0 : ∀ x ∈ frontier (Omega : Set E), g x = 0) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] g) : u ∈ w1p0Submodule mu Omega p := by
  -- `u⁺` and `(-u)⁺` are limits of truncations, which have compact support in `Ω`.
  have hpos {v : W1p mu Omega p} {f : E → ℝ} (hf : ContinuousOn f (closure (Omega : Set E)))
      (hf0 : ∀ x ∈ frontier (Omega : Set E), f x = 0)
      (hv : W1p.value v =ᵐ[mu.restrict Omega] f) : W1p.posPart hp v ∈ w1p0Submodule mu Omega p :=
    W1p.posPart_mem_of_forall_posPartAbove_mem hp hb.measure_lt_top.ne
      (w1p0Submodule mu Omega p).isClosed fun _ hk =>
        posPartAbove_mem_w1p0Submodule_of_continuousOn_closure hp hb hf hf0 hv hk
  have hneg : W1p.value (-u) =ᵐ[mu.restrict Omega] -g := (W1p.value_neg_ae u).trans hu.neg
  rw [← W1p.posPart_sub_posPart_neg hp u]
  exact (w1p0Submodule mu Omega p).toSubmodule.sub_mem (hpos hg hg0 hu)
    (hpos hg.neg (fun x hx => by simp [hg0 x hx]) hneg)

/-- **A `C¹` function vanishing on the boundary gives an element of `W^{1,p}_0(Ω)`.** Let `Ω` be
bounded and `1 ≤ p < ∞`. A `C¹` function `g` on the whole space that is zero on `frontier Ω` is,
on `Ω`, the value of an element of `W^{1,p}_0(Ω)`: it is `C¹` near the compact closure of `Ω`, so
it lies in `W^{1,p}(Ω)`, and it vanishes continuously on the boundary. -/
theorem W1p.exists_mem_w1p0Submodule_value_ae_eq_of_contDiff (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg0 : ∀ x ∈ frontier (Omega : Set E), g x = 0) :
    ∃ u : W1p mu Omega p, u ∈ w1p0Submodule mu Omega p ∧
      W1p.value u =ᵐ[mu.restrict Omega] g := by
  obtain ⟨u, hu, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := mu)
    (p := p) isOpen_univ hg.contDiffOn hb.isCompact_closure subset_closure (Set.subset_univ _)
  exact ⟨u, W1p.mem_w1p0Submodule_of_continuousOn_closure hp hb hg.continuous.continuousOn hg0 hu,
    hu⟩

/-- **Positive parts below continuous boundary values.** Let `Ω` be bounded and `1 ≤ p < ∞`. If
`ψ ∈ W^{1,p}_0(Ω)` and `G ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function `g`
continuous on `closure Ω` and nonpositive on `frontier Ω`, then `(ψ + G)⁺ ∈ W^{1,p}_0(Ω)`: the
boundary values of `ψ + G` are nonpositive. -/
theorem W1p.posPart_add_mem_w1p0Submodule (hp : p ≠ ∞) (hb : Bornology.IsBounded (Omega : Set E))
    {ψ G : W1p mu Omega p} (hψ : ψ ∈ w1p0Submodule mu Omega p) {g : E → ℝ}
    (hg : ContinuousOn g (closure (Omega : Set E)))
    (hg0 : ∀ x ∈ frontier (Omega : Set E), g x ≤ 0) (hG : W1p.value G =ᵐ[mu.restrict Omega] g) :
    W1p.posPart hp (ψ + G) ∈ w1p0Submodule mu Omega p := by
  -- Squeeze: `0 ≤ (ψ + G)⁺ ≤ ψ⁺ + G⁺`, and `G⁺` vanishes continuously on the boundary.
  have hGp : W1p.posPart hp G ∈ w1p0Submodule mu Omega p := by
    refine W1p.mem_w1p0Submodule_of_continuousOn_closure hp hb (g := fun x => max (g x) 0)
      (ContinuousOn.sup hg continuousOn_const) (fun x hx => max_eq_right (hg0 x hx)) ?_
    filter_upwards [Lp.coeFn_posPart (W1p.value G), hG] with x h1 h2
    rw [W1p.value_posPart, h1, h2]
  refine W1p.mem_w1p0Submodule_of_nonneg_of_le hp
    (add_mem (W1p.posPart_mem_w1p0Submodule hp hψ) hGp) ?_ ?_
  · filter_upwards [Lp.coeFn_posPart (W1p.value (ψ + G))] with x h
    rw [W1p.value_posPart, h]
    exact le_max_right _ _
  · filter_upwards [Lp.coeFn_posPart (W1p.value (ψ + G)), Lp.coeFn_posPart (W1p.value ψ),
      Lp.coeFn_posPart (W1p.value G), W1p.value_add_ae ψ G,
      W1p.value_add_ae (W1p.posPart hp ψ) (W1p.posPart hp G)] with x h1 h2 h3 h4 h5
    rw [W1p.value_posPart, h1, h4, h5, Pi.add_apply, W1p.value_posPart, W1p.value_posPart,
      Pi.add_apply, h2, h3]
    exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))

/-! ### Functions vanishing on a part of the boundary -/

section BoundaryPart

variable {Γ : Set E}

/-- A truncation `(u - k)⁺` at a positive level of a Sobolev function on a bounded domain that
agrees with a locally Lipschitz function vanishing on `closure Γ` lies in `W^{1,p}_Γ(Ω)`. -/
private theorem posPartAbove_mem_w1pVanishingOnSubmodule_of_locallyLipschitz (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ} (hg : LocallyLipschitz g)
    (hg0 : ∀ x ∈ closure Γ, g x = 0) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] g) {k : ℝ} (hk : 0 < k) :
    W1p.posPartAbove hp hk.le u ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  -- A cutoff `ψ`, equal to one on the compact closure of `Ω`.
  obtain ⟨psi, hpsi, hpsi01, hpsi1, hpsic, -⟩ :=
    hb.isCompact_closure.exists_contDiff_cutoff isOpen_univ (subset_univ _)
  -- A bound `M` for `g` on `Ω`.
  obtain ⟨C, hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hg.continuous.continuousOn
  set M := max C 0
  -- The truncation of `g` at level `k`, capped by `M ψ`: compactly supported, locally Lipschitz,
  -- and zero where `g ≤ k`, a closed set containing a neighbourhood of `closure Γ`.
  set G : E → ℝ := fun x => min (max (g x - k) 0) (M * psi x)
  have hGx (x : E) : G x = min (max (g x - k) 0) (M * psi x) := rfl
  have hGl : LocallyLipschitz G :=
    ((hg.sub (LocallyLipschitz.const k)).max_const 0).min
      (ContDiff.locallyLipschitz (𝕂 := ℝ) ((contDiff_const.mul hpsi).of_le (by simp)))
  have hsupp : support G ⊆ support psi ∩ g ⁻¹' Ioi k := fun x hx => by
    refine ⟨fun h0 => hx ?_, ?_⟩
    · rw [hGx, h0, mul_zero]
      exact min_eq_right (le_max_right _ _)
    · by_contra hxk
      refine hx ?_
      rw [hGx, max_eq_right (by simp at hxk; linarith)]
      exact min_eq_left (mul_nonneg (le_max_right _ _) (hpsi01 (mem_range_self x)).1)
  have hGc : HasCompactSupport G :=
    hpsic.mono' (hsupp.trans (inter_subset_left.trans subset_closure))
  have hGΓ : Disjoint (tsupport G) (closure Γ) := by
    have hts : tsupport G ⊆ g ⁻¹' Ici k :=
      closure_minimal (hsupp.trans (inter_subset_right.trans (preimage_mono Ioi_subset_Ici_self)))
        (isClosed_Ici.preimage hg.continuous)
    refine Disjoint.mono_left hts (Set.disjoint_left.2 fun x hx hxΓ => ?_)
    simp only [mem_preimage, mem_Ici, hg0 x hxΓ] at hx
    linarith
  refine W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz hp hGl hGc hGΓ ?_
  -- On `Ω` the cutoff is one, so `G = (g - k)⁺`.
  filter_upwards [W1p.value_posPartAbove_ae hp hk.le u, hu,
    ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxg hxO
  have h1 : psi x = 1 := interior_subset (hpsi1 (subset_closure hxO))
  have hgM : g x - k ≤ M := calc
    g x - k ≤ |g x| := by linarith [le_abs_self (g x)]
    _ ≤ C := hC x (subset_closure hxO)
    _ ≤ M := le_max_left C 0
  rw [hx, hxg, hGx, h1, mul_one, min_eq_left (max_le hgM (le_max_right _ _))]

/-- **A Sobolev function equal to a locally Lipschitz function vanishing on `Γ` lies in
`W^{1,p}_Γ(Ω)`.** Let `Ω` be bounded and `1 ≤ p < ∞`. If `u ∈ W^{1,p}(Ω)` agrees almost everywhere
on `Ω` with a locally Lipschitz function `g` on the whole space that is zero on `Γ`, then
`u ∈ W^{1,p}_Γ(Ω)`. No regularity of `Ω` or `Γ` is assumed, and unlike
`TauCeti.W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz`, `g` need not vanish near `Γ` nor
have compact support. -/
theorem W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz_of_eqOn_zero
    (hp : p ≠ ∞) (hb : Bornology.IsBounded (Omega : Set E)) {g : E → ℝ} (hg : LocallyLipschitz g)
    (hg0 : EqOn g 0 Γ) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] g) : u ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  -- `u⁺` and `(-u)⁺` are limits of truncations, which vanish near `closure Γ`.
  have hpos {v : W1p mu Omega p} {f : E → ℝ} (hf : LocallyLipschitz f)
      (hf0 : ∀ x ∈ closure Γ, f x = 0) (hv : W1p.value v =ᵐ[mu.restrict Omega] f) :
      W1p.posPart hp v ∈ w1pVanishingOnSubmodule mu Omega p Γ :=
    W1p.posPart_mem_of_forall_posPartAbove_mem hp hb.measure_lt_top.ne
      (w1pVanishingOnSubmodule mu Omega p Γ).isClosed fun _ hk =>
        posPartAbove_mem_w1pVanishingOnSubmodule_of_locallyLipschitz hp hb hf hf0 hv hk
  have hneg : W1p.value (-u) =ᵐ[mu.restrict Omega] -g := (W1p.value_neg_ae u).trans hu.neg
  -- By continuity, `g` vanishes on `closure Γ`.
  have hgc := hg0.closure hg.continuous continuous_const
  rw [← W1p.posPart_sub_posPart_neg hp u]
  exact (w1pVanishingOnSubmodule mu Omega p Γ).toSubmodule.sub_mem (hpos hg hgc hu)
    (hpos hg.neg (fun x hx => by simp [hgc hx]) hneg)

end BoundaryPart

end TauCeti
