/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.NNRat.Encodable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Instances.Rat
import TauCeti.Probability.Process.Kolmogorov.Edges
import TauCeti.Topology.Instances.NNRat
import TauCeti.Topology.Instances.NNReal.Dyadic.Grid
import TauCeti.Topology.Instances.NNReal.Dyadic.Holder

/-!
# The one-dimensional Kolmogorov–Chentsov continuous modification theorem

Given a stochastic process `X` indexed by nonnegative times (`ℚ≥0` or `ℝ≥0`) with values in a
complete extended metric Borel space `E` and satisfying a local Kolmogorov moment bound of
exponents `p > 0` and `q > 1` on each compact horizon `[0, N]`,
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M N * edist s t ^ q`, this file constructs a process
`Y : ℝ≥0 → Ω → E` such that:

* each coordinate `Y t` is Borel measurable;
* every sample path `t ↦ Y t ω` is continuous;
* `Y` agrees almost everywhere with `X` at each time;
* every sample path `t ↦ Y t ω` is simultaneously `γ`-Hölder continuous on `Iic T` for all
  `γ : ℝ≥0` with `(γ : ℝ) < (q - 1) / p` and all `T : ℝ≥0`.

No finiteness or completeness hypothesis on `P` and no separability hypothesis on `E` is required.
The construction builds on Mathlib's `ProbabilityTheory.IsKolmogorovProcess` and
`IsAEKolmogorovProcess` together with `TauCeti.Probability.Process.Kolmogorov.Edges`,
`TauCeti.Topology.Instances.NNReal.Dyadic.Grid`, and
`TauCeti.Topology.Instances.NNReal.Dyadic.Holder`.

## Main results

* `TauCeti.exists_continuous_extension_of_nnrat`: extends a process on `ℚ≥0` satisfying local
  Kolmogorov bounds to an all-paths continuous, coordinatewise measurable, locally Hölder process
  on `ℝ≥0`.
* `TauCeti.exists_continuous_modification_of_local_isAEKolmogorovProcess`: local
  Kolmogorov–Chentsov modification theorem on `ℝ≥0` for locally `IsAEKolmogorovProcess` processes.
* `ProbabilityTheory.IsKolmogorovProcess.exists_continuous_modification` and
  `ProbabilityTheory.IsAEKolmogorovProcess.exists_continuous_modification`: global specializations.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, Theorem 4.23.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Theorem 2.2.8.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999,
  Theorem I.2.1.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

section StochasticExtension

/-- The measurable event on which every adjacent dyadic increment in `[0, N]` at every level `n`
is bounded by `K * (2⁻ⁿ) ^ γ` for some `K : ℕ`. -/
private def goodDyadicEvent {Ω E : Type*} [PseudoEMetricSpace E] (X : ℚ≥0 → Ω → E)
    (N : ℕ) (γ : ℝ≥0) : Set Ω :=
  ⋃ K : ℕ, ⋂ n : ℕ, ⋂ k : Fin (N * 2 ^ n),
    {ω | edist (X (dyadicNNRat n k) ω) (X (dyadicNNRat n (k + 1)) ω) ≤
      (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ)}

private lemma measurableSet_goodDyadicEvent {Ω E : Type*} {_ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] {X : ℚ≥0 → Ω → E}
    (hedist : ∀ r s : ℚ≥0, Measurable fun ω ↦ edist (X r ω) (X s ω))
    (N : ℕ) (γ : ℝ≥0) :
    MeasurableSet (goodDyadicEvent X N γ) :=
  MeasurableSet.iUnion fun _ ↦ MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le (hedist _ _) measurable_const

/-- Via `IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow`, almost every sample path belongs
to `goodDyadicEvent X N γ` whenever `(γ : ℝ) < (q - 1) / p`. -/
private lemma ae_mem_goodDyadicEvent {Ω E : Type*} {_ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] {P : Measure Ω} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0} {N : ℕ}
    {γ : ℝ≥0} (hγ : (γ : ℝ) < (q - 1) / p)
    (hX : IsAEKolmogorovProcess (fun r : {r : ℚ≥0 // (r : ℝ≥0) ≤ N} ↦ X r.val) P p q M) :
    ∀ᵐ ω ∂P, ω ∈ goodDyadicEvent X N γ := by
  have hp := hX.p_pos
  have hcard (n : ℕ) :
      ((N * 2 ^ n : ℕ) : ℝ≥0) ≤ (N : ℝ≥0) * ((2⁻¹ : ℝ≥0) ^ (-(1 : ℝ))) ^ n := by
    have h2 : (2⁻¹ : ℝ≥0) ^ (-(1 : ℝ)) = 2 := by
      rw [NNReal.rpow_neg, NNReal.rpow_one, inv_inv]
    rw [h2]
    push_cast
    exact le_rfl
  have hedge (n : ℕ) (i : Fin (N * 2 ^ n)) :
      edist
        (⟨dyadicNNRat n i, coe_dyadicNNRat_le_natCast_iff.2 i.isLt.le⟩ :
          {r : ℚ≥0 // (r : ℝ≥0) ≤ N})
        (⟨dyadicNNRat n (i + 1), coe_dyadicNNRat_le_natCast_iff.2 i.isLt⟩ :
          {r : ℚ≥0 // (r : ℝ≥0) ≤ N}) ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [Subtype.edist_eq, ← NNRat.edist_cast_nnreal, edist_dyadicNNRat_succ]
    simp
  have hγ' : 1 + p * (γ : ℝ) < q := by
    have : (γ : ℝ) * p < q - 1 := (lt_div_iff₀ hp).mp hγ
    linarith
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow (C := N) (r := 2⁻¹) (d := 1) (γ := (γ : ℝ))
    (by norm_num) (by norm_num) hcard hedge hγ'] with ω ⟨K, hK⟩
  refine mem_iUnion.2 ⟨⌈(K : ℝ)⌉₊, mem_iInter.2 fun n ↦ mem_iInter.2 fun i ↦ ?_⟩
  have hK_le : (K : ℝ≥0∞) ≤ (⌈(K : ℝ)⌉₊ : ℝ≥0∞) := by
    exact_mod_cast (Nat.le_ceil (K : ℝ))
  have hKi := hK n i
  simp only [ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat] at hKi
  exact hKi.trans (by gcongr)

/-- On `goodDyadicEvent X N γ`, the rational path `r ↦ X r ω` extends from dyadic rationals in
`[0, N]` to a `γ`-Hölder map on `Iic (N : ℝ≥0)`. -/
private lemma exists_holderWith_Iic_of_mem_goodDyadicEvent {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {ω : Ω} {N : ℕ} {γ : ℝ≥0}
    (hγ_pos : 0 < γ) (hω : ω ∈ goodDyadicEvent X N γ) :
    ∃ (C : ℝ≥0) (g : Iic (N : ℝ≥0) → E), HolderWith C γ g ∧
      ∀ n k (hk : k ≤ N * 2 ^ n),
        g ⟨(dyadicNNRat n k : ℝ≥0), coe_dyadicNNRat_le_natCast_iff.2 hk⟩ =
          X (dyadicNNRat n k) ω := by
  obtain ⟨K, hK⟩ := mem_iUnion.mp hω
  refine exists_holderWith_Iic_of_edist_dyadicNNRat_succ_le (f := fun r ↦ X r ω) (K := (K : ℝ≥0))
    hγ_pos fun l k hk ↦ ?_
  simpa using mem_iInter.mp (mem_iInter.mp hK l) ⟨k, hk⟩

/-- Canonical pathwise dyadic limit on `G`, equal to the constant path `X 0 ω` outside `G`. -/
private def dyadicExtension {Ω E : Type*} [TopologicalSpace E] (X : ℚ≥0 → Ω → E)
    (G : Set Ω) [DecidablePred (· ∈ G)] (t : ℝ≥0) (ω : Ω) : E :=
  letI : Nonempty E := ⟨X 0 ω⟩
  limUnder atTop (fun n ↦ if ω ∈ G then X (approxDyadicNNRat n t) ω else X 0 ω)

private lemma dyadicExtension_eq_of_mem {Ω E : Type*} [TopologicalSpace E] [T2Space E]
    {X : ℚ≥0 → Ω → E} {G : Set Ω} [DecidablePred (· ∈ G)] {ω : Ω} (hω : ω ∈ G)
    {N : ℕ} {g : Iic (N : ℝ≥0) → E} (hg_cont : Continuous g)
    (hg_dyad : ∀ n k (hk : k ≤ N * 2 ^ n),
      g ⟨(dyadicNNRat n k : ℝ≥0), coe_dyadicNNRat_le_natCast_iff.2 hk⟩ = X (dyadicNNRat n k) ω)
    {t : ℝ≥0} (ht : t ≤ N) :
    dyadicExtension X G t ω = g ⟨t, ht⟩ := by
  let : Nonempty E := ⟨X 0 ω⟩
  exact ((tendsto_approxDyadicNNRat_apply_of_continuousAt (f := fun r ↦ X r ω)
    (t := ⟨t, ht⟩) hg_cont.continuousAt fun n k hk ↦
      hg_dyad n k (coe_dyadicNNRat_le_natCast_iff.1 hk)) |>.congr fun _ ↦ by simp [hω]).limUnder_eq

private lemma dyadicExtension_eq_of_notMem {Ω E : Type*} [TopologicalSpace E] [T2Space E]
    {X : ℚ≥0 → Ω → E} {G : Set Ω} [DecidablePred (· ∈ G)] {ω : Ω} (hω : ω ∉ G) (t : ℝ≥0) :
    dyadicExtension X G t ω = X 0 ω := by
  let : Nonempty E := ⟨X 0 ω⟩
  exact (tendsto_const_nhds.congr fun _ ↦ by simp [hω]).limUnder_eq

/-- On `G`, the dyadic approximations `X (approxDyadicNNRat n t) ω` converge to
`dyadicExtension X G t ω`. -/
private lemma tendsto_approxDyadicNNRat_dyadicExtension_of_mem {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀)
    {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    Tendsto (fun n ↦ X (approxDyadicNNRat n t) ω) atTop (𝓝 (dyadicExtension X G t ω)) := by
  let N := ⌈(t : ℝ)⌉₊
  have htN : t ≤ N := by exact_mod_cast Nat.le_ceil (t : ℝ)
  obtain ⟨_, g, hg_h, hg_d⟩ :=
    exists_holderWith_Iic_of_mem_goodDyadicEvent hγ₀_pos (hG_sub ω hω N)
  have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
  rw [dyadicExtension_eq_of_mem hω hg_cont hg_d htN]
  exact tendsto_approxDyadicNNRat_apply_of_continuousAt (f := fun r ↦ X r ω)
    (t := ⟨t, htN⟩) hg_cont.continuousAt fun n k hk ↦
      hg_d n k (coe_dyadicNNRat_le_natCast_iff.1 hk)

private lemma measurable_dyadicExtension {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀) (hmeasX : ∀ r : ℚ≥0, Measurable (X r))
    {G : Set Ω} [DecidablePred (· ∈ G)] (hG_meas : MeasurableSet G)
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀) (t : ℝ≥0) :
    Measurable (dyadicExtension X G t) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω ↦ if ω ∈ G then X (approxDyadicNNRat n t) ω else X 0 ω)
    (fun _ ↦ Measurable.ite hG_meas (hmeasX _) (hmeasX 0)) (tendsto_pi_nhds.2 fun ω ↦ ?_)
  by_cases hω : ω ∈ G
  · exact (tendsto_approxDyadicNNRat_dyadicExtension_of_mem hγ₀_pos hG_sub hω t).congr
      fun _ ↦ by simp [hω]
  · simp [hω, dyadicExtension_eq_of_notMem hω]

private lemma continuous_dyadicExtension {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀) (ω : Ω) :
    Continuous (dyadicExtension X G · ω) := by
  by_cases hω : ω ∈ G
  · rw [continuous_iff_continuousAt]
    intro t
    let N := ⌊(t : ℝ)⌋₊ + 1
    have ht_lt : t < (N : ℝ≥0) := by exact_mod_cast Nat.lt_floor_add_one (t : ℝ)
    obtain ⟨_, g, hg_h, hg_d⟩ :=
      exists_holderWith_Iic_of_mem_goodDyadicEvent hγ₀_pos (hG_sub ω hω N)
    have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
    have hcon : ContinuousOn (dyadicExtension X G · ω) (Iic (N : ℝ≥0)) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (hg_cont.congr fun s ↦ (dyadicExtension_eq_of_mem hω hg_cont hg_d s.property).symm)
    exact hcon.continuousAt (Iic_mem_nhds ht_lt)
  · have hconst : (dyadicExtension X G · ω) = fun _ ↦ X 0 ω :=
      funext fun t ↦ dyadicExtension_eq_of_notMem hω t
    rw [hconst]
    exact continuous_const

/-- For any rational time `r : ℚ≥0`, `dyadicExtension X G r` agrees almost everywhere with `X r`. -/
private lemma ae_eq_dyadicExtension_of_nnrat {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] {P : Measure Ω} {X : ℚ≥0 → Ω → E}
    {p q : ℝ} {M : ℕ → ℝ≥0} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)] (hG_ae : ∀ᵐ ω ∂P, ω ∈ G)
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∈ goodDyadicEvent X N γ₀)
    (hX_loc : ∀ N : ℕ, IsAEKolmogorovProcess (fun r : {r : ℚ≥0 // (r : ℝ≥0) ≤ N} ↦ X r.val)
      P p q (M N)) (r : ℚ≥0) :
    dyadicExtension X G r =ᵐ[P] X r := by
  let N := ⌈((r : ℝ≥0) : ℝ)⌉₊
  have hrN : (r : ℝ≥0) ≤ N := by exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
  have hu (n : ℕ) :
      edist
        (⟨approxDyadicNNRat n (r : ℝ≥0), (coe_approxDyadicNNRat_le n _).trans hrN⟩ :
          {s : ℚ≥0 // (s : ℝ≥0) ≤ N})
        (⟨r, hrN⟩ : {s : ℚ≥0 // (s : ℝ≥0) ≤ N}) ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [Subtype.edist_eq, ← NNRat.edist_cast_nnreal]
    simpa using edist_approxDyadicNNRat_le n (r : ℝ≥0)
  filter_upwards [hG_ae, (hX_loc N).ae_tendsto_of_edist_le_pow (r := 2⁻¹) (by norm_num) hu]
    with ω hω hX_tend
  exact tendsto_nhds_unique
    (tendsto_approxDyadicNNRat_dyadicExtension_of_mem hγ₀_pos hG_sub hω r) hX_tend

/-- Every sample path of `dyadicExtension X G` is simultaneously `γ`-Hölder on `Iic T` for all
`γ < (q - 1) / p` and all `T : ℝ≥0`, provided `G` intersects `goodDyadicEvent X N (γSeq k)` for a
cofinal sequence `γSeq k ↑ (q - 1) / p`. -/
private lemma exists_holderOnWith_dyadicExtension {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γSeq : ℕ → ℝ≥0}
    (hγSeq_pos : ∀ k, 0 < γSeq k) {α : ℝ}
    (hcofinal : ∀ γ : ℝ≥0, (γ : ℝ) < α → ∃ k, γ ≤ γSeq k)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N k : ℕ, ω ∈ goodDyadicEvent X N (γSeq k))
    (ω : Ω) (γ : ℝ≥0) (hγ : (γ : ℝ) < α) (T : ℝ≥0) :
    ∃ C : ℝ≥0, HolderOnWith C γ (dyadicExtension X G · ω) (Iic T) := by
  by_cases hω : ω ∈ G
  · obtain ⟨k, hk⟩ := hcofinal γ hγ
    let N := ⌈(T : ℝ)⌉₊
    have hTN : T ≤ N := by exact_mod_cast Nat.le_ceil (T : ℝ)
    obtain ⟨C₁, g, hg_holder, hg_dyad⟩ :=
      exists_holderWith_Iic_of_mem_goodDyadicEvent (hγSeq_pos k) (hG_sub ω hω N k)
    have hg_cont : Continuous g := (hg_holder.uniformContinuous (hγSeq_pos k)).continuous
    have hholder_k : HolderOnWith C₁ (γSeq k) (dyadicExtension X G · ω) (Iic T) := by
      intro s hs t ht
      have hsN : s ≤ N := hs.trans hTN
      have htN : t ≤ N := ht.trans hTN
      dsimp only
      rw [dyadicExtension_eq_of_mem hω hg_cont hg_dyad hsN,
        dyadicExtension_eq_of_mem hω hg_cont hg_dyad htN]
      exact hg_holder ⟨s, hsN⟩ ⟨t, htN⟩
    have hdiam : ∀ s ∈ Iic T, ∀ t ∈ Iic T, edist s t ≤ (T : ℝ≥0∞) := fun s hs t ht ↦ by
      rw [edist_dist, NNReal.dist_eq, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨?_, ?_⟩)
      · have hs' : (s : ℝ) ≤ T := hs
        linarith [t.coe_nonneg]
      · have ht' : (t : ℝ) ≤ T := ht
        linarith [s.coe_nonneg]
    exact ⟨_, hholder_k.of_le hdiam hk⟩
  · refine ⟨0, fun s _ t _ ↦ ?_⟩
    dsimp only
    rw [dyadicExtension_eq_of_notMem hω s, dyadicExtension_eq_of_notMem hω t, edist_self]
    exact zero_le

/-- **Kolmogorov–Chentsov extension from nonnegative rational times.** Let `X : ℚ≥0 → Ω → E` take
values in a complete extended metric Borel space `E`, with Borel-measurable pair evaluations and a
local Kolmogorov bound of exponents `p > 0` and `q > 1` on each bounded horizon `[0, N]`. Then `X`
extends to a process `Y : ℝ≥0 → Ω → E` such that:

1. `Y t` is Borel measurable for every `t : ℝ≥0`;
2. `t ↦ Y t ω` is continuous for *every* `ω : Ω`;
3. `Y r =ᵐ[P] X r` for every `r : ℚ≥0`;
4. every path `t ↦ Y t ω` is simultaneously `γ`-Hölder continuous on `Iic T` for all `γ : ℝ≥0`
   with `(γ : ℝ) < (q - 1) / p` and all `T : ℝ≥0`. -/
theorem exists_continuous_extension_of_nnrat {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0}
    (hp : 0 < p) (hq : 1 < q)
    (hpair : ∀ r s : ℚ≥0, Measurable[_, borel (E × E)] fun ω ↦ (X r ω, X s ω))
    (hkol : ∀ (N : ℕ) (r s : ℚ≥0), (r : ℝ≥0) ≤ N → (s : ℝ≥0) ≤ N →
      ∫⁻ ω, edist (X r ω) (X s ω) ^ p ∂P ≤ M N * edist (r : ℝ≥0) (s : ℝ≥0) ^ q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ r : ℚ≥0, Y r =ᵐ[P] X r) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  classical
  have hedist (r s : ℚ≥0) : Measurable fun ω ↦ edist (X r ω) (X s ω) := by
    borelize (E × E)
    exact continuous_edist.measurable.comp (hpair r s)
  have hmeasX (r : ℚ≥0) : Measurable (X r) :=
    (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hpair r r)
  have hX_loc (N : ℕ) :
      IsAEKolmogorovProcess (fun r : {r : ℚ≥0 // (r : ℝ≥0) ≤ N} ↦ X r.val) P p q (M N) :=
    IsKolmogorovProcess.IsAEKolmogorovProcess
      { measurablePair := fun r s ↦ hpair r.val s.val
        kolmogorovCondition := fun r s ↦ by
          simpa [Subtype.edist_eq] using hkol N r.val s.val r.property s.property
        p_pos := hp
        q_pos := zero_lt_one.trans hq }
  -- Intersect `goodDyadicEvent X N (γSeq k)` along a sequence `γSeq k ↑ (q - 1) / p`.
  let α : ℝ≥0 := Real.toNNReal ((q - 1) / p)
  have hα_coe : (α : ℝ) = (q - 1) / p := Real.coe_toNNReal _ (div_pos (sub_pos.2 hq) hp).le
  have hα_pos : 0 < α := NNReal.coe_pos.mp (hα_coe.symm ▸ div_pos (sub_pos.2 hq) hp)
  obtain ⟨γSeq, _, hγSeq_mem, hγSeq_tend⟩ := exists_seq_strictMono_tendsto' hα_pos
  have hγSeq_pos (k : ℕ) : 0 < γSeq k := (hγSeq_mem k).1
  have hγSeq_lt (k : ℕ) : (γSeq k : ℝ) < (q - 1) / p :=
    hα_coe ▸ NNReal.coe_lt_coe.mpr (hγSeq_mem k).2
  have hcofinal (γ : ℝ≥0) (hγ : (γ : ℝ) < (q - 1) / p) : ∃ k, γ ≤ γSeq k := by
    have hγ_lt : γ < α := NNReal.coe_lt_coe.mp (hα_coe.symm ▸ hγ)
    obtain ⟨k, hk⟩ := (hγSeq_tend.eventually (eventually_gt_nhds hγ_lt)).exists
    exact ⟨k, hk.le⟩
  let G : Set Ω := ⋂ N : ℕ, ⋂ k : ℕ, goodDyadicEvent X N (γSeq k)
  have hG_meas : MeasurableSet G :=
    MeasurableSet.iInter fun N ↦ MeasurableSet.iInter fun k ↦
      measurableSet_goodDyadicEvent hedist N (γSeq k)
  have hG_ae : ∀ᵐ ω ∂P, ω ∈ G := by
    simp only [G, mem_iInter, ae_all_iff]
    exact fun N k ↦ ae_mem_goodDyadicEvent (hγSeq_lt k) (hX_loc N)
  have hG_sub (ω : Ω) (hω : ω ∈ G) (N k : ℕ) : ω ∈ goodDyadicEvent X N (γSeq k) :=
    mem_iInter.mp (mem_iInter.mp hω N) k
  exact ⟨dyadicExtension X G,
    measurable_dyadicExtension (hγSeq_pos 0) hmeasX hG_meas (fun ω hω N ↦ hG_sub ω hω N 0),
    continuous_dyadicExtension (hγSeq_pos 0) (fun ω hω N ↦ hG_sub ω hω N 0),
    ae_eq_dyadicExtension_of_nnrat (hγSeq_pos 0) hG_ae (fun ω hω N ↦ hG_sub ω hω N 0) hX_loc,
    exists_holderOnWith_dyadicExtension hγSeq_pos hcofinal hG_sub⟩

/-- Glue local `IsAEKolmogorovProcess` versions across horizons `N : ℕ` into a single rational-time
process `X' : ℚ≥0 → Ω → E` with Borel-measurable pairs and the same local Kolmogorov bounds. -/
private lemma exists_nnrat_gluing_of_local_isAEKolmogorovProcess
    {Ω E : Type*} {_ : MeasurableSpace Ω} [Nonempty Ω] [EMetricSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0}
    (hX : ∀ N : ℕ, IsAEKolmogorovProcess (fun t : Iic (N : ℝ≥0) ↦ X t) P p q (M N)) :
    ∃ X' : ℚ≥0 → Ω → E,
      (∀ r : ℚ≥0, X' r =ᵐ[P] X r) ∧
      (∀ r s : ℚ≥0, Measurable[_, borel (E × E)] fun ω ↦ (X' r ω, X' s ω)) ∧
      (∀ (N : ℕ) (r s : ℚ≥0), (r : ℝ≥0) ≤ N → (s : ℝ≥0) ≤ N →
        ∫⁻ ω, edist (X' r ω) (X' s ω) ^ p ∂P ≤ M N * edist (r : ℝ≥0) (s : ℝ≥0) ^ q) := by
  classical
  let e₀ : E := X 0 (Classical.arbitrary Ω)
  let Z (N : ℕ) : Iic (N : ℝ≥0) → Ω → E := (hX N).mk _
  let N₀ (r : ℚ≥0) : ℕ := ⌈((r : ℝ≥0) : ℝ)⌉₊
  have hr₀ (r : ℚ≥0) : (r : ℝ≥0) ≤ N₀ r := by exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
  -- Step 1: collect a measurable null set `S` covering all disagreements across horizons `N`.
  let bad (r : ℚ≥0) (N : ℕ) : Set Ω :=
    if h : (r : ℝ≥0) ≤ N then
      toMeasurable P {ω | Z (N₀ r) ⟨r, hr₀ r⟩ ω ≠ Z N ⟨r, h⟩ ω}
    else ∅
  let S : Set Ω := ⋃ r : ℚ≥0, ⋃ N : ℕ, bad r N
  have hS_meas : MeasurableSet S := MeasurableSet.iUnion fun r ↦ MeasurableSet.iUnion fun N ↦ by
    simp only [bad]
    split_ifs
    · exact measurableSet_toMeasurable P _
    · exact MeasurableSet.empty
  have hS_zero : P S = 0 := measure_iUnion_null fun r ↦ measure_iUnion_null fun N ↦ by
    simp only [bad]
    split_ifs with h
    · rw [measure_toMeasurable]
      exact ((hX (N₀ r)).ae_eq_mk ⟨r, hr₀ r⟩).symm.trans ((hX N).ae_eq_mk ⟨r, h⟩)
    · exact measure_empty
  -- Step 2: define `X'` by constant fallback `e₀` on `S`, so pairs match `Z (max (N₀ r) (N₀ s))`.
  let X' : ℚ≥0 → Ω → E := fun r ω ↦ if ω ∈ S then e₀ else Z (N₀ r) ⟨r, hr₀ r⟩ ω
  have hX'_ae (r : ℚ≥0) : X' r =ᵐ[P] X r := by
    filter_upwards [compl_mem_ae_iff.2 hS_zero, (hX (N₀ r)).ae_eq_mk ⟨r, hr₀ r⟩] with ω hω hZ
    have hnot : ω ∉ S := hω
    simp [X', hnot, Z, hZ]
  refine ⟨X', hX'_ae, fun r s ↦ ?_, fun N r s hr hs ↦ ?_⟩
  · let N := max (N₀ r) (N₀ s)
    have hrN : (r : ℝ≥0) ≤ N := (hr₀ r).trans (Nat.cast_le.2 (le_max_left _ _))
    have hsN : (s : ℝ≥0) ≤ N := (hr₀ s).trans (Nat.cast_le.2 (le_max_right _ _))
    have heq : (fun ω ↦ (X' r ω, X' s ω)) =
        S.piecewise (fun _ ↦ (e₀, e₀)) (fun ω ↦ (Z N ⟨r, hrN⟩ ω, Z N ⟨s, hsN⟩ ω)) := by
      ext ω <;> by_cases hω : ω ∈ S <;> simp only [Set.piecewise, X', hω, ↓reduceIte]
      · have hnot : ω ∉ bad r N := fun h ↦ hω (mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨N, h⟩⟩)
        simp only [bad, hrN, ↓reduceDIte] at hnot
        exact not_not.mp fun hne ↦ hnot (subset_toMeasurable P _ hne)
      · have hnot : ω ∉ bad s N := fun h ↦ hω (mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨N, h⟩⟩)
        simp only [bad, hsN, ↓reduceDIte] at hnot
        exact not_not.mp fun hne ↦ hnot (subset_toMeasurable P _ hne)
    rw [heq]
    let : MeasurableSpace (E × E) := borel (E × E)
    exact Measurable.piecewise hS_meas measurable_const
      ((hX N).IsKolmogorovProcess_mk.measurablePair ⟨r, hrN⟩ ⟨s, hsN⟩)
  · have hcongr : (fun ω ↦ edist (X' r ω) (X' s ω) ^ p) =ᵐ[P]
        fun ω ↦ edist (X r ω) (X s ω) ^ p := by
      filter_upwards [hX'_ae r, hX'_ae s] with ω hrω hsω
      rw [hrω, hsω]
    rw [lintegral_congr_ae hcongr]
    exact (hX N).kolmogorovCondition ⟨r, hr⟩ ⟨s, hs⟩

/-- **Local one-dimensional Kolmogorov–Chentsov theorem on `ℝ≥0`.** If `X : ℝ≥0 → Ω → E` into a
complete extended metric Borel space satisfies `IsAEKolmogorovProcess` on each compact horizon
`Iic (N : ℝ≥0)` with exponents `p > 0` and `q > 1`, then `X` admits an all-paths continuous,
coordinatewise measurable modification `Y` whose sample paths are all simultaneously `γ`-Hölder
continuous on `Iic T` for every `γ : ℝ≥0` with `(γ : ℝ) < (q - 1) / p` and every `T : ℝ≥0`. -/
theorem exists_continuous_modification_of_local_isAEKolmogorovProcess
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0} (hq : 1 < q)
    (hX : ∀ N : ℕ, IsAEKolmogorovProcess (fun t : Iic (N : ℝ≥0) ↦ X t) P p q (M N)) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨X, fun _ _ _ ↦ by convert MeasurableSet.empty; exact eq_empty_of_isEmpty _,
      isEmptyElim, fun _ ↦ EventuallyEq.rfl, isEmptyElim⟩
  obtain ⟨X', hX'_ae, hpair', hkol'⟩ := exists_nnrat_gluing_of_local_isAEKolmogorovProcess hX
  obtain ⟨Y, hY_meas, hY_cont, hY_nnrat, hY_holder⟩ :=
    exists_continuous_extension_of_nnrat (hX 0).p_pos hq hpair' hkol'
  refine ⟨Y, hY_meas, hY_cont, fun t ↦ ?_, hY_holder⟩
  let N := ⌈(t : ℝ)⌉₊
  have htN : t ≤ N := by exact_mod_cast Nat.le_ceil (t : ℝ)
  have hu (n : ℕ) :
      edist
        (⟨approxDyadicNNRat n t, (coe_approxDyadicNNRat_le n t).trans htN⟩ : Iic (N : ℝ≥0))
        (⟨t, htN⟩ : Iic (N : ℝ≥0)) ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [Subtype.edist_eq]
    simpa using edist_approxDyadicNNRat_le n t
  have hae_dyad : ∀ᵐ ω ∂P, ∀ n, Y (approxDyadicNNRat n t) ω = X (approxDyadicNNRat n t) ω :=
    ae_all_iff.mpr fun n ↦ (hY_nnrat (approxDyadicNNRat n t)).trans (hX'_ae _)
  filter_upwards [(hX N).ae_tendsto_of_edist_le_pow (r := 2⁻¹) (by norm_num) hu, hae_dyad]
    with ω hX_tend hYX
  have hY_tend : Tendsto (fun n ↦ X (approxDyadicNNRat n t) ω) atTop (𝓝 (Y t ω)) :=
    ((hY_cont ω).tendsto t).comp (tendsto_approxDyadicNNRat t) |>.congr hYX
  exact tendsto_nhds_unique hY_tend hX_tend

end StochasticExtension

end TauCeti

namespace ProbabilityTheory

/-- **One-dimensional Kolmogorov–Chentsov theorem** for `IsAEKolmogorovProcess` on `ℝ≥0`. -/
theorem IsAEKolmogorovProcess.exists_continuous_modification
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) :=
  TauCeti.exists_continuous_modification_of_local_isAEKolmogorovProcess (M := fun _ ↦ M) hq
    fun _ ↦
      ⟨fun t ↦ hX.mk X t.val,
        { measurablePair := fun s t ↦ hX.IsKolmogorovProcess_mk.measurablePair s.val t.val
          kolmogorovCondition := fun s t ↦ hX.IsKolmogorovProcess_mk.kolmogorovCondition s.val t.val
          p_pos := hX.p_pos
          q_pos := hX.q_pos },
        fun t ↦ hX.ae_eq_mk t.val⟩

/-- **One-dimensional Kolmogorov–Chentsov theorem** for `IsKolmogorovProcess` on `ℝ≥0`. -/
theorem IsKolmogorovProcess.exists_continuous_modification
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) :=
  hX.IsAEKolmogorovProcess.exists_continuous_modification hq

end ProbabilityTheory
