/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.UniformSpace.UniformEmbedding
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Kolmogorov.Edges
import TauCeti.Topology.MetricSpace.Chaining
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Kolmogorov–Chentsov continuous and Hölder modification theorem

Given a stochastic process `X : T → Ω → E` satisfying the Kolmogorov increment condition
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q` (`IsAEKolmogorovProcess X P p q M`)
with values in a complete extended metric space `E`, we construct measurable modifications with
everywhere continuous and locally Hölder sample paths:

* `IsKolmogorovProcess.of_integral_dist_rpow_le`: adapter from Bochner `p`-moment bounds on
  `dist (X s ω) (X t ω)` to `IsKolmogorovProcess`.
* `IsKolmogorovProcess.exists_holderWith_of_dense`: uniformly extends an everywhere `γ`-Hölder
  Kolmogorov process from a dense subset `D ⊆ T` to all of `T`, preserving pair Borel
  measurability (without assuming `SecondCountableTopology E`) and the Kolmogorov bound.
* `IsAEKolmogorovProcess.exists_holderWith_modification_of_coveringNumber_le`: on a bounded
  pseudo-emetric space `T` whose small-scale internal covering numbers satisfy
  `coveringNumber ε univ ≤ C * ε ^ (-d)` for `0 < ε ≤ 1`, constructs a modification `Y` with
  `IsKolmogorovProcess Y P p q M` and everywhere `γ`-Hölder paths whenever `0 < γ` and
  `d + p * γ < q` (Krätschmer–Urusov, Theorem 1.1).
* `IsAEKolmogorovProcess.exists_holderWith_extension_of_dense_of_coveringNumber_le`: extends a
  Kolmogorov process defined only on a dense subset `D ⊆ T` to an everywhere `γ`-Hölder
  Kolmogorov process on `T`.
* `IsAEKolmogorovProcess.exists_continuous_modification_of_isOpen_iUnion` and
  `IsAEKolmogorovProcess.exists_continuous_extension_of_dense_of_isOpen_iUnion`: patches local
  Hölder modifications along an increasing open exhaustion of a noncompact parameter space.
* `IsAEKolmogorovProcess.exists_continuous_modification_of_finiteDimensional`,
  `IsAEKolmogorovProcess.exists_continuous_modification_nnreal`, and
  `IsAEKolmogorovProcess.exists_continuous_extension_of_dense_nnreal`: corollaries for
  finite-dimensional real normed spaces (in particular `ℝ`) and `ℝ≥0` when `dim + p * γ < q`.

## References

* V. Krätschmer, M. Urusov, *A general Kolmogorov–Chentsov type theorem on general metric spaces*,
  arXiv:2107.13837v2, Theorem 1.1.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 2.2.8.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section MomentAdapter

/-- Adapter from real Bochner `p`-moment increment bounds to `IsKolmogorovProcess`. Pair Borel
measurability is assumed directly, so second countability of `E` is not needed. -/
theorem IsKolmogorovProcess.of_integral_dist_rpow_le {T Ω E : Type*}
    [PseudoMetricSpace T] [PseudoMetricSpace E] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hp : 0 < p) (hq : 0 < q)
    (hpair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω))
    (hint : ∀ s t : T, Integrable (fun ω ↦ dist (X s ω) (X t ω) ^ p) P)
    (hbound : ∀ s t : T, ∫ ω, dist (X s ω) (X t ω) ^ p ∂P ≤ (M : ℝ) * dist s t ^ q) :
    IsKolmogorovProcess X P p q M where
  measurablePair := hpair
  p_pos := hp
  q_pos := hq
  kolmogorovCondition s t := by
    have heq : ∀ ω, edist (X s ω) (X t ω) ^ p = ENNReal.ofReal (dist (X s ω) (X t ω) ^ p) := by
      intro ω
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint s t)
      (Eventually.of_forall fun _ ↦ Real.rpow_nonneg dist_nonneg p)]
    refine (ENNReal.ofReal_le_ofReal (hbound s t)).trans_eq ?_
    rw [ENNReal.ofReal_mul M.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le, ← edist_dist]

end MomentAdapter

namespace IsAEKolmogorovProcess

/-- Extending `ae_exists_edist_le_mul_pow_rpow` to edge lengths bounded by `A * r ^ n` for an
arbitrary constant `A : ℝ≥0`. -/
theorem ae_exists_edist_le_mul_pow_rpow_of_le_mul {T Ω E : Type*}
    [PseudoEMetricSpace T] [PseudoEMetricSpace E] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0} {k : ℕ → ℕ}
    {s t : (n : ℕ) → Fin (k n) → T}
    (hX : IsAEKolmogorovProcess X P p q M)
    {C A r : ℝ≥0} {d γ : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hcard : ∀ n, (k n : ℝ≥0) ≤ C * (r ^ (-d)) ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n)
    (hγ : d + p * γ < q) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n i,
      edist (X (s n i) ω) (X (t n i) ω) ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
  -- Shift the scale index by `m₀` chosen so that `A * r ^ m₀ ≤ 1`.
  have htend : Tendsto (fun m : ℕ ↦ A * r ^ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hr₁).const_mul A
  obtain ⟨m₀, hm₀⟩ := ((tendsto_order.1 htend).2 1 zero_lt_one).exists
  have hcard_shift : ∀ n, (k (n + m₀) : ℝ≥0) ≤ (C * (r ^ (-d)) ^ m₀) * (r ^ (-d)) ^ n := by
    intro n
    refine (hcard (n + m₀)).trans_eq ?_
    rw [pow_add]
    ring
  have hedge_shift : ∀ n (i : Fin (k (n + m₀))),
      edist (s (n + m₀) i) (t (n + m₀) i) ≤ (r : ℝ≥0∞) ^ n := by
    intro n i
    calc
      edist (s (n + m₀) i) (t (n + m₀) i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ (n + m₀) :=
        hedge (n + m₀) i
      _ = ((A * r ^ m₀ : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
        rw [pow_add, ENNReal.coe_mul, ENNReal.coe_pow]
        ring
      _ ≤ 1 * (r : ℝ≥0∞) ^ n := by
        gcongr
        exact_mod_cast hm₀.le
      _ = (r : ℝ≥0∞) ^ n := one_mul _
  have htail := hX.ae_exists_edist_le_mul_pow_rpow hr hr₁ hcard_shift hedge_shift hγ
  -- The finitely many edges at levels `n < m₀` each have a.e. finite increment.
  have hhead : ∀ n ∈ Finset.range m₀, ∀ᵐ ω ∂P, ∀ i : Fin (k n),
      edist (X (s n i) ω) (X (t n i) ω) < ⊤ := by
    intro n _
    rw [ae_all_iff]
    intro i
    have hlt : ∫⁻ ω, edist (X (s n i) ω) (X (t n i) ω) ^ p ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (hX.kolmogorovCondition (s n i) (t n i))
      have hed_ne : edist (s n i) (t n i) ≠ ⊤ :=
        ne_top_of_le_ne_top
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
          (hedge n i)
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hX.q_pos.le hed_ne)
    filter_upwards [ae_lt_top' (hX.aemeasurable_edist.pow_const p) hlt] with ω hω
    by_contra htop
    rw [eq_top_iff.2 (not_lt.1 htop), ENNReal.top_rpow_of_pos hX.p_pos] at hω
    exact lt_irrefl _ hω
  filter_upwards [htail, (ae_ball_iff (Finset.countable_toSet _)).2 hhead] with ω hω_tail hω_head
  obtain ⟨K₁, hK₁⟩ := hω_tail
  let S_head : Finset ℝ≥0 :=
    (Finset.range m₀).biUnion fun n ↦
      Finset.univ.image fun i : Fin (k n) ↦
        (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n
  let K : ℝ≥0 := max (K₁ * (r ^ (-γ)) ^ m₀) (S_head.sup id)
  refine ⟨K, fun n i ↦ ?_⟩
  rcases lt_or_ge n m₀ with hnm | hnm
  · have hfin : edist (X (s n i) ω) (X (t n i) ω) ≠ ⊤ :=
      (hω_head n (Finset.mem_range.2 hnm) i).ne
    have hmem : (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n ∈ S_head :=
      Finset.mem_biUnion.2
        ⟨n, Finset.mem_range.2 hnm, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    have hle_K : (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n ≤ K :=
      (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)
    calc
      edist (X (s n i) ω) (X (t n i) ω) =
          (((edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n : ℝ≥0) : ℝ≥0∞) *
            ((r ^ γ : ℝ≥0) : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin, mul_assoc, ← ENNReal.coe_pow,
          ← ENNReal.coe_mul, ← mul_pow, ← NNReal.rpow_add hr.ne', neg_add_cancel,
          NNReal.rpow_zero, one_pow, ENNReal.coe_one, mul_one]
      _ ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
        rw [ENNReal.coe_rpow_of_ne_zero hr.ne', ENNReal.pow_rpow_comm]
        gcongr
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hnm
    calc
      edist (X (s (n' + m₀) i) ω) (X (t (n' + m₀) i) ω) ≤
          (K₁ : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n') ^ γ := hK₁ n' i
      _ = ((K₁ * (r ^ (-γ)) ^ m₀ : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (n' + m₀)) ^ γ := by
        rw [ENNReal.pow_rpow_comm, ENNReal.pow_rpow_comm,
          ← ENNReal.coe_rpow_of_ne_zero hr.ne', ← ENNReal.coe_pow, ← ENNReal.coe_pow,
          ← ENNReal.coe_mul, ← ENNReal.coe_mul]
        congr 1
        rw [pow_add, mul_assoc, mul_left_comm ((r ^ (-γ)) ^ m₀), ← mul_pow,
          ← NNReal.rpow_add hr.ne', neg_add_cancel, NNReal.rpow_zero, one_pow, mul_one]
      _ ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (n' + m₀)) ^ γ := by
        gcongr
        exact_mod_cast le_max_left _ _

end IsAEKolmogorovProcess

section DenseExtension

/-- Every point of a pseudo-emetric space is a sequential limit of a dense subset. -/
private lemma exists_seq_tendsto_of_dense {T : Type*} [PseudoEMetricSpace T]
    {D : Set T} (hD : Dense D) (s : T) :
    ∃ u : ℕ → D,
      Tendsto (fun n ↦ (u n : T)) atTop (𝓝 s) ∧
      Tendsto (fun n ↦ edist (u n : T) s) atTop (𝓝 0) := by
  have hmem : ∀ n : ℕ, ∃ y ∈ D, edist s y < ((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n := fun n ↦
    EMetric.mem_closure_iff.1 (hD s) (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n)
      (ENNReal.coe_pow (1 / 2 : ℝ≥0) n ▸ ENNReal.coe_pos.2 (pow_pos (by norm_num) n))
  choose u huD hud using hmem
  have hr1 : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < 1 := by norm_num
  have htend0 : Tendsto (fun n : ℕ ↦ edist ((⟨u n, huD n⟩ : D) : T) s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
      (fun _ ↦ zero_le) (fun n ↦ edist_comm s (u n) ▸ (hud n).le)
  exact ⟨fun n ↦ ⟨u n, huD n⟩, EMetric.tendsto_nhds.2 fun ε hε ↦
    (tendsto_order.1 htend0).2 ε hε, htend0⟩

/-- Uniformly extends an everywhere `γ`-Hölder Kolmogorov process (`γ > 0`) from a dense subset
`D ⊆ T` to the whole space `T`, preserving pair Borel measurability without assuming second
countability of `E`. -/
theorem IsKolmogorovProcess.exists_holderWith_of_dense {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {D : Set T} (hD : Dense D) {Y₀ : D → Ω → E}
    {p q : ℝ} {M γ : ℝ≥0} (hγ : 0 < γ)
    (hY₀ : IsKolmogorovProcess Y₀ P p q M)
    (hH : ∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y₀ · ω)) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω (L : ℝ≥0), HolderWith L γ (Y₀ · ω) → HolderWith L γ (Y · ω)) ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y · ω)) ∧
      ∀ (d : D) ω, Y d.1 ω = Y₀ d ω := by
  have hi := isUniformInducing_val D
  have hd : DenseRange ((↑) : D → T) := hD.denseRange_val
  let Y : T → Ω → E := fun t ω ↦ (hi.isDenseInducing hd).extend (Y₀ · ω) t
  have hY_eq : ∀ (d : D) ω, Y d.1 ω = Y₀ d ω := by
    intro d ω
    obtain ⟨L, hL⟩ := hH ω
    exact uniformly_extend_of_ind hi hd (hL.uniformContinuous hγ) d
  have hY_cont : ∀ ω, Continuous (Y · ω) := by
    intro ω
    obtain ⟨L, hL⟩ := hH ω
    exact (uniformContinuous_uniformly_extend hi hd (hL.uniformContinuous hγ)).continuous
  have hY_holder : ∀ ω (L : ℝ≥0), HolderWith L γ (Y₀ · ω) → HolderWith L γ (Y · ω) := by
    intro ω L hL s t
    have hclosed : IsClosed
        {q : T × T | edist (Y q.1 ω) (Y q.2 ω) ≤ (L : ℝ≥0∞) * edist q.1 q.2 ^ (γ : ℝ)} :=
      isClosed_le ((hY_cont ω).fst'.edist (hY_cont ω).snd')
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          (ENNReal.continuous_rpow_const.comp continuous_edist))
    have hsub : D ×ˢ D ⊆
        {q : T × T | edist (Y q.1 ω) (Y q.2 ω) ≤ (L : ℝ≥0∞) * edist q.1 q.2 ^ (γ : ℝ)} := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      simp only [mem_ofPred_eq, hY_eq ⟨u, hu⟩ ω, hY_eq ⟨v, hv⟩ ω]
      exact hL ⟨u, hu⟩ ⟨v, hv⟩
    exact hclosed.closure_subset_iff.2 hsub ((hD.prod hD).closure_eq.symm ▸ mem_univ (s, t))
  have hY_kol : IsKolmogorovProcess Y P p q M := by
    refine ⟨fun s t ↦ ?_, fun s t ↦ ?_, hY₀.p_pos, hY₀.q_pos⟩
    · borelize (E × E)
      obtain ⟨u, hu, -⟩ := exists_seq_tendsto_of_dense hD s
      obtain ⟨v, hv, -⟩ := exists_seq_tendsto_of_dense hD t
      refine measurable_of_tendsto_metrizable
        (f := fun n ω ↦ (Y₀ (u n) ω, Y₀ (v n) ω)) (fun n ↦ ?_)
        (tendsto_pi_nhds.2 fun ω ↦ ?_)
      · simpa only [BorelSpace.measurable_eq] using hY₀.measurablePair (u n) (v n)
      · simp_rw [← hY_eq]
        exact (((hY_cont ω).tendsto s).comp hu).prodMk_nhds (((hY_cont ω).tendsto t).comp hv)
    · rcases eq_or_ne M 0 with rfl | hM0
      · obtain ⟨u, hu, -⟩ := exists_seq_tendsto_of_dense hD s
        obtain ⟨v, hv, -⟩ := exists_seq_tendsto_of_dense hD t
        have hlim : ∀ ω,
            edist (Y s ω) (Y t ω) ^ p =
              liminf (fun n ↦ edist (Y₀ (u n) ω) (Y₀ (v n) ω) ^ p) atTop := by
          intro ω
          refine (Tendsto.liminf_eq ?_).symm
          simp_rw [← hY_eq]
          exact (ENNReal.continuous_rpow_const.tendsto _).comp
            ((((hY_cont ω).tendsto s).comp hu).edist (((hY_cont ω).tendsto t).comp hv))
        simp_rw [hlim, ENNReal.coe_zero, zero_mul]
        refine (lintegral_liminf_le fun n ↦
          (hY₀.measurable_edist (s := u n) (t := v n)).pow_const p).trans ?_
        refine liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall fun n ↦ ?_))
        simpa using hY₀.kolmogorovCondition (u n) (v n)
      · rcases eq_or_ne (edist s t) ⊤ with hst_top | _
        · simp [hst_top, ENNReal.top_rpow_of_pos hY₀.q_pos, hM0]
        · obtain ⟨u, hu, -⟩ := exists_seq_tendsto_of_dense hD s
          obtain ⟨v, hv, -⟩ := exists_seq_tendsto_of_dense hD t
          have hlim : ∀ ω,
              edist (Y s ω) (Y t ω) ^ p =
                liminf (fun n ↦ edist (Y₀ (u n) ω) (Y₀ (v n) ω) ^ p) atTop := by
            intro ω
            refine (Tendsto.liminf_eq ?_).symm
            simp_rw [← hY_eq]
            exact (ENNReal.continuous_rpow_const.tendsto _).comp
              ((((hY_cont ω).tendsto s).comp hu).edist (((hY_cont ω).tendsto t).comp hv))
          have hed_tend : Tendsto (fun n ↦ edist (u n : T) (v n : T)) atTop (𝓝 (edist s t)) :=
            hu.edist hv
          have hrhs_tend : Tendsto
              (fun n ↦ (M : ℝ≥0∞) * edist (u n) (v n) ^ q) atTop
              (𝓝 ((M : ℝ≥0∞) * edist s t ^ q)) := by
            have h1 := (ENNReal.continuous_rpow_const (y := q).tendsto (edist s t)).comp hed_tend
            exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.coe_ne_top)
          rw [← hrhs_tend.liminf_eq]
          simp_rw [hlim]
          refine (lintegral_liminf_le fun n ↦
            (hY₀.measurable_edist (s := u n) (t := v n)).pow_const p).trans ?_
          exact liminf_le_liminf (Eventually.of_forall fun n ↦ hY₀.kolmogorovCondition (u n) (v n))
  exact ⟨Y, hY_kol, hY_holder, fun ω ↦ let ⟨L, hL⟩ := hH ω; ⟨L, hY_holder ω L hL⟩, hY_eq⟩

end DenseExtension

namespace IsAEKolmogorovProcess

/-- **Kolmogorov–Chentsov Hölder modification theorem on bounded metric spaces**
(Krätschmer–Urusov, Theorem 1.1). If `T` has finite extended diameter and internal covering numbers
bounded by `C * ε ^ (-d)` for `0 < ε ≤ 1`, then every `IsAEKolmogorovProcess X P p q M` with values
in a nonempty complete metric space admits an `IsKolmogorovProcess` modification whose paths are
everywhere `γ`-Hölder for any `γ > 0` with `d + p * γ < q`. -/
theorem exists_holderWith_modification_of_coveringNumber_le {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
    {p q d : ℝ} {M C γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hdiam : ediam (univ : Set T) ≠ ⊤)
    (hd : 0 ≤ d)
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set T) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d))
    (hγ0 : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y · ω)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  classical
  let X' := hX.mk X
  have hX' : IsKolmogorovProcess X' P p q M := hX.IsKolmogorovProcess_mk
  let d' : ℝ := (d + (q - p * γ)) / 2
  have hdd' : d < d' := by dsimp [d']; linarith
  have hd'γ : d' + p * γ < q := by dsimp [d']; linarith
  have hr0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ≥0) < 1 := by norm_num
  obtain ⟨U, k, s, t, C_edge, A, -, -, hU_dense_sub, -, hk_card, hst_len, hchain⟩ :=
    TauCeti.exists_edges_and_holderOnWith_of_coveringNumber_le
      (D := (ediam (univ : Set T)).toNNReal)
      (by simp [ENNReal.coe_toNNReal hdiam]) hr0 hr1 hd hdd' hcov
  have hU_dense : Dense U := dense_iff_closure_eq.2 (subset_antisymm (subset_univ _) hU_dense_sub)
  obtain ⟨C_H, hC_H⟩ := hchain hγ0
  have hae_edge := hX'.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow_of_le_mul
    hr0 hr1 hk_card hst_len hd'γ
  -- Enclose the exceptional null set in a measurable null set `N`.
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hae_edge
  obtain ⟨e₀⟩ := ‹Nonempty E›
  let Y₀ : U → Ω → E := fun u ω ↦ if ω ∈ N then e₀ else X' u.1 ω
  have hY₀_ae : ∀ u : U, Y₀ u =ᵐ[P] X' u.1 := by
    intro u
    filter_upwards [compl_mem_ae_iff.2 hN_null] with ω hω
    exact ite_eq_right hω
  have hY₀_kol : IsKolmogorovProcess Y₀ P p q M := by
    refine ⟨fun u v ↦ ?_, fun u v ↦ ?_, hX'.p_pos, hX'.q_pos⟩
    · let : MeasurableSpace (E × E) := borel (E × E)
      have hite : (fun ω ↦ (Y₀ u ω, Y₀ v ω)) =
          fun ω ↦ if ω ∈ N then (e₀, e₀) else (X' u.1 ω, X' v.1 ω) := by
        funext ω
        by_cases hω : ω ∈ N
        · simp only [Y₀, ite_eq_left hω]
        · simp only [Y₀, ite_eq_right hω]
      rw [hite]
      exact Measurable.ite (p := (· ∈ N)) hN_meas measurable_const
        (hX'.measurablePair u.1 v.1)
    · refine (lintegral_congr_ae ?_).trans_le (hX'.kolmogorovCondition u.1 v.1)
      filter_upwards [hY₀_ae u, hY₀_ae v] with ω hu hv
      simp [hu, hv]
  have hY₀_holder : ∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y₀ · ω) := by
    intro ω
    by_cases hωN : ω ∈ N
    · refine ⟨0, fun u v ↦ by simp [Y₀, hωN]⟩
    · have hω_good : ∃ K : ℝ≥0, ∀ n i,
          edist (X' (s n i) ω) (X' (t n i) ω) ≤
            (K : ℝ≥0∞) * (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n) ^ (γ : ℝ) :=
        not_not.1 fun h ↦ hωN (hN_sub h)
      obtain ⟨K_ω, hK_ω⟩ := hω_good
      have hH_U : HolderOnWith (C_H * K_ω) γ (X' · ω) U := hC_H (X' · ω) K_ω hK_ω
      refine ⟨C_H * K_ω, fun u v ↦ ?_⟩
      dsimp only [Y₀]
      rw [ite_eq_right hωN, ite_eq_right hωN]
      exact hH_U u.1 u.2 v.1 v.2
  obtain ⟨Y, hY_kol, -, hY_holder, hY_eq⟩ :=
    hY₀_kol.exists_holderWith_of_dense hU_dense hγ0 hY₀_holder
  refine ⟨Y, hY_kol, hY_holder, fun t ↦ ?_⟩
  -- Identify `Y t =ᵐ[P] X' t` via Fatou along a sequence `u n ∈ U` converging to `t`.
  obtain ⟨u, hut, hud0⟩ := exists_seq_tendsto_of_dense hU_dense t
  have hY_cont : ∀ ω, Continuous (Y · ω) := fun ω ↦
    let ⟨L, hL⟩ := hY_holder ω; hL.continuous hγ0
  have hed_tend : ∀ ω,
      Tendsto (fun n ↦ edist (Y (u n) ω) (X' t ω) ^ p) atTop
        (𝓝 (edist (Y t ω) (X' t ω) ^ p)) := fun ω ↦
    (ENNReal.continuous_rpow_const.tendsto _).comp
      ((((hY_cont ω).tendsto t).comp hut).edist tendsto_const_nhds)
  have hYu_ae : ∀ n, (fun ω ↦ edist (Y (u n) ω) (X' t ω) ^ p) =ᵐ[P]
      fun ω ↦ edist (X' (u n) ω) (X' t ω) ^ p := by
    intro n
    filter_upwards [hY₀_ae (u n)] with ω hω
    rw [hY_eq (u n) ω, hω]
  have haemeas_seq : ∀ n, AEMeasurable (fun ω ↦ edist (Y (u n) ω) (X' t ω) ^ p) P := fun n ↦
    ((hX'.measurable_edist (s := (u n : T)) (t := t)).pow_const p).aemeasurable.congr
      (hYu_ae n).symm
  have haemeas_lim : AEMeasurable (fun ω ↦ edist (Y t ω) (X' t ω) ^ p) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop haemeas_seq (Eventually.of_forall hed_tend)
  have hlint0 : ∫⁻ ω, edist (Y t ω) (X' t ω) ^ p ∂P ≤ 0 := by
    have hlim : ∀ ω, edist (Y t ω) (X' t ω) ^ p =
        liminf (fun n ↦ edist (Y (u n) ω) (X' t ω) ^ p) atTop :=
      fun ω ↦ ((hed_tend ω).liminf_eq).symm
    have hrhs0 : Tendsto (fun n ↦ (M : ℝ≥0∞) * edist (u n : T) t ^ q) atTop (𝓝 0) := by
      have hq0 : (0 : ℝ≥0∞) ^ q = 0 := ENNReal.zero_rpow_of_pos hX'.q_pos
      have ht1 : Tendsto (fun n ↦ edist (u n : T) t ^ q) atTop (𝓝 ((0 : ℝ≥0∞) ^ q)) :=
        (ENNReal.continuous_rpow_const (y := q).tendsto 0).comp hud0
      have h0 : Tendsto (fun n ↦ (M : ℝ≥0∞) * edist (u n : T) t ^ q) atTop
          (𝓝 ((M : ℝ≥0∞) * (0 : ℝ≥0∞) ^ q)) :=
        ENNReal.Tendsto.const_mul ht1 (Or.inr ENNReal.coe_ne_top)
      simpa only [hq0, mul_zero] using h0
    rw [← hrhs0.liminf_eq]
    simp_rw [hlim]
    refine (lintegral_liminf_le' haemeas_seq).trans ?_
    refine liminf_le_liminf (Eventually.of_forall fun n ↦ ?_)
    exact (lintegral_congr_ae (hYu_ae n)).trans_le (hX'.kolmogorovCondition (u n) t)
  have hed_zero : (fun ω ↦ edist (Y t ω) (X' t ω) ^ p) =ᵐ[P] 0 :=
    (lintegral_eq_zero_iff' haemeas_lim).1 (nonpos_iff_eq_zero.1 hlint0)
  filter_upwards [hed_zero, hX.ae_eq_mk t] with ω hω hXX'
  have hed0 : edist (Y t ω) (X' t ω) = 0 := by
    simpa [hX'.p_pos, not_lt_of_gt hX'.p_pos] using hω
  exact (_root_.edist_eq_zero.1 hed0).trans hXX'.symm

/-- **Dense-subset Kolmogorov–Chentsov Hölder extension.** A Kolmogorov process defined only on a
dense subset `D` of finite extended diameter and covering dimension `d` extends to an
`IsKolmogorovProcess` on the whole space `T` with everywhere `γ`-Hölder paths (`d + p * γ < q`),
agreeing almost everywhere with `X` at every point of `D`. -/
theorem exists_holderWith_extension_of_dense_of_coveringNumber_le {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set T} (hD : Dense D)
    {X : D → Ω → E} {p q d : ℝ} {M C γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hdiam : ediam D ≠ ⊤)
    (hd : 0 ≤ d)
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε D : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d))
    (hγ0 : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y · ω)) ∧
      ∀ t : D, Y t.1 =ᵐ[P] X t := by
  have hiso : Isometry ((↑) : D → T) := isometry_subtype_coe
  have hdiam_D : ediam (univ : Set D) ≠ ⊤ := by
    have h := hiso.ediam_image univ
    rw [Subtype.coe_image_univ] at h
    exact h ▸ hdiam
  have hcov_D : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set D) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d) := by
    intro ε hε0 hε1
    have hcov_eq : coveringNumber ε (((↑) : D → T) '' univ) = coveringNumber ε (univ : Set D) :=
      hiso.coveringNumber_image' Subtype.val_injective.injOn
    rw [Subtype.coe_image_univ] at hcov_eq
    exact hcov_eq ▸ hcov ε hε0 hε1
  obtain ⟨Y₀, hY₀_kol, hY₀_holder, hY₀_ae⟩ :=
    hX.exists_holderWith_modification_of_coveringNumber_le hdiam_D hd hcov_D hγ0 hγ
  obtain ⟨Y, hY_kol, -, hY_holder, hY_eq⟩ :=
    hY₀_kol.exists_holderWith_of_dense hD hγ0 hY₀_holder
  refine ⟨Y, hY_kol, hY_holder, fun t ↦ ?_⟩
  filter_upwards [hY₀_ae t] with ω hω
  exact (hY_eq t ω).trans hω

/-- Finite dyadic covering numbers make a pseudo-emetric space separable. -/
private lemma separableSpace_of_coveringNumber_ne_top {α : Type*} [PseudoEMetricSpace α]
    (h : ∀ n : ℕ, coveringNumber ((1 / 2 : ℝ≥0) ^ n) (univ : Set α) ≠ ⊤) :
    SeparableSpace α := by
  refine ⟨⟨⋃ n : ℕ, minimalCover ((1 / 2 : ℝ≥0) ^ n) (univ : Set α),
    countable_iUnion fun n ↦ finite_minimalCover.countable, fun x ↦ ?_⟩⟩
  rw [EMetric.mem_closure_iff]
  intro ε hε
  have hr1 : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < 1 := by norm_num
  obtain ⟨n, hn⟩ := ((tendsto_order.1
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)).2 ε hε).exists
  obtain ⟨y, hy, hxy⟩ := isCover_minimalCover (h n) (mem_univ x)
  exact ⟨y, mem_iUnion.2 ⟨n, hy⟩, hxy.trans_lt (ENNReal.coe_pow (1 / 2 : ℝ≥0) n ▸ hn)⟩

/-- **Dense-subset Kolmogorov–Chentsov theorem along an increasing open exhaustion.** Given a
Kolmogorov process `X` on a dense subset `D ⊆ T` and an increasing open cover `U : ℕ → Set T` of
`T` such that each `U k` has finite extended diameter and covering dimension `d k` with
`d k + p * γ k < q` (`γ k > 0`), there exists an `IsKolmogorovProcess` extension `Y : T → Ω → E`
whose paths are everywhere continuous on `T` and everywhere `γ k`-Hölder on `U k`, agreeing almost
everywhere with `X` on `D`. -/
theorem exists_continuous_extension_of_dense_of_isOpen_iUnion {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set T} (hD : Dense D)
    {X : D → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_open : ∀ k, IsOpen (U k)) (hU_mono : Monotone U)
    (hU_univ : ⋃ k, U k = univ)
    {C γ : ℕ → ℝ≥0} {d : ℕ → ℝ}
    (hdiam : ∀ k, ediam (U k) ≠ ⊤)
    (hd : ∀ k, 0 ≤ d k)
    (hcov : ∀ k (ε : ℝ≥0), 0 < ε → ε ≤ 1 →
      (coveringNumber ε (U k) : ℝ≥0∞) ≤ (C k : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d k))
    (hγ0 : ∀ k, 0 < γ k)
    (hγ : ∀ k, d k + p * γ k < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ k ω, ∃ L : ℝ≥0, HolderOnWith L (γ k) (Y · ω) (U k)) ∧
      ∀ t : D, Y t.1 =ᵐ[P] X t := by
  classical
  let X' := hX.mk X
  have hX' : IsKolmogorovProcess X' P p q M := hX.IsKolmogorovProcess_mk
  -- On each open stage `U k`, restrict `X'` to the dense subset `D_k = (↑) ⁻¹' D ⊆ U k`.
  have hstage : ∀ k : ℕ, ∃ Yk : U k → Ω → E,
      SeparableSpace (U k) ∧
      IsKolmogorovProcess Yk P p q M ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L (γ k) (Yk · ω)) ∧
      ∀ (t : U k) (htD : t.1 ∈ D), Yk t =ᵐ[P] X' ⟨t.1, htD⟩ := by
    intro k
    let Dk : Set (U k) := ((↑) : U k → T) ⁻¹' D
    have hDk_dense : Dense Dk := by
      rw [dense_iff_inter_open]
      intro W hW ⟨w, hwW⟩
      obtain ⟨y, hyW, hyD⟩ := hD.inter_open_nonempty (((↑) : U k → T) '' W)
        ((hU_open k).isOpenMap_subtype_val W hW) ⟨w.1, mem_image_of_mem _ hwW⟩
      obtain ⟨u, huW, rfl⟩ := hyW
      exact ⟨u, huW, hyD⟩
    have hiso_k : Isometry ((↑) : U k → T) := isometry_subtype_coe
    have hcov_Uk : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
        (coveringNumber ε (univ : Set (U k)) : ℝ≥0∞) ≤
          (C k : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d k) := by
      intro ε hε0 hε1
      have hcov_eq : coveringNumber ε (((↑) : U k → T) '' univ) =
          coveringNumber ε (univ : Set (U k)) :=
        hiso_k.coveringNumber_image' Subtype.val_injective.injOn
      rw [Subtype.coe_image_univ] at hcov_eq
      exact hcov_eq ▸ hcov k ε hε0 hε1
    have hsep_Uk : SeparableSpace (U k) := separableSpace_of_coveringNumber_ne_top fun n ↦ by
      rw [← ENat.toENNReal_ne_top]
      have hrn0 : (0 : ℝ≥0) < (1 / 2) ^ n := pow_pos (by norm_num) n
      have hrn1 : ((1 / 2 : ℝ≥0) ^ n) ≤ 1 := pow_le_one₀ zero_le (by norm_num)
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast hrn0.ne') ENNReal.coe_ne_top))
        (hcov_Uk _ hrn0 hrn1)
    have hdiam_Dk : ediam Dk ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ediam_mono (subset_univ Dk))
      have h := hiso_k.ediam_image univ
      rw [Subtype.coe_image_univ] at h
      exact h ▸ hdiam k
    have hcov_Dk : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
        (coveringNumber ε Dk : ℝ≥0∞) ≤
          ((C k * (2 : ℝ≥0) ^ d k : ℝ≥0) : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d k) := by
      intro ε hε0 hε1
      have hsub : (coveringNumber ε Dk : ℝ≥0∞) ≤ coveringNumber (ε / 2) (univ : Set (U k)) := by
        exact_mod_cast coveringNumber_subset_le (subset_univ Dk)
      have hε2_pos : 0 < ε / 2 := half_pos hε0
      have hε2_le1 : ε / 2 ≤ 1 := (half_le_self zero_le).trans hε1
      refine hsub.trans ((hcov_Uk (ε / 2) hε2_pos hε2_le1).trans_eq ?_)
      rw [div_eq_mul_inv, ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.mul_rpow_of_ne_zero (by exact_mod_cast hε0.ne') (by norm_num),
        ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
        neg_neg, ← ENNReal.coe_rpow_of_ne_zero (by norm_num : (2 : ℝ≥0) ≠ 0)]
      ring
    let Xk : Dk → Ω → E := fun u ω ↦ X' ⟨u.1.1, u.2⟩ ω
    have hXk : IsKolmogorovProcess Xk P p q M :=
      ⟨fun u v ↦ hX'.measurablePair ⟨u.1.1, u.2⟩ ⟨v.1.1, v.2⟩,
       fun u v ↦ hX'.kolmogorovCondition ⟨u.1.1, u.2⟩ ⟨v.1.1, v.2⟩,
       hX'.p_pos, hX'.q_pos⟩
    obtain ⟨Yk, hYk_kol, hYk_holder, hYk_ae⟩ :=
      hXk.IsAEKolmogorovProcess.exists_holderWith_extension_of_dense_of_coveringNumber_le
        hDk_dense hdiam_Dk (hd k) hcov_Dk (hγ0 k) (hγ k)
    exact ⟨Yk, hsep_Uk, hYk_kol, hYk_holder, fun t htD ↦ hYk_ae ⟨t, htD⟩⟩
  choose Yk hsep_Uk hYk_kol hYk_holder hYk_ae using hstage
  -- Compatibility across all stages `k ≤ m` outside one measurable null set `N`.
  have hcompat : ∀ k m : ℕ, ∀ᵐ ω ∂P, ∀ (hkm : k ≤ m) (t : U k),
      Yk k t ω = Yk m ⟨t.1, hU_mono hkm t.2⟩ ω := by
    intro k m
    by_cases hkm : k ≤ m
    · have : SeparableSpace (U k) := hsep_Uk k
      let Dk : Set (U k) := ((↑) : U k → T) ⁻¹' D
      have hDk_dense : Dense Dk := by
        rw [dense_iff_inter_open]
        intro W hW ⟨w, hwW⟩
        obtain ⟨y, hyW, hyD⟩ := hD.inter_open_nonempty (((↑) : U k → T) '' W)
          ((hU_open k).isOpenMap_subtype_val W hW) ⟨w.1, mem_image_of_mem _ hwW⟩
        obtain ⟨u, huW, rfl⟩ := hyW
        exact ⟨u, huW, hyD⟩
      obtain ⟨Sk, hSk_sub, hSk_count, hSk_dense⟩ := hDk_dense.exists_countable_dense_subset
      have hind := TauCeti.indist_of_ae_continuous_of_dense hSk_count hSk_dense
        (Eventually.of_forall fun ω ↦ let ⟨L, hL⟩ := hYk_holder k ω; hL.continuous (hγ0 k))
        (Eventually.of_forall fun ω ↦
          let ⟨L, hL⟩ := hYk_holder m ω
          (hL.continuous (hγ0 m)).comp (continuous_inclusion (hU_mono hkm)))
        fun t htS ↦ (hYk_ae k t (hSk_sub htS)).trans
          (hYk_ae m ⟨t.1, hU_mono hkm t.2⟩ (hSk_sub htS)).symm
      filter_upwards [hind] with ω hω _ t using hω t
    · exact Eventually.of_forall fun _ h ↦ absurd h hkm
  have hae_all : ∀ᵐ ω ∂P, ∀ k m (hkm : k ≤ m) (t : U k),
      Yk k t ω = Yk m ⟨t.1, hU_mono hkm t.2⟩ ω :=
    ae_all_iff.2 fun k ↦ ae_all_iff.2 fun m ↦ hcompat k m
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hae_all
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hex_k : ∀ t : T, ∃ k, t ∈ U k := fun t ↦ mem_iUnion.1 (hU_univ ▸ mem_univ t)
  let k₀ : T → ℕ := fun t ↦ Nat.find (hex_k t)
  have hk₀_mem : ∀ t : T, t ∈ U (k₀ t) := fun t ↦ Nat.find_spec (hex_k t)
  let Y : T → Ω → E := fun t ω ↦ if ω ∈ N then e₀ else Yk (k₀ t) ⟨t, hk₀_mem t⟩ ω
  -- Outside `N`, `Y` agrees on every `U k` with `Yk k`.
  have hY_stage : ∀ {ω : Ω}, ω ∉ N → ∀ k {t : T} (ht : t ∈ U k),
      Y t ω = Yk k ⟨t, ht⟩ ω := by
    intro ω hωN k t ht
    have hgood : ∀ a b (hab : a ≤ b) (u : U a),
        Yk a u ω = Yk b ⟨u.1, hU_mono hab u.2⟩ ω := not_not.1 fun h ↦ hωN (hN_sub h)
    let m := max k (k₀ t)
    dsimp only [Y]
    rw [ite_eq_right hωN]
    exact (hgood (k₀ t) m (le_max_right k (k₀ t)) ⟨t, hk₀_mem t⟩).trans
      (hgood k m (le_max_left k (k₀ t)) ⟨t, ht⟩).symm
  have hY_holder_on : ∀ k ω, ∃ L : ℝ≥0, HolderOnWith L (γ k) (Y · ω) (U k) := by
    intro k ω
    by_cases hωN : ω ∈ N
    · refine ⟨0, fun x _ y _ ↦ ?_⟩
      dsimp only [Y]
      rw [ite_eq_left hωN, ite_eq_left hωN, edist_self]
      exact zero_le
    · obtain ⟨L, hL⟩ := hYk_holder k ω
      refine ⟨L, fun x hx y hy ↦ ?_⟩
      dsimp only
      rw [hY_stage hωN k hx, hY_stage hωN k hy]
      exact hL ⟨x, hx⟩ ⟨y, hy⟩
  have hY_cont : ∀ ω, Continuous (Y · ω) := by
    intro ω
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨L, hL⟩ := hY_holder_on (k₀ t) ω
    exact (hL.continuousOn (hγ0 (k₀ t))).continuousAt
      ((hU_open (k₀ t)).mem_nhds (hk₀_mem t))
  have hY_kol : IsKolmogorovProcess Y P p q M := by
    refine ⟨fun s t ↦ ?_, fun s t ↦ ?_, hX'.p_pos, hX'.q_pos⟩
    · let : MeasurableSpace (E × E) := borel (E × E)
      let m := max (k₀ s) (k₀ t)
      have hs_m : s ∈ U m := hU_mono (le_max_left _ _) (hk₀_mem s)
      have ht_m : t ∈ U m := hU_mono (le_max_right _ _) (hk₀_mem t)
      have hite : (fun ω ↦ (Y s ω, Y t ω)) =
          fun ω ↦ if ω ∈ N then (e₀, e₀) else (Yk m ⟨s, hs_m⟩ ω, Yk m ⟨t, ht_m⟩ ω) := by
        funext ω
        by_cases hωN : ω ∈ N
        · simp only [Y, ite_eq_left hωN]
        · rw [ite_eq_right hωN, hY_stage hωN m hs_m, hY_stage hωN m ht_m]
      rw [hite]
      exact Measurable.ite (p := (· ∈ N)) hN_meas measurable_const
        ((hYk_kol m).measurablePair ⟨s, hs_m⟩ ⟨t, ht_m⟩)
    · let m := max (k₀ s) (k₀ t)
      have hs_m : s ∈ U m := hU_mono (le_max_left _ _) (hk₀_mem s)
      have ht_m : t ∈ U m := hU_mono (le_max_right _ _) (hk₀_mem t)
      refine (lintegral_congr_ae ?_).trans_le ((hYk_kol m).kolmogorovCondition ⟨s, hs_m⟩ ⟨t, ht_m⟩)
      filter_upwards [compl_mem_ae_iff.2 hN_null] with ω hωN
      rw [hY_stage hωN m hs_m, hY_stage hωN m ht_m]
  refine ⟨Y, hY_kol, hY_cont, hY_holder_on, fun t ↦ ?_⟩
  filter_upwards [compl_mem_ae_iff.2 hN_null, hYk_ae (k₀ t.1) ⟨t.1, hk₀_mem t.1⟩ t.2,
    hX.ae_eq_mk t] with ω hωN hYk_eq hXX'
  exact (hY_stage hωN (k₀ t.1) (hk₀_mem t.1)).trans (hYk_eq.trans hXX'.symm)

/-- **Kolmogorov–Chentsov continuous modification theorem along an increasing open exhaustion.**
When `T` is covered by an increasing sequence of open sets `U k` of finite extended diameter and
covering dimension `d k` with `d k + p * γ k < q` (`γ k > 0`), any `IsAEKolmogorovProcess` has an
`IsKolmogorovProcess` modification whose paths are everywhere continuous and locally `γ k`-Hölder
on each `U k`. -/
theorem exists_continuous_modification_of_isOpen_iUnion {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_open : ∀ k, IsOpen (U k)) (hU_mono : Monotone U)
    (hU_univ : ⋃ k, U k = univ)
    {C γ : ℕ → ℝ≥0} {d : ℕ → ℝ}
    (hdiam : ∀ k, ediam (U k) ≠ ⊤)
    (hd : ∀ k, 0 ≤ d k)
    (hcov : ∀ k (ε : ℝ≥0), 0 < ε → ε ≤ 1 →
      (coveringNumber ε (U k) : ℝ≥0∞) ≤ (C k : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d k))
    (hγ0 : ∀ k, 0 < γ k)
    (hγ : ∀ k, d k + p * γ k < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ k ω, ∃ L : ℝ≥0, HolderOnWith L (γ k) (Y · ω) (U k)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  let X_univ : ↥(univ : Set T) → Ω → E := fun t ω ↦ X t.1 ω
  have hX_univ : IsAEKolmogorovProcess X_univ P p q M := by
    refine ⟨fun t ω ↦ hX.mk X t.1 ω,
      ⟨fun s t ↦ hX.IsKolmogorovProcess_mk.measurablePair s.1 t.1,
       fun s t ↦ hX.IsKolmogorovProcess_mk.kolmogorovCondition s.1 t.1,
       hX.p_pos, hX.q_pos⟩,
      fun t ↦ hX.ae_eq_mk t.1⟩
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX_univ.exists_continuous_extension_of_dense_of_isOpen_iUnion dense_univ
      hU_open hU_mono hU_univ hdiam hd hcov hγ0 hγ
  exact ⟨Y, hY_kol, hY_cont, hY_holder, fun t ↦ hY_ae ⟨t, mem_univ t⟩⟩

/-- Volumetric covering-number bound in `ε ^ (-finrank ℝ F)` form on bounded balls. -/
private lemma coveringNumber_ball_le_mul_rpow_neg_finrank {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) {ε : ℝ≥0} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (coveringNumber ε (ball (0 : F) (k + 1 : ℝ)) : ℝ≥0∞) ≤
      (((2 * k + 3 : ℕ) ^ Module.finrank ℝ F : ℝ≥0) : ℝ≥0∞) *
        (ε : ℝ≥0∞) ^ (-(Module.finrank ℝ F : ℝ)) := by
  have hsub : ball (0 : F) (k + 1 : ℝ) ⊆ closedBall (0 : F) ((k + 1 : ℝ≥0) : ℝ) := by
    simpa using ball_subset_closedBall
  refine (TauCeti.coveringNumber_le_of_subset_closedBall hε0.ne' hsub).trans ?_
  have h1 : (1 : ℝ≥0∞) + 2 * (k + 1 : ℝ≥0) / ε ≤ (2 * k + 3 : ℕ) * (ε : ℝ≥0∞)⁻¹ := by
    have hε_inv : (1 : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.one_le_inv]
      exact_mod_cast hε1
    calc
      (1 : ℝ≥0∞) + 2 * (k + 1 : ℝ≥0) / ε = 1 + (2 * (k + 1 : ℝ≥0)) * (ε : ℝ≥0∞)⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ (ε : ℝ≥0∞)⁻¹ + (2 * (k + 1 : ℝ≥0)) * (ε : ℝ≥0∞)⁻¹ := by gcongr
      _ = (2 * k + 3 : ℕ) * (ε : ℝ≥0∞)⁻¹ := by push_cast; ring
  calc
    (1 + 2 * ((k + 1 : ℝ≥0) : ℝ≥0∞) / ε) ^ Module.finrank ℝ F ≤
        ((2 * k + 3 : ℕ) * (ε : ℝ≥0∞)⁻¹) ^ Module.finrank ℝ F := pow_le_pow_left' h1 _
    _ = (((2 * k + 3 : ℕ) ^ Module.finrank ℝ F : ℝ≥0) : ℝ≥0∞) *
          (ε : ℝ≥0∞) ^ (-(Module.finrank ℝ F : ℝ)) := by
      rw [mul_pow, ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
      push_cast
      rfl

/-- **Kolmogorov–Chentsov theorem on finite-dimensional real normed spaces.** When
`Module.finrank ℝ F + p * γ < q` (`γ > 0`), any `IsAEKolmogorovProcess` indexed by `F` with values
in a nonempty complete metric space admits an everywhere-continuous `IsKolmogorovProcess`
modification that is `γ`-Hölder on every ball around the origin (hence on every bounded set). -/
theorem exists_continuous_modification_of_finiteDimensional {F Ω E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : F → Ω → E}
    {p q : ℝ} {M γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hγ0 : 0 < γ) (hγ : (Module.finrank ℝ F : ℝ) + p * γ < q) :
    ∃ Y : F → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ (R : ℝ≥0) ω, ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (closedBall 0 R)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  let U : ℕ → Set F := fun k ↦ ball 0 (k + 1 : ℝ)
  have hU_open : ∀ k, IsOpen (U k) := fun _ ↦ isOpen_ball
  have hU_mono : Monotone U := fun _ _ hij ↦
    ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hU_univ : ⋃ k, U k = univ := eq_univ_of_forall fun x ↦ by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.2 ⟨k, mem_ball_zero_iff.2 (hk.trans (by linarith))⟩
  have hdiam : ∀ k, ediam (U k) ≠ ⊤ := fun _ ↦ isBounded_ball.ediam_ne_top
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX.exists_continuous_modification_of_isOpen_iUnion hU_open hU_mono hU_univ hdiam
      (fun _ ↦ Nat.cast_nonneg _)
      (fun k _ hε0 hε1 ↦ coveringNumber_ball_le_mul_rpow_neg_finrank k hε0 hε1)
      (fun _ ↦ hγ0) (fun _ ↦ hγ)
  refine ⟨Y, hY_kol, hY_cont, fun R ω ↦ ?_, hY_ae⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (R : ℝ)
  obtain ⟨L, hL⟩ := hY_holder k ω
  refine ⟨L, hL.mono ?_⟩
  exact closedBall_subset_ball (hk.trans (by linarith))

/-- **Dense-subset Kolmogorov–Chentsov extension on `ℝ≥0`.** A Kolmogorov process defined on a
dense subset `D ⊆ ℝ≥0` with `1 + p * γ < q` (`γ > 0`) extends to an everywhere-continuous
`IsKolmogorovProcess` on `ℝ≥0` that is `γ`-Hölder on every compact horizon `[0, T]`. -/
theorem exists_continuous_extension_of_dense_nnreal {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set ℝ≥0} (hD : Dense D)
    {X : D → Ω → E} {p q : ℝ} {M γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hγ0 : 0 < γ) (hγ : 1 + p * γ < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ (T : ℝ≥0) ω, ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (Icc 0 T)) ∧
      ∀ t : D, Y t.1 =ᵐ[P] X t := by
  let U : ℕ → Set ℝ≥0 := fun k ↦ Iio (k + 1 : ℝ≥0)
  have hU_open : ∀ k, IsOpen (U k) := fun _ ↦ isOpen_Iio
  have hU_mono : Monotone U := fun _ _ hij ↦
    Iio_subset_Iio (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hU_univ : ⋃ k, U k = univ := eq_univ_of_forall fun t ↦ by
    obtain ⟨k, hk⟩ := exists_nat_gt t
    exact mem_iUnion.2 ⟨k, mem_Iio.2 (hk.trans (lt_add_one _))⟩
  have hdiam : ∀ k, ediam (U k) ≠ ⊤ := by
    intro k
    refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := k + 1))
      (ediam_le fun s hs t ht ↦ ?_)
    rw [edist_nndist, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nndist, NNReal.dist_eq]
    push_cast
    have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
    have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
    have hs1 : (s : ℝ) < k + 1 := by exact_mod_cast (mem_Iio.1 hs : s < (k : ℝ≥0) + 1)
    have ht1 : (t : ℝ) < k + 1 := by exact_mod_cast (mem_Iio.1 ht : t < (k : ℝ≥0) + 1)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hcov : ∀ k (ε : ℝ≥0), 0 < ε → ε ≤ 1 →
      (coveringNumber ε (U k) : ℝ≥0∞) ≤
        ((2 * (2 * k + 3) : ℕ) : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-(1 : ℝ)) := by
    intro k ε hε0 hε1
    have hiso : Isometry ((↑) : ℝ≥0 → ℝ) := NNReal.isometry_coe
    rw [← hiso.coveringNumber_image (A := U k)]
    have himg : ((↑) : ℝ≥0 → ℝ) '' U k ⊆ ball (0 : ℝ) (k + 1 : ℝ) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_ball_zero_iff, Real.norm_of_nonneg t.coe_nonneg]
      exact_mod_cast (mem_Iio.1 ht : t < (k : ℝ≥0) + 1)
    have hsub : (coveringNumber ε (((↑) : ℝ≥0 → ℝ) '' U k) : ℝ≥0∞) ≤
        coveringNumber (ε / 2) (ball (0 : ℝ) (k + 1 : ℝ)) := by
      exact_mod_cast coveringNumber_subset_le himg
    have hε2_pos : 0 < ε / 2 := half_pos hε0
    have hε2_le1 : ε / 2 ≤ 1 := (half_le_self zero_le).trans hε1
    refine hsub.trans ((coveringNumber_ball_le_mul_rpow_neg_finrank k hε2_pos hε2_le1).trans_eq ?_)
    rw [Module.finrank_self, pow_one, Nat.cast_one, div_eq_mul_inv, ENNReal.coe_mul,
      ENNReal.mul_rpow_of_ne_zero (by exact_mod_cast hε0.ne') (by norm_num),
      ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
      neg_neg, ENNReal.rpow_one]
    push_cast
    ring
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX.exists_continuous_extension_of_dense_of_isOpen_iUnion hD hU_open hU_mono hU_univ hdiam
      (fun _ ↦ zero_le_one) hcov (fun _ ↦ hγ0) (fun _ ↦ hγ)
  refine ⟨Y, hY_kol, hY_cont, fun T ω ↦ ?_, hY_ae⟩
  obtain ⟨k, hk⟩ := exists_nat_gt T
  obtain ⟨L, hL⟩ := hY_holder k ω
  exact ⟨L, hL.mono fun t ht ↦ mem_Iio.2 (ht.2.trans_lt (hk.trans (lt_add_one _)))⟩

/-- **One-dimensional Kolmogorov–Chentsov modification on `ℝ≥0`.** When `1 + p * γ < q` (`γ > 0`),
every `IsAEKolmogorovProcess` indexed by `ℝ≥0` with values in a nonempty complete metric space has
an everywhere-continuous `IsKolmogorovProcess` modification whose paths are `γ`-Hölder on every
compact interval `[0, T]`. -/
theorem exists_continuous_modification_nnreal {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] [Nonempty E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    {p q : ℝ} {M γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hγ0 : 0 < γ) (hγ : 1 + p * γ < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ (T : ℝ≥0) ω, ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (Icc 0 T)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  let X_univ : ↥(univ : Set ℝ≥0) → Ω → E := fun t ω ↦ X t.1 ω
  have hX_univ : IsAEKolmogorovProcess X_univ P p q M :=
    ⟨fun t ω ↦ hX.mk X t.1 ω,
      ⟨fun s t ↦ hX.IsKolmogorovProcess_mk.measurablePair s.1 t.1,
       fun s t ↦ hX.IsKolmogorovProcess_mk.kolmogorovCondition s.1 t.1,
       hX.p_pos, hX.q_pos⟩,
      fun t ↦ hX.ae_eq_mk t.1⟩
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX_univ.exists_continuous_extension_of_dense_nnreal dense_univ hγ0 hγ
  exact ⟨Y, hY_kol, hY_cont, hY_holder, fun t ↦ hY_ae ⟨t, mem_univ t⟩⟩

end IsAEKolmogorovProcess

end ProbabilityTheory
