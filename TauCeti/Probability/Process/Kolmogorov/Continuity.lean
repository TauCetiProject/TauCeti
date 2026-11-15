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
    have hfun : (fun ω ↦ edist (X s ω) (X t ω) ^ p) =
        fun ω ↦ ENNReal.ofReal (dist (X s ω) (X t ω) ^ p) :=
      funext fun ω ↦ by rw [edist_dist, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (hint s t)
      (Eventually.of_forall fun _ ↦ Real.rpow_nonneg dist_nonneg p)]
    refine (ENNReal.ofReal_le_ofReal (hbound s t)).trans_eq ?_
    rw [ENNReal.ofReal_mul M.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le, ← edist_dist]

end MomentAdapter

namespace IsAEKolmogorovProcess

private lemma comp_isometry {S T Ω E : Type*} [PseudoEMetricSpace S] [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
    {p q : ℝ} {M : ℝ≥0} (hX : IsAEKolmogorovProcess X P p q M) {f : S → T} (hf : Isometry f) :
    IsAEKolmogorovProcess (fun s ↦ X (f s)) P p q M :=
  ⟨fun s ↦ hX.mk X (f s),
    ⟨fun s t ↦ hX.IsKolmogorovProcess_mk.measurablePair (f s) (f t),
     fun s t ↦ by
       simpa [hf.edist_eq] using hX.IsKolmogorovProcess_mk.kolmogorovCondition (f s) (f t),
     hX.p_pos, hX.q_pos⟩,
    fun s ↦ hX.ae_eq_mk (f s)⟩

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
  have htend : Tendsto (fun m : ℕ ↦ A * r ^ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hr₁).const_mul A
  obtain ⟨m₀, hm₀⟩ := ((tendsto_order.1 htend).2 1 zero_lt_one).exists
  have hcard_shift : ∀ n, (k (n + m₀) : ℝ≥0) ≤ (C * (r ^ (-d)) ^ m₀) * (r ^ (-d)) ^ n :=
    fun n ↦ (hcard (n + m₀)).trans_eq (by rw [pow_add]; ring)
  have hedge_shift : ∀ n i, edist (s (n + m₀) i) (t (n + m₀) i) ≤ (r : ℝ≥0∞) ^ n := fun n i ↦ by
    have hm₀' : ((A * r ^ m₀ : ℝ≥0) : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_coe.2 hm₀.le
    calc
      edist (s (n + m₀) i) (t (n + m₀) i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ (n + m₀) :=
        hedge (n + m₀) i
      _ = ((A * r ^ m₀ : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_mul, ENNReal.coe_pow, pow_add]; ring
      _ ≤ 1 * (r : ℝ≥0∞) ^ n := mul_le_mul_of_nonneg_right hm₀' zero_le
      _ = (r : ℝ≥0∞) ^ n := one_mul _
  have hhead : ∀ n ∈ Finset.range m₀, ∀ᵐ ω ∂P, ∀ i : Fin (k n),
      edist (X (s n i) ω) (X (t n i) ω) < ⊤ := fun n _ ↦ ae_all_iff.2 fun i ↦ by
    have hed_ne : edist (s n i) (t n i) ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)) (hedge n i)
    have hlt : ∫⁻ ω, edist (X (s n i) ω) (X (t n i) ω) ^ p ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hX.q_pos.le hed_ne)) (hX.kolmogorovCondition _ _)
    filter_upwards [ae_lt_top' (hX.aemeasurable_edist.pow_const p) hlt] with ω hω
    exact lt_top_iff_ne_top.2 fun htop ↦ by simp [htop, hX.p_pos] at hω
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow hr hr₁ hcard_shift hedge_shift hγ,
    (ae_ball_iff (Finset.countable_toSet _)).2 hhead] with ω ⟨K₁, hK₁⟩ hω_head
  let S_head : Finset ℝ≥0 := (Finset.range m₀).biUnion fun n ↦ Finset.univ.image fun i : Fin (k n) ↦
    (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n
  let K : ℝ≥0 := max (K₁ * (r ^ (-γ)) ^ m₀) (S_head.sup id)
  refine ⟨K, fun n i ↦ ?_⟩
  rcases lt_or_ge n m₀ with hnm | hnm
  · have hfin : edist (X (s n i) ω) (X (t n i) ω) ≠ ⊤ := (hω_head n (Finset.mem_range.2 hnm) i).ne
    have hle_K : (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n ≤ K :=
      (Finset.le_sup (f := id) (Finset.mem_biUnion.2
        ⟨n, Finset.mem_range.2 hnm, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)).trans
        (le_max_right _ _)
    calc
      edist (X (s n i) ω) (X (t n i) ω) =
          (((edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n : ℝ≥0) : ℝ≥0∞) *
            ((r ^ γ : ℝ≥0) : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin, mul_assoc, ← ENNReal.coe_pow,
          ← ENNReal.coe_mul, ← mul_pow, ← NNReal.rpow_add hr.ne', neg_add_cancel,
          NNReal.rpow_zero, one_pow, ENNReal.coe_one, mul_one]
      _ ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
        rw [ENNReal.coe_rpow_of_ne_zero hr.ne', ENNReal.pow_rpow_comm]; gcongr
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hnm
    refine (hK₁ n' i).trans ?_
    have heq : (K₁ : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n') ^ γ =
        ((K₁ * (r ^ (-γ)) ^ m₀ : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (n' + m₀)) ^ γ := by
      rw [ENNReal.pow_rpow_comm, ENNReal.pow_rpow_comm, ← ENNReal.coe_rpow_of_ne_zero hr.ne',
        ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      congr 1
      rw [pow_add, mul_assoc, mul_left_comm ((r ^ (-γ)) ^ m₀), ← mul_pow,
        ← NNReal.rpow_add hr.ne', neg_add_cancel, NNReal.rpow_zero, one_pow, mul_one]
    have hK₁_le : ((K₁ * (r ^ (-γ)) ^ m₀ : ℝ≥0) : ℝ≥0∞) ≤ K :=
      ENNReal.coe_le_coe.2 (le_max_left _ _)
    exact heq.trans_le (mul_le_mul_of_nonneg_right hK₁_le zero_le)

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
  have htend0 : Tendsto (fun n : ℕ ↦ edist ((⟨u n, huD n⟩ : D) : T) s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
      (fun _ ↦ zero_le) (fun n ↦ edist_comm s (u n) ▸ (hud n).le)
  exact ⟨fun n ↦ ⟨u n, huD n⟩,
    EMetric.tendsto_nhds.2 fun ε hε ↦ (tendsto_order.1 htend0).2 ε hε, htend0⟩

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
  have hY_eq : ∀ (d : D) ω, Y d.1 ω = Y₀ d ω := fun d ω ↦
    let ⟨_, hL⟩ := hH ω; uniformly_extend_of_ind hi hd (hL.uniformContinuous hγ) d
  have hY_cont : ∀ ω, Continuous (Y · ω) := fun ω ↦
    let ⟨_, hL⟩ := hH ω
    (uniformContinuous_uniformly_extend hi hd (hL.uniformContinuous hγ)).continuous
  have hY_holder : ∀ ω (L : ℝ≥0), HolderWith L γ (Y₀ · ω) → HolderWith L γ (Y · ω) := by
    intro ω L hL s t
    have hclosed : IsClosed
        {q : T × T | edist (Y q.1 ω) (Y q.2 ω) ≤ (L : ℝ≥0∞) * edist q.1 q.2 ^ (γ : ℝ)} :=
      isClosed_le ((hY_cont ω).fst'.edist (hY_cont ω).snd')
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          (ENNReal.continuous_rpow_const.comp continuous_edist))
    refine hclosed.closure_subset_iff.2 ?_ ((hD.prod hD).closure_eq.symm ▸ mem_univ (s, t))
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    rw [mem_ofPred_eq, hY_eq ⟨u, hu⟩ ω, hY_eq ⟨v, hv⟩ ω]
    exact hL ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨Y, ⟨fun s t ↦ ?_, fun s t ↦ ?_, hY₀.p_pos, hY₀.q_pos⟩, hY_holder,
    fun ω ↦ let ⟨L, hL⟩ := hH ω; ⟨L, hY_holder ω L hL⟩, hY_eq⟩
  · borelize (E × E)
    obtain ⟨u, hu, -⟩ := exists_seq_tendsto_of_dense hD s
    obtain ⟨v, hv, -⟩ := exists_seq_tendsto_of_dense hD t
    refine measurable_of_tendsto_metrizable (f := fun n ω ↦ (Y₀ (u n) ω, Y₀ (v n) ω))
      (fun n ↦ by simpa only [BorelSpace.measurable_eq] using hY₀.measurablePair (u n) (v n))
      (tendsto_pi_nhds.2 fun ω ↦ ?_)
    simp_rw [← hY_eq]
    exact (((hY_cont ω).tendsto s).comp hu).prodMk_nhds (((hY_cont ω).tendsto t).comp hv)
  · by_cases htop : M ≠ 0 ∧ edist s t = ⊤
    · simp [htop.2, ENNReal.top_rpow_of_pos hY₀.q_pos, htop.1]
    obtain ⟨u, hu, -⟩ := exists_seq_tendsto_of_dense hD s
    obtain ⟨v, hv, -⟩ := exists_seq_tendsto_of_dense hD t
    have hlim : ∀ ω, edist (Y s ω) (Y t ω) ^ p =
        liminf (fun n ↦ edist (Y₀ (u n) ω) (Y₀ (v n) ω) ^ p) atTop := fun ω ↦ by
      refine (Tendsto.liminf_eq ?_).symm
      simp_rw [← hY_eq]
      exact (ENNReal.continuous_rpow_const.tendsto _).comp
        ((((hY_cont ω).tendsto s).comp hu).edist (((hY_cont ω).tendsto t).comp hv))
    have hrhs : Tendsto (fun n ↦ (M : ℝ≥0∞) * edist (u n : T) (v n : T) ^ q) atTop
        (𝓝 ((M : ℝ≥0∞) * edist s t ^ q)) :=
      ENNReal.Tendsto.const_mul
        ((ENNReal.continuous_rpow_const (y := q).tendsto _).comp (hu.edist hv))
        (Or.inr ENNReal.coe_ne_top)
    rw [← hrhs.liminf_eq]
    simp_rw [hlim]
    exact (lintegral_liminf_le fun n ↦
      (hY₀.measurable_edist (s := u n) (t := v n)).pow_const p).trans
      (liminf_le_liminf (Eventually.of_forall fun n ↦ hY₀.kolmogorovCondition (u n) (v n)))

end DenseExtension

namespace IsAEKolmogorovProcess

/-- Replacing a Kolmogorov process by a constant on a measurable null set preserves
`IsKolmogorovProcess`. -/
private lemma isKolmogorovProcess_ite_null {T Ω E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
    {p q : ℝ} {M : ℝ≥0} (hX : IsKolmogorovProcess X P p q M) {N : Set Ω}
    [DecidablePred (· ∈ N)] (hN_meas : MeasurableSet N) (hN_null : P N = 0) (e₀ : E) :
    IsKolmogorovProcess (fun t ω ↦ if ω ∈ N then e₀ else X t ω) P p q M where
  measurablePair s t := by
    let : MeasurableSpace (E × E) := borel (E × E)
    have hite : (fun ω ↦ (if ω ∈ N then e₀ else X s ω, if ω ∈ N then e₀ else X t ω)) =
        fun ω ↦ if ω ∈ N then (e₀, e₀) else (X s ω, X t ω) :=
      funext fun ω ↦ by split_ifs <;> rfl
    rw [hite]
    exact Measurable.ite hN_meas measurable_const (hX.measurablePair s t)
  kolmogorovCondition s t := by
    refine (lintegral_congr_ae ?_).trans_le (hX.kolmogorovCondition s t)
    filter_upwards [compl_mem_ae_iff.2 hN_null] with ω (hωN : ω ∉ N)
    rw [ite_eq_right hωN, ite_eq_right hωN]
  p_pos := hX.p_pos
  q_pos := hX.q_pos

/-- Identifying a continuous process with a Kolmogorov process `X'` at `t` from a.e. agreement on a
dense set `U` via Fatou's lemma. -/
private lemma ae_eq_of_dense_edist_tendsto {T Ω E : Type*} [PseudoEMetricSpace T]
    [EMetricSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {U : Set T} (hU : Dense U)
    {Y X' : T → Ω → E} {p q : ℝ} {M : ℝ≥0} (hX' : IsKolmogorovProcess X' P p q M)
    (hY_cont : ∀ ω, Continuous (Y · ω)) (hU_ae : ∀ u : U, Y u.1 =ᵐ[P] X' u.1) (t : T) :
    Y t =ᵐ[P] X' t := by
  obtain ⟨u, hut, hud0⟩ := exists_seq_tendsto_of_dense hU t
  have hed_tend : ∀ ω, Tendsto (fun n ↦ edist (Y (u n) ω) (X' t ω) ^ p) atTop
      (𝓝 (edist (Y t ω) (X' t ω) ^ p)) := fun ω ↦
    (ENNReal.continuous_rpow_const.tendsto _).comp
      ((((hY_cont ω).tendsto t).comp hut).edist tendsto_const_nhds)
  have hYu_ae : ∀ n, (fun ω ↦ edist (Y (u n) ω) (X' t ω) ^ p) =ᵐ[P]
      fun ω ↦ edist (X' (u n) ω) (X' t ω) ^ p := fun n ↦ by
    filter_upwards [hU_ae (u n)] with ω hω; rw [hω]
  have haemeas_seq : ∀ n, AEMeasurable (fun ω ↦ edist (Y (u n) ω) (X' t ω) ^ p) P := fun n ↦
    ((hX'.measurable_edist (s := (u n : T)) (t := t)).pow_const p).aemeasurable.congr
      (hYu_ae n).symm
  have haemeas_lim : AEMeasurable (fun ω ↦ edist (Y t ω) (X' t ω) ^ p) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop haemeas_seq (Eventually.of_forall hed_tend)
  have hrhs0 : Tendsto (fun n ↦ (M : ℝ≥0∞) * edist (u n : T) t ^ q) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hX'.q_pos, mul_zero] using
      ENNReal.Tendsto.const_mul ((ENNReal.continuous_rpow_const (y := q).tendsto 0).comp hud0)
        (Or.inr ENNReal.coe_ne_top)
  have hlint0 : ∫⁻ ω, edist (Y t ω) (X' t ω) ^ p ∂P ≤ 0 := by
    rw [← hrhs0.liminf_eq]
    simp_rw [fun ω ↦ ((hed_tend ω).liminf_eq).symm]
    exact (lintegral_liminf_le' haemeas_seq).trans (liminf_le_liminf
      (Eventually.of_forall fun n ↦ (lintegral_congr_ae (hYu_ae n)).trans_le
        (hX'.kolmogorovCondition (u n) t)))
  filter_upwards [(lintegral_eq_zero_iff' haemeas_lim).1 (nonpos_iff_eq_zero.1 hlint0)] with ω hω
  exact _root_.edist_eq_zero.1 (by simpa [hX'.p_pos, not_lt_of_gt hX'.p_pos] using hω)

/-- **Kolmogorov–Chentsov Hölder modification theorem on bounded metric spaces**
(Krätschmer–Urusov, Theorem 1.1). If `T` has finite extended diameter and internal covering numbers
bounded by `C * ε ^ (-d)` for `0 < ε ≤ 1`, then every `IsAEKolmogorovProcess X P p q M` with values
in a complete metric space admits an `IsKolmogorovProcess` modification whose paths are everywhere
`γ`-Hölder for any `γ > 0` with `d + p * γ < q`. -/
theorem exists_holderWith_modification_of_coveringNumber_le {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
    {p q d : ℝ} {M C γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hdiam : ediam (univ : Set T) ≠ ⊤)
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set T) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d))
    (hγ0 : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y · ω)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  classical
  cases isEmpty_or_nonempty T
  · exact ⟨isEmptyElim, ⟨isEmptyElim, isEmptyElim, hX.p_pos, hX.q_pos⟩,
      fun _ ↦ ⟨0, isEmptyElim⟩, isEmptyElim⟩
  cases isEmpty_or_nonempty Ω
  · exact ⟨fun _ ↦ isEmptyElim,
      ⟨fun _ _ _ _ ↦ by convert @MeasurableSet.empty _ mΩ; ext x; exact isEmptyElim x,
        fun _ _ ↦ by simp [Measure.eq_zero_of_isEmpty P], hX.p_pos, hX.q_pos⟩,
      isEmptyElim, fun _ ↦ Eventually.of_forall isEmptyElim⟩
  obtain ⟨t₀⟩ := ‹Nonempty T›
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  let e₀ : E := X t₀ ω₀
  let X' := hX.mk X
  have hX' : IsKolmogorovProcess X' P p q M := hX.IsKolmogorovProcess_mk
  let d' : ℝ := (d + (q - p * γ)) / 2
  have hdd' : d < d' := by dsimp [d']; linarith
  have hd'γ : d' + p * γ < q := by dsimp [d']; linarith
  obtain ⟨U, k, s, t, C_edge, A, -, -, hU_dense_sub, -, hk_card, hst_len, hchain⟩ :=
    TauCeti.exists_edges_and_holderOnWith_of_coveringNumber_le
      (D := (ediam (univ : Set T)).toNNReal) (r := 1 / 2)
      (by simp [ENNReal.coe_toNNReal hdiam]) (by norm_num) (by norm_num) hdd' hcov
  have hU_dense : Dense U := dense_iff_closure_eq.2 (subset_antisymm (subset_univ _) hU_dense_sub)
  obtain ⟨C_H, hC_H⟩ := hchain hγ0
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null
    (hX'.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow_of_le_mul
      (by norm_num) (by norm_num) hk_card hst_len hd'γ)
  let Y₀ : U → Ω → E := fun u ω ↦ if ω ∈ N then e₀ else X' u.1 ω
  have hY₀_kol : IsKolmogorovProcess Y₀ P p q M :=
    isKolmogorovProcess_ite_null
      ⟨fun (u v : U) ↦ hX'.measurablePair u.1 v.1,
       fun (u v : U) ↦ hX'.kolmogorovCondition u.1 v.1,
       hX'.p_pos, hX'.q_pos⟩ hN_meas hN_null e₀
  have hY₀_holder : ∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y₀ · ω) := fun ω ↦ by
    by_cases hωN : ω ∈ N
    · exact ⟨0, fun _ _ ↦ by simp [Y₀, hωN]⟩
    · obtain ⟨K_ω, hK_ω⟩ := not_not.1 fun h ↦ hωN (hN_sub h)
      refine ⟨C_H * K_ω, fun u v ↦ ?_⟩
      dsimp only [Y₀]
      rw [ite_eq_right hωN, ite_eq_right hωN]
      exact hC_H (X' · ω) K_ω hK_ω u.1 u.2 v.1 v.2
  obtain ⟨Y, hY_kol, -, hY_holder, hY_eq⟩ :=
    hY₀_kol.exists_holderWith_of_dense hU_dense hγ0 hY₀_holder
  refine ⟨Y, hY_kol, hY_holder, fun t ↦ ?_⟩
  have hU_ae : ∀ u : U, Y u.1 =ᵐ[P] X' u.1 := fun u ↦ by
    filter_upwards [compl_mem_ae_iff.2 hN_null] with ω (hωN : ω ∉ N)
    rw [hY_eq u ω]; exact ite_eq_right hωN
  exact (ae_eq_of_dense_edist_tendsto hU_dense hX'
    (fun ω ↦ let ⟨_, hL⟩ := hY_holder ω; hL.continuous hγ0) hU_ae t).trans (hX.ae_eq_mk t).symm

/-- **Dense-subset Kolmogorov–Chentsov Hölder extension.** A Kolmogorov process defined only on a
dense subset `D` of finite extended diameter and covering dimension `d` extends to an
`IsKolmogorovProcess` on the whole space `T` with everywhere `γ`-Hölder paths (`d + p * γ < q`),
agreeing almost everywhere with `X` at every point of `D`. -/
theorem exists_holderWith_extension_of_dense_of_coveringNumber_le {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set T} (hD : Dense D)
    {X : D → Ω → E} {p q d : ℝ} {M C γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hdiam : ediam D ≠ ⊤)
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε D : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d))
    (hγ0 : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L γ (Y · ω)) ∧
      ∀ t : D, Y t.1 =ᵐ[P] X t := by
  have hiso : Isometry ((↑) : D → T) := isometry_subtype_coe
  have hdiam_D : ediam (univ : Set D) ≠ ⊤ := by
    rw [← hiso.ediam_image, Subtype.coe_image_univ]
    exact hdiam
  have hcov_D : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set D) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d) := fun ε h0 h1 ↦ by
    have heq := hiso.coveringNumber_image' Subtype.val_injective.injOn (ε := ε) (A := univ)
    rw [Subtype.coe_image_univ] at heq
    exact heq ▸ hcov ε h0 h1
  obtain ⟨Y₀, hY₀_kol, hY₀_holder, hY₀_ae⟩ :=
    hX.exists_holderWith_modification_of_coveringNumber_le hdiam_D hcov_D hγ0 hγ
  obtain ⟨Y, hY_kol, -, hY_holder, hY_eq⟩ := hY₀_kol.exists_holderWith_of_dense hD hγ0 hY₀_holder
  exact ⟨Y, hY_kol, hY_holder, fun t ↦ (hY₀_ae t).mono fun ω hω ↦ (hY_eq t ω).trans hω⟩

/-- Finite dyadic covering numbers make a pseudo-emetric space separable. -/
private lemma separableSpace_of_coveringNumber_ne_top {α : Type*} [PseudoEMetricSpace α]
    (h : ∀ n : ℕ, coveringNumber ((1 / 2 : ℝ≥0) ^ n) (univ : Set α) ≠ ⊤) :
    SeparableSpace α := by
  refine ⟨⟨⋃ n : ℕ, minimalCover ((1 / 2 : ℝ≥0) ^ n) (univ : Set α),
    countable_iUnion fun _ ↦ finite_minimalCover.countable, fun x ↦ EMetric.mem_closure_iff.2 ?_⟩⟩
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.1
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((1 / 2 : ℝ≥0) : ℝ≥0∞))
      (by norm_num))).2 ε hε).exists
  obtain ⟨y, hy, hxy⟩ := isCover_minimalCover (h n) (mem_univ x)
  exact ⟨y, mem_iUnion.2 ⟨n, hy⟩, hxy.trans_lt (ENNReal.coe_pow (1 / 2 : ℝ≥0) n ▸ hn)⟩

/-- Local Hölder extension on a single open stage `V` of finite diameter and bounded covering
numbers. -/
private lemma exists_stage_holderWith_of_isOpen {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set T} (hD : Dense D)
    {X' : D → Ω → E} {p q d : ℝ} {M C γ : ℝ≥0}
    (hX' : IsKolmogorovProcess X' P p q M)
    {V : Set T} (hV_open : IsOpen V) (hdiam : ediam V ≠ ⊤)
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε V : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d))
    (hγ0 : 0 < γ) (hγ : d + p * γ < q) :
    ∃ YV : V → Ω → E,
      SeparableSpace V ∧
      IsKolmogorovProcess YV P p q M ∧
      (∀ ω, ∃ L : ℝ≥0, HolderWith L γ (YV · ω)) ∧
      ∀ (t : V) (htD : t.1 ∈ D), YV t =ᵐ[P] X' ⟨t.1, htD⟩ := by
  let DV : Set V := ((↑) : V → T) ⁻¹' D
  have hDV_dense : Dense DV := hD.preimage hV_open.isOpenMap_subtype_val
  have hiso : Isometry ((↑) : V → T) := isometry_subtype_coe
  have hcov_V : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set V) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d) := fun ε h0 h1 ↦ by
    have heq := hiso.coveringNumber_image' Subtype.val_injective.injOn (ε := ε) (A := univ)
    rw [Subtype.coe_image_univ] at heq
    exact heq ▸ hcov ε h0 h1
  have hsep : SeparableSpace V := separableSpace_of_coveringNumber_ne_top fun n ↦ by
    rw [← ENat.toENNReal_ne_top]
    have hrn0 : (0 : ℝ≥0) < (1 / 2) ^ n := pow_pos (by norm_num) n
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast hrn0.ne') ENNReal.coe_ne_top))
      (hcov_V _ hrn0 (pow_le_one₀ zero_le (by norm_num)))
  have hdiam_DV : ediam DV ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ediam_mono (subset_univ DV))
    rw [← hiso.ediam_image, Subtype.coe_image_univ]
    exact hdiam
  have hcov_DV : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε DV : ℝ≥0∞) ≤
        ((C * (2 : ℝ≥0) ^ d : ℝ≥0) : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d) := fun ε hε0 hε1 ↦ by
    have hsub : (coveringNumber ε DV : ℝ≥0∞) ≤ coveringNumber (ε / 2) (univ : Set V) := by
      exact_mod_cast coveringNumber_subset_le (subset_univ DV)
    refine hsub.trans
      ((hcov_V (ε / 2) (half_pos hε0) ((half_le_self zero_le).trans hε1)).trans_eq ?_)
    rw [div_eq_mul_inv, ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.mul_rpow_of_ne_zero (by exact_mod_cast hε0.ne') (by norm_num),
      ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
      neg_neg, ← ENNReal.coe_rpow_of_ne_zero (by norm_num : (2 : ℝ≥0) ≠ 0)]
    ring
  have hXV : IsAEKolmogorovProcess (fun u : DV ↦ X' ⟨u.1.1, u.2⟩) P p q M :=
    hX'.IsAEKolmogorovProcess.comp_isometry fun _ _ ↦ rfl
  obtain ⟨YV, hYV_kol, hYV_holder, hYV_ae⟩ :=
    hXV.exists_holderWith_extension_of_dense_of_coveringNumber_le hDV_dense hdiam_DV hcov_DV hγ0 hγ
  exact ⟨YV, hsep, hYV_kol, hYV_holder, fun t htD ↦ hYV_ae ⟨t, htD⟩⟩

/-- **Dense-subset Kolmogorov–Chentsov theorem along an increasing open exhaustion.** Given a
Kolmogorov process `X` on a dense subset `D ⊆ T` and an increasing open cover `U : ℕ → Set T` of
`T` such that each `U k` has finite extended diameter and covering dimension `d k` with
`d k + p * γ k < q` (`γ k > 0`), there exists an `IsKolmogorovProcess` extension `Y : T → Ω → E`
whose paths are everywhere continuous on `T` and everywhere `γ k`-Hölder on `U k`, agreeing almost
everywhere with `X` on `D`. -/
theorem exists_continuous_extension_of_dense_of_isOpen_iUnion {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set T} (hD : Dense D)
    {X : D → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_open : ∀ k, IsOpen (U k)) (hU_mono : Monotone U)
    (hU_univ : ⋃ k, U k = univ)
    {C γ : ℕ → ℝ≥0} {d : ℕ → ℝ}
    (hdiam : ∀ k, ediam (U k) ≠ ⊤)
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
  cases isEmpty_or_nonempty T
  · exact ⟨isEmptyElim, ⟨isEmptyElim, isEmptyElim, hX.p_pos, hX.q_pos⟩,
      fun _ ↦ continuous_of_discreteTopology, fun _ _ ↦ ⟨0, fun x ↦ isEmptyElim x⟩, isEmptyElim⟩
  cases isEmpty_or_nonempty Ω
  · exact ⟨fun _ ↦ isEmptyElim,
      ⟨fun _ _ _ _ ↦ by convert @MeasurableSet.empty _ mΩ; ext x; exact isEmptyElim x,
        fun _ _ ↦ by simp [Measure.eq_zero_of_isEmpty P], hX.p_pos, hX.q_pos⟩,
      isEmptyElim, fun _ ω ↦ isEmptyElim ω, fun _ ↦ Eventually.of_forall isEmptyElim⟩
  obtain ⟨d₀, hd₀⟩ := hD.nonempty
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  let e₀ : E := X ⟨d₀, hd₀⟩ ω₀
  have hstage := fun k ↦ exists_stage_holderWith_of_isOpen hD hX.IsKolmogorovProcess_mk
    (hU_open k) (hdiam k) (hcov k) (hγ0 k) (hγ k)
  choose Yk hsep_Uk hYk_kol hYk_holder hYk_ae using hstage
  have hcompat : ∀ k m : ℕ, ∀ᵐ ω ∂P, ∀ (hkm : k ≤ m) (t : U k),
      Yk k t ω = Yk m ⟨t.1, hU_mono hkm t.2⟩ ω := fun k m ↦ by
    by_cases hkm : k ≤ m
    · have : SeparableSpace (U k) := hsep_Uk k
      obtain ⟨Sk, hSk_sub, hSk_count, hSk_dense⟩ :=
        (hD.preimage (hU_open k).isOpenMap_subtype_val).exists_countable_dense_subset
      have hind := TauCeti.indist_of_ae_continuous_of_dense hSk_count hSk_dense
        (Eventually.of_forall fun ω ↦ let ⟨_, hL⟩ := hYk_holder k ω; hL.continuous (hγ0 k))
        (Eventually.of_forall fun ω ↦ let ⟨_, hL⟩ := hYk_holder m ω
          (hL.continuous (hγ0 m)).comp (continuous_inclusion (hU_mono hkm)))
        fun t htS ↦ (hYk_ae k t (hSk_sub htS)).trans
          (hYk_ae m ⟨t.1, hU_mono hkm t.2⟩ (hSk_sub htS)).symm
      filter_upwards [hind] with ω hω _ t using hω t
    · exact Eventually.of_forall fun _ h ↦ absurd h hkm
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null
    (ae_all_iff.2 fun k ↦ ae_all_iff.2 fun m ↦ hcompat k m)
  have hex_k : ∀ t : T, ∃ k, t ∈ U k := fun t ↦ mem_iUnion.1 (hU_univ ▸ mem_univ t)
  let k₀ : T → ℕ := fun t ↦ Nat.find (hex_k t)
  have hk₀_mem : ∀ t : T, t ∈ U (k₀ t) := fun t ↦ Nat.find_spec (hex_k t)
  let Y : T → Ω → E := fun t ω ↦ if ω ∈ N then e₀ else Yk (k₀ t) ⟨t, hk₀_mem t⟩ ω
  have hY_stage : ∀ {ω : Ω}, ω ∉ N → ∀ k {t : T} (ht : t ∈ U k), Y t ω = Yk k ⟨t, ht⟩ ω := by
    intro ω hωN k t ht
    have hgood := not_not.1 fun h ↦ hωN (hN_sub h)
    dsimp only [Y]
    rw [ite_eq_right hωN]
    exact (hgood (k₀ t) (max k (k₀ t)) (le_max_right _ _) ⟨t, hk₀_mem t⟩).trans
      (hgood k (max k (k₀ t)) (le_max_left _ _) ⟨t, ht⟩).symm
  have hY_holder_on : ∀ k ω, ∃ L : ℝ≥0, HolderOnWith L (γ k) (Y · ω) (U k) := fun k ω ↦ by
    by_cases hωN : ω ∈ N
    · exact ⟨0, fun _ _ _ _ ↦ by simp [Y, hωN]⟩
    · obtain ⟨L, hL⟩ := hYk_holder k ω
      refine ⟨L, fun x hx y hy ↦ ?_⟩
      dsimp only
      rw [hY_stage hωN k hx, hY_stage hωN k hy]
      exact hL ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨Y, ⟨fun s t ↦ ?_, fun s t ↦ ?_, hX.p_pos, hX.q_pos⟩,
    fun ω ↦ continuous_iff_continuousAt.2 fun t ↦
      let ⟨_, hL⟩ := hY_holder_on (k₀ t) ω
      (hL.continuousOn (hγ0 (k₀ t))).continuousAt ((hU_open (k₀ t)).mem_nhds (hk₀_mem t)),
    hY_holder_on, fun t ↦ ?_⟩
  · let : MeasurableSpace (E × E) := borel (E × E)
    let m := max (k₀ s) (k₀ t)
    have hs_m : s ∈ U m := hU_mono (le_max_left _ _) (hk₀_mem s)
    have ht_m : t ∈ U m := hU_mono (le_max_right _ _) (hk₀_mem t)
    have hite : (fun ω ↦ (Y s ω, Y t ω)) =
        fun ω ↦ if ω ∈ N then (e₀, e₀) else (Yk m ⟨s, hs_m⟩ ω, Yk m ⟨t, ht_m⟩ ω) := by
      funext ω
      by_cases hωN : ω ∈ N
      · simp [Y, hωN]
      · rw [ite_eq_right hωN, hY_stage hωN m hs_m, hY_stage hωN m ht_m]
    rw [hite]
    exact Measurable.ite hN_meas measurable_const
      ((hYk_kol m).measurablePair ⟨s, hs_m⟩ ⟨t, ht_m⟩)
  · let m := max (k₀ s) (k₀ t)
    have hs_m : s ∈ U m := hU_mono (le_max_left _ _) (hk₀_mem s)
    have ht_m : t ∈ U m := hU_mono (le_max_right _ _) (hk₀_mem t)
    refine (lintegral_congr_ae ?_).trans_le ((hYk_kol m).kolmogorovCondition ⟨s, hs_m⟩ ⟨t, ht_m⟩)
    filter_upwards [compl_mem_ae_iff.2 hN_null] with ω (hωN : ω ∉ N)
    rw [hY_stage hωN m hs_m, hY_stage hωN m ht_m]
  · filter_upwards [compl_mem_ae_iff.2 hN_null, hYk_ae (k₀ t.1) ⟨t.1, hk₀_mem t.1⟩ t.2,
      hX.ae_eq_mk t] with ω hωN hYk_eq hXX'
    exact (hY_stage hωN (k₀ t.1) (hk₀_mem t.1)).trans (hYk_eq.trans hXX'.symm)

/-- **Kolmogorov–Chentsov continuous modification theorem along an increasing open exhaustion.**
When `T` is covered by an increasing sequence of open sets `U k` of finite extended diameter and
covering dimension `d k` with `d k + p * γ k < q` (`γ k > 0`), any `IsAEKolmogorovProcess` has an
`IsKolmogorovProcess` modification whose paths are everywhere continuous and locally `γ k`-Hölder
on each `U k`. -/
theorem exists_continuous_modification_of_isOpen_iUnion {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_open : ∀ k, IsOpen (U k)) (hU_mono : Monotone U)
    (hU_univ : ⋃ k, U k = univ)
    {C γ : ℕ → ℝ≥0} {d : ℕ → ℝ}
    (hdiam : ∀ k, ediam (U k) ≠ ⊤)
    (hcov : ∀ k (ε : ℝ≥0), 0 < ε → ε ≤ 1 →
      (coveringNumber ε (U k) : ℝ≥0∞) ≤ (C k : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d k))
    (hγ0 : ∀ k, 0 < γ k)
    (hγ : ∀ k, d k + p * γ k < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ k ω, ∃ L : ℝ≥0, HolderOnWith L (γ k) (Y · ω) (U k)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  have hX_univ := hX.comp_isometry (isometry_subtype_coe (s := (univ : Set T)))
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX_univ.exists_continuous_extension_of_dense_of_isOpen_iUnion
      dense_univ hU_open hU_mono hU_univ hdiam hcov hγ0 hγ
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
  have hε_inv : (1 : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ := ENNReal.one_le_inv.2 (by exact_mod_cast hε1)
  have h1 : (1 : ℝ≥0∞) + 2 * (k + 1 : ℝ≥0) / ε ≤ (2 * k + 3 : ℕ) * (ε : ℝ≥0∞)⁻¹ := by
    calc
      (1 : ℝ≥0∞) + 2 * (k + 1 : ℝ≥0) / ε =
          1 + 2 * ((k : ℝ≥0∞) + 1) * (ε : ℝ≥0∞)⁻¹ := by
        rw [div_eq_mul_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
      _ ≤ (ε : ℝ≥0∞)⁻¹ + 2 * ((k : ℝ≥0∞) + 1) * (ε : ℝ≥0∞)⁻¹ := by gcongr
      _ = (2 * k + 3 : ℕ) * (ε : ℝ≥0∞)⁻¹ := by push_cast; ring
  refine (pow_le_pow_left' h1 _).trans_eq ?_
  rw [mul_pow, ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
  push_cast; rfl

/-- **Kolmogorov–Chentsov theorem on finite-dimensional real normed spaces.** When
`Module.finrank ℝ F + p * γ < q` (`γ > 0`), any `IsAEKolmogorovProcess` indexed by `F` with values
in a complete metric space admits an everywhere-continuous `IsKolmogorovProcess` modification that
is `γ`-Hölder on every ball around the origin (hence on every bounded set). -/
theorem exists_continuous_modification_of_finiteDimensional {F Ω E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [EMetricSpace E] [CompleteSpace E]
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
  have hU_univ : ⋃ k, U k = univ := eq_univ_of_forall fun x ↦ by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.2 ⟨k, mem_ball_zero_iff.2 (hk.trans (by linarith))⟩
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX.exists_continuous_modification_of_isOpen_iUnion (fun _ ↦ isOpen_ball)
      (fun _ _ hij ↦ ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hij 1))
      hU_univ (fun _ ↦ isBounded_ball.ediam_ne_top)
      (fun k _ hε0 hε1 ↦ coveringNumber_ball_le_mul_rpow_neg_finrank k hε0 hε1)
      (fun _ ↦ hγ0) (fun _ ↦ hγ)
  refine ⟨Y, hY_kol, hY_cont, fun R ω ↦ ?_, hY_ae⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (R : ℝ)
  obtain ⟨L, hL⟩ := hY_holder k ω
  exact ⟨L, hL.mono (closedBall_subset_ball (hk.trans (by linarith)))⟩

/-- **Dense-subset Kolmogorov–Chentsov extension on `ℝ≥0`.** A Kolmogorov process defined on a
dense subset `D ⊆ ℝ≥0` with `1 + p * γ < q` (`γ > 0`) extends to an everywhere-continuous
`IsKolmogorovProcess` on `ℝ≥0` that is `γ`-Hölder on every compact horizon `[0, T]`. -/
theorem exists_continuous_extension_of_dense_nnreal {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E]
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
  have hU_univ : ⋃ k, U k = univ := eq_univ_of_forall fun t ↦ by
    obtain ⟨k, hk⟩ := exists_nat_gt t
    exact mem_iUnion.2 ⟨k, mem_Iio.2 (hk.trans (lt_add_one _))⟩
  have himg : ∀ k, ((↑) : ℝ≥0 → ℝ) '' U k ⊆ ball (0 : ℝ) (k + 1 : ℝ) := by
    rintro k _ ⟨t, ht, rfl⟩
    rw [mem_ball_zero_iff, Real.norm_of_nonneg t.coe_nonneg]
    exact_mod_cast (mem_Iio.1 ht : t < (k : ℝ≥0) + 1)
  have hdiam : ∀ k, ediam (U k) ≠ ⊤ := fun k ↦ ne_top_of_le_ne_top isBounded_ball.ediam_ne_top
    (NNReal.isometry_coe.ediam_image (U k) ▸ ediam_mono (himg k))
  have hcov : ∀ k (ε : ℝ≥0), 0 < ε → ε ≤ 1 →
      (coveringNumber ε (U k) : ℝ≥0∞) ≤
        ((2 * (2 * k + 3) : ℕ) : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-(1 : ℝ)) := fun k ε hε0 hε1 ↦ by
    rw [← NNReal.isometry_coe.coveringNumber_image (A := U k)]
    have hsub : (coveringNumber ε (((↑) : ℝ≥0 → ℝ) '' U k) : ℝ≥0∞) ≤
        coveringNumber (ε / 2) (ball (0 : ℝ) (k + 1 : ℝ)) := by
      exact_mod_cast coveringNumber_subset_le (himg k)
    refine hsub.trans ((coveringNumber_ball_le_mul_rpow_neg_finrank k (half_pos hε0)
      ((half_le_self zero_le).trans hε1)).trans_eq ?_)
    rw [Module.finrank_self, pow_one, Nat.cast_one, div_eq_mul_inv, ENNReal.coe_mul,
      ENNReal.mul_rpow_of_ne_zero (by exact_mod_cast hε0.ne') (by norm_num),
      ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
      neg_neg, ENNReal.rpow_one]
    push_cast; ring
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX.exists_continuous_extension_of_dense_of_isOpen_iUnion hD (fun _ ↦ isOpen_Iio)
      (fun _ _ hij ↦ Iio_subset_Iio (by exact_mod_cast Nat.add_le_add_right hij 1))
      hU_univ hdiam hcov (fun _ ↦ hγ0) (fun _ ↦ hγ)
  refine ⟨Y, hY_kol, hY_cont, fun T ω ↦ ?_, hY_ae⟩
  obtain ⟨k, hk⟩ := exists_nat_gt T
  obtain ⟨L, hL⟩ := hY_holder k ω
  exact ⟨L, hL.mono fun _ ht ↦ mem_Iio.2 (ht.2.trans_lt (hk.trans (lt_add_one _)))⟩

/-- **One-dimensional Kolmogorov–Chentsov modification on `ℝ≥0`.** When `1 + p * γ < q` (`γ > 0`),
every `IsAEKolmogorovProcess` indexed by `ℝ≥0` with values in a complete metric space has an
everywhere-continuous `IsKolmogorovProcess` modification whose paths are `γ`-Hölder on every
compact interval `[0, T]`. -/
theorem exists_continuous_modification_nnreal {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    {p q : ℝ} {M γ : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hγ0 : 0 < γ) (hγ : 1 + p * γ < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ (T : ℝ≥0) ω, ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (Icc 0 T)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  have hX_univ := hX.comp_isometry (isometry_subtype_coe (s := (univ : Set ℝ≥0)))
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX_univ.exists_continuous_extension_of_dense_nnreal dense_univ hγ0 hγ
  exact ⟨Y, hY_kol, hY_cont, hY_holder, fun t ↦ hY_ae ⟨t, mem_univ t⟩⟩

end IsAEKolmogorovProcess

end ProbabilityTheory
