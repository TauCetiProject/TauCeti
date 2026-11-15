/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Probability.Process.Kolmogorov
import TauCeti.Probability.Process.Kolmogorov.Edges
import TauCeti.Topology.MetricSpace.Chaining
import TauCeti.Topology.MetricSpace.Holder

/-!
# Metric-parameter Kolmogorov–Chentsov continuity and Hölder modification theorems

Combine the multiscale sparse-star chaining system of
`Metric.HasCoveringExponent.exists_countable_dense_edges` with the geometric edge estimates of
`ProbabilityTheory.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow` and dense Hölder
extension (`HolderOnWith.extend_of_dense`) to obtain coordinatewise measurable, pathwise
continuous and locally Hölder modifications (and extensions from dense index subsets) of
Kolmogorov processes.

## Main results

* `ProbabilityTheory.IsAEKolmogorovProcess.exists_holderWith_of_dense_of_hasCoveringExponent` and
  `exists_holderWith_modification`: if `S ⊆ T` is dense with covering exponent `d < q` and
  `X : S → Ω → E` satisfies `IsAEKolmogorovProcess X P p q M` into a complete Borel extended metric
  space `E`, a single coordinatewise measurable process `Y : T → Ω → E` has everywhere continuous
  paths that are simultaneously `γ`-Hölder on `T` for all `γ : ℝ≥0` with `d + p * γ < q`, and
  agrees `P`-a.e. with `X` on `S`.
* `ProbabilityTheory.IsAEKolmogorovProcess.exists_continuous_holderOnWith_of_isOpen_cover` and
  `exists_continuous_holderOnWith_modification`: when `T` is covered by countably many open sets
  `U n` such that `S ∩ U n` has covering exponent `d n < q`, a single coordinatewise measurable
  process `Y : T → Ω → E` has everywhere continuous paths that are simultaneously `γ`-Hölder on
  `U n` for all `n` and all `γ : ℝ≥0` with `d n + p * γ < q`.
* `exists_continuous_holderOnWith_of_dense_normedSpace`,
  `exists_continuous_holderOnWith_modification_normedSpace`,
  `exists_continuous_holderOnWith_of_dense_nnreal`, and
  `exists_continuous_holderOnWith_modification_nnreal`: specializations to finite-dimensional real
  normed parameter spaces and to nonnegative real time `ℝ≥0`.

No second-countability or nonemptiness assumption on `E`, and no probability normalization on `P`,
is required; measurability on overlaps is preserved via measurable Cauchy-convergence events of the
underlying `IsKolmogorovProcess`. See Krätschmer–Urusov, *A general Kolmogorov–Chentsov type
theorem on general metric spaces*, arXiv:2107.13837v2, Theorem 1.1.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.IsAEKolmogorovProcess

section Helpers

private lemma dense_subtype_of_isOpen {T : Type*} [TopologicalSpace T] {V W : Set T}
    (hW : IsOpen W) (hWV : W ⊆ V) {A : Set T} (hA : Dense {x : V | x.1 ∈ A}) :
    Dense {x : W | x.1 ∈ A} := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨z, hz⟩
  have hOW : IsOpen ((Subtype.val : W → T) '' O) := hW.isOpenMap_subtype_val O hO
  obtain ⟨x, hxO, hxA⟩ := hA.inter_open_nonempty
    ((Subtype.val : V → T) ⁻¹' ((Subtype.val : W → T) '' O))
    (hOW.preimage continuous_subtype_val) ⟨⟨z.1, hWV z.2⟩, z, hz, rfl⟩
  rcases hxO with ⟨w, hwO, hw_eq⟩
  exact ⟨w, hwO, by simpa [hw_eq] using hxA⟩

private lemma dense_subtype_of_dense {T : Type*} [TopologicalSpace T] {S V : Set T}
    (hS : Dense S) (hV : IsOpen V) : Dense {x : V | x.1 ∈ S} := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨z, hz⟩
  obtain ⟨y, ⟨w, hwO, rfl⟩, hyS⟩ := hS.inter_open_nonempty ((Subtype.val : V → T) '' O)
    (hV.isOpenMap_subtype_val O hO) ⟨z.1, z, hz, rfl⟩
  exact ⟨w, hwO, hyS⟩

private lemma ediam_open_le_of_dense {T : Type*} [PseudoEMetricSpace T] {S V : Set T}
    (hS : Dense S) (hV : IsOpen V) : ediam V ≤ ediam (S ∩ V) := by
  have hsub : V ⊆ closure (S ∩ V) := fun x hx ↦ mem_closure_iff.mpr fun O hO hxO ↦ by
    obtain ⟨y, ⟨hyV, hyO⟩, hyS⟩ := hS.inter_open_nonempty (V ∩ O) (hV.inter hO) ⟨x, hx, hxO⟩
    exact ⟨y, hyO, hyS, hyV⟩
  exact (ediam_mono hsub).trans_eq (Metric.ediam_closure (S ∩ V))

private lemma exists_approx_of_dense {T : Type*} [PseudoEMetricSpace T] {S D : Set T}
    (hS : Dense S) {u : ℕ → T → T}
    (hu : ∀ a ∈ S, ∀ n, u n a ∈ D ∧ edist a (u n a) ≤ (2⁻¹ : ℝ≥0∞) ^ n) :
    ∃ v : ℕ → T → D,
      (∀ t n, edist (v n t : T) t ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n) ∧
      (∀ t, Tendsto (fun n ↦ (v n t : T)) atTop (𝓝 t)) ∧ Dense D := by
  have hball (n : ℕ) (t : T) : (Metric.eball t ((2⁻¹ : ℝ≥0∞) ^ n) ∩ S).Nonempty :=
    hS.inter_open_nonempty (Metric.eball t ((2⁻¹ : ℝ≥0∞) ^ n)) Metric.isOpen_eball
      ⟨t, Metric.mem_eball_self (ENNReal.pow_pos (by norm_num) n)⟩
  let v : ℕ → T → D := fun n t ↦
    ⟨u n (hball n t).choose, (hu _ (hball n t).choose_spec.2 n).1⟩
  have hed (t : T) (n : ℕ) : edist (v n t : T) t ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n := by
    have ha := (hball n t).choose_spec
    calc edist (u n (hball n t).choose) t
        ≤ edist (u n (hball n t).choose) (hball n t).choose + edist (hball n t).choose t :=
          edist_triangle _ _ _
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ n + (2⁻¹ : ℝ≥0∞) ^ n := by
          rw [edist_comm]
          exact add_le_add (hu _ ha.2 n).2 (Metric.mem_eball.mp ha.1).le
      _ = 2 * (2⁻¹ : ℝ≥0∞) ^ n := (two_mul _).symm
  have hzero : Tendsto (fun n : ℕ ↦ 2 * (2⁻¹ : ℝ≥0∞) ^ n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) (Or.inr ENNReal.ofNat_ne_top)
  have htend (t : T) : Tendsto (fun n ↦ (v n t : T)) atTop (𝓝 t) :=
    EMetric.tendsto_nhds.mpr fun ε hε ↦
      ((tendsto_order.mp hzero).2 ε hε).mono fun n hn ↦ (hed t n).trans_lt hn
  exact ⟨v, hed, htend, fun t ↦ mem_closure_of_tendsto (htend t)
    (Eventually.of_forall fun n ↦ (v n t).2)⟩

private def convSet {S Ω E : Type*} [PseudoEMetricSpace E]
    (X' : S → Ω → E) (w : ℕ → S) (s : S) : Set Ω :=
  ⋂ j : ℕ, ⋃ N : ℕ, ⋂ n, ⋂ (_ : N ≤ n), {ω | edist (X' (w n) ω) (X' s ω) ≤ (2⁻¹ : ℝ≥0∞) ^ j}

private lemma measurableSet_convSet {S Ω E : Type*} [PseudoEMetricSpace S] [PseudoEMetricSpace E]
    [MeasurableSpace Ω] {P : Measure Ω} {X' : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX' : IsKolmogorovProcess X' P p q M) (w : ℕ → S) (s : S) :
    MeasurableSet (convSet X' w s) :=
  .iInter fun _ ↦ .iUnion fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
    measurableSet_le hX'.measurable_edist measurable_const

private lemma tendsto_of_mem_convSet {S Ω E : Type*} [PseudoEMetricSpace E]
    {X' : S → Ω → E} {w : ℕ → S} {s : S} {ω : Ω} (hω : ω ∈ convSet X' w s) :
    Tendsto (fun n ↦ X' (w n) ω) atTop (𝓝 (X' s ω)) := by
  refine EMetric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hzero : Tendsto (fun j : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ j) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hzero).2 ε hε).exists
  simp only [convSet, mem_iInter, mem_iUnion, mem_ofPred_eq] at hω
  obtain ⟨N, hN⟩ := hω j
  exact eventually_atTop.mpr ⟨N, fun n hn ↦ (hN n hn).trans_lt hj⟩

private lemma ae_mem_convSet {S Ω E : Type*} [PseudoEMetricSpace S] [PseudoEMetricSpace E]
    [MeasurableSpace Ω] {P : Measure Ω} {X' : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX' : IsKolmogorovProcess X' P p q M) {w : ℕ → S} {s : S}
    (hw : ∀ n, edist (w n) s ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n) :
    ∀ᵐ ω ∂P, ω ∈ convSet X' w s := by
  have hedge (n : ℕ) (_ : Fin 1) : edist (w (n + 1)) s ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    refine (hw (n + 1)).trans_eq ?_
    rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    simp
  have hp := hX'.p_pos
  have hq := hX'.q_pos
  have hγ_pos : 0 < q / (2 * p) := div_pos hq (mul_pos two_pos hp)
  have hγ_lt : 0 + p * (q / (2 * p)) < q := by
    have : p * (q / (2 * p)) = q / 2 := by field_simp
    linarith
  have hae := hX'.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow
    (C := 1) (r := 2⁻¹) (d := 0) (γ := q / (2 * p)) (k := fun _ ↦ 1)
    (s := fun n _ ↦ w (n + 1)) (t := fun _ _ ↦ s) (by norm_num) (by norm_num)
    (fun n ↦ by simp) hedge hγ_lt
  filter_upwards [hae] with ω ⟨K, hK⟩
  simp only [convSet, mem_iInter, mem_iUnion, mem_ofPred_eq]
  intro j
  have hbase : ((2⁻¹ : ℝ≥0∞) ^ (q / (2 * p))) < 1 :=
    ENNReal.rpow_lt_one (by norm_num) hγ_pos
  have hlim : Tendsto (fun n : ℕ ↦ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ (q / (2 * p))) ^ n)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase) (Or.inr ENNReal.coe_ne_top)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 ((2⁻¹ : ℝ≥0∞) ^ j) (ENNReal.pow_pos (by norm_num) j))
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ n)
  rw [add_comm]
  refine (hK m 0).trans ?_
  simpa [ENNReal.pow_rpow_comm] using (hN m (by omega)).le

private lemma ae_edist_finset_lt_top {T Ω E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
    [MeasurableSpace Ω] {P : Measure Ω} {S : Set T} {X' : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX' : IsKolmogorovProcess X' P p q M) (hediam : ediam S < ∞)
    {V₀ : Finset T} (hV₀ : (V₀ : Set T) ⊆ S) :
    ∀ᵐ ω ∂P, ∃ K₀ : ℕ, ∀ x : V₀, ∀ y : V₀,
      edist (X' ⟨x.1, hV₀ x.2⟩ ω) (X' ⟨y.1, hV₀ y.2⟩ ω) ≤ K₀ := by
  have hpair (x y : V₀) : ∀ᵐ ω ∂P, edist (X' ⟨x.1, hV₀ x.2⟩ ω) (X' ⟨y.1, hV₀ y.2⟩ ω) < ⊤ := by
    have hed_lt : edist (⟨x.1, hV₀ x.2⟩ : S) ⟨y.1, hV₀ y.2⟩ < ⊤ :=
      (edist_le_ediam_of_mem (hV₀ x.2) (hV₀ y.2)).trans_lt hediam
    have hfin : ∫⁻ ω, edist (X' ⟨x.1, hV₀ x.2⟩ ω) (X' ⟨y.1, hV₀ y.2⟩ ω) ^ p ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hX'.q_pos.le hed_lt.ne))
        (hX'.kolmogorovCondition _ _)
    filter_upwards [ae_lt_top' (hX'.measurable_edist.pow_const p).aemeasurable hfin] with ω hω
    by_contra htop
    rw [eq_top_iff.mpr (not_lt.mp htop), ENNReal.top_rpow_of_pos hX'.p_pos] at hω
    exact lt_irrefl ⊤ hω
  filter_upwards [ae_all_iff.mpr fun x ↦ ae_all_iff.mpr fun y ↦ hpair x y] with ω hω
  classical
  let B : ℝ≥0 := Finset.univ.sup fun p : V₀ × V₀ ↦
    (edist (X' ⟨p.1.1, hV₀ p.1.2⟩ ω) (X' ⟨p.2.1, hV₀ p.2.2⟩ ω)).toNNReal
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge B
  refine ⟨K₀, fun x y ↦ ?_⟩
  rw [← ENNReal.coe_toNNReal (hω x y).ne]
  exact_mod_cast (Finset.le_sup (f := fun p : V₀ × V₀ ↦
    (edist (X' ⟨p.1.1, hV₀ p.1.2⟩ ω) (X' ⟨p.2.1, hV₀ p.2.2⟩ ω)).toNNReal)
    (Finset.mem_univ (x, y))).trans hK₀

private lemma exists_measurableSet_holderOnWith {T Ω E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] [Nonempty T] [MeasurableSpace Ω] {P : Measure Ω}
    {S : Set T} (hS : Dense S) {X' : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX' : IsKolmogorovProcess X' P p q M)
    {c : ℝ≥0∞} {d : ℝ} {γ : ℝ≥0} (hcov : HasCoveringExponent S c d) (hc : c ≠ ∞)
    (hγ : 0 < γ) (hdγ : d + p * γ < q) :
    ∃ (D : Set T) (v : ℕ → T → D) (Ω₀ : Set Ω) (f : Ω → T → E),
      D.Countable ∧ ∃ (hDS : D ⊆ S), Dense D ∧
      (∀ t n, edist (v n t : T) t ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n) ∧
      (∀ t, Tendsto (fun n ↦ (v n t : T)) atTop (𝓝 t)) ∧
      MeasurableSet Ω₀ ∧ (∀ᵐ ω ∂P, ω ∈ Ω₀) ∧
      (∀ (z : D) ω, f ω z.1 = X' ⟨z.1, hDS z.2⟩ ω) ∧
      (∀ ω ∈ Ω₀, ∃ K : ℝ≥0, HolderOnWith K γ (f ω) D) := by
  classical
  let d' : ℝ := (d + (q - p * γ)) / 2
  have hdd' : d < d' := by dsimp [d']; linarith
  have hd'γ : d' + p * γ < q := by dsimp [d']; linarith
  obtain ⟨V₀, D, u, C, k, s_e, t_e, M_H, hDc, hDS, hV₀D, hu, hstD, hcard, hedge, hchain⟩ :=
    hcov.exists_countable_dense_edges hc hdd'
  obtain ⟨v, hv_ed, hv_tend, hD_dense⟩ := exists_approx_of_dense hS hu
  let s' : (n : ℕ) → Fin (k n) → S := fun n i ↦ ⟨s_e n i, hDS (hstD n i).1⟩
  let t' : (n : ℕ) → Fin (k n) → S := fun n i ↦ ⟨t_e n i, hDS (hstD n i).2⟩
  let Ω_e : Set Ω := ⋃ K : ℕ, ⋂ (n : ℕ) (i : Fin (k n)),
    {ω | edist (X' (s' n i) ω) (X' (t' n i) ω) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ)}
  let Ω_v : Set Ω := ⋃ K₀ : ℕ, ⋂ (x : V₀) (y : V₀),
    {ω | edist (X' ⟨x.1, hDS (hV₀D x.2)⟩ ω) (X' ⟨y.1, hDS (hV₀D y.2)⟩ ω) ≤ K₀}
  have hΩ_meas : MeasurableSet (Ω_e ∩ Ω_v) :=
    MeasurableSet.inter
      (.iUnion fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
        measurableSet_le hX'.measurable_edist measurable_const)
      (.iUnion fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
        measurableSet_le hX'.measurable_edist measurable_const)
  have hΩ_e_ae : ∀ᵐ ω ∂P, ω ∈ Ω_e := by
    have hae := hX'.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow
      (r := 2⁻¹) (s := s') (t := t') (by norm_num) (by norm_num) hcard
      (fun n i ↦ (hedge n i).trans_eq (by simp)) hd'γ
    filter_upwards [hae] with ω ⟨K, hK⟩
    obtain ⟨K_nat, hK_nat⟩ := exists_nat_ge K
    refine mem_iUnion.mpr ⟨K_nat, mem_iInter₂.mpr fun n i ↦ (hK n i).trans ?_⟩
    rw [ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
    gcongr
    exact_mod_cast hK_nat
  have hΩ_v_ae : ∀ᵐ ω ∂P, ω ∈ Ω_v :=
    (ae_edist_finset_lt_top hX' hcov.ediam_lt_top (hV₀D.trans hDS)).mono fun ω ⟨K₀, hK₀⟩ ↦
      mem_iUnion.mpr ⟨K₀, mem_iInter₂.mpr hK₀⟩
  obtain ⟨s₀_val, hs₀⟩ := hS.nonempty
  let f : Ω → T → E := fun ω t ↦ if ht : t ∈ S then X' ⟨t, ht⟩ ω else X' ⟨s₀_val, hs₀⟩ ω
  refine ⟨D, v, Ω_e ∩ Ω_v, f, hDc, hDS, hD_dense, hv_ed, hv_tend, hΩ_meas,
    hΩ_e_ae.and hΩ_v_ae, fun z ω ↦ ?_, fun ω ⟨hω₁, hω₂⟩ ↦ ?_⟩
  · simp [f, hDS z.2]
  · obtain ⟨K, hK⟩ := mem_iUnion.mp hω₁
    obtain ⟨K₀, hK₀⟩ := mem_iUnion.mp hω₂
    refine ⟨M_H γ * ((K : ℝ≥0) + K₀), hchain hγ (f ω) K K₀ (fun n i ↦ ?_) (fun x hx y hy ↦ ?_)⟩
    · simpa [f, hDS (hstD n i).1, hDS (hstD n i).2, s', t'] using mem_iInter₂.mp hK n i
    · simpa [f, hDS (hV₀D hx), hDS (hV₀D hy)] using mem_iInter₂.mp hK₀ ⟨x, hx⟩ ⟨y, hy⟩

private lemma exists_holderWith_of_isKolmogorovProcess {T Ω E : Type*} [PseudoEMetricSpace T]
    [EMetricSpace E] [CompleteSpace E] [Nonempty T] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} {S : Set T} (hS : Dense S)
    {X' : S → Ω → E} {p q : ℝ} {M : ℝ≥0} (hX' : IsKolmogorovProcess X' P p q M)
    {c : ℝ≥0∞} {d : ℝ} {γ : ℝ≥0} (hcov : HasCoveringExponent S c d) (hc : c ≠ ∞)
    (hγ : 0 < γ) (hdγ : d + p * γ < q) :
    ∃ (D : Set T) (Y : T → Ω → E) (w : ℕ → T → S) (Ω₀ : Set Ω),
      D.Countable ∧ D ⊆ S ∧ Dense D ∧
      MeasurableSet Ω₀ ∧ (∀ᵐ ω ∂P, ω ∈ Ω₀) ∧
      (∀ t n, edist (w n t : T) t ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, ∃ K, HolderWith K γ (Y · ω)) ∧
      (∀ t, ∀ ω ∈ Ω₀, Tendsto (fun n ↦ X' (w n t) ω) atTop (𝓝 (Y t ω))) := by
  classical
  obtain ⟨D, v, Ω₀, f, hDc, hDS, hD_dense, hv_ed, hv_tend, hΩ₀_meas, hΩ₀_ae, hf_eq, hf_hold⟩ :=
    exists_measurableSet_holderOnWith hS hX' hcov hc hγ hdγ
  obtain ⟨s₀_val, hs₀⟩ := hS.nonempty
  let s₀ : S := ⟨s₀_val, hs₀⟩
  let w : ℕ → T → S := fun n t ↦ ⟨(v n t).1, hDS (v n t).2⟩
  let ext_fn (ω : Ω) (hω : ω ∈ Ω₀) :=
    (hf_hold ω hω).choose_spec.extend_of_dense hD_dense
  let Y : T → Ω → E := fun t ω ↦ if hω : ω ∈ Ω₀ then (ext_fn ω hω).choose t else X' s₀ ω
  have hY_tend : ∀ t, ∀ ω ∈ Ω₀, Tendsto (fun n ↦ X' (w n t) ω) atTop (𝓝 (Y t ω)) := by
    intro t ω hω
    obtain ⟨hg_hold, hg_eq⟩ := (ext_fn ω hω).choose_spec
    have hcont : Continuous (Y · ω) := by
      simpa only [Y, hω, ↓reduceDIte] using hg_hold.continuous hγ
    refine (hcont.tendsto t |>.comp (hv_tend t)).congr' (Eventually.of_forall fun n ↦ ?_)
    have h1 : Y (v n t).1 ω = f ω (v n t).1 := by
      simpa only [Y, hω, ↓reduceDIte] using (hg_eq (v n t).2).symm
    exact h1.trans (hf_eq (v n t) ω)
  have hY_meas (t : T) : Measurable (Y t) := by
    let Z : ℕ → Ω → E := fun n ↦ Ω₀.piecewise (X' (w n t)) (X' s₀)
    have hZ_meas (n : ℕ) : Measurable (Z n) :=
      Measurable.piecewise hΩ₀_meas (hX'.measurable (w n t)) (hX'.measurable s₀)
    refine measurable_of_tendsto_metrizable hZ_meas (tendsto_pi_nhds.mpr fun ω ↦ ?_)
    by_cases hω : ω ∈ Ω₀
    · simpa [Z, Set.piecewise_eq_of_mem _ _ _ hω] using hY_tend t ω hω
    · simp [Z, Y, hω]
  refine ⟨D, Y, w, Ω₀, hDc, hDS, hD_dense, hΩ₀_meas, hΩ₀_ae, hv_ed, hY_meas, fun ω ↦ ?_, hY_tend⟩
  by_cases hω : ω ∈ Ω₀
  · refine ⟨(hf_hold ω hω).choose, ?_⟩
    simpa only [Y, hω, ↓reduceDIte] using (ext_fn ω hω).choose_spec.1
  · exact ⟨0, fun x y ↦ by simp [Y, hω]⟩

private lemma exists_chart_version {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] {P : Measure Ω}
    {S : Set T} (hS : Dense S) {X' : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX' : IsKolmogorovProcess X' P p q M)
    {V : Set T} (hV_open : IsOpen V) {c : ℝ≥0∞} {d : ℝ} {γ : ℝ≥0}
    (hcov : HasCoveringExponent (S ∩ V) c d) (hc : c ≠ ∞) (hγ : 0 < γ) (hdγ : d + p * γ < q) :
    ∃ (D : Set V) (Y : V → Ω → E) (w : ℕ → V → S) (Ω₀ : Set Ω),
      D.Countable ∧ (∀ z ∈ D, z.1 ∈ S) ∧ Dense D ∧
      MeasurableSet Ω₀ ∧ (∀ᵐ ω ∂P, ω ∈ Ω₀) ∧
      (∀ (x : V) k, edist (w k x : T) x.1 ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ k) ∧
      (∀ x : V, Measurable (Y x)) ∧
      (∀ ω, ∃ K, HolderWith K γ (Y · ω)) ∧
      (∀ (x : V), ∀ ω ∈ Ω₀, Tendsto (fun k ↦ X' (w k x) ω) atTop (𝓝 (Y x ω))) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨∅, fun x ↦ isEmptyElim x, fun _ x ↦ isEmptyElim x, univ, countable_empty,
      by simp, fun x ↦ isEmptyElim x, .univ, Eventually.of_forall fun _ ↦ trivial,
      fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x,
      fun _ ↦ ⟨0, HolderWith.of_isEmpty⟩, fun x ↦ isEmptyElim x⟩
  let S_V : Set V := {x : V | x.1 ∈ S}
  have hS_V_dense : Dense S_V := dense_subtype_of_dense hS hV_open
  have himg : (Subtype.val : V → T) '' S_V = S ∩ V := by
    ext y
    simp [S_V, and_comm]
  have hcov_V : HasCoveringExponent S_V c d :=
    isometry_subtype_coe.hasCoveringExponent_of_injOn Subtype.val_injective.injOn (himg ▸ hcov)
  let ι : S_V → S := fun x ↦ ⟨x.1.1, x.2⟩
  have hι : Isometry ι := fun _ _ ↦ rfl
  obtain ⟨D, Y, w_V, Ω₀, hDc, hDS, hD_dense, hΩ_meas, hΩ_ae, hw_ed, hY_meas, hY_hold, hY_tend⟩ :=
    exists_holderWith_of_isKolmogorovProcess hS_V_dense (hX'.comp_isometry hι) hcov_V hc hγ hdγ
  exact ⟨D, Y, fun k x ↦ ι (w_V k x), Ω₀, hDc, fun z hz ↦ hDS hz, hD_dense, hΩ_meas, hΩ_ae,
    hw_ed, hY_meas, hY_hold, hY_tend⟩

private noncomputable def gammaSeq (p q d : ℝ) (j : ℕ) : ℝ≥0 :=
  ((q - d) / p * ((j + 1 : ℝ) / (j + 2 : ℝ))).toNNReal

private lemma gammaSeq_spec {p q d : ℝ} (hp : 0 < p) (hdq : d < q) :
    (∀ j, 0 < gammaSeq p q d j) ∧
    (∀ j, d + p * gammaSeq p q d j < q) ∧
    (∀ {γ : ℝ≥0}, d + p * γ < q → ∃ j, γ ≤ gammaSeq p q d j) := by
  have : 0 < (q - d) / p := div_pos (sub_pos.mpr hdq) hp
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun {γ} hγ ↦ ?_⟩
  · rw [gammaSeq, Real.toNNReal_pos]
    positivity
  · have hpos : 0 ≤ (q - d) / p * ((j + 1 : ℝ) / (j + 2 : ℝ)) := by positivity
    rw [gammaSeq, Real.coe_toNNReal _ hpos]
    have hlt : (j + 1 : ℝ) / (j + 2 : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    have hmul : p * ((q - d) / p * ((j + 1 : ℝ) / (j + 2 : ℝ))) < q - d := by
      calc p * ((q - d) / p * ((j + 1 : ℝ) / (j + 2 : ℝ)))
          = (q - d) * ((j + 1 : ℝ) / (j + 2 : ℝ)) := by field_simp
        _ < (q - d) * 1 := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hdq)
        _ = q - d := mul_one _
    linarith
  · rcases eq_zero_or_pos γ with rfl | _
    · exact ⟨0, by simp⟩
    have hlt : (γ : ℝ) < (q - d) / p := (lt_div_iff₀ hp).mpr (by linarith)
    have hsub : 0 < (q - d) / p - γ := sub_pos.mpr hlt
    obtain ⟨j, hj⟩ := exists_nat_gt ((q - d) / p / ((q - d) / p - γ))
    refine ⟨j, ?_⟩
    rw [← NNReal.coe_le_coe, gammaSeq, Real.coe_toNNReal _ (by positivity)]
    have hj2 : (0 : ℝ) < j + 2 := by positivity
    have hstep : (q - d) / p < ((q - d) / p - γ) * (j + 2 : ℝ) := by
      calc (q - d) / p < (j : ℝ) * ((q - d) / p - γ) := (div_lt_iff₀ hsub).mp hj
        _ ≤ (j + 2 : ℝ) * ((q - d) / p - γ) := by gcongr; linarith
        _ = ((q - d) / p - γ) * (j + 2 : ℝ) := mul_comm _ _
    rw [← mul_div_assoc, le_div_iff₀ hj2]
    linarith

private lemma eq_of_isOpen_inter_dense {T E : Type*} [TopologicalSpace T] [TopologicalSpace E]
    [T2Space E] {U V D : Set T} (hU : IsOpen U) (hV : IsOpen V) (hD : Dense {x : U | x.1 ∈ D})
    {f : U → E} {g : V → E} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ (x : T) (_ : x ∈ D) (hxU : x ∈ U) (hxV : x ∈ V), f ⟨x, hxU⟩ = g ⟨x, hxV⟩)
    {t : T} (htU : t ∈ U) (htV : t ∈ V) :
    f ⟨t, htU⟩ = g ⟨t, htV⟩ := by
  let W : Set T := U ∩ V
  have hd : Dense {x : W | x.1 ∈ D} :=
    dense_subtype_of_isOpen (hU.inter hV) inter_subset_left hD
  have hc1 : Continuous fun x : W ↦ f ⟨x.1, x.2.1⟩ :=
    hf.comp (continuous_inclusion inter_subset_left)
  have hc2 : Continuous fun x : W ↦ g ⟨x.1, x.2.2⟩ :=
    hg.comp (continuous_inclusion inter_subset_right)
  exact congrFun (Continuous.ext_on hd hc1 hc2 fun x hx ↦ hfg x.1 hx x.2.1 x.2.2) ⟨t, htU, htV⟩

private lemma holderOnWith_of_holderWith_subtype {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {U : Set T} (hed : ediam U < ∞) {f : U → E} {g : T → E}
    {K₀ γ₀ γ : ℝ≥0} (hf : HolderWith K₀ γ₀ f) (hγ : γ ≤ γ₀)
    (hfg : ∀ x (hx : x ∈ U), g x = f ⟨x, hx⟩) :
    ∃ K, HolderOnWith K γ g U := by
  have hbd (x y : U) : edist x y ≤ (ediam U).toNNReal := by
    simpa only [Subtype.edist_eq, ENNReal.coe_toNNReal hed.ne] using edist_le_ediam_of_mem x.2 y.2
  obtain ⟨K₁, hsub⟩ : ∃ K₁, HolderWith K₁ γ f := ⟨_, hf.of_le hbd hγ⟩
  refine ⟨K₁, fun x hx y hy ↦ ?_⟩
  simpa only [hfg x hx, hfg y hy, Subtype.edist_eq] using hsub ⟨x, hx⟩ ⟨y, hy⟩

private lemma exists_skeleton_good_event {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [MeasurableSpace Ω]
    {P : Measure Ω} {S : Set T} {X : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX' : IsKolmogorovProcess X P p q M) {U : ℕ → Set T}
    {D_glob : Set T} [Countable D_glob] (hDg_S : D_glob ⊆ S)
    (Y_ch : ∀ n, ℕ → U n → Ω → E) (w_ch : ∀ n, ℕ → ℕ → U n → S) (Ω_ch : ℕ → ℕ → Set Ω)
    (hΩ_meas : ∀ n j, MeasurableSet (Ω_ch n j)) (hΩ_ae : ∀ n j, ∀ᵐ ω ∂P, ω ∈ Ω_ch n j)
    (hw_ed : ∀ n j (x : U n) k, edist (w_ch n j k x : T) x.1 ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ k)
    (hY_tend : ∀ n j (x : U n) ω, ω ∈ Ω_ch n j →
      Tendsto (fun k ↦ X (w_ch n j k x) ω) atTop (𝓝 (Y_ch n j x ω))) :
    ∃ Ω_all : Set Ω, MeasurableSet Ω_all ∧ (∀ᵐ ω ∂P, ω ∈ Ω_all) ∧
      (∀ {ω}, ω ∈ Ω_all → ∀ n j, ω ∈ Ω_ch n j) ∧
      (∀ {ω}, ω ∈ Ω_all → ∀ {z : T} (hz : z ∈ D_glob) (n j : ℕ) (hzn : z ∈ U n),
        Y_ch n j ⟨z, hzn⟩ ω = X ⟨z, hDg_S hz⟩ ω) := by
  let Ω_all : Set Ω := (⋂ (n : ℕ) (j : ℕ), Ω_ch n j) ∩
    (⋂ (z : D_glob) (n : ℕ) (j : ℕ) (hz : z.1 ∈ U n),
      convSet X (fun k ↦ w_ch n j k ⟨z.1, hz⟩) ⟨z.1, hDg_S z.2⟩)
  refine ⟨Ω_all, MeasurableSet.inter (.iInter fun n ↦ .iInter fun j ↦ hΩ_meas n j)
    (.iInter fun z ↦ .iInter fun n ↦ .iInter fun j ↦ .iInter fun hz ↦
      measurableSet_convSet hX' _ _),
    ?_, fun {ω} hω n j ↦ mem_iInter₂.mp hω.1 n j, fun {ω} hω {z} hz n j hzn ↦ ?_⟩
  · have h2 : ∀ᵐ ω ∂P, ∀ (z : D_glob) (n j : ℕ) (hz : z.1 ∈ U n),
        ω ∈ convSet X (fun k ↦ w_ch n j k ⟨z.1, hz⟩) ⟨z.1, hDg_S z.2⟩ :=
      ae_all_iff.mpr fun z ↦ ae_all_iff.mpr fun n ↦ ae_all_iff.mpr fun j ↦
        ae_all_iff.mpr fun hz ↦ ae_mem_convSet hX' (hw_ed n j ⟨z.1, hz⟩)
    filter_upwards [ae_all_iff.mpr fun n ↦ ae_all_iff.mpr fun j ↦ hΩ_ae n j, h2] with ω h1 h2
    exact ⟨mem_iInter₂.mpr h1,
      mem_iInter.mpr fun z ↦ mem_iInter.mpr fun n ↦ mem_iInter.mpr fun j ↦
        mem_iInter.mpr fun hz ↦ h2 z n j hz⟩
  · have h1 := hY_tend n j ⟨z, hzn⟩ ω (mem_iInter₂.mp hω.1 n j)
    have h2 := tendsto_of_mem_convSet
      (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hω.2 ⟨z, hz⟩) n) j) hzn)
    exact tendsto_nhds_unique h1 h2

end Helpers

/-- **Metric-parameter Kolmogorov–Chentsov extension on a countable open cover.**
If `S ⊆ T` is dense, `T` is covered by countably many open sets `U n` such that `S ∩ U n` has
covering exponent `d n` (finite constant `c n`) with `d n < q`, and `X : S → Ω → E` satisfies
`IsAEKolmogorovProcess X P p q M` into a complete Borel extended metric space `E`, then a single
coordinatewise measurable process `Y : T → Ω → E` has everywhere continuous sample paths that are
simultaneously `γ`-Hölder on `U n` for every `n` and every `γ : ℝ≥0` with `d n + p * γ < q`, and
agrees `P`-a.e. with `X` on `S`. -/
theorem exists_continuous_holderOnWith_of_isOpen_cover {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] {P : Measure Ω}
    {S : Set T} (hS : Dense S) {X : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_open : ∀ n, IsOpen (U n)) (hU_cov : ⋃ n, U n = univ)
    {c : ℕ → ℝ≥0∞} {d : ℕ → ℝ} (hcov : ∀ n, HasCoveringExponent (S ∩ U n) (c n) (d n))
    (hc : ∀ n, c n ≠ ∞) (hdq : ∀ n, d n < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ n ⦃γ : ℝ≥0⦄, d n + p * γ < q → ∀ ω, ∃ K, HolderOnWith K γ (Y · ω) (U n)) ∧
      ∀ s : S, Y s =ᵐ[P] X s := by
  classical
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨fun t ↦ isEmptyElim t, fun t ↦ isEmptyElim t, fun _ ↦ continuous_of_discreteTopology,
      fun _ {_} _ _ ↦ ⟨0, Subsingleton.holderOnWith (by simp [eq_empty_of_isEmpty]) _ _ _⟩,
      fun s ↦ isEmptyElim s.1⟩
  let hX' := hX.IsKolmogorovProcess_mk
  have hγ_spec (n : ℕ) := gammaSeq_spec hX'.p_pos (hdq n)
  choose D_ch Y_ch w_ch Ω_ch hD_cnt hD_sub hD_dense hΩ_meas hΩ_ae hw_ed hY_meas hY_hold hY_tend
    using fun n j ↦ exists_chart_version hS hX' (hU_open n) (hcov n) (hc n)
      ((hγ_spec n).1 j) ((hγ_spec n).2.1 j)
  let D_glob : Set T := ⋃ n, Subtype.val '' D_ch n 0
  have : Countable D_glob := (countable_iUnion fun n ↦ (hD_cnt n 0).image _).to_subtype
  have hDg_S : D_glob ⊆ S := iUnion_subset fun n _ ⟨z, hz, hzeq⟩ ↦ hzeq ▸ hD_sub n 0 z hz
  obtain ⟨Ω_all, hΩ_all_meas, hΩ_all_ae, hΩ_mem, hΩ_eq⟩ :=
    exists_skeleton_good_event hX' hDg_S Y_ch w_ch Ω_ch hΩ_meas hΩ_ae hw_ed hY_tend
  have hcompat {m n i j : ℕ} {ω : Ω} (hω : ω ∈ Ω_all) {t : T} (hm : t ∈ U m) (hn : t ∈ U n) :
      Y_ch m i ⟨t, hm⟩ ω = Y_ch n j ⟨t, hn⟩ ω :=
    eq_of_isOpen_inter_dense (D := D_glob) (hU_open m) (hU_open n)
      ((hD_dense m 0).mono fun x hx ↦ mem_iUnion.mpr ⟨m, x, hx, rfl⟩)
      ((hY_hold m i ω).choose_spec.continuous ((hγ_spec m).1 i))
      ((hY_hold n j ω).choose_spec.continuous ((hγ_spec n).1 j))
      (fun _ hz hzm hzn ↦ (hΩ_eq hω hz m i hzm).trans (hΩ_eq hω hz n j hzn).symm) hm hn
  let m₀ (t : T) : ℕ := Nat.find (mem_iUnion.mp (hU_cov ▸ mem_univ t))
  have hm₀ (t : T) : t ∈ U (m₀ t) := Nat.find_spec (mem_iUnion.mp (hU_cov ▸ mem_univ t))
  let s₀ : S := ⟨hS.nonempty.choose, hS.nonempty.choose_spec⟩
  let Y : T → Ω → E := fun t ↦ Ω_all.piecewise (Y_ch (m₀ t) 0 ⟨t, hm₀ t⟩) (hX.mk X s₀)
  have hY_hold_on (n : ℕ) {γ : ℝ≥0} (hγ : d n + p * γ < q) (ω : Ω) :
      ∃ K, HolderOnWith K γ (Y · ω) (U n) := by
    by_cases hω : ω ∈ Ω_all
    · obtain ⟨j, hj⟩ := (hγ_spec n).2.2 hγ
      exact holderOnWith_of_holderWith_subtype
        ((ediam_open_le_of_dense hS (hU_open n)).trans_lt (hcov n).ediam_lt_top)
        (hY_hold n j ω).choose_spec hj fun x hx ↦ by
          simpa [Y, Set.piecewise_eq_of_mem _ _ _ hω] using hcompat hω (hm₀ x) hx
    · exact ⟨0, fun x _ y _ ↦ by simp [Y, hω]⟩
  refine ⟨Y, fun t ↦ Measurable.piecewise hΩ_all_meas (hY_meas _ _ _) (hX'.measurable s₀),
    fun ω ↦ continuous_iff_continuousAt.mpr fun t ↦ ?_, fun n {γ} hγ ω ↦ hY_hold_on n hγ ω,
    fun s ↦ ?_⟩
  · obtain ⟨K, hK⟩ := hY_hold_on (m₀ t) ((hγ_spec (m₀ t)).2.1 0) ω
    exact (hK.continuousOn ((hγ_spec (m₀ t)).1 0)).continuousAt
      ((hU_open (m₀ t)).mem_nhds (hm₀ t))
  · have hconv_s : ∀ᵐ ω ∂P,
        ω ∈ convSet (hX.mk X) (fun k ↦ w_ch (m₀ s.1) 0 k ⟨s.1, hm₀ s.1⟩) s :=
      ae_mem_convSet hX' (hw_ed (m₀ s.1) 0 ⟨s.1, hm₀ s.1⟩)
    filter_upwards [hΩ_all_ae, hconv_s, hX.ae_eq_mk s] with ω hω₁ hω₂ hmk
    simpa [Y, Set.piecewise_eq_of_mem _ _ _ hω₁] using
      (tendsto_nhds_unique (hY_tend _ _ _ ω (hΩ_mem hω₁ _ _))
        (tendsto_of_mem_convSet hω₂)).trans hmk.symm

/-- **Metric-parameter Kolmogorov–Chentsov modification on a countable open cover.**
When `T` is covered by countably many open sets `U n` of covering exponent `d n` (finite constant
`c n`) with `d n < q`, any `X : T → Ω → E` satisfying `IsAEKolmogorovProcess X P p q M` into a
complete Borel extended metric space `E` admits a single coordinatewise measurable modification `Y`
whose paths are everywhere continuous and simultaneously `γ`-Hölder on `U n` for all `n` and all
`γ : ℝ≥0` with `d n + p * γ < q`. -/
theorem exists_continuous_holderOnWith_modification {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0} (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_open : ∀ n, IsOpen (U n)) (hU_cov : ⋃ n, U n = univ)
    {c : ℕ → ℝ≥0∞} {d : ℕ → ℝ} (hcov : ∀ n, HasCoveringExponent (U n) (c n) (d n))
    (hc : ∀ n, c n ≠ ∞) (hdq : ∀ n, d n < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ n ⦃γ : ℝ≥0⦄, d n + p * γ < q → ∀ ω, ∃ K, HolderOnWith K γ (Y · ω) (U n)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    (hX.comp_isometry isometry_subtype_coe).exists_continuous_holderOnWith_of_isOpen_cover
      dense_univ hU_open hU_cov (fun n ↦ by simpa using hcov n) hc hdq
  exact ⟨Y, hY_meas, hY_cont, hY_hold, fun t ↦ hYX ⟨t, trivial⟩⟩

/-- **Global metric-parameter Kolmogorov–Chentsov extension from a dense subset.**
If `S ⊆ T` is dense with covering exponent `d` (finite constant `c`) satisfying `d < q`, any
`X : S → Ω → E` satisfying `IsAEKolmogorovProcess X P p q M` into a complete Borel extended metric
space `E` extends `P`-a.e. to a single coordinatewise measurable process `Y : T → Ω → E` whose
sample paths are everywhere continuous and simultaneously `γ`-Hölder on `T` for all `γ : ℝ≥0` with
`d + p * γ < q`. -/
theorem exists_holderWith_of_dense_of_hasCoveringExponent {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] {P : Measure Ω}
    {S : Set T} (hS : Dense S) {X : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) {c : ℝ≥0∞} {d : ℝ}
    (hcov : HasCoveringExponent S c d) (hc : c ≠ ∞) (hdq : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ⦃γ : ℝ≥0⦄, d + p * γ < q → ∀ ω, ∃ K, HolderWith K γ (Y · ω)) ∧
      ∀ s : S, Y s =ᵐ[P] X s := by
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    hX.exists_continuous_holderOnWith_of_isOpen_cover hS (fun _ ↦ isOpen_univ)
      (iUnion_const univ) (fun _ ↦ by simpa using hcov) (fun _ ↦ hc) (fun _ ↦ hdq)
  refine ⟨Y, hY_meas, hY_cont, fun {γ} hγ ω ↦ ?_, hYX⟩
  obtain ⟨K, hK⟩ := hY_hold 0 hγ ω
  exact ⟨K, holderOnWith_univ.mp hK⟩

/-- **Global metric-parameter Kolmogorov–Chentsov modification.**
If `T` has covering exponent `d` (finite constant `c`) with `d < q`, any `X : T → Ω → E`
satisfying `IsAEKolmogorovProcess X P p q M` into a complete Borel extended metric space `E` admits
a single coordinatewise measurable modification `Y` whose sample paths are everywhere continuous
and simultaneously `γ`-Hölder on `T` for all `γ : ℝ≥0` with `d + p * γ < q`. -/
theorem exists_holderWith_modification {T Ω E : Type*}
    [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0} (hX : IsAEKolmogorovProcess X P p q M)
    {c : ℝ≥0∞} {d : ℝ} (hcov : HasCoveringExponent (univ : Set T) c d)
    (hc : c ≠ ∞) (hdq : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ⦃γ : ℝ≥0⦄, d + p * γ < q → ∀ ω, ∃ K, HolderWith K γ (Y · ω)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    (hX.comp_isometry isometry_subtype_coe).exists_holderWith_of_dense_of_hasCoveringExponent
      dense_univ (by simpa using hcov) hc hdq
  exact ⟨Y, hY_meas, hY_cont, hY_hold, fun t ↦ hYX ⟨t, trivial⟩⟩

/-- **Kolmogorov–Chentsov extension from a dense subset of a finite-dimensional normed space.**
If `F` is a finite-dimensional real normed space with `finrank ℝ F < q` and `S ⊆ F` is dense, any
`X : S → Ω → E` satisfying `IsAEKolmogorovProcess X P p q M` extends `P`-a.e. to a coordinatewise
measurable process `Y : F → Ω → E` with everywhere continuous paths that are `γ`-Hölder on every
bounded set `A ⊆ F` for all `γ : ℝ≥0` with `finrank ℝ F + p * γ < q`. -/
theorem exists_continuous_holderOnWith_of_dense_normedSpace {F Ω E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {S : Set F} (hS : Dense S) {X : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hdq : (Module.finrank ℝ F : ℝ) < q) :
    ∃ Y : F → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ⦃A : Set F⦄, Bornology.IsBounded A → ∀ ⦃γ : ℝ≥0⦄,
        (Module.finrank ℝ F : ℝ) + p * γ < q → ∀ ω, ∃ K, HolderOnWith K γ (Y · ω) A) ∧
      ∀ s : S, Y s =ᵐ[P] X s := by
  let U : ℕ → Set F := fun n ↦ ball 0 (n + 1 : ℝ)
  have hU_cov : ⋃ n, U n = univ := eq_univ_iff_forall.mpr fun x ↦ by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨n, mem_ball_zero_iff.mpr (by linarith)⟩
  have hcov (n : ℕ) : HasCoveringExponent (S ∩ U n)
      (((max 1 (4 * (n + 1 : ℝ≥0))) ^ Module.finrank ℝ F : ℝ≥0) : ℝ≥0∞) (Module.finrank ℝ F) :=
    TauCeti.hasCoveringExponent_of_subset_closedBall (x := (0 : F))
      (inter_subset_right.trans (ball_subset_closedBall.trans (by simp)))
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    hX.exists_continuous_holderOnWith_of_isOpen_cover hS (fun _ ↦ isOpen_ball) hU_cov hcov
      (fun _ ↦ ENNReal.coe_ne_top) (fun _ ↦ hdq)
  refine ⟨Y, hY_meas, hY_cont, fun {A} hA {γ} hγ ω ↦ ?_, hYX⟩
  obtain ⟨r, _, hr⟩ := hA.subset_ball_lt 0 (0 : F)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨K, hK⟩ := hY_hold n hγ ω
  exact ⟨K, hK.mono (hr.trans (ball_subset_ball (by linarith)))⟩

/-- **Kolmogorov–Chentsov modification on a finite-dimensional real normed space.** -/
theorem exists_continuous_holderOnWith_modification_normedSpace {F Ω E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : F → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hdq : (Module.finrank ℝ F : ℝ) < q) :
    ∃ Y : F → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ⦃A : Set F⦄, Bornology.IsBounded A → ∀ ⦃γ : ℝ≥0⦄,
        (Module.finrank ℝ F : ℝ) + p * γ < q → ∀ ω, ∃ K, HolderOnWith K γ (Y · ω) A) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    (hX.comp_isometry isometry_subtype_coe).exists_continuous_holderOnWith_of_dense_normedSpace
      dense_univ hdq
  exact ⟨Y, hY_meas, hY_cont, hY_hold, fun t ↦ hYX ⟨t, trivial⟩⟩

/-- **Kolmogorov–Chentsov extension from a dense subset of `ℝ≥0`.**
If `S ⊆ ℝ≥0` is dense and `1 < q`, any `X : S → Ω → E` satisfying
`IsAEKolmogorovProcess X P p q M` extends `P`-a.e. to a coordinatewise measurable process
`Y : ℝ≥0 → Ω → E` with everywhere continuous paths that are `γ`-Hölder on every bounded set
`A ⊆ ℝ≥0` (in particular on `[0, T]`) for all `γ : ℝ≥0` with `1 + p * γ < q`. -/
theorem exists_continuous_holderOnWith_of_dense_nnreal {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {S : Set ℝ≥0} (hS : Dense S) {X : S → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ⦃A : Set ℝ≥0⦄, Bornology.IsBounded A → ∀ ⦃γ : ℝ≥0⦄,
        1 + p * γ < q → ∀ ω, ∃ K, HolderOnWith K γ (Y · ω) A) ∧
      ∀ s : S, Y s =ᵐ[P] X s := by
  let U : ℕ → Set ℝ≥0 := fun n ↦ ball 0 (n + 1 : ℝ)
  have hU_cov : ⋃ n, U n = univ := eq_univ_iff_forall.mpr fun x ↦ by
    obtain ⟨n, hn⟩ := exists_nat_gt (x : ℝ)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    rw [mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg x)]
    linarith
  have hiso : Isometry ((↑) : ℝ≥0 → ℝ) := fun _ _ ↦ rfl
  have hcov (n : ℕ) : HasCoveringExponent (S ∩ U n)
      (((max 1 (4 * (n + 1 : ℝ≥0))) ^ 1 : ℝ≥0) : ℝ≥0∞) 1 := by
    refine hiso.hasCoveringExponent ?_
    have hsub : ((↑) : ℝ≥0 → ℝ) '' (S ∩ U n) ⊆ closedBall (0 : ℝ) ((n + 1 : ℝ≥0) : ℝ) := by
      rintro _ ⟨x, ⟨_, hxU⟩, rfl⟩
      rw [mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
        abs_of_nonneg (NNReal.coe_nonneg x)] at hxU
      rw [mem_closedBall_zero_iff, Real.norm_of_nonneg (NNReal.coe_nonneg x)]
      exact hxU.le.trans (by simp)
    simpa [Module.finrank_self] using TauCeti.hasCoveringExponent_of_subset_closedBall hsub
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    hX.exists_continuous_holderOnWith_of_isOpen_cover hS (fun _ ↦ isOpen_ball) hU_cov hcov
      (fun _ ↦ ENNReal.coe_ne_top) (fun _ ↦ hq)
  refine ⟨Y, hY_meas, hY_cont, fun {A} hA {γ} hγ ω ↦ ?_, hYX⟩
  obtain ⟨r, _, hr⟩ := hA.subset_ball_lt 0 (0 : ℝ≥0)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨K, hK⟩ := hY_hold n hγ ω
  exact ⟨K, hK.mono (hr.trans (ball_subset_ball (by linarith)))⟩

/-- **Kolmogorov–Chentsov modification on `ℝ≥0`.** -/
theorem exists_continuous_holderOnWith_modification_nnreal {Ω E : Type*}
    [EMetricSpace E] [CompleteSpace E] [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ⦃A : Set ℝ≥0⦄, Bornology.IsBounded A → ∀ ⦃γ : ℝ≥0⦄,
        1 + p * γ < q → ∀ ω, ∃ K, HolderOnWith K γ (Y · ω) A) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  obtain ⟨Y, hY_meas, hY_cont, hY_hold, hYX⟩ :=
    (hX.comp_isometry isometry_subtype_coe).exists_continuous_holderOnWith_of_dense_nnreal
      dense_univ hq
  exact ⟨Y, hY_meas, hY_cont, hY_hold, fun t ↦ hYX ⟨t, trivial⟩⟩

end ProbabilityTheory.IsAEKolmogorovProcess
