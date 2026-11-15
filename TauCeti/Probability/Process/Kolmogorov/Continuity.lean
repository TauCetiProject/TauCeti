/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Topology.MetricSpace.Holder
-- Private: spanner, Hölder extension, covering bounds, and Borel limit measurability are internal.
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Probability.Process.Kolmogorov.Edges
import TauCeti.Topology.MetricSpace.CoveringNumbers
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.MetricSpace.Spanner

/-!
# The Kolmogorov–Chentsov continuous and Hölder modification theorem

Let `X : T → Ω → E` satisfy `ProbabilityTheory.IsAEKolmogorovProcess X P p q M` with values in a
complete extended metric space `E`. When `T` has bounded covering exponent `d ≥ 0`
(`Metric.HasCoveringExponent Set.univ c d` with `c ≠ ∞`), for every Hölder exponent `γ > 0` with
`d + p * γ < q` there exists a modification `Y : T → Ω → E` of `X` such that:

* `IsKolmogorovProcess Y P p q M` (including joint Borel measurability of all pairs `(Y s, Y t)`,
  with no separability assumption on `E`);
* *every* sample path `Y · ω` is `γ`-Hölder continuous on `T`.

On general metric spaces without a doubling assumption, a `2^{-m}`-net of size `≲ 2^{m d}` can
contain `≈ 2^{2 m d}` nearby pairs, so naive pair-counting only reaches `(q - 2 d) / p`. Following
Krätschmer and Urusov, we combine nested dyadic covers with Awerbuch's `(2 k - 1)`-spanner
(`Finset.exists_spanner_rpow`): at scale `m`, each point of the net steps to a single parent at
scale `m - 1` (`≲ 2^{m (d + δ)}` parent edges), while nearby net points are routed through a
`(2 k - 1)`-spanner of size `≲ 2^{m (d + δ) (1 + 1 / k)}`. Choosing `k` large and `δ` small makes
the geometric edge-energy series (`IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow`) converge
for every `γ < (q - d) / p`. Extending from the countable dense union of the nets via
`HolderOnWith.extend_of_dense` on a measurable full-measure event yields global `γ`-Hölder sample
paths and preserves Borel pair measurability as a pointwise limit in `E × E`.

Gluing along a monotone open exhaustion `(U n)` whose pieces have covering exponent `d` extends the
result to unbounded spaces such as `ℝ≥0` and `ℝ`.

## Main results

* `ProbabilityTheory.IsAEKolmogorovProcess.ae_exists_finset_edist_le_mul_pow_rpow`: simultaneous
  random Hölder-scale bound across a sequence of finite edge sets `E : ℕ → Finset (T × T)`.
* `ProbabilityTheory.IsAEKolmogorovProcess.exists_modification_holderWith`: global `γ`-Hölder
  modification under `Metric.HasCoveringExponent Set.univ c d` and `d + p * γ < q`.
* `ProbabilityTheory.IsAEKolmogorovProcess.exists_modification_holderOnWith_of_isOpen_cover`:
  continuous modification that is locally `γ`-Hölder on each piece of a monotone open exhaustion.
* `ProbabilityTheory.IsAEKolmogorovProcess.exists_modification_holderOnWith_Icc_nnreal`,
  `ProbabilityTheory.IsAEKolmogorovProcess.exists_modification_continuous_nnreal`, and
  `ProbabilityTheory.IsAEKolmogorovProcess.exists_modification_continuous_real`: specializations to
  `ℝ≥0` and `ℝ` (`d = 1`).

## References

* Andrey N. Kolmogorov, *Foundations of the Theory of Probability*, Chelsea, 1956.
* Nikolai N. Chentsov, *Weak convergence of stochastic processes whose trajectories have no
  discontinuities of the second kind and the "heuristic" approach to the Kolmogorov–Smirnov tests*,
  Theory Probab. Appl. 1 (1956), 140–144.
* Volker Krätschmer and Mikhail Urusov, *A general Kolmogorov–Chentsov type theorem on general
  metric spaces*, Bernoulli 29 (2023), 2960–2986, arXiv:2107.13837v2, Theorem 1.1.
* Olav Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021, Theorem 4.23.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.IsAEKolmogorovProcess

section FinsetEdges

variable {T Ω E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  {p q : ℝ} {M : ℝ≥0}

/-- Finite-set form of `ae_exists_edist_le_mul_pow_rpow`: if a sequence of finite edge sets
`E : ℕ → Finset (T × T)` satisfies `(E n).card ≤ C * (r ^ (-d)) ^ n` and every edge in `E n` has
length at most `r ^ n` (`0 < r < 1`), then for every `γ` with `d + p * γ < q` a single finite
random constant bounds all normalized edge increments almost surely. -/
theorem ae_exists_finset_edist_le_mul_pow_rpow (hX : IsAEKolmogorovProcess X P p q M)
    {E : ℕ → Finset (T × T)} {C r : ℝ≥0} {d γ : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hcard : ∀ n, ((E n).card : ℝ≥0) ≤ C * (r ^ (-d)) ^ n)
    (hedge : ∀ n, ∀ e ∈ E n, edist e.1 e.2 ≤ (r : ℝ≥0∞) ^ n)
    (hγ : d + p * γ < q) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n, ∀ e ∈ E n,
      edist (X e.1 ω) (X e.2 ω) ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
  let eqv (n : ℕ) : E n ≃ Fin (E n).card := (E n).equivFin
  let s (n : ℕ) (i : Fin (E n).card) : T := ((eqv n).symm i).1.1
  let t (n : ℕ) (i : Fin (E n).card) : T := ((eqv n).symm i).1.2
  have hedge' (n : ℕ) (i : Fin (E n).card) : edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n :=
    hedge n _ ((eqv n).symm i).2
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow hr hr₁ hcard hedge' hγ] with ω ⟨K, hK⟩
  refine ⟨K, fun n e he ↦ ?_⟩
  have hi := hK n (eqv n ⟨e, he⟩)
  simpa only [s, t, Equiv.symm_apply_apply] using hi

end FinsetEdges

section Helpers

/-- Geometric tail bound on `Finset.Ico`: in `ℝ≥0∞`, summing `a ^ n` over `Ico m N` (`m ≤ N`) is at
most `a ^ m * (1 - a)⁻¹`. -/
private lemma sum_Ico_pow_le (a : ℝ≥0∞) :
    ∀ {m N : ℕ}, m ≤ N → ∑ n ∈ Finset.Ico m N, a ^ n ≤ a ^ m * (1 - a)⁻¹ := by
  intro m N _
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ Finset.range (N - m), a ^ (m + k)
    _ ≤ ∑' k : ℕ, a ^ (m + k) := sum_le_tsum _
    _ = ∑' k : ℕ, a ^ m * a ^ k := by simp_rw [pow_add]
    _ = a ^ m * (1 - a)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- `(8 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 3 = 1`. -/
private lemma eight_mul_inv_two_pow_three : (8 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 3 = 1 := by
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc (8 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 3
    _ = ((2 : ℝ≥0∞) * 2⁻¹) * ((2 : ℝ≥0∞) * 2⁻¹) * ((2 : ℝ≥0∞) * 2⁻¹) := by ring
    _ = 1 := by rw [h2]; ring

/-- Absorbing a linear factor `n + 1` into an arbitrarily small exponential `((2 : ℝ≥0) ^ δ) ^ n`
(`0 < δ`) via Bernoulli's inequality. -/
private lemma nat_add_one_le_mul_two_rpow_pow {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ n : ℕ, ((n + 1 : ℕ) : ℝ≥0) ≤ A * ((2 : ℝ≥0) ^ δ) ^ n := by
  have h2δ : (1 : ℝ≥0) < (2 : ℝ≥0) ^ δ := NNReal.one_lt_rpow one_lt_two hδ
  let η : ℝ≥0 := (2 : ℝ≥0) ^ δ - 1
  have hη_pos : 0 < η := tsub_pos_iff_lt.mpr h2δ
  have h1η : 1 + η = (2 : ℝ≥0) ^ δ := add_tsub_cancel_of_le h2δ.le
  refine ⟨1 + η⁻¹, le_self_add, fun n ↦ ?_⟩
  have hbern : 1 + (n : ℝ) * (η : ℝ) ≤ (1 + (η : ℝ)) ^ n :=
    one_add_mul_le_pow (by linarith [η.coe_nonneg]) n
  have hbern' : 1 + (n : ℝ≥0) * η ≤ ((2 : ℝ≥0) ^ δ) ^ n := by
    rw [← h1η]
    exact_mod_cast hbern
  have hlin : ((n + 1 : ℕ) : ℝ≥0) ≤ (1 + η⁻¹) * (1 + (n : ℝ≥0) * η) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have hmul : (η : ℝ)⁻¹ * (η : ℝ) = 1 := inv_mul_cancel₀ (NNReal.coe_ne_zero.mpr hη_pos.ne')
    calc (n : ℝ) + 1
      _ = 1 + (n : ℝ) * ((η : ℝ)⁻¹ * (η : ℝ)) := by rw [hmul]; ring
      _ ≤ 1 + (n : ℝ) * (η : ℝ) + (η : ℝ)⁻¹ + (n : ℝ) * ((η : ℝ)⁻¹ * (η : ℝ)) := by
        have : 0 ≤ (n : ℝ) * (η : ℝ) + (η : ℝ)⁻¹ := by positivity
        linarith
      _ = (1 + (η : ℝ)⁻¹) * (1 + (n : ℝ) * (η : ℝ)) := by ring
  exact hlin.trans (by gcongr)

/-- Nested finite `(2⁻¹)^n`-covers of a space with `HasCoveringExponent univ c d`. -/
private lemma exists_nested_dyadic_covers {T : Type*} [PseudoEMetricSpace T]
    {c : ℝ≥0∞} {d : ℝ} (hcov : HasCoveringExponent (univ : Set T) c d)
    (hc : c ≠ ∞) (hd : 0 ≤ d) :
    ∃ W : ℕ → Finset T,
      (∀ ⦃m n⦄, m ≤ n → W m ⊆ W n) ∧
      (∀ n, IsCover ((2⁻¹ : ℝ≥0) ^ n) univ (W n : Set T)) ∧
      ∀ {δ : ℝ}, 0 < δ → ∃ C : ℝ≥0, 1 ≤ C ∧
        ∀ n, ((W n).card : ℝ≥0) ≤ C * ((2 : ℝ≥0) ^ (d + δ)) ^ n := by
  classical
  let r₂ : ℝ≥0 := 2⁻¹
  have hr₂_ne (n : ℕ) : r₂ ^ n ≠ 0 := pow_ne_zero n (by norm_num [r₂])
  have hr₂_le (n : ℕ) : r₂ ^ n ≤ 1 := pow_le_one₀ zero_le (by norm_num [r₂])
  let V (n : ℕ) : Finset T := (finite_minimalCover (ε := r₂ ^ n) (A := univ)).toFinset
  let W (n : ℕ) : Finset T := (Finset.range (n + 1)).biUnion V
  have hV_fin (n : ℕ) : coveringNumber (r₂ ^ n) (univ : Set T) ≠ ⊤ :=
    hcov.coveringNumber_ne_top (hr₂_ne n) hc hd
  have hV_card (n : ℕ) : ((V n).card : ℝ≥0) ≤ max 1 c.toNNReal * ((2 : ℝ≥0) ^ d) ^ n := by
    have hle := hcov.coveringNumber_le_max_one_mul hd (hr₂_le n)
    have henc : ((V n).card : ℝ≥0∞) = (coveringNumber (r₂ ^ n) (univ : Set T) : ℝ≥0∞) := by
      rw [← encard_minimalCover (hV_fin n),
        (finite_minimalCover (ε := r₂ ^ n) (A := univ)).encard_eq_coe_toFinset_card,
        ENat.toENNReal_coe]
    have hrhs : max 1 c * ((r₂ ^ n : ℝ≥0) : ℝ≥0∞)⁻¹ ^ d =
        ((max 1 c.toNNReal * ((2 : ℝ≥0) ^ d) ^ n : ℝ≥0) : ℝ≥0∞) := by
      have hinv : ((r₂ ^ n : ℝ≥0) : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_pow, ENNReal.inv_pow]
        have h2 : ((r₂ : ℝ≥0∞))⁻¹ = 2 := by
          dsimp [r₂]
          rw [ENNReal.coe_inv two_ne_zero, inv_inv, ENNReal.coe_ofNat]
        rw [h2]
      rw [← ENNReal.coe_toNNReal hc, ← ENNReal.coe_one, ← ENNReal.coe_max, hinv,
        ENNReal.pow_rpow_comm, ← ENNReal.coe_ofNat, ← ENNReal.coe_rpow_of_nonneg _ hd]
      push_cast
      rfl
    exact ENNReal.coe_le_coe.mp (henc.trans_le (hle.trans_eq hrhs))
  refine ⟨W, fun m n hmn ↦ Finset.biUnion_subset_biUnion_of_subset_left V
    (Finset.range_mono (Nat.succ_le_succ hmn)), fun n ↦ ?_, fun {δ} hδ ↦ ?_⟩
  · refine (isCover_minimalCover (hV_fin n)).mono ?_
    intro x hx
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), (Set.Finite.mem_toFinset _).mpr hx⟩)
  · obtain ⟨A, hA1, hA⟩ := nat_add_one_le_mul_two_rpow_pow hδ
    let C₀ : ℝ≥0 := max 1 c.toNNReal
    have h2d_one : (1 : ℝ≥0) ≤ (2 : ℝ≥0) ^ d := NNReal.one_le_rpow one_le_two hd
    refine ⟨A * C₀, one_le_mul_of_one_le_of_one_le hA1 (le_max_left 1 _), fun n ↦ ?_⟩
    have hW_sum : ((W n).card : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) * C₀ * ((2 : ℝ≥0) ^ d) ^ n := by
      calc ((W n).card : ℝ≥0)
        _ ≤ ∑ i ∈ Finset.range (n + 1), ((V i).card : ℝ≥0) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ Finset.range (n + 1), C₀ * ((2 : ℝ≥0) ^ d) ^ n := by
          refine Finset.sum_le_sum fun i hi ↦ (hV_card i).trans ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ h2d_one (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) zero_le
        _ = ((n + 1 : ℕ) : ℝ≥0) * C₀ * ((2 : ℝ≥0) ^ d) ^ n := by
          simp [mul_assoc]
    calc ((W n).card : ℝ≥0)
      _ ≤ ((n + 1 : ℕ) : ℝ≥0) * C₀ * ((2 : ℝ≥0) ^ d) ^ n := hW_sum
      _ ≤ (A * ((2 : ℝ≥0) ^ δ) ^ n) * C₀ * ((2 : ℝ≥0) ^ d) ^ n := by
        have := hA n
        gcongr
      _ = (A * C₀) * (((2 : ℝ≥0) ^ d) ^ n * ((2 : ℝ≥0) ^ δ) ^ n) := by ring
      _ = (A * C₀) * ((2 : ℝ≥0) ^ (d + δ)) ^ n := by
        rw [← mul_pow, ← NNReal.rpow_add two_ne_zero]

/-- Forward chaining along parent projections `π n : T → W n`: every `x ∈ W N` (`m ≤ N`) steps down
to some `u ∈ W m` at parameter distance `≤ 2 * (2⁻¹)^m` and output distance bounded by the
geometric series of parent increments. -/
private lemma chain_to_coarse {T E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
    {W : ℕ → Finset T} {π : ℕ → T → T} (hπ_mem : ∀ n x, π n x ∈ W n)
    (hπ_dist : ∀ n x, edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ n)
    {γ : ℝ≥0} {f : T → E} {Kpar : ℝ≥0}
    (hpar : ∀ n, ∀ z ∈ W (n + 1),
      edist (f z) (f (π n z)) ≤ (Kpar : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    {m N : ℕ} (hmN : m ≤ N) {x : T} (hx : x ∈ W N) :
    ∃ u ∈ W m, edist x u ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ m ∧
      edist (f x) (f u) ≤
        (Kpar : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)) ^ m * (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹ := by
  let aγ : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)
  have hinv2 : (1 - (2⁻¹ : ℝ≥0∞))⁻¹ = 2 := by
    have hsub : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ :=
      ENNReal.sub_eq_of_eq_add (by norm_num) ENNReal.inv_two_add_inv_two.symm
    rw [hsub, inv_inv]
  suffices ∀ z ∈ W N, ∃ u ∈ W m,
      edist z u ≤ ∑ n ∈ Finset.Ico m N, (2⁻¹ : ℝ≥0∞) ^ n ∧
      edist (f z) (f u) ≤ ∑ n ∈ Finset.Ico m N, (Kpar : ℝ≥0∞) * aγ ^ n by
    obtain ⟨u, hu, hdu, hdfu⟩ := this x hx
    refine ⟨u, hu, ?_, ?_⟩
    · exact hdu.trans ((sum_Ico_pow_le 2⁻¹ hmN).trans_eq (by rw [hinv2, mul_comm]))
    · rw [← Finset.mul_sum] at hdfu
      exact hdfu.trans (by rw [mul_assoc]; gcongr; exact sum_Ico_pow_le aγ hmN)
  refine Nat.le_induction (fun z hz ↦ ⟨z, hz, by simp, by simp⟩) (fun n hmn ih z hz ↦ ?_) N hmN
  obtain ⟨u, hu, hdu, hdfu⟩ := ih (π n z) (hπ_mem n z)
  refine ⟨u, hu, ?_, ?_⟩
  · rw [Finset.sum_Ico_succ_top hmn, add_comm]
    exact (edist_triangle z (π n z) u).trans (add_le_add (hπ_dist n z) hdu)
  · rw [Finset.sum_Ico_succ_top hmn, add_comm]
    have hstep : edist (f z) (f (π n z)) ≤ (Kpar : ℝ≥0∞) * aγ ^ n := by
      simpa only [aγ, ENNReal.pow_rpow_comm] using hpar n z hz
    exact (edist_triangle (f z) (f (π n z)) (f u)).trans (add_le_add hstep hdfu)

/-- Scale-`m` chaining bound (`m ≥ 3`): for `x, y ∈ ⋃ N, W N` with `edist x y ≤ (2⁻¹)^m`, chain
both endpoints down to `u, v ∈ W m = W ((m - 3) + 3)` and route `(u, v)` through the spanner at
level `l = m - 3`. -/
private lemma edist_le_mul_pow_of_edges {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {W : ℕ → Finset T}
    (hW_mono : ∀ ⦃m n⦄, m ≤ n → W m ⊆ W n)
    {π : ℕ → T → T} (hπ_mem : ∀ n x, π n x ∈ W n)
    (hπ_dist : ∀ n x, edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ n)
    {k : ℕ} {Espan : ℕ → Finset (T × T)}
    (hspan : ∀ l (w : T → T → ℝ≥0∞),
      (∀ a, w a a = 0) → (∀ a b, w a b = w b a) → (∀ a b c, w a c ≤ w a b + w b c) →
      ∀ {D : ℝ≥0∞}, (∀ e ∈ Espan l, w e.1 e.2 ≤ D) →
      ∀ u ∈ W (l + 3), ∀ v ∈ W (l + 3), edist u v ≤ (2⁻¹ : ℝ≥0∞) ^ l →
        w u v ≤ (2 * k - 1 : ℕ) * D)
    {γ : ℝ≥0} {f : T → E} {Kpar Kspan : ℝ≥0}
    (hpar : ∀ n, ∀ z ∈ W (n + 1),
      edist (f z) (f (π n z)) ≤ (Kpar : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (hsp : ∀ l, ∀ e ∈ Espan l,
      edist (f e.1) (f e.2) ≤ (Kspan : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ))
    {x y : T} (hx : x ∈ ⋃ N, (W N : Set T)) (hy : y ∈ ⋃ N, (W N : Set T))
    {m : ℕ} (hm3 : 3 ≤ m) (hdxy : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ m) :
    edist (f x) (f y) ≤
      (2 * (Kpar : ℝ≥0∞) * (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹ +
        (2 * k - 1 : ℕ) * (Kspan : ℝ≥0∞) * (8 : ℝ≥0∞) ^ (γ : ℝ)) *
      ((2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)) ^ m := by
  let aγ : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)
  obtain ⟨Nx, hxN⟩ := mem_iUnion.mp hx
  obtain ⟨Ny, hyN⟩ := mem_iUnion.mp hy
  let N : ℕ := max (max Nx Ny) m
  have hxWN : x ∈ W N :=
    hW_mono ((le_max_left Nx Ny).trans (le_max_left _ m)) (Finset.mem_coe.mp hxN)
  have hyWN : y ∈ W N :=
    hW_mono ((le_max_right Nx Ny).trans (le_max_left _ m)) (Finset.mem_coe.mp hyN)
  obtain ⟨u, hu, hdu, hdfu⟩ := chain_to_coarse hπ_mem hπ_dist hpar (le_max_right _ m) hxWN
  obtain ⟨v, hv, hdv, hdfv⟩ := chain_to_coarse hπ_mem hπ_dist hpar (le_max_right _ m) hyWN
  let l : ℕ := m - 3
  have hml : m = l + 3 := (Nat.sub_add_cancel hm3).symm
  have hu' : u ∈ W (l + 3) := hml ▸ hu
  have hv' : v ∈ W (l + 3) := hml ▸ hv
  have huv_dist : edist u v ≤ (2⁻¹ : ℝ≥0∞) ^ l := by
    calc edist u v
      _ ≤ edist u x + edist x y + edist y v := edist_triangle4 u x y v
      _ = edist x u + edist x y + edist y v := by rw [edist_comm u x]
      _ ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ m + (2⁻¹ : ℝ≥0∞) ^ m + 2 * (2⁻¹ : ℝ≥0∞) ^ m :=
        add_le_add (add_le_add hdu hdxy) hdv
      _ ≤ 8 * (2⁻¹ : ℝ≥0∞) ^ m := by
        rw [show 2 * (2⁻¹ : ℝ≥0∞) ^ m + (2⁻¹ : ℝ≥0∞) ^ m + 2 * (2⁻¹ : ℝ≥0∞) ^ m =
          5 * (2⁻¹ : ℝ≥0∞) ^ m by ring]
        gcongr
        norm_num
      _ = (2⁻¹ : ℝ≥0∞) ^ l := by
        rw [hml, pow_add]
        calc (8 : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l * (2⁻¹ : ℝ≥0∞) ^ 3)
          _ = ((8 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 3) * (2⁻¹ : ℝ≥0∞) ^ l := by ring
          _ = (2⁻¹ : ℝ≥0∞) ^ l := by rw [eight_mul_inv_two_pow_three, one_mul]
  have huv_f : edist (f u) (f v) ≤
      (2 * k - 1 : ℕ) * (Kspan : ℝ≥0∞) * (8 : ℝ≥0∞) ^ (γ : ℝ) * aγ ^ m := by
    have hsp_l := hspan l (fun a b ↦ edist (f a) (f b))
      (fun _ ↦ edist_self _) (fun _ _ ↦ edist_comm _ _) (fun _ _ _ ↦ edist_triangle _ _ _)
      (hsp l) u hu' v hv' huv_dist
    have hl_rpow : ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ) = (8 : ℝ≥0∞) ^ (γ : ℝ) * aγ ^ m := by
      rw [ENNReal.pow_rpow_comm, hml, pow_add]
      have h8γ : (8 : ℝ≥0∞) ^ (γ : ℝ) * aγ ^ 3 = 1 := by
        dsimp [aγ]
        rw [← ENNReal.pow_rpow_comm, ← ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg,
          eight_mul_inv_two_pow_three, ENNReal.one_rpow]
      calc aγ ^ l
        _ = aγ ^ l * ((8 : ℝ≥0∞) ^ (γ : ℝ) * aγ ^ 3) := by rw [h8γ, mul_one]
        _ = (8 : ℝ≥0∞) ^ (γ : ℝ) * (aγ ^ l * aγ ^ 3) := by ring
    calc edist (f u) (f v)
      _ ≤ (2 * k - 1 : ℕ) * ((Kspan : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ)) := hsp_l
      _ = (2 * k - 1 : ℕ) * (Kspan : ℝ≥0∞) * (8 : ℝ≥0∞) ^ (γ : ℝ) * aγ ^ m := by
        rw [hl_rpow]; ring
  calc edist (f x) (f y)
    _ ≤ edist (f x) (f u) + edist (f u) (f v) + edist (f v) (f y) :=
      edist_triangle4 (f x) (f u) (f v) (f y)
    _ = (edist (f x) (f u) + edist (f y) (f v)) + edist (f u) (f v) := by
      rw [edist_comm (f v) (f y)]; ring
    _ ≤ ((Kpar : ℝ≥0∞) * aγ ^ m * (1 - aγ)⁻¹ + (Kpar : ℝ≥0∞) * aγ ^ m * (1 - aγ)⁻¹) +
        (2 * k - 1 : ℕ) * (Kspan : ℝ≥0∞) * (8 : ℝ≥0∞) ^ (γ : ℝ) * aγ ^ m :=
      add_le_add (add_le_add hdfu hdfv) huv_f
    _ = (2 * (Kpar : ℝ≥0∞) * (1 - aγ)⁻¹ +
          (2 * k - 1 : ℕ) * (Kspan : ℝ≥0∞) * (8 : ℝ≥0∞) ^ (γ : ℝ)) * aγ ^ m := by ring

/-- Deterministic chaining on the union `⋃ N, W N` of nested `(2⁻¹)^n`-covers equipped with parent
projections `π` and `(2 k - 1)`-spanners `Espan`: once parent edges, spanner edges, and coarse `W 0`
pairs have bounded increments, `f` is globally `γ`-Hölder on `⋃ N, (W N : Set T)`. -/
private lemma holderOnWith_iUnion_of_edges {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {W : ℕ → Finset T}
    (hW_mono : ∀ ⦃m n⦄, m ≤ n → W m ⊆ W n)
    {π : ℕ → T → T} (hπ_mem : ∀ n x, π n x ∈ W n)
    (hπ_dist : ∀ n x, edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ n)
    {k : ℕ} {Espan : ℕ → Finset (T × T)}
    (hspan : ∀ l (w : T → T → ℝ≥0∞),
      (∀ a, w a a = 0) → (∀ a b, w a b = w b a) → (∀ a b c, w a c ≤ w a b + w b c) →
      ∀ {D : ℝ≥0∞}, (∀ e ∈ Espan l, w e.1 e.2 ≤ D) →
      ∀ u ∈ W (l + 3), ∀ v ∈ W (l + 3), edist u v ≤ (2⁻¹ : ℝ≥0∞) ^ l →
        w u v ≤ (2 * k - 1 : ℕ) * D)
    {γ : ℝ≥0} (hγ₀ : 0 < γ) {f : T → E} {Kpar Kspan K₀ : ℝ≥0}
    (hpar : ∀ n, ∀ z ∈ W (n + 1),
      edist (f z) (f (π n z)) ≤ (Kpar : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (hsp : ∀ l, ∀ e ∈ Espan l,
      edist (f e.1) (f e.2) ≤ (Kspan : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ))
    (hK₀ : ∀ u ∈ W 0, ∀ v ∈ W 0, edist (f u) (f v) ≤ K₀) :
    ∃ K : ℝ≥0, HolderOnWith K γ f (⋃ N, (W N : Set T)) := by
  let aγ : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)
  have hγ_pos : (0 : ℝ) < γ := NNReal.coe_pos.mpr hγ₀
  have haγ_lt : aγ < 1 := ENNReal.rpow_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1) hγ_pos
  have hinv_ne_top : (1 - aγ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr haγ_lt).ne'
  -- Uniform diameter bound on `⋃ N, W N` by chaining all the way down to `W 0`.
  let D_top : ℝ≥0∞ := K₀ + 2 * (Kpar : ℝ≥0∞) * (1 - aγ)⁻¹
  have hD_ne_top : D_top ≠ ∞ := by
    dsimp [D_top]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hinv_ne_top⟩
  have hdiam_f : ∀ x ∈ ⋃ N, (W N : Set T), ∀ y ∈ ⋃ N, (W N : Set T), edist (f x) (f y) ≤ D_top := by
    rintro x hx y hy
    obtain ⟨Nx, hxN⟩ := mem_iUnion.mp hx
    obtain ⟨Ny, hyN⟩ := mem_iUnion.mp hy
    obtain ⟨u₀, hu₀, -, hdfx⟩ :=
      chain_to_coarse hπ_mem hπ_dist hpar (Nat.zero_le Nx) (Finset.mem_coe.mp hxN)
    obtain ⟨v₀, hv₀, -, hdfy⟩ :=
      chain_to_coarse hπ_mem hπ_dist hpar (Nat.zero_le Ny) (Finset.mem_coe.mp hyN)
    calc edist (f x) (f y)
      _ ≤ edist (f x) (f u₀) + edist (f u₀) (f v₀) + edist (f v₀) (f y) :=
        edist_triangle4 (f x) (f u₀) (f v₀) (f y)
      _ = edist (f u₀) (f v₀) + (edist (f x) (f u₀) + edist (f y) (f v₀)) := by
        rw [edist_comm (f v₀) (f y)]; ring
      _ ≤ K₀ + ((Kpar : ℝ≥0∞) * aγ ^ 0 * (1 - aγ)⁻¹ + (Kpar : ℝ≥0∞) * aγ ^ 0 * (1 - aγ)⁻¹) :=
        add_le_add (hK₀ u₀ hu₀ v₀ hv₀) (add_le_add hdfx hdfy)
      _ = D_top := by dsimp [D_top]; ring
  let C_mid : ℝ≥0∞ :=
    2 * (Kpar : ℝ≥0∞) * (1 - aγ)⁻¹ + (2 * k - 1 : ℕ) * (Kspan : ℝ≥0∞) * (8 : ℝ≥0∞) ^ (γ : ℝ)
  let C_small : ℝ≥0∞ := C_mid * (2 : ℝ≥0∞) ^ (γ : ℝ)
  let C_tot : ℝ≥0∞ := max C_small (D_top * (8 : ℝ≥0∞) ^ (γ : ℝ))
  have hC_tot_ne_top : C_tot ≠ ∞ := by
    refine (max_lt_iff.mpr ⟨?_, ?_⟩).ne
    · refine ENNReal.mul_lt_top ?_ (ENNReal.rpow_lt_top_of_nonneg γ.coe_nonneg (by norm_num))
      refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
      · exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) ENNReal.coe_lt_top) hinv_ne_top.lt_top
      · exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.coe_lt_top)
          (ENNReal.rpow_lt_top_of_nonneg γ.coe_nonneg (by norm_num))
    · exact ENNReal.mul_lt_top hD_ne_top.lt_top
        (ENNReal.rpow_lt_top_of_nonneg γ.coe_nonneg (by norm_num))
  have hscale_m {x y : T} (hx : x ∈ ⋃ N, (W N : Set T)) (hy : y ∈ ⋃ N, (W N : Set T))
      {m : ℕ} (hm3 : 3 ≤ m) (hdxy : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ m) :
      edist (f x) (f y) ≤ C_mid * aγ ^ m :=
    edist_le_mul_pow_of_edges hW_mono hπ_mem hπ_dist hspan hpar hsp hx hy hm3 hdxy
  refine ⟨C_tot.toNNReal, fun x hx y hy ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hC_tot_ne_top]
  rcases eq_or_ne (edist x y) 0 with hd0 | hd_pos
  · -- Zero parameter distance: let `m → ∞` in `hscale_m`.
    have htend : Tendsto (fun m : ℕ ↦ C_mid * aγ ^ (m + 3)) atTop (𝓝 0) := by
      have h0 : C_mid * 0 = 0 := mul_zero _
      rw [← h0]
      have hC_mid_ne : C_mid ≠ ∞ := by
        refine ne_top_of_le_ne_top hC_tot_ne_top ?_
        calc C_mid = C_mid * 1 := (mul_one _).symm
          _ ≤ C_mid * (2 : ℝ≥0∞) ^ (γ : ℝ) := by
            gcongr; exact ENNReal.one_le_rpow (by norm_num) hγ_pos
          _ ≤ C_tot := le_max_left _ _
      exact (ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one haγ_lt)
        (Or.inr hC_mid_ne)).comp (tendsto_add_atTop_nat 3)
    have hle0 : edist (f x) (f y) ≤ 0 :=
      ge_of_tendsto' htend fun m ↦ hscale_m hx hy (by omega) (by simp [hd0])
    simp [nonpos_iff_eq_zero.mp hle0]
  rcases le_or_gt (edist x y) ((2⁻¹ : ℝ≥0∞) ^ 3) with hd_small | hd_large
  · -- Small scale `0 < edist x y ≤ (2⁻¹)^3`: pick `m ≥ 3` bracketing `edist x y`.
    classical
    have hex : ∃ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n < edist x y :=
      ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).eventually
        (gt_mem_nhds (pos_iff_ne_zero.mpr hd_pos))).exists
    let n₀ : ℕ := Nat.find hex
    have hn₀_spec : (2⁻¹ : ℝ≥0∞) ^ n₀ < edist x y := Nat.find_spec hex
    have hn₀_gt3 : 3 < n₀ := by
      by_contra! hle3
      have hge : (2⁻¹ : ℝ≥0∞) ^ 3 ≤ (2⁻¹ : ℝ≥0∞) ^ n₀ :=
        pow_le_pow_right_of_le_one' (by norm_num) hle3
      exact (hd_small.trans hge).not_gt hn₀_spec
    let m : ℕ := n₀ - 1
    have hm_succ : m + 1 = n₀ := Nat.sub_add_cancel (by omega)
    have hm3 : 3 ≤ m := by omega
    have hd_le_m : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ m :=
      not_lt.mp (Nat.find_min hex (by omega : m < n₀))
    have hm_le_2d : aγ ^ m ≤ (2 : ℝ≥0∞) ^ (γ : ℝ) * edist x y ^ (γ : ℝ) := by
      have h2m : (2⁻¹ : ℝ≥0∞) ^ m ≤ 2 * edist x y := by
        have h1 : (2⁻¹ : ℝ≥0∞) ^ m = 2 * (2⁻¹ : ℝ≥0∞) ^ (m + 1) := by
          rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞), mul_assoc,
            ENNReal.mul_inv_cancel (a := 2) (by norm_num) (by norm_num), mul_one]
        rw [h1, hm_succ]
        have := hn₀_spec.le
        gcongr
      calc aγ ^ m
        _ = ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := (ENNReal.pow_rpow_comm _ _ _).symm
        _ ≤ (2 * edist x y) ^ (γ : ℝ) := ENNReal.rpow_le_rpow h2m γ.coe_nonneg
        _ = (2 : ℝ≥0∞) ^ (γ : ℝ) * edist x y ^ (γ : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg
    calc edist (f x) (f y)
      _ ≤ C_mid * aγ ^ m := hscale_m hx hy hm3 hd_le_m
      _ ≤ C_mid * ((2 : ℝ≥0∞) ^ (γ : ℝ) * edist x y ^ (γ : ℝ)) := by gcongr
      _ = C_small * edist x y ^ (γ : ℝ) := by dsimp [C_small]; ring
      _ ≤ C_tot * edist x y ^ (γ : ℝ) := by gcongr; exact le_max_left _ _
  · -- Large scale `(2⁻¹)^3 < edist x y`: use the uniform oscillation bound `D_top`.
    have h1_le : (1 : ℝ≥0∞) ≤ (8 : ℝ≥0∞) ^ (γ : ℝ) * edist x y ^ (γ : ℝ) := by
      calc (1 : ℝ≥0∞)
        _ = ((8 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 3) ^ (γ : ℝ) := by
          rw [eight_mul_inv_two_pow_three, ENNReal.one_rpow]
        _ = (8 : ℝ≥0∞) ^ (γ : ℝ) * ((2⁻¹ : ℝ≥0∞) ^ 3) ^ (γ : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg
        _ ≤ (8 : ℝ≥0∞) ^ (γ : ℝ) * edist x y ^ (γ : ℝ) :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hd_large.le γ.coe_nonneg) zero_le
    calc edist (f x) (f y)
      _ = edist (f x) (f y) * 1 := (mul_one _).symm
      _ ≤ D_top * ((8 : ℝ≥0∞) ^ (γ : ℝ) * edist x y ^ (γ : ℝ)) :=
        mul_le_mul' (hdiam_f x hx y hy) h1_le
      _ = (D_top * (8 : ℝ≥0∞) ^ (γ : ℝ)) * edist x y ^ (γ : ℝ) := by ring
      _ ≤ C_tot * edist x y ^ (γ : ℝ) := by gcongr; exact le_max_right _ _

/-- Probabilistic chaining step: for nested `(2⁻¹)^n`-covers `W` of a space of finite diameter with
exponential cardinality growth `(W n).card ≤ C_δ * 2^{(d + δ) n}`, almost every sample path of a
Kolmogorov process `Z` is `γ`-Hölder on `⋃ N, W N` whenever `0 < γ` and `d + p * γ < q`. -/
private lemma ae_exists_holderOnWith_iUnion_covers {T Ω E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : T → Ω → E}
    {p q : ℝ} {M : ℝ≥0} (hZ : IsKolmogorovProcess Z P p q M)
    (hdiam : ediam (univ : Set T) < ∞) {d : ℝ} (hd : 0 ≤ d)
    {W : ℕ → Finset T} (hW_mono : ∀ ⦃m n⦄, m ≤ n → W m ⊆ W n)
    (hW_card : ∀ {δ : ℝ}, 0 < δ → ∃ C : ℝ≥0, 1 ≤ C ∧
      ∀ n, ((W n).card : ℝ≥0) ≤ C * ((2 : ℝ≥0) ^ (d + δ)) ^ n)
    {π : ℕ → T → T} (hπ_mem : ∀ n x, π n x ∈ W n)
    (hπ_dist : ∀ n x, edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ n)
    {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : d + p * γ < q) :
    ∀ᵐ ω ∂P, ∃ C : ℕ, HolderOnWith C γ (Z · ω) (⋃ N, (W N : Set T)) := by
  classical
  let gap : ℝ := q - (d + p * γ)
  have hgap : 0 < gap := sub_pos.mpr hγ
  let k : ℕ := ⌊3 * (d + 1) / gap⌋₊ + 1
  have hk_ne : k ≠ 0 := Nat.succ_ne_zero _
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk_ne)
  have hdk_lt : d * (k : ℝ)⁻¹ < gap / 3 := by
    have hgt : 3 * (d + 1) / gap < (k : ℝ) := by
      simpa [k] using Nat.lt_floor_add_one (3 * (d + 1) / gap)
    have h1 : 3 * (d + 1) < (k : ℝ) * gap := (div_lt_iff₀ hgap).mp hgt
    rw [← div_eq_mul_inv, div_lt_div_iff₀ hk_pos three_pos]
    linarith
  let δ₁ : ℝ := gap / 2
  let δ₂ : ℝ := gap / (3 * (1 + (k : ℝ)⁻¹))
  obtain ⟨C₁, -, hC₁⟩ := hW_card (show 0 < δ₁ by positivity)
  obtain ⟨C₂, hC₂_one, hC₂⟩ := hW_card (show 0 < δ₂ by positivity)
  have hcoe_r : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by
    rw [ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
  -- Parent edge bound via `ae_exists_finset_edist_le_mul_pow_rpow`.
  let Epar (n : ℕ) : Finset (T × T) := (W (n + 1)).image fun z ↦ (z, π n z)
  have h_ae_par : ∀ᵐ ω ∂P, ∃ Kpar : ℝ≥0, ∀ n, ∀ z ∈ W (n + 1),
      edist (Z z ω) (Z (π n z) ω) ≤ (Kpar : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ) := by
    have hcard_par (n : ℕ) :
        ((Epar n).card : ℝ≥0) ≤
          (C₁ * (2 : ℝ≥0) ^ (d + δ₁)) * ((2⁻¹ : ℝ≥0) ^ (-(d + δ₁))) ^ n := by
      have hinv2 : (2⁻¹ : ℝ≥0) ^ (-(d + δ₁)) = (2 : ℝ≥0) ^ (d + δ₁) := by
        rw [NNReal.inv_rpow, NNReal.rpow_neg, inv_inv]
      rw [hinv2]
      calc ((Epar n).card : ℝ≥0)
        _ ≤ ((W (n + 1)).card : ℝ≥0) := by exact_mod_cast Finset.card_image_le
        _ ≤ C₁ * ((2 : ℝ≥0) ^ (d + δ₁)) ^ (n + 1) := hC₁ (n + 1)
        _ = (C₁ * (2 : ℝ≥0) ^ (d + δ₁)) * ((2 : ℝ≥0) ^ (d + δ₁)) ^ n := by rw [pow_succ]; ring
    have hedge_par (n : ℕ) (e : T × T) (he : e ∈ Epar n) :
        edist e.1 e.2 ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp he
      simpa only [hcoe_r] using hπ_dist n z
    have hγ_par : (d + δ₁) + p * γ < q := by dsimp [δ₁, gap]; linarith
    filter_upwards [hZ.IsAEKolmogorovProcess.ae_exists_finset_edist_le_mul_pow_rpow
      (r := (2⁻¹ : ℝ≥0)) (by norm_num) (by norm_num) hcard_par hedge_par hγ_par] with ω ⟨Kpar, hK⟩
    refine ⟨Kpar, fun n z hz ↦ ?_⟩
    simpa only [hcoe_r] using hK n (z, π n z) (Finset.mem_image_of_mem _ hz)
  -- Spanner edge family at level `l` on `W (l + 3)` for relation `edist u v ≤ (2⁻¹)^l`.
  let Bspan (l : ℕ) : ℝ≥0 := C₂ * ((2 : ℝ≥0) ^ (d + δ₂)) ^ (l + 3)
  have hspan_ex (l : ℕ) := (W (l + 3)).exists_spanner_rpow
    (R := fun u v ↦ edist u v ≤ (2⁻¹ : ℝ≥0∞) ^ l)
    (fun _ _ h ↦ by rwa [edist_comm]) (hC₂ (l + 3)) hk_ne
  let Espan (l : ℕ) : Finset (T × T) := (hspan_ex l).choose
  have h_ae_span : ∀ᵐ ω ∂P, ∃ Kspan : ℝ≥0, ∀ l, ∀ e ∈ Espan l,
      edist (Z e.1 ω) (Z e.2 ω) ≤ (Kspan : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ l) ^ (γ : ℝ) := by
    let αk : ℝ := 1 + (k : ℝ)⁻¹
    let d_sp : ℝ := (d + δ₂) * αk
    have hαk_pos : 0 < αk := by positivity
    have hdδ₂_nonneg : 0 ≤ d + δ₂ := by positivity
    have hcard_sp (l : ℕ) :
        ((Espan l).card : ℝ≥0) ≤
          (2 * (C₂ * ((2 : ℝ≥0) ^ (d + δ₂)) ^ 3) ^ αk) * ((2⁻¹ : ℝ≥0) ^ (-d_sp)) ^ l := by
      have hB_one : 1 ≤ Bspan l :=
        one_le_mul_of_one_le_of_one_le hC₂_one
          (one_le_pow₀ (NNReal.one_le_rpow one_le_two hdδ₂_nonneg))
      have hinv2 : (2⁻¹ : ℝ≥0) ^ (-d_sp) = ((2 : ℝ≥0) ^ (d + δ₂)) ^ αk := by
        rw [NNReal.inv_rpow, NNReal.rpow_neg, inv_inv]
        dsimp [d_sp]
        rw [NNReal.rpow_mul]
      rw [hinv2]
      calc ((Espan l).card : ℝ≥0)
        _ ≤ 2 * (max 1 (Bspan l)) ^ αk := (hspan_ex l).choose_spec.2.1
        _ = 2 * (C₂ * (((2 : ℝ≥0) ^ (d + δ₂)) ^ 3 * ((2 : ℝ≥0) ^ (d + δ₂)) ^ l)) ^ αk := by
          rw [max_eq_right hB_one]
          dsimp [Bspan]
          rw [pow_add, mul_comm (((2 : ℝ≥0) ^ (d + δ₂)) ^ l)]
        _ = (2 * (C₂ * ((2 : ℝ≥0) ^ (d + δ₂)) ^ 3) ^ αk) *
            (((2 : ℝ≥0) ^ (d + δ₂)) ^ αk) ^ l := by
          rw [← mul_assoc C₂, NNReal.mul_rpow, mul_assoc 2,
            ← NNReal.rpow_natCast ((2 : ℝ≥0) ^ (d + δ₂)) l, ← NNReal.rpow_mul,
            mul_comm _ αk, NNReal.rpow_mul, NNReal.rpow_natCast]
    have hedge_sp (l : ℕ) (e : T × T) (he : e ∈ Espan l) :
        edist e.1 e.2 ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ l := by
      simpa only [hcoe_r] using ((hspan_ex l).choose_spec.1 e he).2.2
    have hγ_sp : d_sp + p * γ < q := by
      have hδ₂_mul : δ₂ * αk = gap / 3 := by
        dsimp [δ₂, αk]
        field_simp [hαk_pos.ne']
      have hd_sp_eq : d_sp = d + d * (k : ℝ)⁻¹ + δ₂ * αk := by dsimp [d_sp, αk]; ring
      linarith [hdk_lt, hδ₂_mul, hd_sp_eq]
    filter_upwards [hZ.IsAEKolmogorovProcess.ae_exists_finset_edist_le_mul_pow_rpow
      (r := (2⁻¹ : ℝ≥0)) (by norm_num) (by norm_num) hcard_sp hedge_sp hγ_sp] with ω ⟨Kspan, hK⟩
    refine ⟨Kspan, fun l e he ↦ ?_⟩
    simpa only [hcoe_r] using hK l e he
  -- Coarse pairs in `W 0 ×ˢ W 0` have finite increments almost surely because `ediam univ < ∞`.
  have h_ae_W0 : ∀ᵐ ω ∂P, ∃ K₀ : ℝ≥0, ∀ u ∈ W 0, ∀ v ∈ W 0, edist (Z u ω) (Z v ω) ≤ K₀ := by
    have hfin_pair (e : W 0 ×ˢ W 0) : ∀ᵐ ω ∂P, edist (Z e.1.1 ω) (Z e.1.2 ω) < ∞ := by
      have hdist_lt : edist e.1.1 e.1.2 < ∞ :=
        (edist_le_ediam_of_mem (mem_univ _) (mem_univ _)).trans_lt hdiam
      have hlint : ∫⁻ ω, edist (Z e.1.1 ω) (Z e.1.2 ω) ^ p ∂P ≠ ∞ :=
        ((hZ.kolmogorovCondition e.1.1 e.1.2).trans_lt
          (ENNReal.mul_lt_top ENNReal.coe_lt_top
            (ENNReal.rpow_lt_top_of_nonneg hZ.q_pos.le hdist_lt.ne))).ne
      filter_upwards [ae_lt_top (hZ.measurable_edist.pow_const p) hlint] with ω hω
      by_contra htop
      rw [top_unique (not_lt.mp htop), ENNReal.top_rpow_of_pos hZ.p_pos] at hω
      exact lt_irrefl ∞ hω
    filter_upwards [ae_all_iff.mpr hfin_pair] with ω hω
    refine ⟨(W 0 ×ˢ W 0).attach.sup fun e ↦ (edist (Z e.1.1 ω) (Z e.1.2 ω)).toNNReal,
      fun u hu v hv ↦ ?_⟩
    let e : {x // x ∈ W 0 ×ˢ W 0} := ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩⟩
    rw [← ENNReal.coe_toNNReal (hω e).ne, ENNReal.coe_le_coe]
    exact Finset.le_sup (f := fun e : {x // x ∈ W 0 ×ˢ W 0} ↦
      (edist (Z e.1.1 ω) (Z e.1.2 ω)).toNNReal) (Finset.mem_attach _ e)
  filter_upwards [h_ae_par, h_ae_span, h_ae_W0] with ω ⟨Kpar, hpar⟩ ⟨Kspan, hsp⟩ ⟨K₀, hK₀⟩
  obtain ⟨K, hK⟩ := holderOnWith_iUnion_of_edges hW_mono hπ_mem hπ_dist
    (fun l ↦ (hspan_ex l).choose_spec.2.2) hγ₀ hpar hsp hK₀
  exact ⟨⌈K⌉₊, hK.mono_const (Nat.le_ceil K)⟩

/-- Geometric Borel–Cantelli convergence along dyadic approximations `s n → t`: if
`edist t (s n) ≤ (2⁻¹)^n`, then `Z (s n) ω → Z t ω` almost everywhere. -/
private lemma ae_tendsto_of_edist_le_pow {T Ω E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : T → Ω → E}
    {p q : ℝ} {M : ℝ≥0} (hZ : IsKolmogorovProcess Z P p q M)
    {t : T} {s : ℕ → T} (hs : ∀ n, edist t (s n) ≤ (2⁻¹ : ℝ≥0∞) ^ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ Z (s n) ω) atTop (𝓝 (Z t ω)) := by
  let γ : ℝ := q / (2 * p)
  have hp : 0 < p := hZ.p_pos
  have hγ_pos : 0 < γ := div_pos hZ.q_pos (by positivity)
  have hγ_lt : 0 + p * γ < q := by
    dsimp [γ]
    have : p * (q / (2 * p)) = q / 2 := by field_simp [hp.ne']
    linarith [hZ.q_pos]
  have hcoe_r : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by
    rw [ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
  have hedge (n : ℕ) (_ : Fin 1) : edist (s n) t ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [hcoe_r, edist_comm]
    exact hs n
  have hcard (n : ℕ) : ((1 : ℕ) : ℝ≥0) ≤ 1 * ((2⁻¹ : ℝ≥0) ^ (-(0 : ℝ))) ^ n := by simp
  filter_upwards [hZ.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow
    (by norm_num) (by norm_num) hcard hedge hγ_lt] with ω ⟨K, hK⟩
  have ha_lt : ((2⁻¹ : ℝ≥0∞) ^ γ) < 1 := ENNReal.rpow_lt_one (by norm_num) hγ_pos
  have htend : Tendsto (fun n : ℕ ↦ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ γ) ^ n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ha_lt) (Or.inr ENNReal.coe_ne_top)
  have hd0 : Tendsto (fun n ↦ edist (Z (s n) ω) (Z t ω)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend (fun _ ↦ zero_le) fun n ↦ by
      simpa only [hcoe_r, ENNReal.pow_rpow_comm] using hK n 0
  exact EMetric.tendsto_nhds.mpr fun ε hε ↦ hd0.eventually (gt_mem_nhds hε)

/-- Every set `A` with finite covering exponent (`c ≠ ∞`, `0 ≤ d`) has a countable dense subset in
the subtype topology. -/
private lemma exists_countable_dense_of_hasCoveringExponent {T : Type*} [PseudoEMetricSpace T]
    {A : Set T} {c : ℝ≥0∞} {d : ℝ} (hcov : HasCoveringExponent A c d) (hc : c ≠ ∞) (hd : 0 ≤ d) :
    ∃ D : Set A, D.Countable ∧ Dense D := by
  obtain ⟨Wn, -, hWn_cov, -⟩ := exists_nested_dyadic_covers
    (hasCoveringExponent_univ_subtype_iff.mpr hcov) hc hd
  refine ⟨⋃ k, (Wn k : Set A), countable_iUnion fun k ↦ (Wn k).finite_toSet.countable, fun u ↦ ?_⟩
  refine EMetric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).eventually (gt_mem_nhds hε)).exists
  obtain ⟨v, hv, hvu⟩ := hWn_cov k (mem_univ u)
  change edist u v ≤ _ at hvu
  have hcoe : (((2⁻¹ : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ k := by
    rw [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
  rw [hcoe] at hvu
  exact ⟨v, mem_iUnion.mpr ⟨k, hv⟩, hvu.trans_lt hk⟩

end Helpers

section Global

variable {T Ω E : Type*} [PseudoEMetricSpace T] [EMetricSpace E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  {p q : ℝ} {M : ℝ≥0}

/-- **Kolmogorov–Chentsov theorem on spaces of bounded covering exponent.** If
`X : T → Ω → E` satisfies `IsAEKolmogorovProcess X P p q M` with values in a complete extended
metric space `E`, and `T` has covering exponent `d ≥ 0` with finite constant `c`, then for every
`γ > 0` with `d + p * γ < q` there exists a modification `Y` of `X` satisfying
`IsKolmogorovProcess Y P p q M` whose sample paths are *everywhere* `γ`-Hölder continuous. -/
theorem exists_modification_holderWith (hX : IsAEKolmogorovProcess X P p q M)
    {c : ℝ≥0∞} {d : ℝ} (hcov : HasCoveringExponent (univ : Set T) c d)
    (hc : c ≠ ∞) (hd : 0 ≤ d) {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, ∃ K : ℝ≥0, HolderWith K γ (Y · ω)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  classical
  -- Degenerate cases `IsEmpty T` or `IsEmpty Ω`.
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨X, ⟨fun s ↦ (hT.false s).elim, fun s ↦ (hT.false s).elim, hX.p_pos, hX.q_pos⟩,
      fun _ ↦ ⟨0, fun s ↦ (hT.false s).elim⟩, fun s ↦ (hT.false s).elim⟩
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · refine ⟨X, ⟨fun _ _ _ _ ↦ ?_, fun _ _ ↦ ?_, hX.p_pos, hX.q_pos⟩,
      fun ω ↦ (hΩ.false ω).elim, fun _ ↦ Filter.Eventually.of_forall fun ω ↦ (hΩ.false ω).elim⟩
    · convert MeasurableSet.empty
      ext ω
      exact (hΩ.false ω).elim
    · simp [Measure.eq_zero_of_isEmpty P]
  let Z : T → Ω → E := hX.mk X
  have hZ : IsKolmogorovProcess Z P p q M := hX.IsKolmogorovProcess_mk
  let x₀ : E := Z t₀ ω₀
  obtain ⟨W, hW_mono, hW_cov, hW_card⟩ := exists_nested_dyadic_covers hcov hc hd
  let π (n : ℕ) (x : T) : T :=
    if x ∈ W n then x else (hW_cov n (mem_univ x)).choose
  have hπ_mem (n : ℕ) (x : T) : π n x ∈ W n := by
    by_cases hx : x ∈ W n
    · simp [π, hx]
    · simpa [π, hx] using Finset.mem_coe.mp (hW_cov n (mem_univ x)).choose_spec.1
  have hπ_dist (n : ℕ) (x : T) : edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    by_cases hx : x ∈ W n
    · simp [π, hx]
    · have h : edist x (hW_cov n (mem_univ x)).choose ≤ (((2⁻¹ : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) :=
        (hW_cov n (mem_univ x)).choose_spec.2
      have hcoe : (((2⁻¹ : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
      simpa only [π, hx, ↓reduceIte] using h.trans_eq hcoe
  -- Measurable full-measure event `H` where `Z · ω` is `γ`-Hölder on `S = ⋃ N, W N`.
  let S : Set T := ⋃ N, (W N : Set T)
  have hSc : S.Countable := countable_iUnion fun N ↦ (W N).finite_toSet.countable
  have hSd : Dense S := fun t ↦ EMetric.mem_closure_iff.mpr fun ε hε ↦ by
    obtain ⟨n, hn⟩ := ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).eventually (gt_mem_nhds hε)).exists
    exact ⟨π n t, mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr (hπ_mem n t)⟩, (hπ_dist n t).trans_lt hn⟩
  let H : Set Ω := {ω | ∃ C : ℕ, HolderOnWith C γ (Z · ω) S}
  have hH_meas : MeasurableSet H := by
    have hH_eq : H = ⋃ C : ℕ, ⋂ s ∈ S, ⋂ t ∈ S,
        {ω | edist (Z s ω) (Z t ω) ≤ (C : ℝ≥0∞) * edist s t ^ (γ : ℝ)} := by
      ext ω; simp [H, HolderOnWith]
    rw [hH_eq]
    exact MeasurableSet.iUnion fun C ↦ MeasurableSet.biInter hSc fun s _ ↦
      MeasurableSet.biInter hSc fun t _ ↦ measurableSet_le hZ.measurable_edist measurable_const
  have hH_ae : ∀ᵐ ω ∂P, ω ∈ H :=
    ae_exists_holderOnWith_iUnion_covers hZ hcov.ediam_lt_top hd hW_mono hW_card hπ_mem hπ_dist
      hγ₀ hγ
  -- Extend `Z · ω` from `S` to `T` on `H`, and set `x₀` on `Hᶜ`.
  let extPath (ω : Ω) (hω : ω ∈ H) : T → E :=
    ((Nat.find_spec hω).extend_of_dense hSd).choose
  let Y (t : T) (ω : Ω) : E := if hω : ω ∈ H then extPath ω hω t else x₀
  have hY_holder (ω : Ω) : ∃ K : ℝ≥0, HolderWith K γ (Y · ω) := by
    by_cases hω : ω ∈ H
    · refine ⟨Nat.find hω, ?_⟩
      simpa only [Y, hω, ↓reduceDIte] using ((Nat.find_spec hω).extend_of_dense hSd).choose_spec.1
    · exact ⟨0, fun _ _ ↦ by simp [Y, hω]⟩
  have hY_eqOn {ω : Ω} (hω : ω ∈ H) {s : T} (hs : s ∈ S) : Y s ω = Z s ω := by
    simpa only [Y, hω, ↓reduceDIte] using
      (((Nat.find_spec hω).extend_of_dense hSd).choose_spec.2 hs).symm
  have hπ_tendsto (t : T) : Tendsto (fun n ↦ π n t) atTop (𝓝 t) :=
    EMetric.tendsto_nhds.mpr fun ε hε ↦
      ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).eventually
        (gt_mem_nhds hε)).mono fun n hn ↦ (edist_comm t (π n t) ▸ hπ_dist n t).trans_lt hn
  have hY_tendsto (t : T) (ω : Ω) : Tendsto (fun n ↦ Y (π n t) ω) atTop (𝓝 (Y t ω)) :=
    (((hY_holder ω).choose_spec.continuous hγ₀).tendsto t).comp (hπ_tendsto t)
  have hY_mod (t : T) : Y t =ᵐ[P] X t := by
    filter_upwards [hH_ae, ae_tendsto_of_edist_le_pow hZ (hπ_dist · t), hX.ae_eq_mk t]
      with ω hωH hZt hXZ
    have hZY : Tendsto (fun n ↦ Z (π n t) ω) atTop (𝓝 (Y t ω)) :=
      (hY_tendsto t ω).congr fun n ↦
        hY_eqOn hωH (mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr (hπ_mem n t)⟩)
    exact (tendsto_nhds_unique hZY hZt).trans hXZ.symm
  have hY_pair (s t : T) : Measurable[_, borel (E × E)] fun ω ↦ (Y s ω, Y t ω) := by
    borelize (E × E)
    refine measurable_of_tendsto_metrizable (f := fun n ω ↦ (Y (π n s) ω, Y (π n t) ω))
      (fun n ↦ ?_) (tendsto_pi_nhds.mpr fun ω ↦ (hY_tendsto s ω).prodMk_nhds (hY_tendsto t ω))
    have heq : (fun ω ↦ (Y (π n s) ω, Y (π n t) ω)) =
        H.piecewise (fun ω ↦ (Z (π n s) ω, Z (π n t) ω)) (fun _ ↦ (x₀, x₀)) := by
      funext ω
      by_cases hω : ω ∈ H
      · have hsS : π n s ∈ S := mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr (hπ_mem n s)⟩
        have htS : π n t ∈ S := mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr (hπ_mem n t)⟩
        simp [piecewise, hω, hY_eqOn hω hsS, hY_eqOn hω htS]
      · simp [piecewise, hω, Y]
    rw [heq]
    exact Measurable.piecewise hH_meas (hZ.measurablePair (π n s) (π n t)) measurable_const
  have hY_kol : IsKolmogorovProcess Y P p q M :=
    ⟨hY_pair, (hX.congr fun t ↦ (hY_mod t).symm).kolmogorovCondition, hX.p_pos, hX.q_pos⟩
  exact ⟨Y, hY_kol, hY_holder, hY_mod⟩

/-- Subset form of `exists_modification_holderWith` on `A : Set T` with covering exponent `(c, d)`.
Produces `Y : A → Ω → E` with `γ`-Hölder sample paths on the subtype `A`. -/
theorem exists_modification_holderOnWith_subtype (hX : IsAEKolmogorovProcess X P p q M)
    {A : Set T} {c : ℝ≥0∞} {d : ℝ} (hcov : HasCoveringExponent A c d)
    (hc : c ≠ ∞) (hd : 0 ≤ d) {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : A → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, ∃ K : ℝ≥0, HolderWith K γ (Y · ω)) ∧
      ∀ t : A, Y t =ᵐ[P] X t.1 := by
  let Z : T → Ω → E := hX.mk X
  have hZ : IsKolmogorovProcess Z P p q M := hX.IsKolmogorovProcess_mk
  have hZA : IsKolmogorovProcess (fun (t : A) ω ↦ Z t.1 ω) P p q M :=
    ⟨fun s t ↦ hZ.measurablePair s.1 t.1, fun s t ↦ hZ.kolmogorovCondition s.1 t.1,
      hZ.p_pos, hZ.q_pos⟩
  obtain ⟨Y, hY_kol, hY_hold, hY_mod⟩ := hZA.IsAEKolmogorovProcess.exists_modification_holderWith
    (hasCoveringExponent_univ_subtype_iff.mpr hcov) hc hd hγ₀ hγ
  exact ⟨Y, hY_kol, hY_hold, fun t ↦ (hY_mod t).trans (hX.ae_eq_mk t.1).symm⟩

/-- **Kolmogorov–Chentsov theorem along a monotone open exhaustion.** If `T` is covered by a
monotone sequence of open sets `U n` each having covering exponent `d ≥ 0` (with possibly growing
finite constants `c n`), then for every `γ > 0` with `d + p * γ < q` there exists a modification
`Y` of `X` satisfying `IsKolmogorovProcess Y P p q M` such that every sample path `Y · ω` is
globally continuous on `T` and `γ`-Hölder on each `U n`. -/
theorem exists_modification_holderOnWith_of_isOpen_cover (hX : IsAEKolmogorovProcess X P p q M)
    {U : ℕ → Set T} (hU_mono : Monotone U) (hU_open : ∀ n, IsOpen (U n))
    (hU_cov : ⋃ n, U n = univ) {c : ℕ → ℝ≥0∞} {d : ℝ} (hc : ∀ n, c n ≠ ∞) (hd : 0 ≤ d)
    (hcov : ∀ n, HasCoveringExponent (U n) (c n) d)
    {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : d + p * γ < q) :
    ∃ Y : T → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω n, ∃ K : ℝ≥0, HolderOnWith K γ (Y · ω) (U n)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  classical
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨X, ⟨fun s ↦ (hT.false s).elim, fun s ↦ (hT.false s).elim, hX.p_pos, hX.q_pos⟩,
      fun _ ↦ continuous_of_discreteTopology,
      fun _ _ ↦ ⟨0, fun s _ ↦ (hT.false s).elim⟩, fun s ↦ (hT.false s).elim⟩
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · refine ⟨X, ⟨fun _ _ _ _ ↦ ?_, fun _ _ ↦ ?_, hX.p_pos, hX.q_pos⟩,
      fun ω ↦ (hΩ.false ω).elim, fun ω ↦ (hΩ.false ω).elim,
      fun _ ↦ Filter.Eventually.of_forall fun ω ↦ (hΩ.false ω).elim⟩
    · convert MeasurableSet.empty
      ext ω
      exact (hΩ.false ω).elim
    · simp [Measure.eq_zero_of_isEmpty P]
  let Z : T → Ω → E := hX.mk X
  let x₀ : E := Z t₀ ω₀
  have hloc (n : ℕ) :=
    hX.exists_modification_holderOnWith_subtype (hcov n) (hc n) hd hγ₀ hγ
  let W (n : ℕ) : U n → Ω → E := (hloc n).choose
  have hW_kol (n : ℕ) : IsKolmogorovProcess (W n) P p q M := (hloc n).choose_spec.1
  have hW_hold (n : ℕ) (ω : Ω) : ∃ K : ℝ≥0, HolderWith K γ (W n · ω) := (hloc n).choose_spec.2.1 ω
  have hW_mod (n : ℕ) (u : U n) : W n u =ᵐ[P] X u.1 := (hloc n).choose_spec.2.2 u
  have hD_ex (n : ℕ) := exists_countable_dense_of_hasCoveringExponent (hcov n) (hc n) hd
  let D (n : ℕ) : Set (U n) := (hD_ex n).choose
  have _hDc (n : ℕ) : Countable (D n) := (hD_ex n).choose_spec.1.to_subtype
  have hDd (n : ℕ) : Dense (D n) := (hD_ex n).choose_spec.2
  -- Null set `N` where two stages `n ≤ m` disagree on `D n`, enlarged to a measurable null set `B`.
  let N : Set Ω :=
    {ω | ¬ ∀ (n m : ℕ) (hnm : n ≤ m) (d : D n),
      W n d.1 ω = W m ⟨d.1.1, hU_mono hnm d.1.2⟩ ω}
  have hPN : P N = 0 := by
    apply ae_iff.mp
    have hae : ∀ᵐ ω ∂P, ∀ (n m : ℕ) (hnm : n ≤ m) (d : D n),
        W n d.1 ω = W m ⟨d.1.1, hU_mono hnm d.1.2⟩ ω :=
      ae_all_iff.mpr fun n ↦ ae_all_iff.mpr fun m ↦ ae_all_iff.mpr fun hnm ↦
        ae_all_iff.mpr fun d ↦ (hW_mod n d.1).trans (hW_mod m ⟨d.1.1, hU_mono hnm d.1.2⟩).symm
    filter_upwards [hae] with ω hω
    simpa [N] using hω
  let B : Set Ω := toMeasurable P N
  have hB_meas : MeasurableSet B := measurableSet_toMeasurable P N
  have hPB : P B = 0 := (measure_toMeasurable N).trans hPN
  have hW_agree {ω : Ω} (hω : ω ∉ B) {n m : ℕ} (hnm : n ≤ m) (u : U n) :
      W n u ω = W m ⟨u.1, hU_mono hnm u.2⟩ ω := by
    have hωN : ∀ (n m : ℕ) (hnm : n ≤ m) (d : D n),
        W n d.1 ω = W m ⟨d.1.1, hU_mono hnm d.1.2⟩ ω :=
      of_not_not fun h ↦ hω (subset_toMeasurable P N h)
    have hc1 : Continuous (W n · ω) := (hW_hold n ω).choose_spec.continuous hγ₀
    have hc2 : Continuous fun v : U n ↦ W m ⟨v.1, hU_mono hnm v.2⟩ ω :=
      ((hW_hold m ω).choose_spec.continuous hγ₀).comp (continuous_inclusion (hU_mono hnm))
    exact congrFun (Continuous.ext_on (hDd n) hc1 hc2 fun v hv ↦ hωN n m hnm ⟨v, hv⟩) u
  have hex_idx (t : T) : ∃ n, t ∈ U n := mem_iUnion.mp (hU_cov ▸ mem_univ t)
  let idx (t : T) : ℕ := Nat.find (hex_idx t)
  have hidx (t : T) : t ∈ U (idx t) := Nat.find_spec (hex_idx t)
  let Y (t : T) (ω : Ω) : E := B.piecewise (fun _ ↦ x₀) (W (idx t) ⟨t, hidx t⟩) ω
  have hY_on {ω : Ω} (hω : ω ∉ B) {n : ℕ} {t : T} (ht : t ∈ U n) :
      Y t ω = W n ⟨t, ht⟩ ω := by
    have hle : idx t ≤ n := Nat.find_le ht
    simpa only [Y, piecewise, hω, ↓reduceIte] using hW_agree hω hle ⟨t, hidx t⟩
  have hY_hold_Un (ω : Ω) (n : ℕ) : ∃ K : ℝ≥0, HolderOnWith K γ (Y · ω) (U n) := by
    by_cases hω : ω ∈ B
    · refine ⟨0, fun s _ t _ ↦ ?_⟩
      simp [Y, piecewise, hω]
    · obtain ⟨K, hK⟩ := hW_hold n ω
      refine ⟨K, fun s hs t ht ↦ ?_⟩
      dsimp only
      rw [hY_on hω hs, hY_on hω ht]
      exact hK ⟨s, hs⟩ ⟨t, ht⟩
  have hY_cont (ω : Ω) : Continuous (Y · ω) := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨K, hK⟩ := hY_hold_Un ω (idx t)
    exact (hK.continuousOn hγ₀).continuousAt ((hU_open (idx t)).mem_nhds (hidx t))
  have hY_mod (t : T) : Y t =ᵐ[P] X t := by
    have hBae : ∀ᵐ ω ∂P, ω ∉ B := measure_mono_null (fun _ h ↦ of_not_not h) hPB
    filter_upwards [hBae, hW_mod (idx t) ⟨t, hidx t⟩] with ω hω hWω
    exact (hY_on hω (hidx t)).trans hWω
  have hY_pair (s t : T) : Measurable[_, borel (E × E)] fun ω ↦ (Y s ω, Y t ω) := by
    borelize (E × E)
    let m := max (idx s) (idx t)
    have hs : s ∈ U m := hU_mono (le_max_left _ _) (hidx s)
    have ht : t ∈ U m := hU_mono (le_max_right _ _) (hidx t)
    have heq : (fun ω ↦ (Y s ω, Y t ω)) =
        B.piecewise (fun _ ↦ (x₀, x₀)) (fun ω ↦ (W m ⟨s, hs⟩ ω, W m ⟨t, ht⟩ ω)) := by
      funext ω
      by_cases hω : ω ∈ B
      · simp [Y, piecewise, hω]
      · simp [piecewise, hω, hY_on hω hs, hY_on hω ht]
    rw [heq]
    exact Measurable.piecewise hB_meas measurable_const ((hW_kol m).measurablePair ⟨s, hs⟩ ⟨t, ht⟩)
  have hY_kol : IsKolmogorovProcess Y P p q M :=
    ⟨hY_pair, (hX.congr fun t ↦ (hY_mod t).symm).kolmogorovCondition, hX.p_pos, hX.q_pos⟩
  exact ⟨Y, hY_kol, hY_cont, hY_hold_Un, hY_mod⟩

/-- **Kolmogorov–Chentsov theorem on `ℝ≥0`.** For any `X : ℝ≥0 → Ω → E` satisfying
`IsAEKolmogorovProcess X P p q M` and any `γ > 0` with `1 + p * γ < q`, there exists a modification
`Y` of `X` satisfying `IsKolmogorovProcess Y P p q M` whose sample paths are everywhere continuous
on `ℝ≥0` and `γ`-Hölder on every compact interval `[0, R]`. -/
theorem exists_modification_holderOnWith_Icc_nnreal {X : ℝ≥0 → Ω → E}
    (hX : IsAEKolmogorovProcess X P p q M) {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : 1 + p * γ < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω (R : ℝ≥0), ∃ K : ℝ≥0, HolderOnWith K γ (Y · ω) (Icc 0 R)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  let U (n : ℕ) : Set ℝ≥0 := Iio ((n : ℝ≥0) + 1)
  have hU_mono : Monotone U := fun m n hmn x hx ↦
    lt_of_lt_of_le hx (add_le_add_left (Nat.cast_le.mpr hmn) 1)
  have hU_cov : ⋃ n, U n = univ := eq_univ_of_forall fun t ↦
    mem_iUnion.mpr ⟨⌊t⌋₊, Nat.lt_floor_add_one t⟩
  obtain ⟨Y, hY_kol, hY_cont, hY_hold, hY_mod⟩ :=
    hX.exists_modification_holderOnWith_of_isOpen_cover hU_mono (fun _ ↦ isOpen_Iio) hU_cov
      (fun n ↦ ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) zero_le_one
      (fun n ↦ TauCeti.hasCoveringExponent_Iio_nnreal ((n : ℝ≥0) + 1)) hγ₀ hγ
  refine ⟨Y, hY_kol, hY_cont, fun ω R ↦ ?_, hY_mod⟩
  obtain ⟨K, hK⟩ := hY_hold ω ⌊R⌋₊
  refine ⟨K, hK.mono fun t ht ↦ ?_⟩
  exact lt_of_le_of_lt ht.2 (Nat.lt_floor_add_one R)

/-- On `ℝ≥0`, every process `X : ℝ≥0 → Ω → E` satisfying `IsAEKolmogorovProcess X P p q M` with
`1 < q` admits a modification with everywhere continuous sample paths. -/
theorem exists_modification_continuous_nnreal {X : ℝ≥0 → Ω → E}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  have hp : 0 < p := hX.p_pos
  let γ : ℝ≥0 := ((q - 1) / (2 * p)).toNNReal
  have hγ_real : (γ : ℝ) = (q - 1) / (2 * p) :=
    Real.coe_toNNReal _ (div_nonneg (sub_nonneg.mpr hq.le) (by positivity))
  have hγ₀ : 0 < γ := NNReal.coe_pos.mp (hγ_real ▸ div_pos (sub_pos.mpr hq) (by positivity))
  have hγ : 1 + p * γ < q := by
    rw [hγ_real]
    have : p * ((q - 1) / (2 * p)) = (q - 1) / 2 := by field_simp [hp.ne']
    linarith
  obtain ⟨Y, hY_kol, hY_cont, -, hY_mod⟩ := hX.exists_modification_holderOnWith_Icc_nnreal hγ₀ hγ
  exact ⟨Y, hY_kol, hY_cont, hY_mod⟩

/-- On `ℝ`, every process `X : ℝ → Ω → E` satisfying `IsAEKolmogorovProcess X P p q M` with
`1 < q` admits a modification with everywhere continuous sample paths. -/
theorem exists_modification_continuous_real {X : ℝ → Ω → E}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ → Ω → E,
      IsKolmogorovProcess Y P p q M ∧
      (∀ ω, Continuous (Y · ω)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  have hp : 0 < p := hX.p_pos
  let γ : ℝ≥0 := ((q - 1) / (2 * p)).toNNReal
  have hγ_real : (γ : ℝ) = (q - 1) / (2 * p) :=
    Real.coe_toNNReal _ (div_nonneg (sub_nonneg.mpr hq.le) (by positivity))
  have hγ₀ : 0 < γ := NNReal.coe_pos.mp (hγ_real ▸ div_pos (sub_pos.mpr hq) (by positivity))
  have hγ : 1 + p * γ < q := by
    rw [hγ_real]
    have : p * ((q - 1) / (2 * p)) = (q - 1) / 2 := by field_simp [hp.ne']
    linarith
  let U (n : ℕ) : Set ℝ := Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1)
  have hU_mono : Monotone U := fun m n hmn x hx ↦
    ⟨by linarith [hx.1, (Nat.cast_le.mpr hmn : (m : ℝ) ≤ n)],
      by linarith [hx.2, (Nat.cast_le.mpr hmn : (m : ℝ) ≤ n)]⟩
  have hU_cov : ⋃ n, U n = univ := eq_univ_of_forall fun t ↦ by
    refine mem_iUnion.mpr ⟨⌈|t|⌉₊, ?_⟩
    have habs : |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil |t|
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hcov (n : ℕ) : HasCoveringExponent (U n)
      (2 ^ (1 : ℝ) * max 1 (2 * ENNReal.ofReal (((n : ℝ) + 1) - (-(n : ℝ) - 1)))) 1 :=
    (TauCeti.hasCoveringExponent_Icc_real (by linarith : -(n : ℝ) - 1 ≤ (n : ℝ) + 1)).subset
      Ioo_subset_Icc_self zero_le_one
  have hc (n : ℕ) :
      (2 : ℝ≥0∞) ^ (1 : ℝ) * max 1 (2 * ENNReal.ofReal (((n : ℝ) + 1) - (-(n : ℝ) - 1))) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (max_lt_iff.mpr
      ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top⟩).ne
  obtain ⟨Y, hY_kol, hY_cont, -, hY_mod⟩ :=
    hX.exists_modification_holderOnWith_of_isOpen_cover hU_mono (fun _ ↦ isOpen_Ioo) hU_cov
      hc zero_le_one hcov hγ₀ hγ
  exact ⟨Y, hY_kol, hY_cont, hY_mod⟩

end Global

end ProbabilityTheory.IsAEKolmogorovProcess
