/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.Order.Compact
import TauCeti.Topology.MetricSpace.SeparatedBalls
import TauCeti.Topology.Sequences

/-!
# Finitely many energy concentration points

Let `e k ≥ 0` be a sequence of densities on a set `Ω` of a metric space, with total energy
`∫_Ω e k ≤ E`. A point `z` is an *energy concentration point* of threshold `δ > 0` along the
sequence when every ball about `z` eventually carries energy at least `δ`:
for every `ε > 0`, eventually `δ ≤ ∫_{B_ε(z) ∩ Ω} e k`. Balls about distinct points are disjoint
once they are small, so a finite set `Z` of such points satisfies `#Z * δ ≤ E`
(`TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`). If instead the densities
`1 + e k` concentrate energy `δ` at a null point `z`, then the `e k` concentrate energy `δ'` there
for every `δ' < δ`, since small balls about `z` have small measure
(`TauCeti.eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball`).

Now let `g k` be continuous functions on `Ω`, for instance the norms of the differentials of
maps `u k` whose energy densities are `e k`. Suppose that energy concentrates wherever the `g k`
blow up: whenever `g (φ n) (z n) → ∞` along a subsequence `φ` at points `z n → z₀ ∈ Ω`, the
point `z₀` is an energy concentration point of threshold `δ` along `φ`. Then, after passing to a
subsequence, the `g k` are uniformly bounded on every compact subset of `Ω` off a finite set `Z`
of energy concentration points, so `#Z * δ ≤ E`
(`TauCeti.exists_strictMono_finset_forall_le_of_concentration`).

The proof adds blow-up points one at a time. If the `g k` are not bounded on a compact set `C`
off the current set `Z`, then, since each single `g k` is bounded on `C`, they blow up along a
subsequence at points of `C` converging to a point of `C`
(`IsCompact.exists_strictMono_tendsto_atTop`), which is a new concentration point. Every step
raises `#Z` by one, and `#Z * δ ≤ E` stops the process.

This is the counting step of the bubbling analysis in Gromov compactness: for `J`-holomorphic
curves, the mean-value inequality supplies the energy concentration hypothesis, and the points of
`Z` are the concentration points at which further bubbling analysis is required.

Conversely, energy concentration forces blow-up, with no equation involved. A ball of measure
below `δ / c` carrying energy at least `δ` contains a point where the density exceeds `c`
(`TauCeti.exists_lt_of_measure_lt_of_le_setIntegral`), so if energy `δ > 0` concentrates at a
null point `z`, then along a subsequence there are points `y k → z` at which the densities tend
to infinity
(`TauCeti.exists_strictMono_tendsto_atTop_of_forall_eventually_le_setIntegral_ball`). The same
holds for functions `g k` controlling the densities, such as the norms `‖du_k‖` of the
differentials of maps with energy densities `‖∂ₛu_k‖²`. These blow-up sequences are the input
of the rescaling that produces a bubble at `z`. Consequently, when the `g k` are bounded on
compact sets off a finite set `Z` of concentration points, `Z` is exactly the set of points near
which the `g k` are unbounded (`TauCeti.coe_eq_setOf_forall_exists_lt_of_concentration`).

## Main results

* `TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`: a finite set of energy
  concentration points of threshold `δ` has at most `E / δ` elements.
* `TauCeti.eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball`: removing the
  measure of small balls from concentrating energy loses arbitrarily little of it.
* `TauCeti.exists_strictMono_finset_forall_le_of_concentration`: when energy concentrates at
  blow-up points, a subsequence is bounded on compact sets off finitely many concentration points.
* `TauCeti.exists_lt_of_measure_lt_of_le_setIntegral`: a set of measure below `δ / c` carrying
  energy at least `δ` contains a point where the density exceeds `c`.
* `TauCeti.exists_strictMono_tendsto_atTop_of_forall_eventually_le_setIntegral_ball`: energy
  concentration at a null point gives a subsequence blowing up at points converging to it.
* `TauCeti.coe_eq_setOf_forall_exists_lt_of_concentration`: a finite set of concentration
  points off which the sequence is locally bounded is its set of blow-up points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.6 (the finite set of points at which the
  derivatives of a sequence of curves with bounded energy blow up).
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {Ω : Set X} {δ E : ℝ}

/-- The balls about a point `z`, one of which has finite measure, have measures tending to the
measure of `{z}` as the radius decreases to `0`. -/
theorem tendsto_measure_ball_nhdsGT_zero {z : X} (hfin : ∃ R > 0, μ (ball z R) ≠ ⊤) :
    Tendsto (fun r ↦ μ (ball z r)) (𝓝[>] 0) (𝓝 (μ {z})) := by
  simpa [thickening_singleton] using
    tendsto_measure_thickening (μ := μ) (s := {z}) (by simpa [thickening_singleton] using hfin)

/-- **Large energy on a small set forces a large density.** If a set `S` of measure less than
`δ / c`, with `c > 0`, carries energy `∫_S f ≥ δ`, then `f` exceeds `c` at some point of `S`. No
integrability, measurability or sign condition on `f` is needed. -/
theorem exists_lt_of_measure_lt_of_le_setIntegral {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {f : α → ℝ} {S : Set α} {c : ℝ} (hc : 0 < c)
    (hS : ν S < ENNReal.ofReal (δ / c)) (hδS : δ ≤ ∫ y in S, f y ∂ν) : ∃ y ∈ S, c < f y := by
  have hδ : 0 < δ := (div_pos_iff_of_pos_right hc).1 (ENNReal.ofReal_pos.1 (pos_of_gt hS))
  have hint : IntegrableOn f S ν := by
    by_contra h
    rw [integral_undef h] at hδS
    linarith
  have hν0 : ν S ≠ 0 := fun h ↦ by
    rw [setIntegral_measure_zero _ h] at hδS
    linarith
  have hνS : ν S ≠ ⊤ := (hS.trans ENNReal.ofReal_lt_top).ne
  obtain ⟨y, hy, hle⟩ := exists_setAverage_le hν0 hνS hint
  have hpos : 0 < ν.real S := ENNReal.toReal_pos hν0 hνS
  have hlt : ν.real S * c < δ := by
    rw [← lt_div_iff₀ hc]
    exact ENNReal.toReal_lt_of_lt_ofReal hS
  rw [setAverage_eq, smul_eq_mul, inv_mul_eq_div] at hle
  refine ⟨y, hy, lt_of_lt_of_le ?_ hle⟩
  rw [lt_div_iff₀ hpos]
  linarith

/-- **Counting energy concentration points.** Let `e i ≥ 0` be densities on a measurable set `Ω`
with `∫_Ω e i ≤ E`, and let `Z` be a finite set of points at which energy at least `δ`
concentrates: for every `z ∈ Z` and `ε > 0`, eventually `δ ≤ ∫_{B_ε(z) ∩ Ω} e i`. Then
`#Z * δ ≤ E`. -/
theorem card_mul_le_of_forall_eventually_le_setIntegral_ball {ι : Type*} {l : Filter ι}
    [l.NeBot] {e : ι → X → ℝ} (hΩ : MeasurableSet Ω) (he : ∀ i, ∀ y ∈ Ω, 0 ≤ e i y)
    (hint : ∀ i, IntegrableOn (e i) Ω μ) (hE : ∀ i, ∫ y in Ω, e i y ∂μ ≤ E) {Z : Finset X}
    (hZ : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ y in ball z ε ∩ Ω, e i y ∂μ) :
    Z.card * δ ≤ E := by
  -- Choose a radius `ε` for which the balls about the points of `Z` are pairwise disjoint.
  obtain ⟨ε, hε, -, hsep⟩ :=
    exists_pos_closedBall_subset_and_lt_dist (T := Z) (U := fun _ ↦ univ) fun _ _ ↦ univ_mem
  obtain ⟨i, hi⟩ := ((eventually_all_finset Z).2 fun z hz ↦ hZ z hz ε hε).exists
  have hdisj : (Z : Set X).Pairwise (Disjoint on fun z ↦ ball z ε ∩ Ω) :=
    fun z hz z' hz' hne ↦ (ball_disjoint_ball (by linarith [hsep z hz z' hz' hne])).mono
      inter_subset_left inter_subset_left
  calc Z.card * δ = ∑ z ∈ Z, δ := by simp
    _ ≤ ∑ z ∈ Z, ∫ y in ball z ε ∩ Ω, e i y ∂μ := Finset.sum_le_sum hi
    _ = ∫ y in ⋃ z ∈ Z, ball z ε ∩ Ω, e i y ∂μ :=
      (integral_biUnion_finset Z (fun _ _ ↦ measurableSet_ball.inter hΩ) hdisj
        fun _ _ ↦ (hint i).mono_set inter_subset_right).symm
    _ ≤ ∫ y in Ω, e i y ∂μ :=
      setIntegral_mono_set (hint i) (ae_restrict_of_forall_mem hΩ (he i))
        (iUnion₂_subset fun _ _ ↦ inter_subset_right).eventuallyLE
    _ ≤ E := hE i

/-- **Concentration without the area term.** Let `e i ≥ 0` be integrable densities on a measurable
set `Ω`, and let `z` be a point of measure zero about which some ball has finite measure. If for
every `ρ > 0` eventually `δ ≤ μ(B_ρ(z) ∩ Ω) + ∫_{B_ρ(z) ∩ Ω} e i`, then for every `δ' < δ` and
`ε > 0` eventually `δ' ≤ ∫_{B_ε(z) ∩ Ω} e i`: the balls about `z` shrink to a null set, so a small
one has measure below `δ - δ'`. -/
theorem eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball {ι : Type*}
    {l : Filter ι} {e : ι → X → ℝ} {z : X} {δ' ε : ℝ} (hΩ : MeasurableSet Ω) (hz : μ {z} = 0)
    (hfin : ∃ R > 0, μ (ball z R) ≠ ⊤) (he : ∀ i, ∀ y ∈ Ω, 0 ≤ e i y)
    (hint : ∀ i, IntegrableOn (e i) Ω μ) (hδ' : δ' < δ) (hε : 0 < ε)
    (hconc : ∀ ρ > 0, ∀ᶠ i in l, δ ≤ μ.real (ball z ρ ∩ Ω) + ∫ y in ball z ρ ∩ Ω, e i y ∂μ) :
    ∀ᶠ i in l, δ' ≤ ∫ y in ball z ε ∩ Ω, e i y ∂μ := by
  have hlim : Tendsto (fun r ↦ μ (ball z r)) (𝓝[>] 0) (𝓝 0) := by
    simpa [hz] using tendsto_measure_ball_nhdsGT_zero hfin
  obtain ⟨ρ, hρμ, hρ⟩ := ((hlim.eventually (gt_mem_nhds
    (ENNReal.ofReal_pos.2 (sub_pos.2 hδ')))).and (Ioo_mem_nhdsGT hε)).exists
  have hρvol : μ.real (ball z ρ ∩ Ω) < δ - δ' :=
    (measureReal_mono inter_subset_left (hρμ.trans ENNReal.ofReal_lt_top).ne).trans_lt
      (ENNReal.toReal_lt_of_lt_ofReal hρμ)
  filter_upwards [hconc ρ hρ.1] with i hi
  calc δ' ≤ ∫ y in ball z ρ ∩ Ω, e i y ∂μ := by linarith
    _ ≤ ∫ y in ball z ε ∩ Ω, e i y ∂μ :=
      setIntegral_mono_set ((hint i).mono_set inter_subset_right)
        (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ) fun y hy ↦ he i y hy.2)
        (inter_subset_inter_left _ (ball_subset_ball hρ.2.le)).eventuallyLE

/-- **Finitely many blow-up points.** Let `g k` be functions continuous on a measurable set `Ω`,
and let `e k ≥ 0` be densities on `Ω` with `∫_Ω e k ≤ E`. Suppose that energy at least `δ > 0`
concentrates wherever the `g k` blow up: whenever `g (φ n) (z n) → ∞` along a subsequence `φ` at
points `z n ∈ Ω` converging to `z₀ ∈ Ω`, eventually `δ ≤ ∫_{B_ε(z₀) ∩ Ω} e (φ n)` for every
`ε > 0`. Then there are a subsequence `φ` and a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` such that
energy at least `δ` concentrates along `φ` at every point of `Z`, and the `g (φ n)` are uniformly
bounded above on every compact subset of `Ω \ Z`. -/
theorem exists_strictMono_finset_forall_le_of_concentration {g e : ℕ → X → ℝ}
    (hΩ : MeasurableSet Ω) (hδ : 0 < δ) (hg : ∀ k, ContinuousOn (g k) Ω)
    (he : ∀ k, ∀ y ∈ Ω, 0 ≤ e k y) (hint : ∀ k, IntegrableOn (e k) Ω μ)
    (hE : ∀ k, ∫ y in Ω, e k y ∂μ ≤ E)
    (hconc : ∀ ⦃φ : ℕ → ℕ⦄, StrictMono φ → ∀ ⦃z : ℕ → X⦄ ⦃z₀ : X⦄, (∀ n, z n ∈ Ω) → z₀ ∈ Ω →
      Tendsto z atTop (𝓝 z₀) → Tendsto (fun n ↦ g (φ n) (z n)) atTop atTop →
      ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z₀ ε ∩ Ω, e (φ n) y ∂μ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset X, ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, e (φ n) y ∂μ) ∧
      ∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C, g (φ n) y ≤ M := by
  classical
  -- `P φ Z`: `φ` is a subsequence along which energy at least `δ` concentrates at every point of
  -- the subset `Z` of `Ω`.
  set P : (ℕ → ℕ) → Finset X → Prop := fun φ Z ↦ StrictMono φ ∧ ↑Z ⊆ Ω ∧
    ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, e (φ n) y ∂μ
  have hcard : ∀ φ Z, P φ Z → Z.card * δ ≤ E := fun φ Z h ↦
    card_mul_le_of_forall_eventually_le_setIntegral_ball (l := atTop) hΩ (fun k ↦ he (φ k))
      (fun k ↦ hint (φ k)) (fun k ↦ hE (φ k)) h.2.2
  suffices ∃ φ Z, P φ Z ∧ ∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C, g (φ n) y ≤ M by
    obtain ⟨φ, Z, hPZ, hb⟩ := this
    exact ⟨φ, hPZ.1, Z, hPZ.2.1, hcard φ Z hPZ, hPZ.2.2, hb⟩
  by_contra! hne
  -- If the conclusion fails for `(φ, Z)`, a blow-up point off `Z` extends `Z` by one point.
  have hstep : ∀ φ Z, P φ Z → ∃ ψ : ℕ → ℕ, ∃ z₀ ∉ Z, P (φ ∘ ψ) (insert z₀ Z) := by
    intro φ Z hPZ
    obtain ⟨C, hC, hCZ, hunb⟩ := hne φ Z hPZ
    obtain ⟨ψ, hψ, z, hzC, z₀, hz₀C, hz, hblow⟩ :=
      hC.exists_strictMono_tendsto_atTop (g := fun k ↦ g (φ k))
        (fun k ↦ hC.bddAbove_image ((hg (φ k)).mono (hCZ.trans sdiff_subset))) hunb
    have hz₀ := hCZ hz₀C
    refine ⟨ψ, z₀, hz₀.2, hPZ.1.comp hψ, ?_, fun w hw ε hε ↦ ?_⟩
    · rw [Finset.coe_insert]
      exact insert_subset hz₀.1 hPZ.2.1
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hconc (hPZ.1.comp hψ) (fun n ↦ (hCZ (hzC n)).1) hz₀.1 hz hblow ε hε
      · exact hψ.tendsto_atTop.eventually (hPZ.2.2 w hw ε hε)
  -- Iterating, there would be concentration sets of every cardinality.
  have hall : ∀ N : ℕ, ∃ φ Z, P φ Z ∧ Z.card = N := by
    intro N
    induction N with
    | zero => exact ⟨id, ∅, ⟨strictMono_id, by simp, by simp⟩, rfl⟩
    | succ N ih =>
      obtain ⟨φ, Z, hPZ, rfl⟩ := ih
      obtain ⟨ψ, z₀, hz₀, hP'⟩ := hstep φ Z hPZ
      exact ⟨φ ∘ ψ, insert z₀ Z, hP', Finset.card_insert_of_notMem hz₀⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (E / δ)
  obtain ⟨φ, Z, hPZ, hcardZ⟩ := hall N
  have h := hcard φ Z hPZ
  rw [hcardZ] at h
  rw [div_lt_iff₀ hδ] at hN
  linarith

/-- **Energy concentration forces blow-up.** Let `z` be a point of measure zero about which some
ball has finite measure, and suppose that energy at least `δ > 0` of the densities `e n`
concentrates at `z`: for every `ε > 0`, eventually `δ ≤ ∫_{B_ε(z) ∩ Ω} e n`. Let `g n` be functions
on `Ω` that control the densities, in the sense that `e n` is bounded above wherever `g n` is,
uniformly in `n`. Then the `g n` blow up at `z`: along a subsequence `φ` there are points
`y k ∈ Ω` with `y k → z` and `g (φ k) (y k) → ∞`. For `g = e` the control hypothesis holds
trivially, and for the energy densities `e n = ‖∂ₛuₙ‖²` of maps `uₙ` it holds with `g n = ‖duₙ‖`.

No integrability, nonnegativity or continuity is assumed: a small ball carrying energy at least
`δ` must contain a point where the density is at least `δ` divided by the measure of the ball. -/
theorem exists_strictMono_tendsto_atTop_of_forall_eventually_le_setIntegral_ball
    {g e : ℕ → X → ℝ} {z : X} (hδ : 0 < δ) (hz : μ {z} = 0) (hfin : ∃ R > 0, μ (ball z R) ≠ ⊤)
    (hge : ∀ M, ∃ M', ∀ n, ∀ y ∈ Ω, g n y ≤ M → e n y ≤ M')
    (hconc : ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, e n y ∂μ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → X, (∀ k, y k ∈ Ω) ∧ Tendsto y atTop (𝓝 z) ∧
      Tendsto (fun k ↦ g (φ k) (y k)) atTop atTop := by
  have hlim : Tendsto (fun r ↦ μ (ball z r)) (𝓝[>] 0) (𝓝 0) := by
    simpa [hz] using tendsto_measure_ball_nhdsGT_zero hfin
  -- For each `k`, the density bound `M k` matching the control bound `k`, and a radius
  -- `ε k < 1 / (k + 1)` whose ball has measure below `δ / (|M k| + 1)`.
  choose M hM using fun k : ℕ ↦ hge k
  have hc : ∀ k, 0 < |M k| + 1 := fun k ↦ by positivity
  choose ε hεμ hε using fun k : ℕ ↦ ((hlim.eventually (gt_mem_nhds
    (ENNReal.ofReal_pos.2 (div_pos hδ (hc k))))).and (Ioo_mem_nhdsGT (Nat.one_div_pos_of_nat
      (n := k)))).exists
  -- Eventually the ball of radius `ε k` contains a point where `g n` exceeds `k`.
  have hev : ∀ k, ∀ᶠ n in atTop, ∃ y ∈ ball z (ε k) ∩ Ω, (k : ℝ) < g n y := fun k ↦ by
    filter_upwards [hconc (ε k) (hε k).1] with n hn
    obtain ⟨y, hy, hlt⟩ := exists_lt_of_measure_lt_of_le_setIntegral (hc k)
      ((measure_mono inter_subset_left).trans_lt (hεμ k)) hn
    refine ⟨y, hy, lt_of_not_ge fun hgy ↦ ?_⟩
    linarith [hM k n y hy.2 hgy, le_abs_self (M k)]
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually hev
  choose y hy hgy using hφP
  refine ⟨φ, hφ, y, fun k ↦ (hy k).2, ?_,
    tendsto_atTop_mono (fun k ↦ (hgy k).le) tendsto_natCast_atTop_atTop⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ((mem_ball.1 (hy k).1).trans (hε k).2).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Concentration points are exactly the blow-up points.** Let `Ω` be open in a locally compact
space and `Z ⊆ Ω` a finite set of points of measure zero, each with a ball of finite measure. Let
the densities `e n` concentrate energy at least `δ > 0` at every point of `Z`, and let the `g n`
be uniformly bounded above on every compact subset of `Ω \ Z` and control the `e n`, in the sense
that `e n` is bounded above wherever `g n` is, uniformly in `n`. Then `Z` is exactly the set of
points of `Ω` near which the `g n` are not uniformly bounded above. So when the functions of
`TauCeti.exists_strictMono_finset_forall_le_of_concentration` control its densities and its
points have measure zero with balls of finite measure, the finite set it produces is determined
by the subsequence it comes with. -/
theorem coe_eq_setOf_forall_exists_lt_of_concentration [LocallyCompactSpace X]
    {g e : ℕ → X → ℝ} {Z : Finset X} (hΩ : IsOpen Ω) (hδ : 0 < δ) (hZΩ : ↑Z ⊆ Ω)
    (hz : ∀ z ∈ Z, μ {z} = 0) (hfin : ∀ z ∈ Z, ∃ R > 0, μ (ball z R) ≠ ⊤)
    (hge : ∀ M, ∃ M', ∀ n, ∀ y ∈ Ω, g n y ≤ M → e n y ≤ M')
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, e n y ∂μ)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C, g n y ≤ M) :
    (↑Z : Set X) = {z ∈ Ω | ∀ ε > 0, ∀ M, ∃ n, ∃ y ∈ ball z ε ∩ Ω, M < g n y} := by
  ext z
  refine ⟨fun hzZ ↦ ⟨hZΩ hzZ, fun ε hε M ↦ ?_⟩, fun ⟨hzΩ, hunb⟩ ↦ ?_⟩
  · obtain ⟨φ, -, y, hyΩ, hy, hgy⟩ :=
      exists_strictMono_tendsto_atTop_of_forall_eventually_le_setIntegral_ball hδ (hz z hzZ)
        (hfin z hzZ) hge (hconc z hzZ)
    obtain ⟨k, hk, hgk⟩ := ((hy.eventually (ball_mem_nhds z hε)).and
      (hgy.eventually_gt_atTop M)).exists
    exact ⟨φ k, y k, ⟨hk, hyΩ k⟩, hgk⟩
  · -- Off `Z`, a compact neighbourhood of `z` in `Ω \ Z` carries a uniform bound.
    by_contra hzZ
    have hnhds : Ω \ ↑Z ∈ 𝓝 z :=
      (hΩ.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hzΩ, hzZ⟩
    obtain ⟨C, hCz, hCZ, hC⟩ := local_compact_nhds hnhds
    obtain ⟨ε, hε, hεC⟩ := Metric.mem_nhds_iff.1 hCz
    obtain ⟨M, hM⟩ := hbd C hC hCZ
    obtain ⟨n, y, hy, hMy⟩ := hunb ε hε M
    exact (hM n y (hεC hy.1)).not_gt hMy

end TauCeti
