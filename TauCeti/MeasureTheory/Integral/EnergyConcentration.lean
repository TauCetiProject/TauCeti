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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Fatou
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.InterBall
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
(`TauCeti.eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball`). A pointwise
bound `g ≤ A e + B` with `A, B ≥ 0` bounds the energy of `g` on `S` by a multiple of
`μ(S) + ∫_S e` (`TauCeti.setIntegral_le_mul_measureReal_add_setIntegral_of_le`), which brings
concentration of `g` into this form.

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

Once the densities converge locally uniformly off a finite set `Z ⊆ Ω` to a limit `f`, the energy
that does not reach `f` is concentrated at the points of `Z`. Along a subsequence each `z ∈ Z`
carries a *mass* `m z`: for small `ε > 0`, `∫_{B_ε(z)} e k → m z + ∫_{B_ε(z) \ {z}} f`, and
`∫_{Ω \ Z} f + ∑_{z ∈ Z} m z ≤ E`
(`TauCeti.exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le`). The masses are
found by extracting a convergent subsequence of the energies of a fixed small ball about each point
of `Z`, whose annuli about `z` lie in compact subsets of `Ω \ Z`; the bound is Fatou's lemma off
those balls. A point at which energy at least `δ` concentrates carries mass at least `δ`
(`TauCeti.le_of_tendsto_setIntegral_ball`), since the energy of `f` on small punctured balls tends
to zero.

## Main results

* `TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`: a finite set of energy
  concentration points of threshold `δ` has at most `E / δ` elements.
* `TauCeti.eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball`: removing the
  measure of small balls from concentrating energy loses arbitrarily little of it.
* `TauCeti.exists_strictMono_finset_forall_le_of_concentration`: when energy concentrates at
  blow-up points, a subsequence is bounded on compact sets off finitely many concentration points.
* `TauCeti.exists_strictMono_tendsto_atTop_of_forall_eventually_le_setIntegral_ball`: energy
  concentration at a null point gives a subsequence blowing up at points converging to it.
* `TauCeti.coe_eq_setOf_forall_exists_lt_of_concentration`: a finite set of concentration
  points off which the sequence is locally bounded is its set of blow-up points.
* `TauCeti.exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le`: densities
  converging locally uniformly off a finite set `Z` converge, along a subsequence, to the limit
  density plus masses at the points of `Z`, with no energy created.
* `TauCeti.le_of_tendsto_setIntegral_ball`: the mass at a concentration point of threshold `δ` is
  at least `δ`.
* `TauCeti.eventually_tendsto_setIntegral_ball_congr`: the mass at a point only depends on the
  densities near it.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.6 (the finite set of points at which the
  derivatives of a sequence of curves with bounded energy blow up, and Theorem 4.6.1, the
  convergence of the energy densities to the energy density of the limit plus point masses).
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {S : Set α} {A B : ℝ}

/-- A function `g ≥ 0` bounded by `A f + B` on a measurable set `S` of finite measure, for an
integrable density `f`, is integrable on `S`. -/
theorem integrableOn_of_le_mul_add (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (hg : AEStronglyMeasurable g (μ.restrict S)) (hf : IntegrableOn f S μ)
    (hg0 : ∀ z ∈ S, 0 ≤ g z) (hle : ∀ z ∈ S, g z ≤ A * f z + B) : IntegrableOn g S μ :=
  Integrable.mono' ((hf.const_mul A).fun_add (integrableOn_const (C := B) hSfin)) hg
    (ae_restrict_of_forall_mem hS fun z hz ↦ by
      rw [Real.norm_of_nonneg (hg0 z hz)]
      exact hle z hz)

/-- **Energy bounds from a pointwise bound.** If `g ≤ A f + B` on a measurable set `S` of finite
measure, with `A, B ≥ 0` and `f ≥ 0`, then `∫_S g ≤ (A + B + 1)(μ(S) + ∫_S f)`. This is the shape
of hypothesis in `TauCeti.eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball`. -/
theorem setIntegral_le_mul_measureReal_add_setIntegral_of_le (hS : MeasurableSet S)
    (hSfin : μ S ≠ ⊤) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hg : IntegrableOn g S μ)
    (hf : IntegrableOn f S μ) (hf0 : ∀ z ∈ S, 0 ≤ f z) (hle : ∀ z ∈ S, g z ≤ A * f z + B) :
    ∫ z in S, g z ∂μ ≤ (A + B + 1) * (μ.real S + ∫ z in S, f z ∂μ) := by
  have hint0 : 0 ≤ ∫ z in S, f z ∂μ := setIntegral_nonneg hS hf0
  have hm0 : 0 ≤ μ.real S := measureReal_nonneg
  calc ∫ z in S, g z ∂μ
      ≤ ∫ z in S, (A * f z + B) ∂μ :=
        setIntegral_mono_on hg ((hf.const_mul A).fun_add (integrableOn_const (C := B) hSfin))
          hS hle
    _ = A * (∫ z in S, f z ∂μ) + B * μ.real S := by
        rw [integral_add (hf.const_mul A) (integrableOn_const hSfin), integral_const_mul,
          setIntegral_const, smul_eq_mul, mul_comm (μ.real S)]
    _ ≤ (A + B + 1) * (μ.real S + ∫ z in S, f z ∂μ) := by
        nlinarith [mul_nonneg hA0 hm0, mul_nonneg hB0 hint0]

end Comparison

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {Ω : Set X} {δ E : ℝ}

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
  calc Z.card * δ = ∑ _ ∈ Z, δ := by simp
    _ ≤ ∑ z ∈ Z, ∫ y in ball z ε ∩ Ω, e i y ∂μ := Finset.sum_le_sum hi
    _ = ∫ y in ⋃ z ∈ Z, ball z ε ∩ Ω, e i y ∂μ :=
      (integral_biUnion_finset Z (fun _ _ ↦ measurableSet_ball.inter hΩ) hdisj
        fun _ _ ↦ (hint i).mono_set inter_subset_right).symm
    _ ≤ ∫ y in Ω, e i y ∂μ :=
      setIntegral_mono_set (hint i) (ae_restrict_of_forall_mem hΩ (he i))
        (iUnion₂_subset fun _ _ ↦ inter_subset_right).eventuallySubset
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
        (inter_subset_inter_left _ (ball_subset_ball hρ.2.le)).eventuallySubset

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

/-- **Concentration points are exactly the blow-up points.** Let `Ω` be a set and `Z ⊆ Ω` a
finite set of points of measure zero, each with a ball of finite measure. Let the densities `e n`
concentrate energy at least `δ > 0` at every point of `Z`, and let the `g n` be uniformly bounded
above on every compact subset of `Ω \ Z` and control the `e n`, in the sense that `e n` is bounded
above wherever `g n` is, uniformly in `n`. Then `Z` is exactly the set of points of `Ω` near which
the `g n` are not uniformly bounded above. So when the functions of
`TauCeti.exists_strictMono_finset_forall_le_of_concentration` control its densities and its points
have measure zero with balls of finite measure, the finite set it produces is determined by the
subsequence it comes with. -/
theorem coe_eq_setOf_forall_exists_lt_of_concentration
    {g e : ℕ → X → ℝ} {Z : Finset X} (hδ : 0 < δ) (hZΩ : ↑Z ⊆ Ω)
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
  · -- Off `Z`, a convergent sequence of blow-up points together with its limit is a compact set
    -- in `Ω \ Z` carrying a uniform bound.
    by_contra hzZ
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 Z.finite_toSet.isClosed.isOpen_compl z hzZ
    choose n y hy hgy using fun k : ℕ ↦ hunb (min ε₀ (1 / (k + 1))) (lt_min hε₀ (by positivity)) k
    have hyz : Tendsto y atTop (𝓝 z) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg)
        (fun k ↦ ((mem_ball.1 (hy k).1).trans_le (min_le_right _ _)).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hsub : insert z (Set.range y) ⊆ Ω \ ↑Z := by
      rintro _ (rfl | ⟨k, rfl⟩)
      · exact ⟨hzΩ, hzZ⟩
      · exact ⟨(hy k).2, fun h ↦
          hball (mem_ball.2 ((mem_ball.1 (hy k).1).trans_le (min_le_left _ _))) h⟩
    obtain ⟨M, hM⟩ := hbd _ hyz.isCompact_insert_range hsub
    obtain ⟨k, hk⟩ := exists_nat_gt M
    exact ((hM (n k) (y k) (Set.mem_insert_of_mem _ (Set.mem_range_self k))).trans_lt hk).not_gt
      (hgy k)

/-- **Masses of energy concentration points.** Suppose that the energy of the balls about `z ∈ Ω`
converges to a mass `m` plus the energy of a density `f` on the punctured ball, as in
`TauCeti.exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le`. If energy at
least `δ` concentrates at `z`, that is, for every `ε > 0` eventually `δ ≤ ∫_{B_ε(z) ∩ Ω} e n`, then
`δ ≤ m`: the energy of `f` on the punctured balls tends to zero. -/
theorem le_of_tendsto_setIntegral_ball {e : ℕ → X → ℝ} {f : X → ℝ} {z : X} {m r : ℝ}
    (hΩ : IsOpen Ω) (hz : z ∈ Ω) (hr : 0 < r) (hf : IntegrableOn f (ball z r \ {z}) μ)
    (hm : ∀ᶠ ε in 𝓝[>] 0, Tendsto (fun n ↦ ∫ y in ball z ε, e n y ∂μ) atTop
      (𝓝 (m + ∫ y in ball z ε \ {z}, f y ∂μ)))
    (hconc : ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, e n y ∂μ) : δ ≤ m := by
  -- The energy of `f` on `B_ε(z) \ {z}` tends to zero, by dominated convergence.
  have hzero : Tendsto (fun ε ↦ ∫ y in ball z ε \ {z}, f y ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun ε ↦ ∫ y in ball z r \ {z}, (ball z ε).indicator f y ∂μ) (𝓝[>] 0)
        (𝓝 (∫ _ in ball z r \ {z}, (0 : ℝ) ∂μ)) :=
      tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖f y‖)
        (.of_forall fun _ ↦ hf.aestronglyMeasurable.indicator measurableSet_ball)
        (.of_forall fun _ ↦ .of_forall fun y ↦ norm_indicator_le_norm_self _ _) hf.norm
        (ae_restrict_of_forall_mem (measurableSet_ball.diff (measurableSet_singleton z))
          fun y hy ↦ tendsto_const_nhds.congr' <| by
            filter_upwards [Ioo_mem_nhdsGT (dist_pos.2 hy.2)] with ε hε
            rw [indicator_of_notMem (fun h ↦ (mem_ball.1 h).not_ge hε.2.le)])
    rw [integral_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hr] with ε hε
    have hset : (ball z r \ {z}) ∩ ball z ε = ball z ε \ {z} := by
      ext y
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff]
      exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨ball_subset_ball hε.2 h.1, h.2⟩, h.1⟩⟩
    rw [setIntegral_indicator measurableSet_ball, hset]
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ ≤ m + ∫ y in ball z ε \ {z}, f y ∂μ := by
    filter_upwards [hm, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_closedBall_subset (hΩ.mem_nhds hz))] with ε hε hε0 hεΩ
    refine ge_of_tendsto hε ((hconc ε hε0).mono fun n hn ↦ ?_)
    rwa [inter_eq_left.2 (ball_subset_closedBall.trans hεΩ)] at hn
  simpa using ge_of_tendsto (tendsto_const_nhds.add hzero) hev

/-- **Energy masses only see the densities near the point.** If the energy of the balls about
`z ∈ Ω` along `e'` converges to `m` plus the energy of `f'` on the punctured balls, the same holds
for densities `e n` agreeing with `e' n` on `Ω` and a density `f` agreeing with `f'` on `Ω \ Z`, for
a finite set `Z`: small balls about `z` lie in `Ω` and meet `Z` at most in `z`. -/
theorem eventually_tendsto_setIntegral_ball_congr {e e' : ℕ → X → ℝ} {f f' : X → ℝ}
    {Z : Finset X} {z : X} {m : ℝ} (hΩ : IsOpen Ω) (hz : z ∈ Ω) (he : ∀ n, EqOn (e n) (e' n) Ω)
    (hf : EqOn f f' (Ω \ ↑Z))
    (h : ∀ᶠ ε in 𝓝[>] 0, Tendsto (fun n ↦ ∫ y in ball z ε, e' n y ∂μ) atTop
      (𝓝 (m + ∫ y in ball z ε \ {z}, f' y ∂μ))) :
    ∀ᶠ ε in 𝓝[>] 0, Tendsto (fun n ↦ ∫ y in ball z ε, e n y ∂μ) atTop
      (𝓝 (m + ∫ y in ball z ε \ {z}, f y ∂μ)) := by
  obtain ⟨r, hr, hrΩ, hrS⟩ :=
    exists_pos_ball_subset_and_ball_sdiff_singleton_subset_sdiff hΩ Z.finite_toSet hz
  filter_upwards [h, Ioc_mem_nhdsGT hr] with ε hlim hε
  have hεΩ : ball z ε ⊆ Ω := (ball_subset_ball hε.2).trans hrΩ
  have hεS : ball z ε \ {z} ⊆ Ω \ ↑Z := (sdiff_subset_sdiff_left (ball_subset_ball hε.2)).trans hrS
  rw [setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton z)) (hf.mono hεS)]
  exact hlim.congr fun n ↦ (setIntegral_congr_fun measurableSet_ball ((he n).mono hεΩ)).symm

/-- The energy accounting behind
`TauCeti.exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le`. Let the balls
`B_r(z)` about the points of a finite set `Z` lie in `Ω` and be far apart. If along `ψ` the
energies of these balls converge to `A z`, then the energy of the limit `f` off `Z` plus the masses
`A z - ∫_{B_r(z) \ {z}} f` is at most `E`: split `Ω` into the balls and the rest `V`, and `Ω \ Z`
into the punctured balls and the same `V`, and apply Fatou's lemma on `V`. -/
private theorem setIntegral_add_sum_le_of_tendsto_setIntegral_ball {e : ℕ → X → ℝ} {f : X → ℝ}
    {Z : Finset X} {r : ℝ} {ψ : ℕ → ℕ} {A : Z → ℝ} (hΩ : IsOpen Ω) (hr : 0 < r)
    (hballΩ : ∀ z ∈ Z, ball z r ⊆ Ω) (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * r < dist z w)
    (he : ∀ n, ∀ y ∈ Ω, 0 ≤ e n y) (hint : ∀ n, IntegrableOn (e n) Ω μ)
    (hE : ∀ n, ∫ y in Ω, e n y ∂μ ≤ E) (hf : IntegrableOn f (Ω \ ↑Z) μ)
    (hlim : ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ e n y) atTop (𝓝 (f y)))
    (hψ : Tendsto ψ atTop atTop)
    (hA : ∀ z : Z, Tendsto (fun n ↦ ∫ y in ball (z : X) r, e (ψ n) y ∂μ) atTop (𝓝 (A z))) :
    ∫ y in Ω \ ↑Z, f y ∂μ + ∑ z : Z, (A z - ∫ y in ball (z : X) r \ {(z : X)}, f y ∂μ) ≤ E := by
  set V := Ω \ ⋃ z : Z, ball (z : X) r
  have hdisj : Pairwise (Disjoint on fun z : Z ↦ ball (z : X) r) := fun z w hzw ↦
    ball_disjoint_ball (by linarith [hsep z z.property w w.property (Subtype.coe_injective.ne hzw)])
  have hpunct (z : Z) : ball (z : X) r \ {(z : X)} ⊆ Ω \ ↑Z := fun y hy ↦
    ⟨hballΩ z z.property hy.1, fun hyZ ↦
      hy.2 (eq_of_mem_closedBall_of_lt_dist (hsep y hyZ z z.property)
        (ball_subset_closedBall hy.1))⟩
  have hsplit (n : ℕ) : ∫ y in Ω, e n y ∂μ =
      ∫ y in V, e n y ∂μ + ∑ z : Z, ∫ y in ball (z : X) r, e n y ∂μ :=
    setIntegral_eq_setIntegral_sdiff_iUnion_add_sum (fun _ ↦ measurableSet_ball) hdisj
      (fun z ↦ hballΩ z z.property) (hint n)
  have hV : (Ω \ ↑Z) \ ⋃ z : Z, (ball (z : X) r \ {(z : X)}) = V := by
    ext y
    simp only [V, Set.mem_sdiff, mem_iUnion, mem_singleton_iff, not_exists, not_and, not_not,
      Finset.mem_coe, Subtype.forall]
    constructor
    · rintro ⟨⟨hyΩ, hyZ⟩, h⟩
      exact ⟨hyΩ, fun z hz hy ↦ hyZ (h z hz hy ▸ hz)⟩
    · rintro ⟨hyΩ, h⟩
      exact ⟨⟨hyΩ, fun hyZ ↦ h y hyZ (mem_ball_self hr)⟩, fun z hz hy ↦ absurd hy (h z hz)⟩
  have hfsplit : ∫ y in Ω \ ↑Z, f y ∂μ =
      ∫ y in V, f y ∂μ + ∑ z : Z, ∫ y in ball (z : X) r \ {(z : X)}, f y ∂μ := by
    rw [← hV]
    exact setIntegral_eq_setIntegral_sdiff_iUnion_add_sum
      (fun _ ↦ measurableSet_ball.diff (measurableSet_singleton _))
      (fun z w hzw ↦ (hdisj hzw).mono sdiff_subset sdiff_subset) hpunct hf
  have hVS : V ⊆ Ω \ ↑Z := hV ▸ sdiff_subset
  have hVm : MeasurableSet V := hΩ.measurableSet.diff (.iUnion fun _ ↦ measurableSet_ball)
  have hfV : ∫ y in V, f y ∂μ ≤ E - ∑ z : Z, A z := by
    refine le_of_forall_gt_imp_ge_of_dense fun D hD ↦
      TauCeti.integral_le_of_tendsto_of_integral_le
        (.of_forall fun n ↦ (hint (ψ n)).mono_set sdiff_subset)
        (.of_forall fun n ↦ ae_restrict_of_forall_mem hVm fun y hy ↦ he (ψ n) y (hVS hy).1)
        (ae_restrict_of_forall_mem hVm fun y hy ↦ (hlim y (hVS hy)).comp hψ) ?_
    have hc : Tendsto (fun n ↦ E - ∑ z : Z, ∫ y in ball (z : X) r, e (ψ n) y ∂μ) atTop
        (𝓝 (E - ∑ z : Z, A z)) :=
      tendsto_const_nhds.sub (tendsto_finsetSum _ fun z _ ↦ hA z)
    exact ((hc.eventually (gt_mem_nhds hD)).mono fun n hn ↦ by
      linarith [hsplit (ψ n), hE (ψ n)]).frequently
  rw [hfsplit, Finset.sum_sub_distrib]
  linarith

section Mass

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]

/-- The ball step behind
`TauCeti.exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le`. Let the closed
ball `closedBall z r ⊆ Ω` meet the finite set `Z` only in `z`, and let the energies of `B_r(z)`
converge to `A` along `ψ`. For `0 < ε ≤ r` the annulus `B_r(z) \ B_ε(z)` lies in a compact subset
of `Ω \ Z`, where the densities converge uniformly, so the energies of `B_ε(z)` converge to
`A - ∫_{B_r(z) \ {z}} f + ∫_{B_ε(z) \ {z}} f`. -/
private theorem tendsto_setIntegral_ball_of_tendsto_setIntegral_ball {e : ℕ → X → ℝ}
    {f : X → ℝ} {Z : Finset X} {z : X} {r ε A : ℝ} {ψ : ℕ → ℕ} (hS : IsOpen (Ω \ ↑Z))
    (hrΩ : closedBall z r ⊆ Ω) (hZr : ∀ w ∈ Z, w ∈ closedBall z r → w = z) (hε : ε ∈ Ioc 0 r)
    (hint : ∀ n, IntegrableOn (e n) Ω μ) (hf : IntegrableOn f (Ω \ ↑Z) μ)
    (hlim : TendstoLocallyUniformlyOn e f atTop (Ω \ ↑Z)) (hψ : Tendsto ψ atTop atTop)
    (hA : Tendsto (fun n ↦ ∫ y in ball z r, e (ψ n) y ∂μ) atTop (𝓝 A)) :
    Tendsto (fun n ↦ ∫ y in ball z ε, e (ψ n) y ∂μ) atTop
      (𝓝 (A - ∫ y in ball z r \ {z}, f y ∂μ + ∫ y in ball z ε \ {z}, f y ∂μ)) := by
  set R := ball z r \ ball z ε
  have hrΩ' : ball z r ⊆ Ω := ball_subset_closedBall.trans hrΩ
  have hCS : closedBall z r \ ball z ε ⊆ Ω \ ↑Z := fun y hy ↦ ⟨hrΩ hy.1, fun hyZ ↦
    hy.2 (by rw [hZr y hyZ hy.1]; exact mem_ball_self hε.1)⟩
  have hCc : IsCompact (closedBall z r \ ball z ε) := (isCompact_closedBall z r).diff isOpen_ball
  have hRC : R ⊆ closedBall z r \ ball z ε := sdiff_subset_sdiff_left ball_subset_closedBall
  have hR : Tendsto (fun n ↦ ∫ y in R, e n y ∂μ) atTop (𝓝 (∫ y in R, f y ∂μ)) :=
    (((tendstoLocallyUniformlyOn_iff_forall_isCompact hS).1 hlim _ hCS hCc).mono
      hRC).tendsto_setIntegral ((measure_mono hRC).trans_lt hCc.measure_lt_top).ne
      (.of_forall fun n ↦ (hint n).mono_set (sdiff_subset.trans hrΩ'))
      (hf.mono_set (hRC.trans hCS))
  have hεr : ball z ε ⊆ ball z r := ball_subset_ball hε.2
  have hset : (ball z r \ {z}) \ (ball z ε \ {z}) = R := by
    ext y
    simp only [R, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hyz⟩, h⟩
      exact ⟨hy, fun hyε ↦ h ⟨hyε, hyz⟩⟩
    · rintro ⟨hy, hyε⟩
      exact ⟨⟨hy, fun h ↦ hyε (h ▸ mem_ball_self hε.1)⟩, fun h ↦ hyε h.1⟩
  have hfeq : ∫ y in ball z r \ {z}, f y ∂μ =
      ∫ y in ball z ε \ {z}, f y ∂μ + ∫ y in R, f y ∂μ := by
    have hpunct : ball z r \ {z} ⊆ Ω \ ↑Z := fun y hy ↦
      ⟨hrΩ' hy.1, fun hyZ ↦ hy.2 (hZr y hyZ (ball_subset_closedBall hy.1))⟩
    rw [← hset, setIntegral_sdiff (measurableSet_ball.diff (measurableSet_singleton z))
      (hf.mono_set hpunct) (sdiff_subset_sdiff_left hεr)]
    ring
  have heq (n : ℕ) : ∫ y in ball z ε, e (ψ n) y ∂μ =
      ∫ y in ball z r, e (ψ n) y ∂μ - ∫ y in R, e (ψ n) y ∂μ := by
    rw [setIntegral_sdiff measurableSet_ball ((hint (ψ n)).mono_set hrΩ') hεr]
    ring
  have hlim' := hA.sub (hR.comp hψ)
  simp only [Function.comp_def] at hlim'
  simp_rw [heq]
  convert hlim' using 2
  rw [hfeq]
  ring

/-- **Energy masses at the points of a finite set.** Let `e n ≥ 0` be densities on an open set `Ω`
with `∫_Ω e n ≤ E`, converging locally uniformly on `Ω \ Z` to a density `f`, for a finite set
`Z ⊆ Ω`. Then `f` is integrable on `Ω \ Z`, by Fatou's lemma, and along a subsequence `ψ` each point
`z ∈ Z` carries a mass `m z`: for every small `ε > 0`, the energy of the ball about `z` converges to
the mass plus the energy of the limit on the punctured ball,

`∫_{B_ε(z)} e (ψ n) → m z + ∫_{B_ε(z) \ {z}} f`,

and the energy of the limit off `Z` and the masses together are at most `E`. In other words the
energy measures `e n μ` converge on the balls about `Z` to `f μ` plus point masses `m z` at the
points of `Z`, and no energy is created in the limit. -/
theorem exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le
    {e : ℕ → X → ℝ} {f : X → ℝ} {Z : Finset X} (hΩ : IsOpen Ω) (hZΩ : ↑Z ⊆ Ω)
    (he : ∀ n, ∀ y ∈ Ω, 0 ≤ e n y) (hint : ∀ n, IntegrableOn (e n) Ω μ)
    (hE : ∀ n, ∫ y in Ω, e n y ∂μ ≤ E) (hlim : TendstoLocallyUniformlyOn e f atTop (Ω \ ↑Z)) :
    ∃ (ψ : ℕ → ℕ) (m : X → ℝ), StrictMono ψ ∧ IntegrableOn f (Ω \ ↑Z) μ ∧
      (∀ z ∈ Z, ∀ᶠ ε in 𝓝[>] 0, Tendsto (fun n ↦ ∫ y in ball z ε, e (ψ n) y ∂μ) atTop
        (𝓝 (m z + ∫ y in ball z ε \ {z}, f y ∂μ))) ∧
      ∫ y in Ω \ ↑Z, f y ∂μ + ∑ z ∈ Z, m z ≤ E := by
  classical
  -- The limit is integrable off `Z`, by Fatou's lemma.
  have hSm : MeasurableSet (Ω \ ↑Z) := hΩ.measurableSet.diff Z.finite_toSet.measurableSet
  have hf : IntegrableOn f (Ω \ ↑Z) μ :=
    TauCeti.integrable_of_tendsto_of_integral_le (l := atTop) (D := E)
      (.of_forall fun n ↦ (hint n).mono_set sdiff_subset)
      (.of_forall fun n ↦ ae_restrict_of_forall_mem hSm fun y hy ↦ he n y hy.1)
      (ae_restrict_of_forall_mem hSm fun y hy ↦ hlim.tendsto_at hy)
      (.of_forall fun n ↦ (setIntegral_mono_set (hint n)
        (ae_restrict_of_forall_mem hΩ.measurableSet (he n)) sdiff_subset.eventuallySubset).trans
        (hE n))
  -- A common radius `r` for which the closed balls about the points of `Z` lie in `Ω` and are far
  -- apart, so that each of them meets `Z` only in its centre.
  obtain ⟨r, hr, hrΩ, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist (T := Z)
    (U := fun _ ↦ Ω) fun w hw ↦ hΩ.mem_nhds (hZΩ hw)
  have hballΩ (z : X) (hz : z ∈ Z) : ball z r ⊆ Ω := ball_subset_closedBall.trans (hrΩ z hz)
  have hZr (z : X) (hz : z ∈ Z) (w : X) (hw : w ∈ Z) (hwr : w ∈ closedBall z r) : w = z :=
    eq_of_mem_closedBall_of_lt_dist (hsep w hw z hz) hwr
  -- The energies of the balls of radius `r` lie in `[0, E]`; extract a convergent subsequence.
  set a : ℕ → Z → ℝ := fun n z ↦ ∫ y in ball (z : X) r, e n y ∂μ
  have ha (n : ℕ) : a n ∈ Set.pi univ fun _ ↦ Icc 0 E := fun z _ ↦
    ⟨setIntegral_nonneg measurableSet_ball fun y hy ↦ he n y (hballΩ z z.property hy),
      (setIntegral_mono_set (hint n) (ae_restrict_of_forall_mem hΩ.measurableSet (he n))
        (hballΩ z z.property).eventuallySubset).trans (hE n)⟩
  obtain ⟨A, -, ψ, hψ, hA⟩ := (isCompact_univ_pi fun _ ↦ isCompact_Icc).tendsto_subseq ha
  have hAz (z : Z) : Tendsto (fun n ↦ a (ψ n) z) atTop (𝓝 (A z)) := tendsto_pi_nhds.1 hA z
  set m : X → ℝ := fun z ↦ if hz : z ∈ Z then A ⟨z, hz⟩ - ∫ y in ball z r \ {z}, f y ∂μ else 0
  have hm (z : Z) : m z = A z - ∫ y in ball (z : X) r \ {(z : X)}, f y ∂μ := by simp [m]
  refine ⟨ψ, m, hψ, hf, fun z hz ↦ ?_, ?_⟩
  · filter_upwards [Ioc_mem_nhdsGT hr] with ε hε
    rw [hm ⟨z, hz⟩]
    exact tendsto_setIntegral_ball_of_tendsto_setIntegral_ball
      (hΩ.sdiff Z.finite_toSet.isClosed) (hrΩ z hz) (hZr z hz) hε hint hf hlim
      hψ.tendsto_atTop (hAz ⟨z, hz⟩)
  · rw [← Finset.sum_coe_sort Z m]
    simp only [hm]
    exact setIntegral_add_sum_le_of_tendsto_setIntegral_ball hΩ hr hballΩ hsep he hint hE hf
      (fun y hy ↦ hlim.tendsto_at hy) hψ.tendsto_atTop hAz

end Mass

end TauCeti
