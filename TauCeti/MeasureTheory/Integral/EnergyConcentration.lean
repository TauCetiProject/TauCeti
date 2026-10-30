/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Sequences
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
(`TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`).

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

## Main results

* `TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`: a finite set of energy
  concentration points of threshold `δ` has at most `E / δ` elements.
* `TauCeti.exists_strictMono_finset_forall_le_of_concentration`: when energy concentrates at
  blow-up points, a subsequence is bounded on compact sets off finitely many concentration points.

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

end TauCeti
