/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.Product
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import TauCeti.MeasureTheory.Constructions.Cylinder.Approximation
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Invariant events of a proper action are almost surely tail events

Let a group `Γ` act on a countable index set `ι`, properly in the sense that for finite sets
`F, F' ⊆ ι` only finitely many `g ∈ Γ` move a point of `F` into `F'`, and let `Γ` act on
configurations `ω : ι → S` by `(g • ω) i = ω (g⁻¹ • i)`. If `Γ` is infinite, every event that is
almost invariant under a finite invariant measure `μ` coincides `μ`-almost everywhere with a tail
event (`TauCeti.Probability.tailEvents`).

The general statement, `TauCeti.Probability.exists_measurableSet_tailEvents_ae_eq`, only asks that
for all finite `F, Λ ⊆ ι` some `g ∈ Γ` moves `F` off `Λ`; for an infinite group acting properly this
holds because all but finitely many `g` do
(`TauCeti.Probability.exists_forall_smul_notMem_of_proper`, used in
`TauCeti.Probability.exists_measurableSet_tailEvents_ae_eq_of_proper`).

This is the ingredient of the face property of invariant Gibbs measures: Georgii, *Gibbs measures
and phase transitions* (2nd ed., 2011), Theorem 14.15, and Sheffield, *Random surfaces*
(Astérisque 304, 2005), Lemma 3.2.2. The argument approximates the event by measurable cylinders
(`TauCeti.MeasureTheory.exists_cylinder_measure_symmDiff_lt`), uses that hypothesis to translate the
`n`-th cylinder off the `n`-th set of an exhaustion of `ι` by finite sets, and takes the `limsup` of
the translates, which is a tail event and, by the Borel–Cantelli lemma, almost equal to the event.

For proper actions the infinitude of `Γ` is needed: the trivial group acts properly on `ℕ`, every
event is invariant for it, and the event `ω 0 = 1` is not almost surely a tail event under a
nontrivial product measure.
-/

public section

open Filter MeasureTheory Set TauCeti.MeasureTheory

open scoped ENNReal symmDiff

namespace TauCeti

namespace Probability

variable {Γ ι S : Type*} [Group Γ] [MulAction Γ ι] [MeasurableSpace S]
  {μ : Measure (ι → S)} [IsFiniteMeasure μ] {A : Set (ι → S)}

/-- Under the hypotheses of `exists_measurableSet_tailEvents_ae_eq`, an almost invariant event is
approximated in measure by events depending only on the coordinates outside a given finite set. -/
private lemma exists_measurableSet_cylinderEvents_compl_measure_symmDiff_lt
    (hmove : ∀ F Λ : Finset ι, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ)
    (hμ : ∀ g : Γ, MeasurePreserving (fun (ω : ι → S) i => ω (g⁻¹ • i)) μ μ)
    (hA : NullMeasurableSet A μ) (hAg : ∀ g : Γ, (fun (ω : ι → S) i => ω (g⁻¹ • i)) ⁻¹' A =ᵐ[μ] A)
    (Λ : Finset ι) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B, MeasurableSet[cylinderEvents (↑Λ)ᶜ] B ∧ μ (B ∆ A) < ε := by
  obtain ⟨F, C, hC, hFC⟩ := exists_cylinder_measure_symmDiff_lt hA hε
  obtain ⟨g, hg⟩ := hmove F Λ
  have hμg := hμ g⁻¹
  have hAg' := hAg g⁻¹
  simp only [inv_inv] at hμg hAg'
  set T : (ι → S) → ι → S := fun ω i => ω (g • i)
  refine ⟨T ⁻¹' cylinder F C, ?_, ?_⟩
  · have hT : Measurable[cylinderEvents (↑Λ)ᶜ] (F.restrict ∘ T) := by
      rw [@measurable_pi_iff]
      exact fun i => measurable_cylinderEvent_apply fun hi => hg i i.property hi
    rw [cylinder, ← preimage_comp]
    exact hT hC
  · calc μ ((T ⁻¹' cylinder F C) ∆ A)
        ≤ μ ((T ⁻¹' cylinder F C) ∆ (T ⁻¹' A)) + μ ((T ⁻¹' A) ∆ A) := measure_symmDiff_le _ _ _
      _ = μ (cylinder F C ∆ A) := by
        rw [← preimage_symmDiff, hμg.measure_preimage
          ((hC.cylinder F).nullMeasurableSet.symmDiff hA), measure_symmDiff_eq_zero_iff.2 hAg',
          add_zero]
      _ < ε := hFC

/-- **Invariant events are almost surely tail events.** Let a group `Γ` act on a countable index
set `ι` so that every finite `F ⊆ ι` can be moved off every finite `Λ ⊆ ι` by some `g ∈ Γ`. Let `μ`
be a finite measure on `ι → S` invariant under `(g • ω) i = ω (g⁻¹ • i)`. Then every
null-measurable event `A` with `g • A` almost equal to `A` for every `g` is almost equal to a tail
event. See `exists_measurableSet_tailEvents_ae_eq_of_proper` for proper actions of infinite
groups. -/
theorem exists_measurableSet_tailEvents_ae_eq [Countable ι]
    (hmove : ∀ F Λ : Finset ι, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ)
    (hμ : ∀ g : Γ, MeasurePreserving (fun (ω : ι → S) i => ω (g⁻¹ • i)) μ μ)
    (hA : NullMeasurableSet A μ) (hAg : ∀ g : Γ, (fun (ω : ι → S) i => ω (g⁻¹ • i)) ⁻¹' A =ᵐ[μ] A) :
    ∃ T, MeasurableSet[tailEvents] T ∧ T =ᵐ[μ] A := by
  classical
  -- An exhaustion of `ι` by finite sets `D n`: every finite set is some `Λs j ⊆ D n` for `j ≤ n`.
  obtain ⟨Λs, hΛs⟩ := exists_surjective_nat (Finset ι)
  let D n := (Finset.range (n + 1)).biUnion Λs
  have hD {j n : ℕ} (h : j ≤ n) : Λs j ⊆ D n :=
    Finset.subset_biUnion_of_mem Λs (Finset.mem_range.2 (Nat.lt_succ_of_le h))
  -- The `n`-th approximant depends only on the coordinates outside `D n`, with error `2⁻¹ ^ n`.
  have h2 : (0 : ℝ≥0∞) < 2⁻¹ := by simp
  choose B hBm hBμ using fun n => exists_measurableSet_cylinderEvents_compl_measure_symmDiff_lt
    hmove hμ hA hAg (D n) (ENNReal.pow_pos h2 n)
  refine ⟨limsup B atTop, measurableSet_tailEvents_iff.2 fun Λ => ?_, ?_⟩
  · -- From time `j` on, the approximants depend only on the coordinates outside `Λ = Λs j`.
    obtain ⟨j, rfl⟩ := hΛs Λ
    rw [← blimsup_true, blimsup_congr' (q := (j ≤ ·)) (eventually_ge_atTop j |>.mono
      fun n hn _ => iff_of_true trivial hn)]
    exact @MeasurableSet.measurableSet_blimsup _ (cylinderEvents _) _ _ fun n hn =>
      cylinderEvents_mono (compl_subset_compl.2 (Finset.coe_subset.2 (hD hn))) _ (hBm n)
  · -- By Borel–Cantelli, almost every configuration is eventually in `B n` iff it is in `A`.
    have hsum : ∑' n, μ (B n ∆ A) ≠ ∞ :=
      ne_top_of_le_ne_top (b := ∑' n : ℕ, 2⁻¹ ^ n) (by simp)
        (tsum_le_tsum fun n => (hBμ n).le)
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    rw [mem_limsup_iff_frequently_mem, ← frequently_const (f := (atTop : Filter ℕ)) (p := ω ∈ A)]
    refine frequently_congr (hω.mono fun n hn => ?_)
    simp only [mem_symmDiff, not_or, not_and, not_not] at hn
    tauto

/-- **An infinite group acting properly moves every finite set off every finite set.** If only
finitely many `g` move a point of `F` into `F'` for all finite `F, F' ⊆ ι`, then, `Γ` being
infinite, for all finite `F, Λ ⊆ ι` some `g` moves every point of `F` outside `Λ`. -/
theorem exists_forall_smul_notMem_of_proper [Infinite Γ]
    (hproper : ∀ F F' : Finset ι, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite) (F Λ : Finset ι) :
    ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ :=
  let ⟨g, hg⟩ := (hproper F Λ).infinite_compl.nonempty
  ⟨g, fun i hi hgi => hg ⟨i, hi, hgi⟩⟩

/-- **An infinite group moves every finite subset of itself off every finite subset** by left
multiplication. -/
theorem exists_forall_smul_notMem_self [Infinite Γ] (F Λ : Finset Γ) :
    ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ := by
  classical
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset ((F ×ˢ Λ).image fun p => p.2 * p.1⁻¹)
  refine ⟨g, fun i hi hgi => hg (Finset.mem_image.2 ⟨(i, g • i), Finset.mem_product.2 ⟨hi, hgi⟩,
    ?_⟩)⟩
  simp [smul_eq_mul]

/-- **Invariant events of a proper action are almost surely tail events.** Let an infinite group
`Γ` act properly on a countable index set `ι`: for finite `F, F' ⊆ ι`, only finitely many `g` move
a point of `F` into `F'`. Let `μ` be a finite measure on `ι → S` invariant under
`(g • ω) i = ω (g⁻¹ • i)`. Then every null-measurable event `A` with `g • A` almost equal to `A`
for every `g` is almost equal to a tail event. -/
theorem exists_measurableSet_tailEvents_ae_eq_of_proper [Countable ι] [Infinite Γ]
    (hproper : ∀ F F' : Finset ι, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite)
    (hμ : ∀ g : Γ, MeasurePreserving (fun (ω : ι → S) i => ω (g⁻¹ • i)) μ μ)
    (hA : NullMeasurableSet A μ) (hAg : ∀ g : Γ, (fun (ω : ι → S) i => ω (g⁻¹ • i)) ⁻¹' A =ᵐ[μ] A) :
    ∃ T, MeasurableSet[tailEvents] T ∧ T =ᵐ[μ] A :=
  exists_measurableSet_tailEvents_ae_eq (exists_forall_smul_notMem_of_proper hproper) hμ hA hAg

end Probability

end TauCeti
