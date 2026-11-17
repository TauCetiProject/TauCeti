/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Measure.Measurability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Probability.IdentDistrib

/-!
# Cumulative coordinates of random measures on the half-line

For measures finite on bounded initial intervals, measurability of every cumulative mass
`μ [0, t]` is equivalent to measurability of the measure-valued map. The same coordinates
also generate its entire information sigma-algebra. Restricting a measure to `[0, t]`
uses only cumulative masses at times at most `t`. Equality in law of the entire cumulative
process characterizes equality in law of almost surely boundedly finite random measures,
including realizations on different sample spaces.

For random measures whose `(0, n]` restrictions are almost surely integer-valued and whose sum
is almost surely finite on `(0, n]`, the natural-valued `(0, t]` cumulative counts add
simultaneously at all times `t` almost surely, with no finiteness assumption at zero.

These results allow a counting process to describe a random measure and its observed history
without requiring finite total mass, simplicity, or the absence of an atom at zero.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 2 and 7.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℝ≥0}

/-- A family of measures finite on bounded initial intervals is measurable exactly when all
its cumulative masses are measurable. In particular, total mass may be infinite. -/
theorem measurable_measure_iff_Iic (hfinite : ∀ ω t, M ω (Iic t) ≠ ∞) :
    Measurable M ↔ ∀ t, Measurable fun ω ↦ M ω (Iic t) := by
  refine ⟨fun h t ↦ (Measure.measurable_coe measurableSet_Iic).comp h, fun h ↦ ?_⟩
  refine Measurable.measure_of_isPiSystem_of_iUnion
    (B := fun n ↦ Iic (n : ℝ≥0))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic ℝ≥0)) isPiSystem_Iic
    (fun n ↦ ⟨n, rfl⟩) ?_ (fun ω n ↦ hfinite ω n) ?_
  · ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact ⟨n, hn.le⟩
  · rintro _ ⟨t, rfl⟩
    exact h t

/-- Through a fixed time `t`, the restricted measure is measurable exactly when the
cumulative masses through times at most `t` are measurable. The endpoint `t` and any mass
at zero are included. -/
theorem measurable_restrict_Iic_iff (t : ℝ≥0) (hfinite : ∀ ω, M ω (Iic t) ≠ ∞) :
    Measurable (fun ω ↦ (M ω).restrict (Iic t)) ↔
      ∀ s ≤ t, Measurable fun ω ↦ M ω (Iic s) := by
  have hrest : ∀ ω s, (M ω).restrict (Iic t) (Iic s) ≠ ∞ := by
    intro ω s
    exact ne_top_of_le_ne_top (hfinite ω) (by simp [Measure.restrict_apply, measure_mono])
  rw [measurable_measure_iff_Iic hrest]
  simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic]
  constructor
  · intro h s hs
    simpa only [min_eq_left hs] using h s
  · intro h s
    exact h (min s t) (min_le_right _ _)

omit [MeasurableSpace Ω] in
/-- The information carried by a boundedly finite random measure is precisely that carried
by its cumulative-mass process. No measurability of `M` in an ambient sigma-algebra is needed. -/
theorem comap_measure_eq_comap_Iic (hfinite : ∀ ω t, M ω (Iic t) ≠ ∞) :
    MeasurableSpace.comap M inferInstance =
      MeasurableSpace.comap (fun ω t ↦ M ω (Iic t)) inferInstance := by
  apply le_antisymm
  · let := MeasurableSpace.comap (fun ω t ↦ M ω (Iic t)) inferInstance
    have h : Measurable (fun ω t ↦ M ω (Iic t)) := Measurable.of_comap_le le_rfl
    exact ((measurable_measure_iff_Iic hfinite).mpr
      (fun t ↦ (measurable_pi_apply t).comp h)).comap_le
  · let := MeasurableSpace.comap M inferInstance
    have h : Measurable M := Measurable.of_comap_le le_rfl
    exact (measurable_pi_iff.mpr fun t ↦
      (Measure.measurable_coe measurableSet_Iic).comp h).comap_le

omit [MeasurableSpace Ω] in
/-- The history carried by the measure restricted to `[0, t]` equals the history of its
cumulative masses indexed by `[0, t]`. This includes multiplicities and the mass at zero. -/
theorem comap_restrict_Iic_eq_comap_Iic (t : ℝ≥0)
    (hfinite : ∀ ω, M ω (Iic t) ≠ ∞) :
    MeasurableSpace.comap (fun ω ↦ (M ω).restrict (Iic t)) inferInstance =
      MeasurableSpace.comap (fun ω (s : Iic t) ↦ M ω (Iic s.1)) inferInstance := by
  apply le_antisymm
  · let := MeasurableSpace.comap (fun ω (s : Iic t) ↦ M ω (Iic s.1)) inferInstance
    have h : Measurable (fun ω (s : Iic t) ↦ M ω (Iic s.1)) :=
      Measurable.of_comap_le le_rfl
    exact ((measurable_restrict_Iic_iff t hfinite).mpr
      (fun s hs ↦ (measurable_pi_apply (⟨s, hs⟩ : Iic t)).comp h)).comap_le
  · let := MeasurableSpace.comap (fun ω ↦ (M ω).restrict (Iic t)) inferInstance
    have hM : Measurable (fun ω ↦ (M ω).restrict (Iic t)) :=
      Measurable.of_comap_le le_rfl
    refine (measurable_pi_iff.mpr fun s ↦ ?_).comap_le
    have h := (Measure.measurable_coe (s := Iic s.1) measurableSet_Iic).comp hM
    simpa only [Function.comp_def, Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
      min_eq_left (show s.1 ≤ t from s.2)] using h

/-- Two almost surely boundedly finite random measures have the same law exactly when their
entire cumulative-mass processes have the same law. This is equality in distribution, not
pathwise equality; the realizations and their sample measures may be different. -/
theorem identDistrib_measure_iff_Iic {Ω' : Type*} [MeasurableSpace Ω']
    {N : Ω' → Measure ℝ≥0} {P : Measure Ω} {Q : Measure Ω'}
    (hM : AEMeasurable M P) (hN : AEMeasurable N Q)
    (hMf : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) ≠ ∞)
    (hNf : ∀ᵐ ω ∂Q, ∀ t, N ω (Iic t) ≠ ∞) :
    ProbabilityTheory.IdentDistrib M N P Q ↔
      ProbabilityTheory.IdentDistrib (fun ω t ↦ M ω (Iic t)) (fun ω t ↦ N ω (Iic t)) P Q := by
  constructor
  · intro h
    exact h.comp (measurable_pi_iff.mpr fun t ↦ Measure.measurable_coe measurableSet_Iic)
  · intro h
    obtain ⟨M', hM', hM'f, heqM⟩ := hM.exists_ae_eq_range_subset
      (t := {μ : Measure ℝ≥0 | ∀ t, μ (Iic t) ≠ ∞}) hMf ⟨0, by simp⟩
    obtain ⟨N', hN', hN'f, heqN⟩ := hN.exists_ae_eq_range_subset
      (t := {μ : Measure ℝ≥0 | ∀ t, μ (Iic t) ≠ ∞}) hNf ⟨0, by simp⟩
    have hcM : (fun ω t ↦ M ω (Iic t)) =ᵐ[P] (fun ω t ↦ M' ω (Iic t)) :=
      heqM.mono fun ω hω ↦ by simp [hω]
    have hcN : (fun ω t ↦ N ω (Iic t)) =ᵐ[Q] (fun ω t ↦ N' ω (Iic t)) :=
      heqN.mono fun ω hω ↦ by simp [hω]
    have h' := (ProbabilityTheory.IdentDistrib.of_ae_eq h.aemeasurable_fst hcM).symm.trans
      (h.trans (ProbabilityTheory.IdentDistrib.of_ae_eq h.aemeasurable_snd hcN))
    refine ⟨hM, hN, ?_⟩
    rw [Measure.map_congr heqM, Measure.map_congr heqN]
    refine Measure.ext fun s hs ↦ ?_
    -- Use a common family on the disjoint union so both realizations use the same
    -- measurable event in cumulative-coordinate space.
    let C : Ω ⊕ Ω' → Measure ℝ≥0 := Sum.elim M' N'
    have hCf (ω : Ω ⊕ Ω') (t : ℝ≥0) : C ω (Iic t) ≠ ∞ := by
      cases ω with
      | inl ω => exact hM'f (mem_range_self ω) t
      | inr ω => exact hN'f (mem_range_self ω) t
    have hsC : MeasurableSet[MeasurableSpace.comap C inferInstance] (C ⁻¹' s) :=
      hs.preimage (Measurable.of_comap_le le_rfl)
    rw [comap_measure_eq_comap_Iic hCf] at hsC
    obtain ⟨u, hu, heq⟩ := MeasurableSpace.measurableSet_comap.mp hsC
    have hleft : (fun ω t ↦ M' ω (Iic t)) ⁻¹' u = M' ⁻¹' s := by
      exact congrArg (fun A ↦ Sum.inl ⁻¹' A) heq
    have hright : (fun ω t ↦ N' ω (Iic t)) ⁻¹' u = N' ⁻¹' s := by
      exact congrArg (fun A ↦ Sum.inr ⁻¹' A) heq
    rw [Measure.map_apply hM' hs, Measure.map_apply hN' hs, ← hleft, ← hright]
    exact h'.measure_preimage_eq hu

/-- If a finite family of random measures on `ℝ≥0` has almost surely integer-valued restrictions
on `(0, n]` for every `n : ℕ` and sums almost surely to `M₀` with almost surely finite mass on
`(0, n]`, then the natural-valued `(0, t]` cumulative counts sum to those of `M₀` simultaneously
for all `t : ℝ≥0` almost surely. Neither pathwise regularity nor finiteness at `0` is required. -/
theorem ae_forall_natFloor_toNNReal_Ioc_finsetSum_eq {ι : Type*} (s : Finset ι)
    {Q : Measure Ω} {M : ι → Ω → Measure ℝ≥0} {M₀ : Ω → Measure ℝ≥0}
    (hint : ∀ i ∈ s, ∀ n : ℕ, ∀ᵐ z ∂Q, ((M i z).restrict (Ioc 0 (n : ℝ≥0))).IsIntegerValued)
    (hfin : ∀ n : ℕ, ∀ᵐ z ∂Q, M₀ z (Ioc 0 (n : ℝ≥0)) < ∞)
    (hsum : ∀ᵐ z ∂Q, ∑ i ∈ s, M i z = M₀ z) :
    ∀ᵐ z ∂Q, ∀ t : ℝ≥0,
      ∑ i ∈ s, ⌊(M i z (Ioc 0 t)).toNNReal⌋₊ = ⌊(M₀ z (Ioc 0 t)).toNNReal⌋₊ := by
  classical
  have hint' : ∀ᵐ z ∂Q, ∀ (i : s) (n : ℕ),
      ((M i.1 z).restrict (Ioc 0 (n : ℝ≥0))).IsIntegerValued :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 (hint i.1 i.2)
  filter_upwards [hint', ae_all_iff.2 hfin, hsum] with z hzint hzfin hzsum t
  have ht₀ : M₀ z (Ioc 0 t) < ∞ :=
    (measure_mono (Ioc_subset_Ioc_right (Nat.le_ceil t))).trans_lt (hzfin ⌈t⌉₊)
  have heq (i : s) :
      M i.1 z (Ioc 0 t) = (⌊(M i.1 z (Ioc 0 t)).toNNReal⌋₊ : ℝ≥0∞) := by
    have hsub : Ioc (0 : ℝ≥0) t ⊆ Ioc 0 (⌈t⌉₊ : ℝ≥0) :=
      Ioc_subset_Ioc_right (Nat.le_ceil t)
    have hle : M i.1 z (Ioc 0 t) ≤ M₀ z (Ioc 0 t) := by
      rw [← hzsum, sum_apply]
      exact Finset.single_le_sum (f := fun j ↦ M j z (Ioc 0 t)) (fun _ _ ↦ by positivity) i.2
    have hrest : (M i.1 z).restrict (Ioc 0 (⌈t⌉₊ : ℝ≥0)) (Ioc 0 t) = M i.1 z (Ioc 0 t) :=
      Measure.restrict_eq_self _ hsub
    obtain ⟨k, hk⟩ := (hzint i ⌈t⌉₊).exists_eq_natCast measurableSet_Ioc
      (hrest.trans_lt (hle.trans_lt ht₀))
    rw [hrest] at hk
    simp [hk]
  have htot : M₀ z (Ioc 0 t) =
      ((∑ i ∈ s, ⌊(M i z (Ioc 0 t)).toNNReal⌋₊ : ℕ) : ℝ≥0∞) := by
    rw [← hzsum, sum_apply, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i hi ↦ heq ⟨i, hi⟩
  rw [htot, ENNReal.toNNReal_natCast, Nat.floor_natCast]

/-- Binary specialization of `ae_forall_natFloor_toNNReal_Ioc_finsetSum_eq`: if two random
measures on `ℝ≥0` have almost surely integer-valued restrictions on `(0, n]` and sum almost
surely to `M₀` with almost surely finite mass on `(0, n]`, then their natural-valued `(0, t]`
counts add to those of `M₀` simultaneously at all times `t` almost surely. -/
theorem ae_forall_natFloor_toNNReal_Ioc_add_eq {Q : Measure Ω} {M₁ M₂ M₀ : Ω → Measure ℝ≥0}
    (hint₁ : ∀ n : ℕ, ∀ᵐ z ∂Q, ((M₁ z).restrict (Ioc 0 (n : ℝ≥0))).IsIntegerValued)
    (hint₂ : ∀ n : ℕ, ∀ᵐ z ∂Q, ((M₂ z).restrict (Ioc 0 (n : ℝ≥0))).IsIntegerValued)
    (hfin : ∀ n : ℕ, ∀ᵐ z ∂Q, M₀ z (Ioc 0 (n : ℝ≥0)) < ∞)
    (hadd : ∀ᵐ z ∂Q, M₁ z + M₂ z = M₀ z) :
    ∀ᵐ z ∂Q, ∀ t : ℝ≥0,
      ⌊(M₁ z (Ioc 0 t)).toNNReal⌋₊ + ⌊(M₂ z (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(M₀ z (Ioc 0 t)).toNNReal⌋₊ := by
  let M : Bool → Ω → Measure ℝ≥0 := fun b ↦ cond b M₁ M₂
  have h := ae_forall_natFloor_toNNReal_Ioc_finsetSum_eq (Finset.univ : Finset Bool)
    (M := M) (M₀ := M₀)
    (fun b _ ↦ by cases b <;> assumption) hfin
    (by simpa only [M, Fintype.sum_bool, Bool.cond_true, Bool.cond_false] using hadd)
  simpa only [M, Fintype.sum_bool, Bool.cond_true, Bool.cond_false] using h

end TauCeti.Probability
