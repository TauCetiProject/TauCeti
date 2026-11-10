/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Measure.Decomposition.Atomic
public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic

/-!
# Atomic decomposition of integer-valued measures

A σ-finite integer-valued measure on a standard Borel space is a countable sum of
Dirac occurrences. The indexing counts occurrences, not distinct locations: a point of
mass three contributes three Dirac measures. This is the measure-theoretic reconstruction
underlying enumeration and independent marking of point configurations.

The argument first identifies the support of an outer regular integer-valued measure
with its positive-mass singletons. Finite restrictions then show that a σ-finite
integer-valued measure has no diffuse remainder. We use the existing atomic/diffuse
measure decomposition and expand each finite natural singleton mass into occurrences.
No topology or local finiteness is required in the standard Borel reconstruction theorem.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 6 (point measures and their atomic representations).
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.Measure

universe u

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- For an outer regular integer-valued measure, the support consists exactly of
its positive-mass singleton points. Unlike the support of a general atomic measure,
it contains no additional accumulation points with zero mass. -/
theorem IsIntegerValued.support_eq_positiveSingletons [TopologicalSpace X]
    [OpensMeasurableSpace X] [μ.OuterRegular] (hμ : μ.IsIntegerValued) :
    μ.support = μ.positiveSingletons := by
  ext x
  constructor
  · intro hx
    by_contra hx0
    have hz : μ {x} = 0 := not_ne_iff.1 (by simpa only [mem_positiveSingletons_iff] using hx0)
    obtain ⟨U, hxU, hU, hmass⟩ :=
      ({x} : Set X).exists_isOpen_lt_of_lt (μ := μ) 1 (by simp [hz])
    have hpos := (mem_support_iff_forall x).1 hx U (hU.mem_nhds (hxU (mem_singleton x)))
    exact hmass.not_ge (hμ.one_le_apply hU.measurableSet hpos.ne')
  · intro hx
    refine (mem_support_iff_forall x).2 fun U hU ↦ ?_
    exact (pos_iff_ne_zero.2 ((mem_positiveSingletons_iff μ x).1 hx)).trans_le
      (measure_mono (singleton_subset_iff.2 (mem_of_mem_nhds hU)))

/-- A σ-finite integer-valued measure on a standard Borel space cannot have a nonzero
diffuse component: if all singletons have zero mass, the measure is zero. -/
theorem IsIntegerValued.eq_zero_of_nullSingletonClass [StandardBorelSpace X]
    [SigmaFinite μ] [NullSingletonClass μ] (hμ : μ.IsIntegerValued) : μ = 0 := by
  let := upgradeStandardBorel X
  have hz (n : ℕ) : μ.restrict (spanningSets μ n) = 0 := by
    have : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      ⟨by simpa using measure_spanningSets_lt_top μ n⟩
    rw [← support_eq_empty_iff, hμ.restrict.support_eq_positiveSingletons]
    ext x
    simp only [mem_positiveSingletons_iff, measure_singleton, ne_self_iff_false,
      mem_empty_iff_false]
  apply measure_univ_eq_zero.1
  rw [← iSup_restrict_spanningSets (μ := μ) univ]
  simp [hz]

/-- The diffuse remainder of a σ-finite integer-valued measure on a standard Borel
space vanishes.

The hypothesis `hμ` precedes the instance arguments so that `simp` checks it before searching for a
`StandardBorelSpace X` instance. -/
@[simp]
theorem IsIntegerValued.diffusePart_eq_zero (hμ : μ.IsIntegerValued) [StandardBorelSpace X]
    [SigmaFinite μ] : μ.diffusePart = 0 := by
  have : SigmaFinite μ.diffusePart := sigmaFinite_of_le μ μ.diffusePart_le
  have hint : μ.diffusePart.IsIntegerValued := by
    rw [diffusePart_def]
    exact hμ.restrict
  exact hint.eq_zero_of_nullSingletonClass

/-- A σ-finite integer-valued measure on a standard Borel space equals its atomic part.

The hypothesis `hμ` precedes the instance arguments so that `simp` checks it before searching for a
`StandardBorelSpace X` instance. -/
@[simp]
theorem IsIntegerValued.atomicPart_eq_self (hμ : μ.IsIntegerValued) [StandardBorelSpace X]
    [SigmaFinite μ] : μ.atomicPart = μ := by
  simpa [hμ.diffusePart_eq_zero] using μ.atomicPart_add_diffusePart

/-- Reconstruct a σ-finite integer-valued measure from its singleton masses.
The index set of positive-mass points is countable. -/
theorem IsIntegerValued.eq_sum_smul_dirac [StandardBorelSpace X] [SigmaFinite μ]
    (hμ : μ.IsIntegerValued) :
    μ = Measure.sum fun x : μ.positiveSingletons ↦ μ {(x : X)} • dirac (x : X) := by
  rw [← μ.atomicPart_eq_sum_dirac, hμ.atomicPart_eq_self]

/-- Reconstruct an integer-valued measure by individual occurrences. Each positive-mass
point is repeated a number of times equal to its singleton mass; σ-finiteness makes
that mass a finite natural number. -/
theorem IsIntegerValued.eq_sum_dirac [StandardBorelSpace X] [SigmaFinite μ]
    (hμ : μ.IsIntegerValued) :
    μ = Measure.sum fun p : (Σ x : μ.positiveSingletons, Fin ⌊(μ {(x : X)}).toNNReal⌋₊) ↦
      dirac (p.1 : X) := by
  calc
    μ = Measure.sum (fun x : μ.positiveSingletons ↦ μ {(x : X)} • dirac (x : X)) :=
      hμ.eq_sum_smul_dirac
    _ = _ := by
      ext A hA
      rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA, tsum_sigma']
      apply tsum_congr
      intro x
      obtain ⟨n, hn⟩ := hμ.exists_eq_natCast (measurableSet_singleton (x : X))
        measure_singleton_lt_top
      simp [hn, smul_apply, smul_eq_mul]

/-- A σ-finite integer-valued measure on a standard Borel space is a sum of a sequence
of Dirac occurrences. Missing indices contribute zero and repeated locations retain
multiplicities. This is an existence result, not a measurable choice of the sequence. -/
theorem IsIntegerValued.exists_eq_sum_dirac [StandardBorelSpace X] [SigmaFinite μ]
    (hμ : μ.IsIntegerValued) :
    ∃ x : ℕ → Option X, μ = Measure.sum fun n ↦ (x n).elim 0 dirac := by
  classical
  have := μ.countable_positiveSingletons.to_subtype
  let ι := Σ x : μ.positiveSingletons, Fin ⌊(μ {(x : X)}).toNNReal⌋₊
  let f : ι → X := fun p ↦ (p.1 : X)
  let := Encodable.ofCountable ι
  refine ⟨fun n ↦ (Encodable.decode₂ ι n).map f, ?_⟩
  calc
    μ = Measure.sum (fun i ↦ dirac (f i)) := hμ.eq_sum_dirac
    _ = Measure.sum (Function.extend Encodable.encode (fun i ↦ dirac (f i)) 0) :=
      (Measure.sum_extend_zero Encodable.encode_injective _).symm
    _ = _ := by
      congr 1
      funext n
      by_cases hn : n ∈ range (Encodable.encode : ι → ℕ)
      · obtain ⟨i, rfl⟩ := hn
        simp [Encodable.encode_injective.extend_apply]
      · have hnone : Encodable.decode₂ ι n = none := by
          simpa using not_congr Encodable.decode₂_ne_none_iff |>.mpr hn
        simp [Function.extend_apply' _ _ _ hn, hnone]

/-- On standard Borel spaces, a σ-finite measure is integer-valued exactly when it is
a countable sum of Dirac occurrences, with optional missing indices. -/
theorem isIntegerValued_iff_exists_eq_sum_dirac [StandardBorelSpace X] [SigmaFinite μ] :
    μ.IsIntegerValued ↔ ∃ x : ℕ → Option X, μ = Measure.sum fun n ↦ (x n).elim 0 dirac := by
  refine ⟨IsIntegerValued.exists_eq_sum_dirac, ?_⟩
  rintro ⟨x, rfl⟩
  apply IsIntegerValued.sum
  intro n
  cases x n <;> simp

end MeasureTheory.Measure
