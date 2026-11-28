/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar

/-!
# Haar characters on finite products

On a finite product the Haar character is the product of the factors on the coordinates.
These formulas assemble local change of variables into a global one.
-/

public noncomputable section

open MeasureTheory Measure Set
open scoped Pointwise ENNReal

namespace MeasureTheory

/-- The Haar character of a coordinatewise action on a finite product is the product of
its coordinate Haar characters. -/
@[simp]
theorem distribHaarChar_pi {ι : Type*} [Fintype ι] {A : ι → Type*} {G : Type*} [Group G]
    [∀ i, AddCommGroup (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalAddGroup (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, SecondCountableTopology (A i)]
    [∀ i, DistribMulAction G (A i)] [∀ i, ContinuousConstSMul G (A i)]
    (g : G) :
    distribHaarChar (∀ i, A i) g = ∏ i, distribHaarChar (A i) g := by
  classical
  let _ (i : ι) : MeasurableSpace (A i) := borel _
  have _ (i : ι) : BorelSpace (A i) := ⟨rfl⟩
  let K (i : ι) : TopologicalSpace.PositiveCompacts (A i) := Classical.choice inferInstance
  let μ (i : ι) : Measure (A i) := addHaarMeasure (K i)
  have hμ (i : ι) : μ i (K i) = 1 := addHaarMeasure_self
  let s : Set (∀ i, A i) := univ.pi fun i ↦ (K i : Set (A i))
  have hs : Measure.pi μ s = 1 := by simp [s, Measure.pi_pi, hμ]
  have hgs : g • s = univ.pi fun i ↦ g • (K i : Set (A i)) := by
    ext x
    simp only [mem_smul_set_iff_inv_smul_mem, s, mem_univ_pi, Pi.smul_apply]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ) (s := s)
    (by simp [hs]) (by simp [hs]) ?_
  rw [hgs, hs, mul_one, Measure.pi_pi]
  push_cast
  exact Finset.prod_congr rfl fun i _ ↦ by rw [← distribHaarChar_mul, hμ, mul_one]

/-- The Haar character on a product is the product of the two Haar characters. -/
@[simp]
theorem distribHaarChar_prod {A B G : Type*}
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [SecondCountableTopology B]
    [Group G] [DistribMulAction G A] [ContinuousConstSMul G A]
    [DistribMulAction G B] [ContinuousConstSMul G B]
    (g : G) :
    distribHaarChar (A × B) g = distribHaarChar A g * distribHaarChar B g := by
  borelize A B
  let μ : Measure A := Measure.addHaar
  let ν : Measure B := Measure.addHaar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  obtain ⟨L⟩ : Nonempty (TopologicalSpace.PositiveCompacts B) := inferInstance
  have hKL : g • ((K : Set A) ×ˢ (L : Set B)) =
      (g • (K : Set A)) ×ˢ (g • (L : Set B)) := by
    ext x
    simp [mem_smul_set_iff_inv_smul_mem]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.prod ν)
    (s := (K : Set A) ×ˢ (L : Set B)) ?_ ?_ ?_
  · rw [Measure.prod_prod]
    exact mul_ne_zero (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
      (Measure.measure_pos_of_nonempty_interior ν L.interior_nonempty).ne'
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top K.isCompact.measure_ne_top L.isCompact.measure_ne_top
  · rw [hKL, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul,
      ← distribHaarChar_mul]
    push_cast
    ring

end MeasureTheory
