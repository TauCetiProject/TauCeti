/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Residue classes over a subring

For a subring `R` of a ring `A`, `R.residueClass g x₀` is the class
`x₀ + g R^ι`, where `g` is a unit of `A`. Compactness passes from the subring
to each class; for finite `ι`, openness passes as well. The product Haar measure
of a class is `Δ(g)^|ι| μ(R)^|ι|`, where `Δ` is Mathlib's distributive Haar
character. In particular, when `μ(R) = 1`, its volume is `Δ(g)^|ι|`.
These classes are the domains of local quadratic Gauss integrals.
-/

public section

open MeasureTheory
open scoped Pointwise ENNReal

namespace Subring

variable {A ι : Type*} [Ring A] (R : Subring A)

/-- The class `x₀ + g R^ι`, described by its coordinates. -/
def residueClass (g : Aˣ) (x₀ : ι → A) : Set (ι → A) :=
  {x | ∀ i, (↑g⁻¹ : A) * (x i - x₀ i) ∈ R}

@[simp]
theorem mem_residueClass (g : Aˣ) (x₀ x : ι → A) :
    x ∈ R.residueClass g x₀ ↔ ∀ i, (↑g⁻¹ : A) * (x i - x₀ i) ∈ R := Iff.rfl

/-- Membership in a class is equivalent to an integral displacement. -/
theorem mem_residueClass_iff (g : Aˣ) (x₀ x : ι → A) :
    x ∈ R.residueClass g x₀ ↔ ∃ y : ι → R, x = x₀ + g • (fun i ↦ (y i : A)) := by
  constructor
  · intro hx
    refine ⟨fun i ↦ ⟨_, hx i⟩, ?_⟩
    ext i
    simp [Units.smul_def, ← mul_assoc]
  · rintro ⟨y, rfl⟩
    simp [residueClass, Units.smul_def, ← mul_assoc]

/-- A class is a product of one-dimensional affine images of the subring. -/
theorem residueClass_eq_pi (g : Aˣ) (x₀ : ι → A) :
    R.residueClass g x₀ = Set.pi Set.univ
      (fun i ↦ (fun y : A ↦ x₀ i + g * y) '' (R : Set A)) := by
  ext x
  simp only [mem_residueClass, Set.mem_univ_pi, Set.mem_image]
  constructor
  · intro h i
    refine ⟨_, h i, ?_⟩
    simp [← mul_assoc]
  · intro h i
    obtain ⟨y, hy, hi⟩ := h i
    rw [← hi]
    simpa [← mul_assoc] using hy

/-- Changing the centre within a class does not change the class. -/
theorem residueClass_eq_of_mem (g : Aˣ) {x₀ x₁ : ι → A}
    (h : x₁ ∈ R.residueClass g x₀) : R.residueClass g x₁ = R.residueClass g x₀ := by
  ext x
  constructor
  · intro hx i
    have heq : (↑g⁻¹ : A) * (x i - x₀ i) =
        (↑g⁻¹ : A) * (x i - x₁ i) + (↑g⁻¹ : A) * (x₁ i - x₀ i) := by noncomm_ring
    rw [heq]
    exact R.add_mem (hx i) (h i)
  · intro hx i
    have heq : (↑g⁻¹ : A) * (x i - x₁ i) =
        (↑g⁻¹ : A) * (x i - x₀ i) - (↑g⁻¹ : A) * (x₁ i - x₀ i) := by noncomm_ring
    rw [heq]
    exact R.sub_mem (hx i) (h i)

/-- Adding two class members adds their centres. -/
theorem add_mem_residueClass (g : Aˣ) {x₀ y₀ x y : ι → A}
    (hx : x ∈ R.residueClass g x₀) (hy : y ∈ R.residueClass g y₀) :
    x + y ∈ R.residueClass g (x₀ + y₀) := by
  intro i
  convert R.add_mem (hx i) (hy i) using 1
  · dsimp
    noncomm_ring

/-- Negation takes a class to the class with opposite centre. -/
theorem neg_mem_residueClass (g : Aˣ) {x₀ x : ι → A}
    (hx : x ∈ R.residueClass g x₀) : -x ∈ R.residueClass g (-x₀) := by
  intro i
  convert R.neg_mem (hx i) using 1
  · dsimp
    noncomm_ring

/-- Two classes of the same scale agree exactly when their centres are congruent. -/
theorem residueClass_eq_iff (g : Aˣ) (x₀ x₁ : ι → A) :
    R.residueClass g x₁ = R.residueClass g x₀ ↔ x₁ ∈ R.residueClass g x₀ := by
  constructor
  · intro h
    rw [← h]
    simp
  · exact R.residueClass_eq_of_mem g

section Topology

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- A class of a compact subring is compact. -/
theorem isCompact_residueClass (hR : IsCompact (R : Set A)) (g : Aˣ) (x₀ : ι → A) :
    IsCompact (R.residueClass g x₀) := by
  rw [R.residueClass_eq_pi]
  exact isCompact_univ_pi fun i ↦ hR.image (by fun_prop)

/-- A class of an open subring is open. -/
theorem isOpen_residueClass [Finite ι] (hR : IsOpen (R : Set A)) (g : Aˣ) (x₀ : ι → A) :
    IsOpen (R.residueClass g x₀) := by
  have heq : R.residueClass g x₀ =
      ⋂ i, (fun x : ι → A ↦ (↑g⁻¹ : A) * (x i - x₀ i)) ⁻¹' (R : Set A) := by
    ext x
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ hR.preimage (by fun_prop)

end Topology

section Measure

variable [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A] [Fintype ι]
  (μ : Measure A) [SigmaFinite μ] [μ.IsAddHaarMeasure] [μ.Regular]

/-- The volume of a class for the product Haar measure, without normalizing `μ R`. -/
theorem measure_residueClass (g : Aˣ) (x₀ : ι → A) :
    Measure.pi (fun _ : ι ↦ μ) (R.residueClass g x₀) =
      (distribHaarChar A g : ℝ≥0∞) ^ Fintype.card ι * μ R ^ Fintype.card ι := by
  rw [R.residueClass_eq_pi, Measure.pi_pi]
  have hcoord (i : ι) : μ ((fun y : A ↦ x₀ i + g * y) '' (R : Set A)) =
      (distribHaarChar A g : ℝ≥0∞) * μ R := by
    rw [← Set.image_image]
    rw [Set.image_add_left, measure_preimage_add]
    exact (distribHaarChar_mul μ g (R : Set A)).symm
  simp_rw [hcoord]
  simp [mul_pow]

/-- For a Haar measure giving the subring volume one, a class has volume `Δ(g)^|ι|`. -/
theorem measure_residueClass_of_measure_eq_one (hμ : μ R = 1) (g : Aˣ) (x₀ : ι → A) :
    Measure.pi (fun _ : ι ↦ μ) (R.residueClass g x₀) =
      (distribHaarChar A g : ℝ≥0∞) ^ Fintype.card ι := by
  simp [R.measure_residueClass μ, hμ]

end Measure

end Subring
