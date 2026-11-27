/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Residue classes over a subring

For a subring `R` of a ring `A`, `R.residueClass g x₀` is the class
`x₀ + g R^ι`, where `g` is a unit of `A`. It is the additive coset through `x₀` of the
lattice `R.latticeMultiple g = g R^ι`, so centre independence comes from Mathlib's coset API.
These classes are the domains of local quadratic Gauss integrals.
-/

public section

open scoped Pointwise

namespace Subring

variable {A ι : Type*} [Ring A] (R : Subring A)

/-- The lattice `g R^ι` of coordinate vectors whose coordinates lie in `g R`. -/
def latticeMultiple (g : Aˣ) : AddSubgroup (ι → A) :=
  AddSubgroup.pi Set.univ fun _ ↦ R.toAddSubgroup.comap (AddMonoidHom.mulLeft (↑g⁻¹ : A))

@[simp]
theorem mem_latticeMultiple (g : Aˣ) (d : ι → A) :
    d ∈ R.latticeMultiple g ↔ ∀ i, (↑g⁻¹ : A) * d i ∈ R := by
  simp [latticeMultiple, AddSubgroup.mem_pi]

/-- The class `x₀ + g R^ι`, described by its coordinates. -/
def residueClass (g : Aˣ) (x₀ : ι → A) : Set (ι → A) :=
  {x | ∀ i, (↑g⁻¹ : A) * (x i - x₀ i) ∈ R}

@[simp]
theorem mem_residueClass (g : Aˣ) (x₀ x : ι → A) :
    x ∈ R.residueClass g x₀ ↔ ∀ i, (↑g⁻¹ : A) * (x i - x₀ i) ∈ R := Iff.rfl

/-- Membership in a class is equivalent to an integral displacement. -/
theorem mem_residueClass_iff_exists (g : Aˣ) (x₀ x : ι → A) :
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

/-- A class is the additive coset through its centre of the lattice `g R^ι`. -/
theorem residueClass_eq_vadd (g : Aˣ) (x₀ : ι → A) :
    R.residueClass g x₀ = x₀ +ᵥ ((R.latticeMultiple g : AddSubgroup (ι → A)) : Set (ι → A)) := by
  ext x
  simp [mem_leftAddCoset_iff, neg_add_eq_sub]

/-- Two classes of the same scale agree exactly when their centres are congruent. -/
theorem residueClass_eq_iff (g : Aˣ) (x₀ x₁ : ι → A) :
    R.residueClass g x₁ = R.residueClass g x₀ ↔ x₁ ∈ R.residueClass g x₀ := by
  rw [residueClass_eq_vadd, residueClass_eq_vadd, leftAddCoset_eq_iff, ← neg_mem_iff]
  simp [mem_leftAddCoset_iff, neg_add_eq_sub]

/-- Changing the centre within a class does not change the class. -/
theorem residueClass_eq_of_mem (g : Aˣ) {x₀ x₁ : ι → A}
    (h : x₁ ∈ R.residueClass g x₀) : R.residueClass g x₁ = R.residueClass g x₀ :=
  (R.residueClass_eq_iff g x₀ x₁).2 h

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

/-- Translating a class member by an element of the lattice `g R^ι` stays in the class. -/
theorem add_mem_residueClass_of_mem_latticeMultiple (g : Aˣ) {x₀ x d : ι → A}
    (hx : x ∈ R.residueClass g x₀) (hd : d ∈ R.latticeMultiple g) :
    x + d ∈ R.residueClass g x₀ := by
  intro i
  convert R.add_mem (hx i) ((R.mem_latticeMultiple g d).1 hd i) using 1
  · dsimp
    noncomm_ring

end Subring
