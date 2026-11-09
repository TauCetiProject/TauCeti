/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.DegreeTail
public import TauCeti.RingTheory.FilteredAlgebra.Basic
public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# The decreasing filtration defined by an integral degree

An additive integral degree on the grading monoid defines the sum of the
homogeneous components of degree at least `n`. When the grading has no negative
degree components, these sums are two-sided ideals and form a separated
decreasing multiplicative filtration. No commutativity, freeness, or local
finiteness assumption on the graded algebra is required.

The filtration measures how far an element lies in positive degree and defines
the corresponding degree completion. Unlike the strict positive cutoffs used for
positively graded Lie algebras, the order-zero ideal includes the unit component.

## Attribution

Adapted from `Mei/RingTheory/GradedAlgebra/DegreeFiltration.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). Original copyright and author credit
are retained.
-/

public section

namespace TauCeti.GradedAlgebra

open TauCeti.DirectSum

section Mul

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [SetLike.GradedMul 𝒜] (d : ι →+ ℤ)

/-- Multiplication adds the lower degree bounds. -/
theorem degreeTail_mul_le (m n : ℕ) :
    degreeTail 𝒜 d m * degreeTail 𝒜 d n ≤ degreeTail 𝒜 d (m + n) := by
  simp only [degreeTail_def, Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
  intro i hi j hj
  apply (mul_le_grade_add 𝒜 j i).trans
  have hij : ((m + n : ℕ) : ℤ) ≤ d (j + i) := by
    simpa only [map_add, Nat.cast_add] using add_le_add hj hi
  simpa only [degreeTail_def] using le_degreeTail 𝒜 d hij

end Mul

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid ι] (𝒜 : ι → Submodule R A) (d : ι →+ ℤ)
  [DecidableEq ι] [_root_.GradedAlgebra 𝒜]

variable (hneg : ∀ i, d i < 0 → 𝒜 i = ⊥)

/-- The ideal of elements supported in degrees at least `n`. -/
def degreeIdeal (n : ℕ) : Ideal A where
  carrier := degreeTail 𝒜 d n
  zero_mem' := (degreeTail 𝒜 d n).zero_mem
  add_mem' := (degreeTail 𝒜 d n).add_mem
  smul_mem' a x hx := by
    have ha : a ∈ degreeTail 𝒜 d 0 := by rw [degreeTail_zero 𝒜 d hneg]; trivial
    simpa only [zero_add, smul_eq_mul, SetLike.mem_coe] using
      degreeTail_mul_le 𝒜 d 0 n (Submodule.mul_mem_mul ha hx)

/-- Ideal membership agrees with membership in the scalar degree tail. -/
@[simp]
theorem mem_degreeIdeal_iff (n : ℕ) (x : A) :
    x ∈ degreeIdeal 𝒜 d hneg n ↔ x ∈ degreeTail 𝒜 d n := Iff.rfl

/-- Restricting the degree ideal to the scalar ring recovers its degree tail. -/
@[simp]
theorem degreeIdeal_restrictScalars (n : ℕ) :
    (degreeIdeal 𝒜 d hneg n).restrictScalars R = degreeTail 𝒜 d n := by
  ext x
  exact mem_degreeIdeal_iff 𝒜 d hneg n x

/-- A homogeneous component above the cutoff is contained in the degree ideal. -/
theorem le_degreeIdeal {n : ℕ} {i : ι} (hi : (n : ℤ) ≤ d i) :
    ∀ x ∈ 𝒜 i, x ∈ degreeIdeal 𝒜 d hneg n := fun x hx =>
  (mem_degreeIdeal_iff 𝒜 d hneg n x).mpr (le_degreeTail 𝒜 d hi hx)

/-- To contain the degree ideal, it suffices to contain its homogeneous components. -/
theorem degreeIdeal_le_iff (n : ℕ) (K : Ideal A) :
    degreeIdeal 𝒜 d hneg n ≤ K ↔
      ∀ i, (n : ℤ) ≤ d i → ∀ x ∈ 𝒜 i, x ∈ K := by
  constructor
  · intro h i hi x hx
    exact h (le_degreeIdeal 𝒜 d hneg hi x hx)
  · intro h x hx
    have ht : degreeTail 𝒜 d n ≤ K.restrictScalars R := by
      simp only [degreeTail_def, iSup_le_iff]
      exact h
    exact ht ((mem_degreeIdeal_iff 𝒜 d hneg n x).mp hx)

/-- The degree ideals are two-sided. -/
instance degreeIdeal_isTwoSided (n : ℕ) : (degreeIdeal 𝒜 d hneg n).IsTwoSided where
  mul_mem_of_left a hx := by
    have ha : a ∈ degreeTail 𝒜 d 0 := by rw [degreeTail_zero 𝒜 d hneg]; trivial
    apply (mem_degreeIdeal_iff 𝒜 d hneg n _).mpr
    simpa only [add_zero] using degreeTail_mul_le 𝒜 d n 0 (Submodule.mul_mem_mul hx ha)

/-- The decreasing degree filtration of a nonnegatively graded algebra. -/
def degreeFiltration : TauCeti.AlgFiltration A where
  ideal := degreeIdeal 𝒜 d hneg
  isTwoSided _ := inferInstance
  antitone := degreeTail_antitone 𝒜 d
  ideal_zero := by ext x; simp [degreeTail_zero 𝒜 d hneg]
  mul_mem {m n} {x y} hx hy := degreeTail_mul_le 𝒜 d m n (Submodule.mul_mem_mul hx hy)

/-- The terms of the degree filtration are the degree ideals. -/
@[simp]
theorem degreeFiltration_ideal (n : ℕ) :
    (degreeFiltration 𝒜 d hneg).ideal n = degreeIdeal 𝒜 d hneg n := (rfl)

/-- The ideal degree filtration is separated. -/
theorem iInf_degreeIdeal_eq_bot : (⨅ n : ℕ, degreeIdeal 𝒜 d hneg n) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have ht : x ∈ ⨅ n : ℕ, degreeTail 𝒜 d n := by
    apply (Submodule.mem_iInf _).mpr
    intro n
    exact (mem_degreeIdeal_iff 𝒜 d hneg n x).mp
      ((iInf_le (fun n => degreeIdeal 𝒜 d hneg n) n) hx)
  rwa [iInf_degreeTail_eq_bot, Submodule.mem_bot] at ht

end TauCeti.GradedAlgebra
