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

The filtration measures how far an element lies in positive degree. The order-zero
ideal is the whole algebra, unit component included. This filtration feeds
`TauCeti.UniversalEnvelopingAlgebra.degreeFiltration`.

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
  [AddMonoid ι] (𝒜 : ι → Submodule R A) [SetLike.GradedMul 𝒜] (d : ι →+ ℤ)

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
  [AddMonoid ι] (𝒜 : ι → Submodule R A) (d : ι →+ ℤ)
  [DecidableEq ι] [_root_.GradedAlgebra 𝒜]

/-- Every element lies in the degree-zero tail of a nonnegatively graded algebra. -/
theorem mem_degreeTail_zero (hneg : ∀ i, d i < 0 → 𝒜 i = ⊥) (a : A) :
    a ∈ degreeTail 𝒜 d 0 := by
  rw [degreeTail_zero 𝒜 d hneg]
  trivial

variable (hneg : ∀ i, d i < 0 → 𝒜 i = ⊥)

/-- The ideal of elements supported in degrees at least `n`. -/
def degreeIdeal (n : ℕ) : Ideal A where
  carrier := degreeTail 𝒜 d n
  zero_mem' := (degreeTail 𝒜 d n).zero_mem
  add_mem' := (degreeTail 𝒜 d n).add_mem
  smul_mem' a x hx := by
    simpa only [zero_add, smul_eq_mul, SetLike.mem_coe] using
      degreeTail_mul_le 𝒜 d 0 n
        (Submodule.mul_mem_mul (mem_degreeTail_zero 𝒜 d hneg a) hx)

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
      intro i hi y hy
      exact (Submodule.restrictScalars_mem R K y).mpr (h i hi y hy)
    exact ht ((mem_degreeIdeal_iff 𝒜 d hneg n x).mp hx)

/-- The degree ideals are two-sided. -/
instance degreeIdeal_isTwoSided (n : ℕ) : (degreeIdeal 𝒜 d hneg n).IsTwoSided where
  mul_mem_of_left a hx := by
    apply (mem_degreeIdeal_iff 𝒜 d hneg n _).mpr
    simpa only [add_zero] using degreeTail_mul_le 𝒜 d n 0
      (Submodule.mul_mem_mul ((mem_degreeIdeal_iff 𝒜 d hneg n _).mp hx)
        (mem_degreeTail_zero 𝒜 d hneg a))

/-- Higher degree ideals are smaller. -/
theorem degreeIdeal_antitone : Antitone (degreeIdeal 𝒜 d hneg) := fun _ _ hmn _ hx =>
  (mem_degreeIdeal_iff 𝒜 d hneg _ _).mpr
    (degreeTail_antitone 𝒜 d hmn ((mem_degreeIdeal_iff 𝒜 d hneg _ _).mp hx))

/-- Multiplication adds the lower degree bounds of the degree ideals. -/
theorem degreeIdeal_mul_mem {m n : ℕ} {x y : A} (hx : x ∈ degreeIdeal 𝒜 d hneg m)
    (hy : y ∈ degreeIdeal 𝒜 d hneg n) : x * y ∈ degreeIdeal 𝒜 d hneg (m + n) :=
  (mem_degreeIdeal_iff 𝒜 d hneg _ _).mpr <| degreeTail_mul_le 𝒜 d m n <|
    Submodule.mul_mem_mul ((mem_degreeIdeal_iff 𝒜 d hneg _ _).mp hx)
      ((mem_degreeIdeal_iff 𝒜 d hneg _ _).mp hy)

/-- The degree ideal of order zero is the whole algebra. -/
@[simp]
theorem degreeIdeal_zero : degreeIdeal 𝒜 d hneg 0 = ⊤ := by
  rw [eq_top_iff]
  exact fun x _ => (mem_degreeIdeal_iff 𝒜 d hneg 0 x).mpr (mem_degreeTail_zero 𝒜 d hneg x)

/-- The decreasing degree filtration of a nonnegatively graded algebra. -/
def degreeFiltration : TauCeti.AlgFiltration A where
  ideal := degreeIdeal 𝒜 d hneg
  isTwoSided _ := inferInstance
  antitone := degreeIdeal_antitone 𝒜 d hneg
  ideal_zero := degreeIdeal_zero 𝒜 d hneg
  mul_mem := degreeIdeal_mul_mem 𝒜 d hneg

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

/-- Membership in the degree filtration means that all components of lower degree vanish. -/
theorem mem_degreeFiltration_ideal_iff {n : ℕ} {x : A} :
    x ∈ (degreeFiltration 𝒜 d hneg).ideal n ↔
      ∀ i, d i < n → (_root_.DirectSum.decompose 𝒜 x i : A) = 0 := by
  rw [degreeFiltration_ideal, mem_degreeIdeal_iff, TauCeti.DirectSum.mem_degreeTail_iff]

end TauCeti.GradedAlgebra
