/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.FiniteType

/-!
# The integral degree filtration of one root factor

For an element `x` of an associative rational algebra, the integral span of
`1, x, x²/2!, …, xⁿ/n!` is its divided-power degree stage. These stages exhaust the integral
divided-power lattice and multiply with additive degree bounds. Each stage is finite free.
If the divided powers up to degree `n` are integrally independent, the stage has a displayed
basis of rank `n + 1`.

These are the finite root-factor stages used in a filtered integral triangular factorization
of an enveloping algebra. No nilpotence or commutativity of the ambient algebra is required.
Independence is needed for the basis and the exact degree test, not for the filtration laws.
In particular the filtration is not the filtration by powers of the first divided power:
its integral stages contain the factorial denominators prescribed by divided powers.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Submodule

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The integral span of the divided powers of `x` of degree at most `n`. -/
noncomputable def dividedPowerFiltration (x : A) (n : ℕ) : Submodule ℤ A :=
  span ℤ (Set.range fun k : Fin (n + 1) => dividedPower k.val x)

/-- The defining finite span of a divided-power degree stage. -/
theorem dividedPowerFiltration_def (x : A) (n : ℕ) :
    dividedPowerFiltration x n =
      span ℤ (Set.range fun k : Fin (n + 1) => dividedPower k.val x) := by
  rfl

/-- Stage membership means being an integral linear combination of the bounded divided powers. -/
theorem mem_dividedPowerFiltration_iff {x y : A} {n : ℕ} :
    y ∈ dividedPowerFiltration x n ↔
      ∃ c : Fin (n + 1) → ℤ, ∑ k, c k • dividedPower k.val x = y :=
  Submodule.mem_span_range_iff_exists_fun ℤ

/-- To bound a degree stage, it suffices to bound its divided-power generators. -/
@[simp] theorem dividedPowerFiltration_le_iff {x : A} {n : ℕ} {p : Submodule ℤ A} :
    dividedPowerFiltration x n ≤ p ↔ ∀ k ≤ n, dividedPower k x ∈ p := by
  simp only [dividedPowerFiltration_def, span_le, Set.range_subset_iff]
  exact ⟨fun h k hk => h ⟨k, by omega⟩, fun h k => h k.val (by omega)⟩

/-- A divided power belongs to every stage at least its degree. -/
theorem dividedPower_mem_dividedPowerFiltration (x : A) {k n : ℕ} (hkn : k ≤ n) :
    dividedPower k x ∈ dividedPowerFiltration x n :=
  subset_span ⟨⟨k, by omega⟩, rfl⟩

/-- The divided-power stages increase with degree. -/
theorem dividedPowerFiltration_mono (x : A) : Monotone (dividedPowerFiltration x) := by
  intro m n hmn
  exact dividedPowerFiltration_le_iff.mpr fun k hk =>
    dividedPower_mem_dividedPowerFiltration x (hk.trans hmn)

/-- Degree zero consists precisely of integral multiples of the identity. -/
@[simp] theorem dividedPowerFiltration_zero (x : A) :
    dividedPowerFiltration x 0 = ℤ ∙ (1 : A) := by
  apply le_antisymm
  · exact dividedPowerFiltration_le_iff.mpr fun k hk => by
      have : k = 0 := by omega
      subst k
      simp
  · exact (span_singleton_le_iff_mem _ _).mpr (by
      simpa using dividedPower_mem_dividedPowerFiltration x (le_refl 0))

/-- Every finite degree stage lies in the integral divided-power lattice. -/
theorem dividedPowerFiltration_le_lattice (x : A) (n : ℕ) :
    dividedPowerFiltration x n ≤ dividedPowerLattice x :=
  dividedPowerFiltration_le_iff.mpr fun k _ => dividedPower_mem_dividedPowerLattice x k

/-- The degree stages exhaust the integral divided-power lattice. -/
theorem iSup_dividedPowerFiltration (x : A) :
    ⨆ n, dividedPowerFiltration x n = dividedPowerLattice x := by
  apply le_antisymm
  · exact iSup_le (dividedPowerFiltration_le_lattice x)
  · exact dividedPowerLattice_le_iff.mpr fun n =>
      (le_iSup (dividedPowerFiltration x) n)
        (dividedPower_mem_dividedPowerFiltration x le_rfl)

/-- Every element of the integral divided-power lattice has a finite degree bound. -/
theorem mem_dividedPowerLattice_iff_exists_mem_filtration {x y : A} :
    y ∈ dividedPowerLattice x ↔ ∃ n, y ∈ dividedPowerFiltration x n := by
  rw [← iSup_dividedPowerFiltration, mem_iSup_of_directed _
    (dividedPowerFiltration_mono x).directed_le]

/-- Products of divided-power stages have the sum degree bound. -/
theorem dividedPowerFiltration_mul_le (x : A) (m n : ℕ) :
    dividedPowerFiltration x m * dividedPowerFiltration x n ≤
      dividedPowerFiltration x (m + n) := by
  rw [dividedPowerFiltration_def, dividedPowerFiltration_def, span_mul_span, span_le]
  rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
  dsimp only
  rw [mul_dividedPower]
  exact nsmul_mem (dividedPower_mem_dividedPowerFiltration x (by omega)) _

/-- Multiplication of elements with bounded divided-power degree has the sum degree bound. -/
theorem mul_mem_dividedPowerFiltration {x a b : A} {m n : ℕ}
    (ha : a ∈ dividedPowerFiltration x m) (hb : b ∈ dividedPowerFiltration x n) :
    a * b ∈ dividedPowerFiltration x (m + n) :=
  dividedPowerFiltration_mul_le x m n (mul_mem_mul ha hb)

/-- Each divided-power degree stage is finitely generated, even with dependent generators. -/
instance (x : A) (n : ℕ) : Module.Finite ℤ (dividedPowerFiltration x n) :=
  Module.Finite.span_of_finite ℤ (Set.finite_range _)

/-- A finite divided-power stage is torsion-free over the integers, hence free. -/
instance (x : A) (n : ℕ) : Module.Free ℤ (dividedPowerFiltration x n) := by
  have : Module.IsTorsionFree ℤ A := Module.IsTorsionFree.trans ℚ
  infer_instance

section Independent

variable (x : A)

/-- Integrally independent divided powers up to degree `n` form a basis of that stage. -/
noncomputable def dividedPowerFiltrationBasis (n : ℕ)
    (h : LinearIndependent ℤ (fun k : Fin (n + 1) => dividedPower k.val x)) :
    Module.Basis (Fin (n + 1)) ℤ (dividedPowerFiltration x n) :=
  Module.Basis.span h

/-- A finite-stage basis vector is the indicated divided power in the ambient algebra. -/
@[simp] theorem coe_dividedPowerFiltrationBasis (n : ℕ)
    (h : LinearIndependent ℤ (fun k : Fin (n + 1) => dividedPower k.val x))
    (k : Fin (n + 1)) :
    (dividedPowerFiltrationBasis x n h k : A) = dividedPower k.val x :=
  Module.Basis.coe_span_apply _ _

/-- Independence through degree `n` gives the integral stage rank `n + 1`. -/
@[simp] theorem finrank_dividedPowerFiltration (n : ℕ)
    (h : LinearIndependent ℤ (fun k : Fin (n + 1) => dividedPower k.val x)) :
    Module.finrank ℤ (dividedPowerFiltration x n) = n + 1 := by
  simpa using Module.finrank_eq_card_basis (dividedPowerFiltrationBasis x n h)

variable (h : LinearIndependent ℤ (fun k : ℕ => dividedPower k x))

include h

/-- Under integral independence, a divided power belongs to a stage exactly in its degree range. -/
@[simp] theorem dividedPower_mem_dividedPowerFiltration_iff (k n : ℕ) :
    dividedPower k x ∈ dividedPowerFiltration x n ↔ k ≤ n := by
  refine ⟨fun hk => ?_, dividedPower_mem_dividedPowerFiltration x⟩
  by_contra hkn
  apply h.notMem_span_image (s := Set.Iic n) hkn
  rw [dividedPowerFiltration_def] at hk
  apply span_mono ?_ hk
  rintro _ ⟨i, rfl⟩
  exact ⟨i.val, by simp; omega, rfl⟩

end Independent

end TauCeti.Associative
