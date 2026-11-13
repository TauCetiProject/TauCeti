/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Geometry.Convex.Cone.Alternative
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite vector-partition fibers

For an integer matrix `A`, `Matrix.NatFiber A b` is the type of natural multiplicity vectors
whose image is `b`. Distinct multiplicity vectors are counted separately, including when columns
of `A` coincide. A strictly positive integral covector on the columns bounds every coordinate in
a fiber and gives its finite enumeration. The count is defined for every matrix as the natural
cardinality of its fiber, so it is zero for infinite fibers. Under a positive covector it counts
the finite solution set and is independent of that covector.

The existence of a positive integral covector is equivalent to the real kernel containing no
nonzero nonnegative vector. Its construction uses the integral form of Tucker's theorem in
`TauCeti.Geometry.Convex.Cone.Alternative`, including that theorem's denominator clearing.
Neither full row rank nor unimodularity is needed for these finiteness results.
-/

public section

namespace Matrix

variable {m : Type*} {n : Type*} [Fintype n]

/-- The natural multiplicity vectors with image `b` under the integer matrix `A`. -/
abbrev NatFiber (A : Matrix m n ℤ) (b : m → ℤ) :=
  {c : n → ℕ // A *ᵥ (fun j => (c j : ℤ)) = b}

/-- The vector-partition count, counting distinct multiplicity vectors even when columns
coincide. It is zero for infinite fibers; a positive integral covector guarantees finiteness. -/
noncomputable def natFiberCount (A : Matrix m n ℤ) (b : m → ℤ) : ℕ :=
  Nat.card (NatFiber A b)

/-- The total vector-partition count is the natural cardinality of the solution type. -/
theorem natFiberCount_def (A : Matrix m n ℤ) (b : m → ℤ) :
    A.natFiberCount b = Nat.card (NatFiber A b) := by
  rfl

variable [Fintype m]

/-- The height of a multiplicity vector is the height of its image. -/
theorem NatFiber.dotProduct_eq {A : Matrix m n ℤ} {b : m → ℤ} (c : NatFiber A b)
    (h : m → ℤ) : (h ᵥ* A) ⬝ᵥ (fun j => (c.1 j : ℤ)) = h ⬝ᵥ b := by
  rw [← dotProduct_mulVec, c.2]

/-- Each multiplicity is bounded by the integral height of the right-hand side. -/
theorem NatFiber.apply_le_toNat_dotProduct {A : Matrix m n ℤ} {b : m → ℤ} (c : NatFiber A b)
    {h : m → ℤ} (hh : ∀ j, 0 < (h ᵥ* A) j) (j : n) :
    c.1 j ≤ (h ⬝ᵥ b).toNat := by
  have hterm : ∀ k, 0 ≤ (h ᵥ* A) k * (c.1 k : ℤ) :=
    fun k => mul_nonneg (hh k).le (Int.natCast_nonneg _)
  have hle : (c.1 j : ℤ) ≤ h ⬝ᵥ b := by
    rw [← c.dotProduct_eq h]
    exact (le_mul_of_one_le_left (Int.natCast_nonneg _) (hh j)).trans
      (Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j))
  omega

/-- A bounded candidate enumeration for a natural fiber. If `h` is positive on every column,
`mem_natFiberFinset_iff_of_vecMul_pos` identifies this enumeration with the entire fiber. -/
def natFiberFinset [DecidableEq n] (A : Matrix m n ℤ) (h b : m → ℤ) : Finset (n → ℕ) :=
  (Fintype.piFinset fun _ : n => Finset.Iic (h ⬝ᵥ b).toNat).filter
    (fun c => A *ᵥ (fun j => (c j : ℤ)) = b)

/-- The candidate enumeration filters the coordinate box bounded by the integral height. -/
theorem natFiberFinset_def [DecidableEq n] (A : Matrix m n ℤ) (h b : m → ℤ) :
    A.natFiberFinset h b =
      (Fintype.piFinset fun _ : n => Finset.Iic (h ⬝ᵥ b).toNat).filter
        (fun c => A *ᵥ (fun j => (c j : ℤ)) = b) := by
  rfl

/-- The candidate enumeration consists of solutions within its coordinate box, without any
positivity assumption on the chosen covector. -/
@[grind =] theorem mem_natFiberFinset_iff [DecidableEq n] (A : Matrix m n ℤ) (h b : m → ℤ)
    (c : n → ℕ) : c ∈ A.natFiberFinset h b ↔
      (∀ j, c j ≤ (h ⬝ᵥ b).toNat) ∧ A *ᵥ (fun j => (c j : ℤ)) = b := by
  simp only [natFiberFinset_def, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Iic]

/-- Under a positive height, the bounded enumeration contains exactly the solutions. -/
@[simp] theorem mem_natFiberFinset_iff_of_vecMul_pos [DecidableEq n] (A : Matrix m n ℤ) {h : m → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) (c : n → ℕ) :
    c ∈ A.natFiberFinset h b ↔ A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [mem_natFiberFinset_iff]
  exact ⟨And.right, fun hc => ⟨fun j => NatFiber.apply_le_toNat_dotProduct ⟨c, hc⟩ hh j, hc⟩⟩

/-- Natural fibers are finite whenever an integral height is strictly positive on all columns. -/
theorem finite_natFiber (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    Finite (NatFiber A b) := by
  classical
  obtain ⟨h, hh⟩ := hA
  have hf : {c : n → ℕ | A *ᵥ (fun j => (c j : ℤ)) = b}.Finite :=
    (A.natFiberFinset h b).finite_toSet.subset
      (fun c hc => (mem_natFiberFinset_iff_of_vecMul_pos A hh b c).mpr hc)
  exact hf.to_subtype

/-- A positive height computes the count by filtering an explicit finite coordinate box. -/
theorem card_natFiberFinset [DecidableEq n] (A : Matrix m n ℤ) {h : m → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    (A.natFiberFinset h b).card = A.natFiberCount b := by
  rw [natFiberCount_def, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c =>
    mem_natFiberFinset_iff_of_vecMul_pos A hh b c)

/-- The count is positive precisely when there is a natural solution. -/
@[simp] theorem natFiberCount_pos_iff (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    0 < A.natFiberCount b ↔ ∃ c : n → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [natFiberCount_def, Nat.card_pos_iff, nonempty_subtype]
  exact and_iff_left (A.finite_natFiber hA b)

/-- The count vanishes precisely when there is no natural solution. -/
@[simp] theorem natFiberCount_eq_zero_iff (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    A.natFiberCount b = 0 ↔ ¬ ∃ c : n → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [← natFiberCount_pos_iff A hA b, Nat.pos_iff_ne_zero, not_ne_iff]

/-- The zero vector is the unique natural solution with image zero. -/
theorem NatFiber.eq_zero {A : Matrix m n ℤ}
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (c : NatFiber A 0) : c.1 = 0 := by
  obtain ⟨h, hh⟩ := hA
  ext j
  have := c.apply_le_toNat_dotProduct hh j
  simpa using this

/-- The fiber at zero has exactly one point, including for an empty column family. -/
@[simp] theorem natFiberCount_zero (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) : A.natFiberCount 0 = 1 := by
  rw [natFiberCount_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun c d => Subtype.ext ((c.eq_zero hA).trans (d.eq_zero hA).symm)⟩,
    ⟨⟨0, by ext i; simp [mulVec, dotProduct]⟩⟩⟩

end Matrix
