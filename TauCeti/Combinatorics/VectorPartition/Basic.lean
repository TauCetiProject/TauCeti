/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Geometry.Convex.Cone.Alternative
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite vector-partition fibres

For an integer matrix `A`, `Matrix.NatFibre A b` is the type of natural multiplicity vectors
whose image is `b`. Distinct multiplicity vectors are counted separately, including when columns
of `A` coincide. A strictly positive integral covector on the columns bounds every coordinate in
a fibre and gives its finite enumeration. The count requires the existence of such a covector;
it is independent of its choice.

The existence of a positive integral covector is equivalent to the real kernel containing no
nonzero nonnegative vector. Its construction uses the integral form of Tucker's theorem in
`TauCeti.Geometry.Convex.Cone.Alternative`, including that theorem's denominator clearing.
Neither full row rank nor unimodularity is needed for these finiteness results.
-/

public section

namespace Matrix

variable {m : Type*} {n : Type*} [Fintype m] [Fintype n]

/-- The natural multiplicity vectors with image `b` under the integer matrix `A`. -/
abbrev NatFibre (A : Matrix m n ℤ) (b : m → ℤ) :=
  {c : n → ℕ // A *ᵥ (fun j => (c j : ℤ)) = b}

/-- An integer matrix has a covector strictly positive on every column exactly when its real
kernel contains no nonzero nonnegative vector. -/
theorem exists_pos_vecMul_iff (A : Matrix m n ℤ) :
    (∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) ↔
      ∀ x : n → ℝ, 0 ≤ x → A.map (Int.castRingHom ℝ) *ᵥ x = 0 → x = 0 := by
  constructor
  · rintro ⟨h, hh⟩ x hx hAx
    have hhR : ∀ j, 0 < ((fun i => (h i : ℝ)) ᵥ* A.map (Int.castRingHom ℝ)) j := by
      intro j
      simpa only [← Int.coe_castRingHom, RingHom.map_vecMul, Function.comp_def] using
        (Int.cast_pos.mpr (hh j) : (0 : ℝ) < ((h ᵥ* A) j : ℝ))
    apply (TauCeti.dotProduct_eq_zero_iff_of_pos hhR hx).mp
    rw [← dotProduct_mulVec, hAx, dotProduct_zero]
  · intro hA
    classical
    obtain ⟨c, f, hc, _, hcf⟩ :=
      TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos
        (fun j => fun i => A i j)
    have hcA : A *ᵥ (fun j => (c j : ℤ)) = 0 := by
      ext i
      simpa [mulVec, dotProduct, Finset.sum_apply, nsmul_eq_mul, mul_comm] using congrFun hc i
    have hcR : A.map (Int.castRingHom ℝ) *ᵥ (fun j => (c j : ℝ)) = 0 := by
      ext i
      have hi := congrFun hcA i
      simpa only [RingHom.map_mulVec, Function.comp_def, Int.coe_castRingHom,
        Int.cast_natCast, Pi.zero_apply, Int.cast_zero] using congrArg (Int.castRingHom ℝ) hi
    have hc0 : c = 0 := by
      have hz := hA (fun j => (c j : ℝ)) (fun _ => Nat.cast_nonneg _) hcR
      ext j
      simpa only [Pi.zero_apply, Nat.cast_eq_zero] using congrFun hz j
    let h : m → ℤ := fun i => f (Pi.single i 1)
    have hf (v : m → ℤ) : f v = h ⬝ᵥ v := by
      conv_lhs => rw [pi_eq_sum_univ' v]
      simp only [map_sum, dotProduct, h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul]
      simp only [zsmul_eq_mul, Int.cast_id]
      exact mul_comm _ _
    refine ⟨h, fun j => ?_⟩
    simpa only [hc0, Pi.zero_apply, Nat.cast_zero, zero_add, hf, vecMul] using hcf j

/-- The height of a multiplicity vector is the height of its image. -/
theorem NatFibre.dotProduct_eq (A : Matrix m n ℤ) {b : m → ℤ} (c : NatFibre A b)
    (h : m → ℤ) : (h ᵥ* A) ⬝ᵥ (fun j => (c.1 j : ℤ)) = h ⬝ᵥ b := by
  rw [← dotProduct_mulVec, c.2]

/-- Each multiplicity is bounded by the integral height of the right-hand side. -/
theorem NatFibre.apply_le_height (A : Matrix m n ℤ) {b : m → ℤ} (c : NatFibre A b)
    {h : m → ℤ} (hh : ∀ j, 0 < (h ᵥ* A) j) (j : n) :
    c.1 j ≤ (h ⬝ᵥ b).toNat := by
  have hterm : ∀ k, 0 ≤ (h ᵥ* A) k * (c.1 k : ℤ) :=
    fun k => mul_nonneg (hh k).le (Int.natCast_nonneg _)
  have hle : (c.1 j : ℤ) ≤ h ⬝ᵥ b := by
    rw [← c.dotProduct_eq A h]
    exact (le_mul_of_one_le_left (Int.natCast_nonneg _) (hh j)).trans
      (Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j))
  omega

/-- A bounded candidate enumeration for a natural fibre. If `h` is positive on every column,
`mem_natFibreFinset` identifies this enumeration with the entire fibre. -/
def natFibreFinset [DecidableEq n] (A : Matrix m n ℤ) (h b : m → ℤ) : Finset (n → ℕ) :=
  (Fintype.piFinset fun _ : n => Finset.Iic (h ⬝ᵥ b).toNat).filter
    (fun c => A *ᵥ (fun j => (c j : ℤ)) = b)

/-- The candidate enumeration consists of solutions within its coordinate box, without any
positivity assumption on the chosen covector. -/
theorem mem_natFibreFinset_iff [DecidableEq n] (A : Matrix m n ℤ) (h b : m → ℤ)
    (c : n → ℕ) : c ∈ A.natFibreFinset h b ↔
      (∀ j, c j ≤ (h ⬝ᵥ b).toNat) ∧ A *ᵥ (fun j => (c j : ℤ)) = b := by
  simp only [natFibreFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Iic]

/-- Under a positive height, the bounded enumeration contains exactly the solutions. -/
@[simp] theorem mem_natFibreFinset [DecidableEq n] (A : Matrix m n ℤ) {h : m → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) (c : n → ℕ) :
    c ∈ A.natFibreFinset h b ↔ A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [mem_natFibreFinset_iff]
  exact ⟨And.right, fun hc => ⟨fun j => NatFibre.apply_le_height A ⟨c, hc⟩ hh j, hc⟩⟩

/-- Natural fibres are finite whenever an integral height is strictly positive on all columns. -/
theorem finite_natFibre (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    Finite (NatFibre A b) := by
  classical
  obtain ⟨h, hh⟩ := hA
  have hf : {c : n → ℕ | A *ᵥ (fun j => (c j : ℤ)) = b}.Finite :=
    (A.natFibreFinset h b).finite_toSet.subset
      (fun c hc => (mem_natFibreFinset A hh b c).mpr hc)
  exact hf.to_subtype

/-- The vector-partition count, defined only for matrices admitting a positive integral height.
It counts preimages, so repeated columns still give different partitions. -/
noncomputable def natFibreCount (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) : ℕ :=
  letI : Finite (NatFibre A b) := A.finite_natFibre hA b
  letI := Fintype.ofFinite (NatFibre A b)
  Fintype.card (NatFibre A b)

/-- The finite vector-partition count is the cardinality of the actual solution type. -/
theorem natFibreCount_eq_natCard (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    A.natFibreCount hA b = Nat.card (NatFibre A b) := by
  unfold natFibreCount
  exact Fintype.card_eq_nat_card

/-- A positive height computes the count by filtering an explicit finite coordinate box. -/
theorem card_natFibreFinset [DecidableEq n] (A : Matrix m n ℤ) {h : m → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    (A.natFibreFinset h b).card = A.natFibreCount ⟨h, hh⟩ b := by
  rw [natFibreCount_eq_natCard, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => mem_natFibreFinset A hh b c)

/-- The count is positive precisely when there is a natural solution. -/
@[simp] theorem natFibreCount_pos_iff (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    0 < A.natFibreCount hA b ↔ ∃ c : n → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [natFibreCount_eq_natCard, Nat.card_pos_iff, nonempty_subtype]
  exact and_iff_left (A.finite_natFibre hA b)

/-- The count vanishes precisely when there is no natural solution. -/
@[simp] theorem natFibreCount_eq_zero_iff (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    A.natFibreCount hA b = 0 ↔ ¬ ∃ c : n → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [← natFibreCount_pos_iff A hA b, Nat.pos_iff_ne_zero, not_ne_iff]

/-- The zero vector is the unique natural solution with image zero. -/
theorem NatFibre.eq_zero (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (c : NatFibre A 0) : c.1 = 0 := by
  obtain ⟨h, hh⟩ := hA
  ext j
  have := c.apply_le_height A hh j
  simpa using this

/-- The fibre at zero has exactly one point, including for an empty column family. -/
@[simp] theorem natFibreCount_zero (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) : A.natFibreCount hA 0 = 1 := by
  rw [natFibreCount_eq_natCard, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun c d => Subtype.ext ((c.eq_zero A hA).trans (d.eq_zero A hA).symm)⟩,
    ⟨⟨0, by ext i; simp [mulVec, dotProduct]⟩⟩⟩

end Matrix
