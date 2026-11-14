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
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite vector-partition fibers

`Matrix.nonnegFiber A b` is the nonnegative solution set over a partially ordered semiring.
When the row index type is finite, a covector nonnegative on every column bounds each coordinate
contribution by the target height over an ordered semiring. A covector strictly positive on every
column bounds each coordinate over an ordered field.

For an integer matrix `A`, `Matrix.NatFiber A b` consists of decompositions of the target `b`
as a natural linear combination of the columns of `A`. Distinct multiplicity vectors are counted
separately, including when columns coincide. When the row index type is finite, an integral
covector strictly positive on every column bounds each multiplicity and gives a finite enumeration
of the fiber. The count is defined for every matrix as the natural cardinality of its fiber, so it
is zero for infinite fibers.
For a finite row index type and an integral covector strictly positive on every column, it counts
the finite solution set and is independent of that covector. Natural fibers are identified with
the integer points of the corresponding nonnegative fibers over any strictly ordered ring; this
identification does not require finitely many rows.

The criterion `Matrix.exists_forall_vecMul_pos_iff` in
`TauCeti.Geometry.Convex.Cone.Alternative` characterizes the existence of an integral covector
strictly positive on every column by the absence of nonzero nonnegative vectors in the real kernel.
Neither full row rank nor unimodularity is needed for these finiteness results.
-/

public section

namespace Matrix

variable {m : Type*} {n : Type*} [Fintype n]

/-- The nonnegative solutions of the matrix equation `A x = b`. -/
def nonnegFiber {R : Type*} [Semiring R] [PartialOrder R]
    (A : Matrix m n R) (b : m → R) : Set (n → R) :=
  {x | 0 ≤ x ∧ A *ᵥ x = b}

/-- The nonnegative fiber is the solution set cut out by nonnegativity and the matrix equation. -/
theorem nonnegFiber_def {R : Type*} [Semiring R] [PartialOrder R]
    (A : Matrix m n R) (b : m → R) :
    A.nonnegFiber b = {x | 0 ≤ x ∧ A *ᵥ x = b} := by
  rfl

/-- Membership in a fiber means nonnegativity and the matrix equation. -/
@[simp, grind =] theorem mem_nonnegFiber {R : Type*} [Semiring R] [PartialOrder R]
    (A : Matrix m n R) (b : m → R) (x : n → R) :
    x ∈ A.nonnegFiber b ↔ 0 ≤ x ∧ A *ᵥ x = b := by
  rw [nonnegFiber_def]
  rfl

/-- A covector nonnegative on every column bounds the contribution of each coordinate of a
nonnegative solution. -/
theorem mul_apply_le_dotProduct_of_mem_nonnegFiber {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [Fintype m] (A : Matrix m n R) {h : m → R}
    (hh : ∀ j, 0 ≤ (h ᵥ* A) j) {b : m → R} {x : n → R}
    (hx : x ∈ A.nonnegFiber b) (j : n) : (h ᵥ* A) j * x j ≤ h ⬝ᵥ b := by
  rw [mem_nonnegFiber] at hx
  have hheight : (h ᵥ* A) ⬝ᵥ x = h ⬝ᵥ b := by
    rw [← dotProduct_mulVec, hx.2]
  rw [← hheight]
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hh k) (hx.1 k))
    (Finset.mem_univ j)

/-- A covector strictly positive on every column bounds every coordinate of a nonnegative
solution over an ordered field. -/
theorem apply_le_div_of_mem_nonnegFiber {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype m] (A : Matrix m n K) {h : m → K}
    (hh : ∀ j, 0 < (h ᵥ* A) j) {b : m → K} {x : n → K}
    (hx : x ∈ A.nonnegFiber b) (j : n) : x j ≤ (h ⬝ᵥ b) / (h ᵥ* A) j := by
  apply (le_div_iff₀ (hh j)).mpr
  rw [mul_comm]
  exact A.mul_apply_le_dotProduct_of_mem_nonnegFiber (fun k => (hh k).le) hx j

/-- The natural multiplicity vectors with image `b` under the integer matrix `A`. -/
abbrev NatFiber (A : Matrix m n ℤ) (b : m → ℤ) :=
  {c : n → ℕ // A *ᵥ (fun j => (c j : ℤ)) = b}

/-- The vector-partition count, counting distinct multiplicity vectors even when columns
coincide. It is zero for infinite fibers; for finite `m`, an integral covector strictly positive
on every column guarantees finiteness. -/
noncomputable def natFiberCount (A : Matrix m n ℤ) (b : m → ℤ) : ℕ :=
  Nat.card (NatFiber A b)

/-- The total vector-partition count is the natural cardinality of the solution type. -/
theorem natFiberCount_def (A : Matrix m n ℤ) (b : m → ℤ) :
    A.natFiberCount b = Nat.card (NatFiber A b) := by
  rfl

/-- Integer points of a fiber over a strictly ordered ring are precisely the nonnegative
integer solutions. -/
theorem intCast_mem_nonnegFiber_iff {R : Type*} [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] (A : Matrix m n ℤ) (b : m → ℤ) (x : n → ℤ) :
    (fun j => (x j : R)) ∈ (A.map (Int.castRingHom R)).nonnegFiber
      (fun i => (b i : R)) ↔
      0 ≤ x ∧ A *ᵥ x = b := by
  have he (i : m) : ((A *ᵥ x) i : R) =
      (A.map (Int.castRingHom R) *ᵥ fun j => (x j : R)) i := by
    simpa only [Int.coe_castRingHom, Function.comp_def] using
      (Int.castRingHom R).map_mulVec A x i
  rw [mem_nonnegFiber]
  constructor
  · rintro ⟨hx, hAx⟩
    refine ⟨fun j => Int.cast_nonneg_iff.mp (hx j), funext fun i => ?_⟩
    exact Int.cast_injective (α := R) ((he i).trans (congrFun hAx i))
  · rintro ⟨hx, hAx⟩
    refine ⟨fun j => Int.cast_nonneg (hx j), funext fun i => ?_⟩
    rw [← he, hAx]

/-- Natural solutions are exactly the integer points of the corresponding fiber over a
strictly ordered ring. -/
def natFiberEquivIntegerPoints (A : Matrix m n ℤ) (R : Type*) [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] (b : m → ℤ) :
    NatFiber A b ≃
      {x : n → ℤ // (fun j => (x j : R)) ∈
        (A.map (Int.castRingHom R)).nonnegFiber (fun i => (b i : R))} where
  toFun c := ⟨fun j => (c.1 j : ℤ),
    (A.intCast_mem_nonnegFiber_iff (R := R) b _).mpr ⟨fun _ => Int.natCast_nonneg _, c.2⟩⟩
  invFun x := ⟨fun j => (x.1 j).toNat, by
    have hx := (A.intCast_mem_nonnegFiber_iff (R := R) b x.1).mp x.2
    simpa only [Int.toNat_of_nonneg (hx.1 _)] using hx.2⟩
  left_inv c := by ext j; simp
  right_inv x := by
    ext j
    exact Int.toNat_of_nonneg (((A.intCast_mem_nonnegFiber_iff (R := R) b x.1).mp x.2).1 j)

@[simp, grind =] theorem natFiberEquivIntegerPoints_apply (A : Matrix m n ℤ) (R : Type*)
    [Ring R] [PartialOrder R] [IsStrictOrderedRing R] (b : m → ℤ)
    (c : NatFiber A b) (j : n) : (A.natFiberEquivIntegerPoints R b c).1 j = (c.1 j : ℤ) := (rfl)

@[simp, grind =] theorem natFiberEquivIntegerPoints_symm_apply (A : Matrix m n ℤ) (R : Type*)
    [Ring R] [PartialOrder R] [IsStrictOrderedRing R] (b : m → ℤ)
    (x : {x : n → ℤ // (fun j => (x j : R)) ∈
      (A.map (Int.castRingHom R)).nonnegFiber (fun i => (b i : R))})
    (j : n) : ((A.natFiberEquivIntegerPoints R b).symm x).1 j = (x.1 j).toNat := (rfl)

variable [Fintype m]

/-- The height of a multiplicity vector is the height of its image. -/
theorem NatFiber.dotProduct_eq {A : Matrix m n ℤ} {b : m → ℤ} (c : NatFiber A b)
    (h : m → ℤ) : (h ᵥ* A) ⬝ᵥ (fun j => (c.1 j : ℤ)) = h ⬝ᵥ b := by
  rw [← dotProduct_mulVec, c.2]

/-- If the integral covector is strictly positive on every column, each multiplicity is bounded
by the height of the right-hand side. -/
theorem NatFiber.apply_le_toNat_dotProduct {A : Matrix m n ℤ} {b : m → ℤ} (c : NatFiber A b)
    {h : m → ℤ} (hh : ∀ j, 0 < (h ᵥ* A) j) (j : n) :
    c.1 j ≤ (h ⬝ᵥ b).toNat := by
  have hle : (c.1 j : ℤ) ≤ h ⬝ᵥ b :=
    (le_mul_of_one_le_left (Int.natCast_nonneg _) (hh j)).trans
      (A.mul_apply_le_dotProduct_of_mem_nonnegFiber (fun k => (hh k).le)
        ⟨fun _ => Int.natCast_nonneg _, c.2⟩ j)
  omega

/-- A bounded candidate enumeration for a natural fiber. If `h` is strictly positive on every
column, `mem_natFiberFinset_iff_of_vecMul_pos` identifies this enumeration with the entire fiber. -/
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

/-- Under an integral covector strictly positive on every column, the bounded enumeration
contains exactly the solutions. -/
@[simp] theorem mem_natFiberFinset_iff_of_vecMul_pos [DecidableEq n] (A : Matrix m n ℤ) {h : m → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) (c : n → ℕ) :
    c ∈ A.natFiberFinset h b ↔ A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [mem_natFiberFinset_iff]
  exact ⟨And.right, fun hc => ⟨fun j => NatFiber.apply_le_toNat_dotProduct ⟨c, hc⟩ hh j, hc⟩⟩

/-- For finite `m`, natural fibers are finite whenever an integral covector is strictly positive
on every column. -/
theorem finite_natFiber (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    Finite (NatFiber A b) := by
  classical
  obtain ⟨h, hh⟩ := hA
  have hf : {c : n → ℕ | A *ᵥ (fun j => (c j : ℤ)) = b}.Finite :=
    (A.natFiberFinset h b).finite_toSet.subset
      (fun c hc => (mem_natFiberFinset_iff_of_vecMul_pos A hh b c).mpr hc)
  exact hf.to_subtype

/-- An integral covector strictly positive on every column computes the count by filtering an
explicit finite coordinate box. -/
theorem card_natFiberFinset [DecidableEq n] (A : Matrix m n ℤ) {h : m → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    (A.natFiberFinset h b).card = A.natFiberCount b := by
  rw [natFiberCount_def, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c =>
    mem_natFiberFinset_iff_of_vecMul_pos A hh b c)

/-- Under an integral covector strictly positive on every column, the count is positive precisely
when there is a natural solution. -/
@[simp] theorem natFiberCount_pos_iff (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    0 < A.natFiberCount b ↔ ∃ c : n → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [natFiberCount_def, Nat.card_pos_iff, nonempty_subtype]
  exact and_iff_left (A.finite_natFiber hA b)

/-- Under an integral covector strictly positive on every column, the count vanishes precisely
when there is no natural solution. -/
@[simp] theorem natFiberCount_eq_zero_iff (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℤ) :
    A.natFiberCount b = 0 ↔ ¬ ∃ c : n → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  rw [← natFiberCount_pos_iff A hA b, Nat.pos_iff_ne_zero, not_ne_iff]

/-- Under an integral covector strictly positive on every column, the zero vector is the unique
natural solution with image zero. -/
theorem NatFiber.val_eq_zero {A : Matrix m n ℤ} (c : NatFiber A 0)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) : c.1 = 0 := by
  obtain ⟨h, hh⟩ := hA
  ext j
  have := c.apply_le_toNat_dotProduct hh j
  simpa using this

/-- Under an integral covector strictly positive on every column, the fiber at zero has exactly
one point, including for an empty column family. -/
@[simp] theorem natFiberCount_zero (A : Matrix m n ℤ)
    (hA : ∃ h : m → ℤ, ∀ j, 0 < (h ᵥ* A) j) : A.natFiberCount 0 = 1 := by
  rw [natFiberCount_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun c d => Subtype.ext ((c.val_eq_zero hA).trans (d.val_eq_zero hA).symm)⟩,
    ⟨⟨0, by ext i; simp [mulVec, dotProduct]⟩⟩⟩

end Matrix
