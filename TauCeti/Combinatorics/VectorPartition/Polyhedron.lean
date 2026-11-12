/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.VectorPartition.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Basic.Finite.Sum
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Real vector-partition polyhedra

`Matrix.realFibre A b` is the nonnegative real solution set of a matrix equation.
It is a native convex polyhedron, and a positive real height bounds all its coordinates,
making it compact. For integer matrices, the natural multiplicity vectors are identified with
the integer points of the corresponding real fibre.

These results do not require unimodularity: real feasibility alone need not supply an integer
point, and no such conclusion is asserted here.
-/

public section

namespace Matrix

variable {m : Type*} {n : Type*} [Fintype n]

/-- The nonnegative real solutions of the matrix equation `A x = b`. -/
def realFibre (A : Matrix m n ℝ) (b : m → ℝ) : Set (n → ℝ) :=
  {x | 0 ≤ x ∧ A *ᵥ x = b}

/-- Membership in a real fibre means nonnegativity and the matrix equation. -/
@[simp] theorem mem_realFibre (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) :
    x ∈ A.realFibre b ↔ 0 ≤ x ∧ A *ᵥ x = b := Iff.rfl

/-- A real vector-partition fibre is a convex polyhedron, even when unbounded or empty. -/
theorem isConvexPolyhedron_realFibre [Finite m] (A : Matrix m n ℝ) (b : m → ℝ) :
    TauCeti.IsConvexPolyhedron (A.realFibre b) := by
  let coord (j : n) : (n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let row (i : m) : (n → ℝ) →L[ℝ] ℝ := ∑ j, A i j • coord j
  let g : n ⊕ (m ⊕ m) → (n → ℝ) →ᴬ[ℝ] ℝ :=
    Sum.elim (fun j => -(coord j).toContinuousAffineMap)
      (Sum.elim (fun i => (row i).toContinuousAffineMap -
          ContinuousAffineMap.const ℝ (n → ℝ) (b i))
        (fun i => ContinuousAffineMap.const ℝ (n → ℝ) (b i) -
          (row i).toContinuousAffineMap))
  convert TauCeti.isConvexPolyhedron_setOf_forall g using 1
  ext x
  simp only [mem_realFibre, Set.mem_ofPred_eq, Sum.forall, g, Sum.elim_inl, Sum.elim_inr,
    ContinuousAffineMap.neg_apply, ContinuousAffineMap.sub_apply,
    ContinuousAffineMap.coe_const, Function.const_apply, neg_nonpos, sub_nonpos, row, coord,
    ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.proj_apply,
    sum_apply, smul_apply, smul_eq_mul, Pi.le_def, Pi.zero_apply, funext_iff, mulVec,
    dotProduct]
  exact ⟨fun ⟨hx, he⟩ => ⟨hx, fun i => (he i).le, fun i => (he i).ge⟩,
    fun ⟨hx, hlo, hhi⟩ => ⟨hx, fun i => le_antisymm (hlo i) (hhi i)⟩⟩

/-- A positive height bounds every coordinate of a real nonnegative solution. -/
theorem realFibre_apply_le_div [Fintype m] (A : Matrix m n ℝ) {h : m → ℝ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) {b : m → ℝ} {x : n → ℝ}
    (hx : x ∈ A.realFibre b) (j : n) : x j ≤ (h ⬝ᵥ b) / (h ᵥ* A) j := by
  apply (le_div_iff₀ (hh j)).mpr
  have hheight : (h ᵥ* A) ⬝ᵥ x = h ⬝ᵥ b := by
    rw [← dotProduct_mulVec, hx.2]
  rw [mul_comm, ← hheight]
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hh k).le (hx.1 k))
    (Finset.mem_univ j)

/-- If the columns have a strictly positive height, every real fibre is compact. -/
theorem isCompact_realFibre [Fintype m] (A : Matrix m n ℝ)
    (hA : ∃ h : m → ℝ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℝ) :
    IsCompact (A.realFibre b) := by
  obtain ⟨h, hh⟩ := hA
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : n → ℝ)
    (fun j => (h ⬝ᵥ b) / (h ᵥ* A) j))).of_isClosed_subset
      (A.isConvexPolyhedron_realFibre b).isClosed ?_
  intro x hx
  exact ⟨hx.1, fun j => A.realFibre_apply_le_div hh hx j⟩

/-- Integer points of a real fibre are precisely the nonnegative integer solutions. -/
theorem intCast_mem_realFibre_iff (A : Matrix m n ℤ) (b : m → ℤ) (x : n → ℤ) :
    (fun j => (x j : ℝ)) ∈ (A.map (Int.castRingHom ℝ)).realFibre
      (fun i => (b i : ℝ)) ↔
      0 ≤ x ∧ A *ᵥ x = b := by
  have he (i : m) : ((A *ᵥ x) i : ℝ) =
      (A.map (Int.castRingHom ℝ) *ᵥ fun j => (x j : ℝ)) i := by
    simpa only [Int.coe_castRingHom, Function.comp_def] using
      (Int.castRingHom ℝ).map_mulVec A x i
  rw [mem_realFibre]
  constructor
  · rintro ⟨hx, hAx⟩
    refine ⟨fun j => Int.cast_nonneg_iff.mp (hx j), funext fun i => ?_⟩
    exact Int.cast_injective (α := ℝ) ((he i).trans (congrFun hAx i))
  · rintro ⟨hx, hAx⟩
    refine ⟨fun j => Int.cast_nonneg (hx j), funext fun i => ?_⟩
    rw [← he, hAx]

/-- Natural solutions are exactly the integer points of the corresponding real fibre. -/
def natFibreEquivIntegerPoints (A : Matrix m n ℤ) (b : m → ℤ) :
    NatFibre A b ≃
      {x : n → ℤ // (fun j => (x j : ℝ)) ∈
        (A.map (Int.castRingHom ℝ)).realFibre (fun i => (b i : ℝ))} where
  toFun c := ⟨fun j => (c.1 j : ℤ),
    (A.intCast_mem_realFibre_iff b _).mpr ⟨fun _ => Int.natCast_nonneg _, c.2⟩⟩
  invFun x := ⟨fun j => (x.1 j).toNat, by
    have hx := (A.intCast_mem_realFibre_iff b x.1).mp x.2
    simpa only [Int.toNat_of_nonneg (hx.1 _)] using hx.2⟩
  left_inv c := by ext j; simp
  right_inv x := by
    ext j
    exact Int.toNat_of_nonneg (((A.intCast_mem_realFibre_iff b x.1).mp x.2).1 j)

@[simp] theorem natFibreEquivIntegerPoints_apply (A : Matrix m n ℤ) (b : m → ℤ)
    (c : NatFibre A b) (j : n) : (A.natFibreEquivIntegerPoints b c).1 j = (c.1 j : ℤ) := (rfl)

@[simp] theorem natFibreEquivIntegerPoints_symm_apply (A : Matrix m n ℤ) (b : m → ℤ)
    (x : {x : n → ℤ // (fun j => (x j : ℝ)) ∈
      (A.map (Int.castRingHom ℝ)).realFibre (fun i => (b i : ℝ))})
    (j : n) : ((A.natFibreEquivIntegerPoints b).symm x).1 j = (x.1 j).toNat := (rfl)

end Matrix
