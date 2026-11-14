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

`Matrix.nonnegFiber A b`, specialized to real matrices, satisfies `TauCeti.IsConvexPolyhedron`
when the row index type is finite. A covector strictly positive on every column bounds all
coordinates over any linearly ordered field, making the real fiber compact. For integer
matrices, the natural fibers are identified with the integer points of the corresponding
nonnegative fibers over any strictly ordered ring. Real feasibility need not imply integer
feasibility, and these results do not require unimodularity.
-/

public section

namespace Matrix

variable {m : Type*} {n : Type*} [Fintype n]

/-- A real vector-partition fiber is a convex polyhedron, even when unbounded or empty. -/
theorem isConvexPolyhedron_nonnegFiber [Finite m] (A : Matrix m n ℝ) (b : m → ℝ) :
    TauCeti.IsConvexPolyhedron (A.nonnegFiber b) := by
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
  simp only [mem_nonnegFiber, Set.mem_ofPred_eq, Sum.forall, g, Sum.elim_inl, Sum.elim_inr,
    ContinuousAffineMap.neg_apply, ContinuousAffineMap.sub_apply,
    ContinuousAffineMap.coe_const, Function.const_apply, neg_nonpos, sub_nonpos, row, coord,
    ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.proj_apply,
    sum_apply, smul_apply, smul_eq_mul, Pi.le_def, Pi.zero_apply, funext_iff, mulVec,
    dotProduct]
  exact ⟨fun ⟨hx, he⟩ => ⟨hx, fun i => (he i).le, fun i => (he i).ge⟩,
    fun ⟨hx, hlo, hhi⟩ => ⟨hx, fun i => le_antisymm (hlo i) (hhi i)⟩⟩

/-- A positive height bounds every coordinate of a nonnegative solution over an ordered field. -/
theorem apply_le_div_of_mem_nonnegFiber {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype m] (A : Matrix m n K) {h : m → K}
    (hh : ∀ j, 0 < (h ᵥ* A) j) {b : m → K} {x : n → K}
    (hx : x ∈ A.nonnegFiber b) (j : n) : x j ≤ (h ⬝ᵥ b) / (h ᵥ* A) j := by
  apply (le_div_iff₀ (hh j)).mpr
  rw [mul_comm]
  exact A.mul_apply_le_dotProduct_of_mem_nonnegFiber (fun k => (hh k).le) hx j

/-- If the columns have a strictly positive height, every real fiber is compact. -/
theorem isCompact_nonnegFiber [Fintype m] (A : Matrix m n ℝ)
    (hA : ∃ h : m → ℝ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℝ) :
    IsCompact (A.nonnegFiber b) := by
  obtain ⟨h, hh⟩ := hA
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : n → ℝ)
    (fun j => (h ⬝ᵥ b) / (h ᵥ* A) j))).of_isClosed_subset
      (A.isConvexPolyhedron_nonnegFiber b).isClosed ?_
  intro x hx
  exact ⟨((mem_nonnegFiber A b x).mp hx).1,
    fun j => A.apply_le_div_of_mem_nonnegFiber hh hx j⟩

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

end Matrix
