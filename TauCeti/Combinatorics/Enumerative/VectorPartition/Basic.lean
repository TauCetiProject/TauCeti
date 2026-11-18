/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.List.TFAE
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.TFAE
import TauCeti.Data.Matrix.DotProduct
import TauCeti.Geometry.Convex.Cone.Alternative

/-!
# Vector partitions and positive heights

For an integer matrix `A` with columns `A₁, …, Aₘ` and a target vector `b`, a *vector partition*
of `b` is a multiplicity vector `c : ι → ℕ` with `∑ⱼ cⱼ Aⱼ = b`, that is, a nonnegative integer
solution of `A c = b`. The *vector partition function* counts them. It specializes to the Kostant
partition function when the columns are the positive roots, and to the number of integer points of
a transportation or flow polytope for suitable network matrices.

The count is only meaningful when every fibre is finite. This file proves that this happens exactly
when the column cone of `A` is pointed, in any of the following equivalent forms
(`Matrix.tfae_exists_forall_pos_vecMul`):

* some integral covector `h` is a *positive height*: `h ᵥ* A` is strictly positive on every column;
* the only nonnegative solution of `A x = 0` over a linearly ordered ring is `x = 0`;
* the zero vector has only the empty partition;
* the zero vector has finitely many partitions;
* every vector has finitely many partitions.

A positive height bounds every coordinate of a partition of `b` by `h ⬝ᵥ b`
(`Matrix.natCast_le_dotProduct_of_mem_vectorPartitions`), which gives an explicit finite enumeration
`Matrix.vectorPartitionFinset` inside a box. The passage from pointedness to an integral height is
Gordan's alternative, in the integral form of Tucker's theorem
`TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos`.

The count is invariant under reordering the columns and under an injective change of the row
lattice. As basic examples, the identity matrix has exactly one partition of each nonnegative
vector; the matrix with columns `e₁, e₂, e₁ + e₂` has `min a b + 1` partitions of `(a, b)`; and the
non-unimodular `1 × 1` matrix `[2]` has a partition count on the nonnegative integers given by
parity, which no polynomial represents.

## Main definitions

* `Matrix.vectorPartitions A b`: the set of vector partitions of `b` by the columns of `A`.
* `Matrix.vectorPartitionCount A b`: the vector partition function.
* `Matrix.vectorPartitionFinset A h b`: the partitions of `b`, enumerated in the box cut out by a
  positive height `h`.

## Main results

* `Matrix.tfae_exists_forall_pos_vecMul`: the characterizations of pointedness above.
* `Matrix.finite_vectorPartitions`: under a positive height every fibre is finite.
* `Matrix.vectorPartitionCount_eq_card`: the count is the cardinality of the explicit enumeration.
* `Matrix.vectorPartitionCount_zero`: under a positive height the zero vector has one partition.
* `Matrix.not_exists_polynomial_vectorPartitionCount_two`: the count of `[2]` is not polynomial.

## References

* B. Sturmfels, *On vector partition functions*, J. Combin. Theory Ser. A **72** (1995), 302–309.
* J. A. De Loera and B. Sturmfels, *Algebraic unimodular counting*, Math. Program. **96** (2003),
  183–203.
-/

public section

open scoped Matrix
open Finset

namespace Matrix

variable {κ κ' ι ι' : Type*} [Fintype ι]

/-! ### Vector partitions -/

section Partitions

/-- The **vector partitions** of `b` by the columns of an integer matrix `A`: the multiplicity
vectors `c : ι → ℕ` with `∑ⱼ cⱼ Aⱼ = b`, that is, the nonnegative integer solutions of
`A c = b`. -/
def vectorPartitions (A : Matrix κ ι ℤ) (b : κ → ℤ) : Set (ι → ℕ) :=
  {c | A *ᵥ (fun j ↦ (c j : ℤ)) = b}

/-- A multiplicity vector is a vector partition of `b` when it solves `A c = b`. -/
@[simp]
theorem mem_vectorPartitions {A : Matrix κ ι ℤ} {b : κ → ℤ} {c : ι → ℕ} :
    c ∈ A.vectorPartitions b ↔ A *ᵥ (fun j ↦ (c j : ℤ)) = b := Iff.rfl

/-- The zero multiplicity vector is a partition of `0`. -/
theorem zero_mem_vectorPartitions (A : Matrix κ ι ℤ) : 0 ∈ A.vectorPartitions 0 := by
  simp [mem_vectorPartitions, ← Pi.zero_def]

/-- Partitions of `b` and of `b'` add up to a partition of `b + b'`. -/
theorem add_mem_vectorPartitions {A : Matrix κ ι ℤ} {b b' : κ → ℤ} {c c' : ι → ℕ}
    (hc : c ∈ A.vectorPartitions b) (hc' : c' ∈ A.vectorPartitions b') :
    c + c' ∈ A.vectorPartitions (b + b') := by
  rw [mem_vectorPartitions] at hc hc' ⊢
  have hcast : (fun j ↦ ((c + c') j : ℤ)) = (fun j ↦ (c j : ℤ)) + fun j ↦ (c' j : ℤ) := by
    ext j
    simp
  rw [hcast, mulVec_add, hc, hc']

/-- The `n`-fold multiple of a partition of `b` is a partition of `n • b`. -/
theorem nsmul_mem_vectorPartitions {A : Matrix κ ι ℤ} {b : κ → ℤ} {c : ι → ℕ}
    (hc : c ∈ A.vectorPartitions b) (n : ℕ) : n • c ∈ A.vectorPartitions (n • b) := by
  rw [mem_vectorPartitions] at hc ⊢
  have hcast : (fun j ↦ ((n • c) j : ℤ)) = n • fun j ↦ (c j : ℤ) := by
    ext j
    simp
  rw [hcast, mulVec_smul, hc]

/-- The **vector partition function** of `A`: the number of vector partitions of `b` by the
columns of `A`. It is a genuine finite count when `A` has a positive height
(`Matrix.finite_vectorPartitions`); for an infinite fibre it is `0` by the convention of
`Nat.card`. -/
noncomputable def vectorPartitionCount (A : Matrix κ ι ℤ) (b : κ → ℤ) : ℕ :=
  Nat.card (A.vectorPartitions b)

/-- The vector partition function is the cardinality of the set of vector partitions. -/
theorem vectorPartitionCount_def (A : Matrix κ ι ℤ) (b : κ → ℤ) :
    A.vectorPartitionCount b = Nat.card (A.vectorPartitions b) := (rfl)

/-- Reordering the columns of `A` does not change the vector partition function. -/
theorem vectorPartitionCount_submatrix_equiv [Fintype ι'] (A : Matrix κ ι ℤ) (σ : ι' ≃ ι)
    (b : κ → ℤ) : (A.submatrix id σ).vectorPartitionCount b = A.vectorPartitionCount b := by
  refine Nat.card_congr ((σ.arrowCongr (Equiv.refl ℕ)).subtypeEquiv fun c ↦ ?_)
  simp [submatrix_mulVec_equiv, Equiv.arrowCongr_apply, Function.comp_def]

/-- Multiplying `A` and `b` on the left by a matrix `U` with injective action, such as an
invertible change of basis of the row lattice, does not change the vector partitions. -/
theorem vectorPartitions_mul_left [Fintype κ] {U : Matrix κ' κ ℤ} (hU : Function.Injective U.mulVec)
    (A : Matrix κ ι ℤ) (b : κ → ℤ) :
    (U * A).vectorPartitions (U *ᵥ b) = A.vectorPartitions b := by
  ext c
  simp [← mulVec_mulVec, hU.eq_iff]

/-- Multiplying `A` and `b` on the left by a matrix `U` with injective action, such as an
invertible change of basis of the row lattice, does not change the vector partition function. -/
theorem vectorPartitionCount_mul_left [Fintype κ] {U : Matrix κ' κ ℤ}
    (hU : Function.Injective U.mulVec) (A : Matrix κ ι ℤ) (b : κ → ℤ) :
    (U * A).vectorPartitionCount (U *ᵥ b) = A.vectorPartitionCount b := by
  rw [vectorPartitionCount, vectorPartitions_mul_left hU, vectorPartitionCount]

end Partitions

/-! ### Positive heights -/

section Height

variable [Fintype κ] {A : Matrix κ ι ℤ} {b : κ → ℤ} {c : ι → ℕ} {h : κ → ℤ}

/-- Pairing a vector partition `c` of `b` with the heights `h ᵥ* A` of the columns gives the
height `h ⬝ᵥ b` of `b`. -/
theorem vecMul_dotProduct_of_mem_vectorPartitions (hc : c ∈ A.vectorPartitions b)
    (h : κ → ℤ) : (h ᵥ* A) ⬝ᵥ (fun j ↦ (c j : ℤ)) = h ⬝ᵥ b := by
  rw [← dotProduct_mulVec, mem_vectorPartitions.1 hc]

/-- Under a positive height `h`, the total multiplicity of a vector partition of `b` is at most
`h ⬝ᵥ b`. -/
theorem sum_le_dotProduct_of_mem_vectorPartitions (hh : ∀ j, 0 < (h ᵥ* A) j)
    (hc : c ∈ A.vectorPartitions b) : ∑ j, (c j : ℤ) ≤ h ⬝ᵥ b := by
  rw [← vecMul_dotProduct_of_mem_vectorPartitions hc h, dotProduct]
  exact Finset.sum_le_sum fun j _ ↦
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by have := hh j; omega)

/-- Under a positive height `h`, every coordinate of a vector partition of `b` is at most
`h ⬝ᵥ b`. -/
theorem natCast_le_dotProduct_of_mem_vectorPartitions (hh : ∀ j, 0 < (h ᵥ* A) j)
    (hc : c ∈ A.vectorPartitions b) (j : ι) : (c j : ℤ) ≤ h ⬝ᵥ b :=
  (Finset.single_le_sum (fun i _ ↦ Nat.cast_nonneg (c i)) (Finset.mem_univ j)).trans
    (sum_le_dotProduct_of_mem_vectorPartitions hh hc)

/-- Under a positive height the zero vector has only the empty partition. -/
theorem vectorPartitions_zero (hh : ∀ j, 0 < (h ᵥ* A) j) : A.vectorPartitions 0 = {0} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨A.zero_mem_vectorPartitions, fun c hc ↦ ?_⟩
  ext j
  have := natCast_le_dotProduct_of_mem_vectorPartitions hh hc j
  rw [dotProduct_zero] at this
  simpa using this

variable [DecidableEq ι]

/-- The candidate vector partitions of `b` in the box `cⱼ ≤ h ⬝ᵥ b`, filtered by the equation
`A c = b`. For a positive height `h` these are all the vector partitions of `b`
(`Matrix.coe_vectorPartitionFinset`), so this is a finite enumeration of them. -/
def vectorPartitionFinset (A : Matrix κ ι ℤ) (h b : κ → ℤ) : Finset (ι → ℕ) :=
  {c ∈ Fintype.piFinset fun _ ↦ Finset.range ((h ⬝ᵥ b).toNat + 1) |
    A *ᵥ (fun j ↦ (c j : ℤ)) = b}

/-- Under a positive height `h`, the enumeration `Matrix.vectorPartitionFinset A h b` contains
exactly the vector partitions of `b`. -/
theorem mem_vectorPartitionFinset (hh : ∀ j, 0 < (h ᵥ* A) j) :
    c ∈ A.vectorPartitionFinset h b ↔ c ∈ A.vectorPartitions b := by
  simp only [vectorPartitionFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    mem_vectorPartitions]
  refine ⟨And.right, fun hc ↦ ⟨fun j ↦ ?_, hc⟩⟩
  have := natCast_le_dotProduct_of_mem_vectorPartitions hh hc j
  omega

/-- Under a positive height `h`, the enumeration `Matrix.vectorPartitionFinset A h b` is the set of
vector partitions of `b`. -/
theorem coe_vectorPartitionFinset (hh : ∀ j, 0 < (h ᵥ* A) j) :
    (A.vectorPartitionFinset h b : Set (ι → ℕ)) = A.vectorPartitions b :=
  Set.ext fun _ ↦ mem_vectorPartitionFinset hh

omit [DecidableEq ι] in
/-- Under a positive height every vector has only finitely many vector partitions. -/
theorem finite_vectorPartitions (hh : ∀ j, 0 < (h ᵥ* A) j) (b : κ → ℤ) :
    (A.vectorPartitions b).Finite := by
  classical
  rw [← coe_vectorPartitionFinset hh]
  exact (A.vectorPartitionFinset h b).finite_toSet

/-- Under a positive height `h`, the vector partition function is the cardinality of the explicit
enumeration `Matrix.vectorPartitionFinset`. -/
theorem vectorPartitionCount_eq_card (hh : ∀ j, 0 < (h ᵥ* A) j) :
    A.vectorPartitionCount b = (A.vectorPartitionFinset h b).card := by
  rw [vectorPartitionCount, ← coe_vectorPartitionFinset hh, Nat.card_coe_set_eq,
    Set.ncard_coe_finset]

omit [DecidableEq ι] in
/-- Under a positive height the vector partition function of `A` takes the value `1` at `0`. -/
theorem vectorPartitionCount_zero (hh : ∀ j, 0 < (h ᵥ* A) j) : A.vectorPartitionCount 0 = 1 := by
  rw [vectorPartitionCount, vectorPartitions_zero hh, Nat.card_unique]

omit [DecidableEq ι] in
/-- Under a positive height the vector partition function is positive exactly at the vectors that
have a vector partition. -/
theorem vectorPartitionCount_pos_iff (hh : ∀ j, 0 < (h ᵥ* A) j) :
    0 < A.vectorPartitionCount b ↔ (A.vectorPartitions b).Nonempty := by
  rw [vectorPartitionCount, Nat.card_coe_set_eq]
  exact Set.ncard_pos (finite_vectorPartitions hh b)

end Height

/-! ### Pointed column cones -/

section Pointed

variable [Fintype κ]

/-- An integral covector `h` with `h ᵥ* A` strictly positive on every column exists exactly when
the column cone of `A` is pointed, measured over any linearly ordered ring `K`: the only
nonnegative solution of `A x = 0` is `0`. Both are equivalent to `0` having only the empty vector
partition, and to the finiteness of the vector partitions of `0`, or of every vector. -/
theorem tfae_exists_forall_pos_vecMul (K : Type*) [Ring K] [LinearOrder K]
    [IsStrictOrderedRing K] (A : Matrix κ ι ℤ) :
    [∃ h : κ → ℤ, ∀ j, 0 < (h ᵥ* A) j,
      ∀ x : ι → K, 0 ≤ x → A.map (Int.cast : ℤ → K) *ᵥ x = 0 → x = 0,
      A.vectorPartitions 0 = {0},
      (A.vectorPartitions 0).Finite,
      ∀ b, (A.vectorPartitions b).Finite].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨h, hh⟩ x hx hAx
    have hw : (fun j ↦ ((h ᵥ* A) j : K)) = (fun i ↦ (h i : K)) ᵥ* A.map (Int.cast : ℤ → K) :=
      funext fun j ↦ (Int.castRingHom K).map_vecMul A h j
    refine (TauCeti.dotProduct_eq_zero_iff_of_pos (c := fun j ↦ ((h ᵥ* A) j : K))
      (fun j ↦ by exact_mod_cast hh j) hx).1 ?_
    rw [hw, ← dotProduct_mulVec, hAx, dotProduct_zero]
  tfae_have 2 → 3 := by
    intro hK
    refine Set.eq_singleton_iff_unique_mem.2 ⟨A.zero_mem_vectorPartitions, fun c hc ↦ ?_⟩
    have hx := hK (fun j ↦ (c j : K)) (fun j ↦ Nat.cast_nonneg _) <| funext fun i ↦ by
      have := (Int.castRingHom K).map_mulVec A (fun j ↦ (c j : ℤ)) i
      rw [mem_vectorPartitions.1 hc] at this
      simpa [Function.comp_def] using this.symm
    ext j
    simpa using congrFun hx j
  tfae_have 3 → 1 := by
    classical
    intro h0
    -- Gordan's alternative, in the integral form of Tucker's theorem, applied to the columns.
    obtain ⟨x, m, hsum, -, hpos⟩ :=
      TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos fun j ↦ Aᵀ j
    -- The nonnegative relation `x` among the columns is a partition of `0`, hence trivial.
    have hx : x = 0 := by
      have hmem : x ∈ A.vectorPartitions 0 := by
        rw [mem_vectorPartitions, ← hsum]
        ext i
        simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rwa [h0] at hmem
    -- So `m` is positive on every column; its values on the basis vectors form the height.
    refine ⟨fun i ↦ m fun k ↦ if i = k then 1 else 0, fun j ↦ ?_⟩
    have hm : m (Aᵀ j) = ((fun i ↦ m fun k ↦ if i = k then 1 else 0) ᵥ* A) j := by
      simpa [vecMul, dotProduct, mul_comm] using m.toIntLinearMap.pi_apply_eq_sum_univ (Aᵀ j)
    simpa [hx, hm] using hpos j
  tfae_have 1 → 5 := fun ⟨_, hh⟩ ↦ finite_vectorPartitions hh
  tfae_have 5 → 4 := fun hfin ↦ hfin 0
  tfae_have 4 → 3 := by
    intro hfin
    refine Set.eq_singleton_iff_unique_mem.2 ⟨A.zero_mem_vectorPartitions, fun c hc ↦ ?_⟩
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    rw [Pi.zero_apply] at hj
    -- The multiples of a nonzero partition of `0` are infinitely many partitions of `0`.
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ n • c) (fun n n' e ↦ ?_)
      (fun n ↦ by simpa using nsmul_mem_vectorPartitions hc n) hfin
    simpa [hj] using congrFun e j
  tfae_finish

end Pointed

/-! ### Examples -/

section Examples

/-- The identity matrix has exactly one vector partition of each nonnegative vector, namely the
vector itself, and none of any other vector. -/
theorem vectorPartitions_one [DecidableEq ι] (b : ι → ℤ) :
    (1 : Matrix ι ι ℤ).vectorPartitions b =
      if 0 ≤ b then {fun j ↦ (b j).toNat} else ∅ := by
  ext c
  simp only [mem_vectorPartitions, one_mulVec, funext_iff]
  split_ifs with hb
  · simp only [Set.mem_singleton_iff, funext_iff]
    exact forall_congr' fun j ↦ by have : 0 ≤ b j := hb j; omega
  · simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    exact hb fun j ↦ by simp [← hc j]

/-- The vector partition function of the identity matrix is the indicator of the nonnegative
vectors. -/
theorem vectorPartitionCount_one [DecidableEq ι] (b : ι → ℤ) :
    (1 : Matrix ι ι ℤ).vectorPartitionCount b = if 0 ≤ b then 1 else 0 := by
  rw [vectorPartitionCount, vectorPartitions_one]
  split_ifs <;> simp

private theorem mem_vectorPartitions_a2 {a b : ℤ} {c : Fin 3 → ℕ} :
    c ∈ (!![1, 0, 1; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℤ).vectorPartitions ![a, b] ↔
      (c 0 : ℤ) + c 2 = a ∧ (c 1 : ℤ) + c 2 = b := by
  simp [funext_iff, Fin.forall_fin_two, dotProduct, Fin.sum_univ_three]

/-- The matrix with columns `e₁, e₂, e₁ + e₂` (the positive roots of type `A₂` in simple-root
coordinates) has `min a b + 1` vector partitions of `(a, b)` when `a, b ≥ 0`, and none otherwise:
the partitions are `(a - z, b - z, z)` for `0 ≤ z ≤ min a b`. -/
theorem vectorPartitionCount_a2 (a b : ℤ) :
    (!![1, 0, 1; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℤ).vectorPartitionCount ![a, b] =
      (min a b + 1).toNat := by
  rw [vectorPartitionCount, ← Finset.card_range (min a b + 1).toNat, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun c := ⟨c.1 2, ?_⟩
      invFun z := ⟨![(a - z).toNat, (b - z).toNat, z], ?_⟩
      left_inv c := ?_
      right_inv z := rfl }
  · have := mem_vectorPartitions_a2.1 c.2
    simp only [Finset.mem_range]
    omega
  · have := Finset.mem_range.1 z.2
    rw [mem_vectorPartitions_a2]
    simp only [Matrix.cons_val]
    omega
  · have := mem_vectorPartitions_a2.1 c.2
    ext j
    fin_cases j <;> simp <;> omega

/-- The non-unimodular `1 × 1` matrix `[2]` has one vector partition of each nonnegative even
integer and none of any other integer. -/
theorem vectorPartitionCount_two (b : Fin 1 → ℤ) :
    (2 : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitionCount b =
      if 0 ≤ b 0 ∧ Even (b 0) then 1 else 0 := by
  have hmem (c : Fin 1 → ℕ) :
      c ∈ (2 : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitions b ↔ 2 * (c 0 : ℤ) = b 0 := by
    simp [ofNat_mulVec, funext_iff, Fin.forall_fin_one]
  rw [vectorPartitionCount]
  split_ifs with hb
  · obtain ⟨hb0, k, hk⟩ := hb
    have : (2 : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitions b = {fun _ ↦ k.toNat} := by
      ext c
      rw [hmem, Set.mem_singleton_iff, funext_iff, Fin.forall_fin_one]
      omega
    simp [this]
  · have : (2 : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitions b = ∅ :=
      Set.eq_empty_of_forall_notMem fun c hc ↦
        hb ⟨by have := (hmem c).1 hc; omega, ⟨c 0, by have := (hmem c).1 hc; omega⟩⟩
    simp [this]

/-- No polynomial agrees with the vector partition function of `[2]` on the nonnegative integers:
without unimodularity the count need not be polynomial even on a single chamber. -/
theorem not_exists_polynomial_vectorPartitionCount_two :
    ¬ ∃ p : Polynomial ℚ, ∀ k : ℕ,
      p.eval (k : ℚ) = (2 : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitionCount fun _ ↦ k := by
  rintro ⟨p, hp⟩
  have heven (n : ℕ) : p.eval ((2 * n : ℕ) : ℚ) = 1 := by
    have hn : 0 ≤ ((2 * n : ℕ) : ℤ) ∧ Even ((2 * n : ℕ) : ℤ) :=
      ⟨by positivity, n, by push_cast; ring⟩
    simp only [hp, vectorPartitionCount_two, hn, and_self, ↓reduceIte, Nat.cast_one]
  -- `p` takes the value `1` at every even natural number, so it is the constant `1`.
  have hconst : p = Polynomial.C 1 := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ <|
      Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ ((2 * n : ℕ) : ℚ)) ?_ fun n ↦ ?_
    · intro n n' e
      simpa using e
    · simpa using heven n
  have h1 := hp 1
  rw [hconst, vectorPartitionCount_two] at h1
  simp at h1

end Examples

end Matrix
