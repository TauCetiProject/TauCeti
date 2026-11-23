/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.LinearAlgebra.Matrix.NonnegSolution
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Order.Compact
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Vector partition functions

For an integer matrix `A` with rows indexed by `κ` and columns by `ι`, a *vector partition* of an
integer vector `b` is a vector `c` of natural numbers with `A *ᵥ c = b`: a way of writing `b` as a
sum of columns of `A`, the column `j` used `c j` times. The vector partition function counts them,
`b ↦ #{c : ι → ℕ | A *ᵥ c = b}`. For the positive roots of a root system in simple-root
coordinates it is Kostant's partition function.

The counts are finite when `A` admits a *positive height*: an integer functional `h` with
`0 < (h ᵥ* A) j` on every column. Then every coordinate of a vector partition of `b` is at most
`h ⬝ᵥ b`, which gives an explicit enumeration of the vector partitions inside a box. A
positive height exists exactly when `0` has only the empty partition; otherwise the multiples of
a nonzero partition of `0` are infinitely many.

The vector partitions of `b` are the lattice points of the real *partition polyhedron*
`{x : ι → ℝ | 0 ≤ x ∧ A *ᵥ x = b}`, which is compact under a positive height. If moreover `A`
has independent rows and unit or zero maximal minors (for instance if it is totally unimodular),
the count is positive exactly when this polyhedron is nonempty, that is
when `b` lies in the cone spanned by the columns; this rests on integral basic solutions,
`Matrix.exists_natCast_mulVec_eq_of_nonneg`. Without unimodularity the count can vanish inside the
cone: for the `1 × 1` matrix `[2]` it is `0` at `b = 1`.

These are the finiteness, support and positivity statements on which the chamberwise
polynomiality of unimodular vector partition functions (De Loera–Sturmfels) is built.

## Main definitions

* `Matrix.vectorPartitions A b`: the vector partitions of `b` with parts the columns of `A`.
* `Matrix.vectorPartitionCount A b`: their number, `0` when there are infinitely many.
* `Matrix.partitionPolyhedron A b`: the real polyhedron `{x | 0 ≤ x ∧ A *ᵥ x = b}`.
* `Matrix.vectorPartitionsFinset A h b`: the vector partitions of `b` enumerated inside the box
  of side `h ⬝ᵥ b`, for a positive height `h`.

## Main results

* `Matrix.natCast_le_dotProduct_of_mem_vectorPartitions`: the coordinate bound by a positive height.
* `Matrix.finite_vectorPartitions`, `Matrix.vectorPartitionCount_eq_card`: finiteness and
  enumeration under a positive height.
* `Matrix.vectorPartitions_zero_eq_singleton_iff`, `Matrix.vectorPartitionCount_zero`: `0` has only
  the empty partition exactly when there is a positive height.
* `Matrix.image_natCast_vectorPartitions`: the vector partitions are the lattice points of the
  partition polyhedron.
* `Matrix.isConvexPolyhedron_partitionPolyhedron`, `Matrix.isCompact_partitionPolyhedron`.
* `Matrix.vectorPartitionCount_eq_zero_of_partitionPolyhedron_eq_empty`: the count vanishes off the
  column cone.
* `Matrix.vectorPartitionCount_pos_iff`, `Matrix.IsTotallyUnimodular.vectorPartitionCount_pos_iff`:
  for unimodular `A` with a positive height, the count is positive exactly on the lattice points of
  the column cone.

## References

* J. A. De Loera and B. Sturmfels, *Algebraic unimodular counting*, Math. Program. **96** (2003),
  183–203, §1.
* S. Billey, V. Guillemin and E. Rassart, *A vector partition function for the multiplicities of
  sl_k ℂ*, J. Algebra **278** (2004), 251–293, §1.
-/

public section

open Function

namespace Matrix

variable {κ ι : Type*} [Fintype ι]

/-! ### Vector partitions and their count -/

/-- The *vector partitions* of `b` with parts the columns of the integer matrix `A`: the vectors
`c` of natural numbers with `A *ᵥ c = b`. -/
def vectorPartitions (A : Matrix κ ι ℤ) (b : κ → ℤ) : Set (ι → ℕ) :=
  {c | A *ᵥ (fun j => (c j : ℤ)) = b}

@[simp] theorem mem_vectorPartitions {A : Matrix κ ι ℤ} {b : κ → ℤ} {c : ι → ℕ} :
    c ∈ A.vectorPartitions b ↔ A *ᵥ (fun j => (c j : ℤ)) = b := Iff.rfl

instance [Fintype κ] (A : Matrix κ ι ℤ) (b : κ → ℤ) :
    DecidablePred (· ∈ A.vectorPartitions b) := fun _ =>
  decidable_of_iff _ mem_vectorPartitions.symm

/-- The *vector partition function* of `A`: the number of vector partitions of `b` with parts the
columns of `A`. It is `0` when there are infinitely many, which cannot happen when `A` has a
positive height (`Matrix.finite_vectorPartitions`). -/
noncomputable def vectorPartitionCount (A : Matrix κ ι ℤ) (b : κ → ℤ) : ℕ :=
  Nat.card (A.vectorPartitions b)

theorem vectorPartitionCount_def (A : Matrix κ ι ℤ) (b : κ → ℤ) :
    A.vectorPartitionCount b = Nat.card (A.vectorPartitions b) := (rfl)

/-! ### Coordinate bounds and enumeration under a positive height -/

section Height

variable [Fintype κ] {A : Matrix κ ι ℤ} {h : κ → ℤ}

/-- Under a positive height `h`, each coordinate of a vector partition of `b` is at most
`h ⬝ᵥ b`. -/
theorem natCast_le_dotProduct_of_mem_vectorPartitions (hh : ∀ j, 0 < (h ᵥ* A) j) {b : κ → ℤ}
    {c : ι → ℕ} (hc : c ∈ A.vectorPartitions b) (j : ι) : (c j : ℤ) ≤ h ⬝ᵥ b := by
  rw [← mem_vectorPartitions.1 hc, dotProduct_mulVec]
  exact le_dotProduct_of_one_le (fun k => (zero_add 1).symm.trans_le (Int.add_one_le_of_lt (hh k)))
    (x := fun k => (c k : ℤ)) (fun k => Int.natCast_nonneg _) j

variable [DecidableEq ι]

variable (A h) in
/-- The vector partitions of `b` enumerated in the box `{c | ∀ j, c j ≤ h ⬝ᵥ b}`. For a positive
height `h` this is all of them (`Matrix.coe_vectorPartitionsFinset`). -/
def vectorPartitionsFinset (b : κ → ℤ) : Finset (ι → ℕ) :=
  {c ∈ Fintype.piFinset fun _ => Finset.range ((h ⬝ᵥ b).toNat + 1) | c ∈ A.vectorPartitions b}

/-- Membership in `Matrix.vectorPartitionsFinset`, with no height hypothesis: a vector partition
of `b` inside the box. -/
@[simp] theorem mem_vectorPartitionsFinset {b : κ → ℤ} {c : ι → ℕ} :
    c ∈ A.vectorPartitionsFinset h b ↔
      (∀ j, c j ≤ (h ⬝ᵥ b).toNat) ∧ c ∈ A.vectorPartitions b := by
  simp [vectorPartitionsFinset]

@[simp] theorem coe_vectorPartitionsFinset (hh : ∀ j, 0 < (h ᵥ* A) j) (b : κ → ℤ) :
    (A.vectorPartitionsFinset h b : Set (ι → ℕ)) = A.vectorPartitions b := by
  ext c
  simp only [Finset.mem_coe, mem_vectorPartitionsFinset, and_iff_right_iff_imp]
  intro hc j
  have := natCast_le_dotProduct_of_mem_vectorPartitions hh hc j
  omega

theorem mem_vectorPartitionsFinset_of_pos (hh : ∀ j, 0 < (h ᵥ* A) j) {b : κ → ℤ} {c : ι → ℕ} :
    c ∈ A.vectorPartitionsFinset h b ↔ c ∈ A.vectorPartitions b := by
  rw [← Finset.mem_coe, coe_vectorPartitionsFinset hh]

omit [DecidableEq ι] in
/-- Under a positive height every vector partition fibre is finite. -/
theorem finite_vectorPartitions (hh : ∀ j, 0 < (h ᵥ* A) j) (b : κ → ℤ) :
    (A.vectorPartitions b).Finite := by
  classical
  rw [← coe_vectorPartitionsFinset hh]
  exact Finset.finite_toSet _

/-- Under a positive height the vector partition function is the cardinality of the explicit
enumeration `Matrix.vectorPartitionsFinset`. -/
theorem vectorPartitionCount_eq_card (hh : ∀ j, 0 < (h ᵥ* A) j) (b : κ → ℤ) :
    A.vectorPartitionCount b = (A.vectorPartitionsFinset h b).card := by
  rw [vectorPartitionCount_def, ← coe_vectorPartitionsFinset hh, Nat.card_coe_set_eq,
    Set.ncard_coe_finset]

end Height

/-! ### The zero vector -/

/-- `0` has only the empty vector partition exactly when `A` has a positive height. -/
theorem vectorPartitions_zero_eq_singleton_iff [Fintype κ] (A : Matrix κ ι ℤ) :
    A.vectorPartitions 0 = {0} ↔ ∃ h : κ → ℤ, ∀ j, 0 < (h ᵥ* A) j := by
  rw [exists_pos_vecMul_iff, Set.eq_singleton_iff_unique_mem]
  simp only [mem_vectorPartitions, Pi.zero_apply, Nat.cast_zero, and_iff_right_iff_imp]
  intro _
  funext i
  simp [mulVec, dotProduct]

/-- Under a positive height the vector partition function takes the value `1` at `0`. -/
theorem vectorPartitionCount_zero [Fintype κ] {A : Matrix κ ι ℤ} {h : κ → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) : A.vectorPartitionCount 0 = 1 := by
  rw [vectorPartitionCount_def, (vectorPartitions_zero_eq_singleton_iff A).2 ⟨h, hh⟩,
    Nat.card_unique]

/-! ### The partition polyhedron -/

/-- The *partition polyhedron* `{x : ι → ℝ | 0 ≤ x ∧ A *ᵥ x = b}`, whose lattice points are the
vector partitions of `b` (`Matrix.image_natCast_vectorPartitions`). It is compact under a positive
height (`Matrix.isCompact_partitionPolyhedron`), and nonempty exactly when `b` lies in the cone
spanned by the columns of `A`. -/
def partitionPolyhedron (A : Matrix κ ι ℤ) (b : κ → ℝ) : Set (ι → ℝ) :=
  {x | 0 ≤ x ∧ A.map (Int.cast : ℤ → ℝ) *ᵥ x = b}

@[simp] theorem mem_partitionPolyhedron {A : Matrix κ ι ℤ} {b : κ → ℝ} {x : ι → ℝ} :
    x ∈ A.partitionPolyhedron b ↔ 0 ≤ x ∧ A.map (Int.cast : ℤ → ℝ) *ᵥ x = b := Iff.rfl

/-- A vector of natural numbers lies in the partition polyhedron of an integer vector `b` exactly
when it is a vector partition of `b`. -/
theorem natCast_mem_partitionPolyhedron_iff {A : Matrix κ ι ℤ} {b : κ → ℤ} {c : ι → ℕ} :
    (fun j => (c j : ℝ)) ∈ A.partitionPolyhedron (fun i => (b i : ℝ)) ↔
      c ∈ A.vectorPartitions b := by
  have hcast := map_intCast_mulVec (R := ℝ) A fun j => (c j : ℤ)
  simp only [Int.cast_natCast] at hcast
  simp only [mem_partitionPolyhedron, mem_vectorPartitions, hcast]
  refine ⟨fun ⟨_, h⟩ => funext fun i => by exact_mod_cast congrFun h i,
    fun h => ⟨fun j => by simp, by rw [h]⟩⟩

/-- The vector partitions of an integer vector `b` are the lattice points of the partition
polyhedron of `b`. -/
theorem image_natCast_vectorPartitions (A : Matrix κ ι ℤ) (b : κ → ℤ) :
    (fun (c : ι → ℕ) j => (c j : ℝ)) '' A.vectorPartitions b =
      A.partitionPolyhedron (fun i => (b i : ℝ)) ∩ Set.range fun (z : ι → ℤ) j => (z j : ℝ) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨natCast_mem_partitionPolyhedron_iff.2 hc, fun j => (c j : ℤ), by simp⟩
  · rintro ⟨hx, z, rfl⟩
    have hzc : (fun j => (((z j).toNat : ℕ) : ℝ)) = fun j => (z j : ℝ) := funext fun j => by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by simpa using hx.1 j)]
    exact ⟨fun j => (z j).toNat, natCast_mem_partitionPolyhedron_iff.1 (hzc ▸ hx), hzc⟩

/-- The partition polyhedron is a convex polyhedron in the sense of `TauCeti.IsConvexPolyhedron`:
it is cut out by the inequalities `0 ≤ x j` and the two inequalities of each equation. -/
theorem isConvexPolyhedron_partitionPolyhedron [Finite κ] (A : Matrix κ ι ℤ) (b : κ → ℝ) :
    TauCeti.IsConvexPolyhedron (A.partitionPolyhedron b) := by
  let row (i : κ) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap
      ((LinearMap.proj i).comp (A.map (Int.cast : ℤ → ℝ)).mulVecLin)).toContinuousAffineMap
  let g : ι ⊕ κ ⊕ κ → (ι → ℝ) →ᴬ[ℝ] ℝ :=
    Sum.elim (fun j => (-ContinuousLinearMap.proj j).toContinuousAffineMap)
      (Sum.elim (fun i => row i - ContinuousAffineMap.const ℝ (ι → ℝ) (b i))
        (fun i => ContinuousAffineMap.const ℝ (ι → ℝ) (b i) - row i))
  convert TauCeti.isConvexPolyhedron_setOf_forall g using 1
  ext x
  simp [g, row, Sum.forall, Pi.le_def, le_antisymm_iff]

/-- Under a positive height every coordinate of a point of the partition polyhedron of `b` is at
most `h ⬝ᵥ b`. -/
theorem le_dotProduct_of_mem_partitionPolyhedron [Fintype κ] {A : Matrix κ ι ℤ} {h : κ → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) {b : κ → ℝ} {x : ι → ℝ} (hx : x ∈ A.partitionPolyhedron b)
    (j : ι) : x j ≤ (fun k => (h k : ℝ)) ⬝ᵥ b := by
  obtain ⟨hx0, hxb⟩ := hx
  rw [← hxb, dotProduct_mulVec, map_intCast_vecMul]
  exact le_dotProduct_of_one_le
    (fun k => by exact_mod_cast (zero_add 1).symm.trans_le (Int.add_one_le_of_lt (hh k))) hx0 j

/-- Under a positive height every partition polyhedron is compact. -/
theorem isCompact_partitionPolyhedron [Fintype κ] {A : Matrix κ ι ℤ} {h : κ → ℤ}
    (hh : ∀ j, 0 < (h ᵥ* A) j) (b : κ → ℝ) : IsCompact (A.partitionPolyhedron b) :=
  (isCompact_Icc (a := (0 : ι → ℝ)) (b := fun _ => (fun k => (h k : ℝ)) ⬝ᵥ b)).of_isClosed_subset
    (isConvexPolyhedron_partitionPolyhedron A b).isClosed
    fun _ hx => ⟨hx.1, fun j => le_dotProduct_of_mem_partitionPolyhedron hh hx j⟩

/-! ### Support and positivity -/

/-- The vector partition function vanishes at every integer vector outside the cone spanned by the
columns, where the partition polyhedron is empty. -/
theorem vectorPartitionCount_eq_zero_of_partitionPolyhedron_eq_empty {A : Matrix κ ι ℤ}
    {b : κ → ℤ} (hb : A.partitionPolyhedron (fun i => (b i : ℝ)) = ∅) :
    A.vectorPartitionCount b = 0 := by
  have : A.vectorPartitions b = ∅ :=
    Set.eq_empty_of_forall_notMem fun c hc =>
      (Set.eq_empty_iff_forall_notMem.1 hb) _ (natCast_mem_partitionPolyhedron_iff.2 hc)
  simp [vectorPartitionCount_def, this]

/-- **Positivity of unimodular vector partition functions.** If `A` has a positive height,
linearly independent rows and all maximal minors in `{0, 1, -1}`, then the vector partition
function is positive at an integer vector `b` exactly when `b` lies in the cone spanned by the
columns, that is when the partition polyhedron of `b` is nonempty. -/
theorem vectorPartitionCount_pos_iff [Fintype κ] [DecidableEq κ] {A : Matrix κ ι ℤ}
    {h : κ → ℤ} (hh : ∀ j, 0 < (h ᵥ* A) j) (hA : LinearIndependent ℤ A.row)
    (hunit : ∀ e : κ → ι, Injective e → (A.submatrix id e).det ∈ Set.range SignType.cast)
    (b : κ → ℤ) :
    0 < A.vectorPartitionCount b ↔ (A.partitionPolyhedron (fun i => (b i : ℝ))).Nonempty := by
  have := (finite_vectorPartitions hh b).to_subtype
  rw [vectorPartitionCount_def, Nat.card_pos_iff, and_iff_left this, Set.nonempty_coe_sort]
  refine ⟨fun ⟨c, hc⟩ => ⟨_, natCast_mem_partitionPolyhedron_iff.2 hc⟩, fun ⟨x, hx0, hxb⟩ => ?_⟩
  exact exists_natCast_mulVec_eq_of_nonneg A hA hunit hx0 hxb

/-- **Positivity of totally unimodular vector partition functions.** If `A` is totally unimodular
with a positive height and linearly independent rows, then the vector partition function is
positive at an integer vector `b` exactly when the partition polyhedron of `b` is nonempty. -/
theorem IsTotallyUnimodular.vectorPartitionCount_pos_iff [Fintype κ] {A : Matrix κ ι ℤ}
    (hTU : A.IsTotallyUnimodular) {h : κ → ℤ} (hh : ∀ j, 0 < (h ᵥ* A) j)
    (hA : LinearIndependent ℤ A.row) (b : κ → ℤ) :
    0 < A.vectorPartitionCount b ↔ (A.partitionPolyhedron (fun i => (b i : ℝ))).Nonempty := by
  classical
  exact Matrix.vectorPartitionCount_pos_iff hh hA
    (fun e _ => (isTotallyUnimodular_iff_fintype A).1 hTU κ id e) b

/-! ### Examples -/

-- The `1 × 1` matrix `[2]` has the positive height `1` and nonzero maximal minor, but is not
-- unimodular: `1` lies in its column cone (the partition polyhedron contains `1 / 2`) while it has
-- no vector partition. So the unimodularity hypothesis of `Matrix.vectorPartitionCount_pos_iff`
-- cannot be dropped.
example :
    (!![2] : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitionCount ![1] = 0 ∧
      ((!![2] : Matrix (Fin 1) (Fin 1) ℤ).partitionPolyhedron ![1]).Nonempty := by
  refine ⟨?_, ⟨![1 / 2], fun _ => by simp, by ext i; fin_cases i; simp [mulVec]⟩⟩
  have : (!![2] : Matrix (Fin 1) (Fin 1) ℤ).vectorPartitions ![1] = ∅ :=
    Set.eq_empty_of_forall_notMem fun c hc => by
      have := congrFun hc 0
      simp [mulVec, dotProduct] at this
      omega
  simp [vectorPartitionCount_def, this]

-- Without a positive height the vector partition fibres can be infinite: for the matrix with no
-- rows and one column every vector is a vector partition of `0`, so the count, which is `0` on
-- infinite fibres, is not `1` at `0`.
example :
    (0 : Matrix (Fin 0) (Fin 1) ℤ).vectorPartitionCount 0 = 0 := by
  have : (0 : Matrix (Fin 0) (Fin 1) ℤ).vectorPartitions 0 = Set.univ :=
    Set.eq_univ_of_forall fun c => funext fun i => i.elim0
  rw [vectorPartitionCount_def, this, Nat.card_univ]
  exact Nat.card_eq_zero_of_infinite

end Matrix
