/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ColumnRowFixing
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup

/-!
# The split hermitian form, levels, floors, and the Bessel subgroups

Let `R` be a commutative ring with involution, `ϱ` a natural number, and `κ` a finite type. The
space `R^𝐁` has the basis `e₀, …, e_{ϱ-1}`, then a middle block `x_i` (`i ∈ κ`) and `z`, then
`e*₀, …, e*_{ϱ-1}`; the index type is `TauCeti.BesselIndex ϱ κ`. For a matrix `T` on the middle
block, the **split form** `TauCeti.splitGram ϱ T` pairs `e_a` with `e*_b` by `δ_ab`, makes the
hyperbolic pairs orthogonal to the middle block, and has Gram matrix `T` on the middle block. Its
unitary group is `Matrix.unitaryGroupOf (TauCeti.splitGram ϱ T)`.

The basis vectors carry a **level** (`a` for `e_a`, `ϱ` on the middle block, `2ϱ - a` for `e*_a`)
and a **floor** (`a` for `e_a` and `e*_a`, `ϱ` for `z`, `ϱ + 1` for `x_i`). The **frame** is
`(e₀, …, e_{ϱ-1}, z)`, and the **frame Gram matrix** `T.frameGram γ` of `γ` is the matrix of the
products of the frame with its image under `γ`.

## Main definitions

* `TauCeti.SplitIndex`, `TauCeti.BesselIndex`, `TauCeti.BesselIndex.z`: the index types for the
  split form and the Bessel basis.
* `TauCeti.splitGram`, `TauCeti.middleGram`: the split Gram matrix attached to a middle block `T`,
  and the standard middle Gram matrix `diag(1_κ, -N)`.
* `TauCeti.splitLevel`, `TauCeti.besselFloor`, `TauCeti.besselFrame`: the level, floor, and frame
  functions on `BesselIndex ϱ κ`.
* `Matrix.frameGram`: the frame Gram matrix of a matrix `γ` for the split form of `T`.
* `TauCeti.besselU`, `TauCeti.frameFixingSubgroup`, `TauCeti.besselU0`,
  `TauCeti.floorFixingSubgroup`: the unipotent Bessel group `U` of isometries that are block
  unitriangular for the levels, the fixing subgroup of the frame, their intersection `U⁰`, and
  the group `H_l` of isometries fixing every basis vector of floor `< l`.

## Main results

* `TauCeti.isHermitian_splitGram`: the split form of a hermitian `T` is hermitian.
* `TauCeti.isHermitian_middleGram`: `middleGram N` is hermitian when `star N = N`.
* `Matrix.frameGram_one`: the frame Gram matrix of `1` has the single entry `T z z`.
* `TauCeti.det_eq_one_of_mem_besselU`: elements of the unipotent Bessel group have determinant `1`.
* `TauCeti.mem_besselU_iff_forall_le`: membership in the unipotent Bessel group, entry by entry.
* `TauCeti.splitGram_mul_apply_inl`, `TauCeti.splitGram_mul_apply_eStar`: the Gram matrix of the
  split form exchanges the rows `e_a` and `e*_a`.
* `TauCeti.exists_eq_inl_of_splitLevel_lt`, `TauCeti.exists_besselFrame_eq_of_besselFloor_lt`: the
  basis vectors of small level, or of small floor and level, are frame vectors.

## References

The definitions are adapted from the Lean project grh-lean, also called riemann-hypothesis
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/Groups/BesselGroups.lean` (declarations `New.Shape.Form.splitGram`,
`New.BesselIndex.level`, `New.Shape.Form.besselU`, `New.Shape.Form.besselU0`).
For the Bessel subgroups compare
* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical
  L-values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), Section 12.
-/

public section

open Matrix

namespace TauCeti

/-! ### The basis, the split form, levels, floors, and the frame -/

/-- The index set made of `ϱ` indices, a middle set `μ`, and `ϱ` further indices. -/
abbrev SplitIndex (ϱ : ℕ) (μ : Type*) : Type _ := Fin ϱ ⊕ μ ⊕ Fin ϱ

/-- The index set of the basis `e₀, …, e_{ϱ-1}, x_i (i ∈ κ), z, e*₀, …, e*_{ϱ-1}`. -/
abbrev BesselIndex (ϱ : ℕ) (κ : Type*) : Type _ := SplitIndex ϱ (κ ⊕ Unit)

/-- The index of the vector `z`. -/
abbrev BesselIndex.z (ϱ : ℕ) (κ : Type*) : BesselIndex ϱ κ := Sum.inr (Sum.inl (Sum.inr ()))

section SplitGram

variable {R : Type*} [Zero R] [One R] (ϱ : ℕ) {μ : Type*}

/-- The Gram matrix of `ϱ` hyperbolic planes and a middle block with Gram matrix `T`: identity
blocks pair the first and the last `ϱ` indices, `T` is the middle block, all else is zero. -/
def splitGram (T : Matrix μ μ R) : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (fromBlocks T 0 0 0)

variable {ϱ} (T : Matrix μ μ R)

@[simp] lemma splitGram_inl_inl (a b : Fin ϱ) :
    splitGram ϱ T (.inl a) (.inl b) = 0 := (rfl)
@[simp] lemma splitGram_inl_middle (a : Fin ϱ) (j : μ) :
    splitGram ϱ T (.inl a) (.inr (.inl j)) = 0 := (rfl)
@[simp] lemma splitGram_middle_inl (i : μ) (b : Fin ϱ) :
    splitGram ϱ T (.inr (.inl i)) (.inl b) = 0 := (rfl)
@[simp] lemma splitGram_middle_middle (i j : μ) :
    splitGram ϱ T (.inr (.inl i)) (.inr (.inl j)) = T i j := (rfl)
@[simp] lemma splitGram_inl_eStar (a b : Fin ϱ) :
    splitGram ϱ T (.inl a) (.inr (.inr b)) = (1 : Matrix (Fin ϱ) (Fin ϱ) R) a b := (rfl)
@[simp] lemma splitGram_eStar_inl (a b : Fin ϱ) :
    splitGram ϱ T (.inr (.inr a)) (.inl b) = (1 : Matrix (Fin ϱ) (Fin ϱ) R) a b := (rfl)
@[simp] lemma splitGram_middle_eStar (i : μ) (b : Fin ϱ) :
    splitGram ϱ T (.inr (.inl i)) (.inr (.inr b)) = 0 := (rfl)
@[simp] lemma splitGram_eStar_middle (a : Fin ϱ) (j : μ) :
    splitGram ϱ T (.inr (.inr a)) (.inr (.inl j)) = 0 := (rfl)
@[simp] lemma splitGram_eStar_eStar (a b : Fin ϱ) :
    splitGram ϱ T (.inr (.inr a)) (.inr (.inr b)) = 0 := (rfl)

end SplitGram

/-- The split form of a hermitian matrix is hermitian. -/
theorem isHermitian_splitGram {R : Type*} [Semiring R] [StarRing R] {ϱ : ℕ} {μ : Type*}
    {T : Matrix μ μ R} (hT : T.IsHermitian) : (splitGram ϱ T).IsHermitian := by
  ext (a | i | a) (b | j | b) <;>
    simp [hT.apply, (isHermitian_one (n := Fin ϱ) (α := R)).apply]

section MiddleGram

variable {R : Type*} [Zero R] [One R] [Neg R] {κ : Type*} [DecidableEq κ]

/-- The Gram matrix `diag(1_κ, -N)` on the middle block `κ ⊕ {z}`. -/
def middleGram (N : R) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R :=
  fromBlocks 1 0 0 (of fun _ _ ↦ -N)

@[simp] lemma middleGram_inl_inl (N : R) (i j : κ) :
    middleGram (κ := κ) N (.inl i) (.inl j) = (1 : Matrix κ κ R) i j := (rfl)
@[simp] lemma middleGram_inl_inr (N : R) (i : κ) (u : Unit) :
    middleGram (κ := κ) N (.inl i) (.inr u) = 0 := (rfl)
@[simp] lemma middleGram_inr_inl (N : R) (u : Unit) (j : κ) :
    middleGram (κ := κ) N (.inr u) (.inl j) = 0 := (rfl)
@[simp] lemma middleGram_inr_inr (N : R) (u v : Unit) :
    middleGram (κ := κ) N (.inr u) (.inr v) = -N := (rfl)

end MiddleGram

/-- The middle Gram matrix `diag(1_κ, -N)` is hermitian when `N` is self-adjoint. -/
theorem isHermitian_middleGram {R : Type*} [Ring R] [StarRing R] {κ : Type*} [DecidableEq κ]
    {N : R} (hN : star N = N) : (middleGram (κ := κ) N).IsHermitian := by
  ext (i | u) (j | v) <;>
    simp [hN, (isHermitian_one (n := κ) (α := R)).apply]

section LevelFloorFrame

variable {ϱ : ℕ} {μ κ : Type*}

/-- The level of a basis index: `a` for `e_a`, `ϱ` on the middle block, `2ϱ - a` for `e*_a`. -/
def splitLevel : SplitIndex ϱ μ → ℕ :=
  Sum.elim (fun a ↦ a) (Sum.elim (fun _ ↦ ϱ) fun a ↦ 2 * ϱ - a)

@[simp] lemma splitLevel_inl (a : Fin ϱ) : splitLevel (μ := μ) (.inl a) = a := (rfl)
@[simp] lemma splitLevel_middle (i : μ) : splitLevel (ϱ := ϱ) (.inr (.inl i)) = ϱ := (rfl)
@[simp] lemma splitLevel_eStar (a : Fin ϱ) :
    splitLevel (μ := μ) (.inr (.inr a)) = 2 * ϱ - a := (rfl)

/-- The levels of the indices of the first block are below `ϱ`. -/
lemma splitLevel_inl_lt (a : Fin ϱ) : splitLevel (μ := μ) (.inl a) < ϱ := a.isLt

/-- The levels of the indices of the last block are above `ϱ`. -/
lemma lt_splitLevel_eStar (a : Fin ϱ) : ϱ < splitLevel (μ := μ) (.inr (.inr a)) := by
  simp only [splitLevel_eStar]; omega

/-- The floor of a basis index: `a` for `e_a` and `e*_a`, `ϱ` for `z`, `ϱ + 1` for `x_i`. -/
def besselFloor : BesselIndex ϱ κ → ℕ :=
  Sum.elim (fun a ↦ a) (Sum.elim (Sum.elim (fun _ ↦ ϱ + 1) fun _ ↦ ϱ) fun a ↦ a)

@[simp] lemma besselFloor_inl (a : Fin ϱ) : besselFloor (κ := κ) (.inl a) = a := (rfl)
@[simp] lemma besselFloor_x (i : κ) :
    besselFloor (ϱ := ϱ) (.inr (.inl (.inl i))) = ϱ + 1 := (rfl)
@[simp] lemma besselFloor_z (u : Unit) :
    besselFloor (ϱ := ϱ) (κ := κ) (.inr (.inl (.inr u))) = ϱ := (rfl)
@[simp] lemma besselFloor_eStar (a : Fin ϱ) : besselFloor (κ := κ) (.inr (.inr a)) = a := (rfl)

/-- The indices of the frame `(e₀, …, e_{ϱ-1}, z)`. -/
def besselFrame : Fin (ϱ + 1) → BesselIndex ϱ κ := Fin.snoc Sum.inl (BesselIndex.z ϱ κ)

@[simp] lemma besselFrame_castSucc (a : Fin ϱ) : besselFrame (κ := κ) a.castSucc = .inl a := by
  simp [besselFrame]
@[simp] lemma besselFrame_last : besselFrame (κ := κ) (Fin.last ϱ) = BesselIndex.z ϱ κ := by
  simp [besselFrame]

end LevelFloorFrame

/-! ### Floors, levels and the frame -/

section Index

variable {ϱ : ℕ} {κ : Type*}

/-- The floor of a basis vector is at most one more than its level. -/
theorem besselFloor_le_splitLevel_add_one (i : BesselIndex ϱ κ) :
    besselFloor i ≤ splitLevel i + 1 := by
  rcases i with a | (i | ⟨⟩) | a
  · simp
  · simp
  · simp
  · simp only [besselFloor_eStar, splitLevel_eStar]; omega

/-- Every floor is at most `ϱ + 1`. -/
theorem besselFloor_le (i : BesselIndex ϱ κ) : besselFloor i ≤ ϱ + 1 := by
  rcases i with a | (i | ⟨⟩) | a
  · simp only [besselFloor_inl]; omega
  · simp
  · simp
  · simp only [besselFloor_eStar]; omega

/-- The frame vector `f_b` has level `b`. -/
@[simp]
theorem splitLevel_besselFrame (b : Fin (ϱ + 1)) : splitLevel (besselFrame (κ := κ) b) = b := by
  induction b using Fin.lastCases <;> simp

/-- The frame vector `f_b` has floor `b`. -/
@[simp]
theorem besselFloor_besselFrame (b : Fin (ϱ + 1)) : besselFloor (besselFrame (κ := κ) b) = b := by
  induction b using Fin.lastCases <;> simp

/-- Distinct indices give distinct frame vectors. -/
theorem besselFrame_injective : Function.Injective (besselFrame (ϱ := ϱ) (κ := κ)) :=
  fun b b' h ↦ Fin.ext <| by simpa using congrArg splitLevel h

/-- A frame vector of index below `ϱ` is `e_b`. -/
theorem besselFrame_eq_inl {b : Fin (ϱ + 1)} (hb : (b : ℕ) < ϱ) :
    besselFrame (κ := κ) b = .inl ⟨b, hb⟩ :=
  besselFrame_castSucc (κ := κ) ⟨b, hb⟩

/-- A basis vector of level below `b ≤ ϱ` is one of the `e_c`. -/
theorem exists_eq_inl_of_splitLevel_lt {i : BesselIndex ϱ κ} {b : ℕ} (hi : splitLevel i < b)
    (hb : b ≤ ϱ) : ∃ c : Fin ϱ, i = .inl c := by
  rcases i with a | (i | ⟨⟩) | a
  · exact ⟨a, rfl⟩
  · simp at hi; omega
  · simp at hi; omega
  · simp only [splitLevel_eStar] at hi; omega

/-- A basis vector of floor and level below `l ≤ ϱ + 1` is a frame vector `f_b` with `b < l`. -/
theorem exists_besselFrame_eq_of_besselFloor_lt {j : BesselIndex ϱ κ} {l : ℕ}
    (hf : besselFloor j < l) (hj : splitLevel j < l) (hl : l ≤ ϱ + 1) :
    ∃ b : Fin (ϱ + 1), (b : ℕ) < l ∧ besselFrame b = j := by
  rcases j with a | (i | ⟨⟩) | a
  · exact ⟨a.castSucc, by simpa using hf, by simp⟩
  · simp at hf; omega
  · exact ⟨Fin.last ϱ, by simpa using hj, by simp⟩
  · simp only [splitLevel_eStar] at hj; omega

end Index

/-! ### Rows of the split form -/

section SplitGramRows

variable {R : Type*} [CommRing R] {ϱ : ℕ} {μ : Type*} (T : Matrix μ μ R)

/-- The row `e_a` of the Gram matrix of the split form is the basis row `e*_a`. -/
theorem splitGram_apply_inl [DecidableEq μ] (a : Fin ϱ) (k : SplitIndex ϱ μ) :
    splitGram ϱ T (.inl a) k =
      (1 : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (.inr (.inr a)) k := by
  rcases k with b | j | b <;> simp [Matrix.one_apply]

/-- The row `e*_a` of the Gram matrix of the split form is the basis row `e_a`. -/
theorem splitGram_apply_eStar [DecidableEq μ] (a : Fin ϱ) (k : SplitIndex ϱ μ) :
    splitGram ϱ T (.inr (.inr a)) k =
      (1 : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (.inl a) k := by
  rcases k with b | j | b <;> simp [Matrix.one_apply]

variable [Fintype μ]

/-- The row `e_a` of `J M` is the row `e*_a` of `M`, for the Gram matrix `J` of the split form. -/
theorem splitGram_mul_apply_inl (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (a : Fin ϱ)
    (k : SplitIndex ϱ μ) : (splitGram ϱ T * M) (.inl a) k = M (.inr (.inr a)) k := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- The row `e*_a` of `J M` is the row `e_a` of `M`, for the Gram matrix `J` of the split form. -/
theorem splitGram_mul_apply_eStar (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (a : Fin ϱ)
    (k : SplitIndex ϱ μ) : (splitGram ϱ T * M) (.inr (.inr a)) k = M (.inl a) k := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- A row of the middle block of `J M` is the corresponding combination, by `T`, of the rows of the
middle block of `M`, for the Gram matrix `J` of the split form. -/
theorem splitGram_mul_apply_middle (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (i : μ)
    (k : SplitIndex ϱ μ) :
    (splitGram ϱ T * M) (.inr (.inl i)) k = ∑ j, T i j * M (.inr (.inl j)) k := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

end SplitGramRows

end TauCeti

namespace Matrix

open TauCeti

section FrameGram

variable {R : Type*} [Semiring R] {ϱ : ℕ} {κ : Type*} [Fintype κ]
  (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)
  (γ : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)

/-- The matrix of the products of the frame with its image under `γ`, for the split form of
`T`. -/
def frameGram : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) R :=
  (splitGram ϱ T * γ).submatrix besselFrame besselFrame

@[simp] lemma frameGram_apply (a b : Fin (ϱ + 1)) :
    frameGram T γ a b = (splitGram ϱ T * γ) (besselFrame a) (besselFrame b) := (rfl)

/-- The frame Gram matrix of `1` has the single entry `T z z`, at the corner of `z`. -/
@[simp] theorem frameGram_one [DecidableEq κ] :
    frameGram T 1 = single (Fin.last ϱ) (Fin.last ϱ) (T (.inr ()) (.inr ())) := by
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [fun i : Fin ϱ ↦ (Fin.castSucc_lt_last i).ne']

end FrameGram

end Matrix

namespace TauCeti

/-! ### The Bessel subgroups -/

section BesselSubgroups

variable {R : Type*} [CommRing R] [StarRing R] (ϱ : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
  (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)

/-- The unipotent Bessel group `U`: the isometries of the split form of `T` that are block
upper unitriangular for the levels. -/
def besselU : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (unitriangularSubgroup splitLevel R).subgroupOf _

@[simp] theorem mem_besselU {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ besselU ϱ T ↔
      ((g : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R).BlockUnitriangular splitLevel := by
  simp only [besselU, Subgroup.mem_subgroupOf, mem_unitriangularSubgroup]

/-- An isometry lies in the unipotent Bessel group exactly when it agrees with the identity matrix
at every entry `(i, j)` with `level j ≤ level i`. -/
theorem mem_besselU_iff_forall_le {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ besselU ϱ T ↔ ∀ i j : BesselIndex ϱ κ, splitLevel j ≤ splitLevel i →
      ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j := by
  rw [mem_besselU, blockUnitriangular_iff_forall_le]

/-- The isometries of the split form of `T` that fix each vector of the frame. -/
def frameFixingSubgroup : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (columnRowFixingSubgroup R (Set.range besselFrame) ∅).subgroupOf _

@[simp] theorem mem_frameFixingSubgroup {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ frameFixingSubgroup ϱ T ↔
      ∀ i j : BesselIndex ϱ κ, j ∈ Set.range besselFrame →
        ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
          (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j := by
  simp only [frameFixingSubgroup, Subgroup.mem_subgroupOf, mem_columnRowFixingSubgroup_iff,
    Set.notMem_empty, false_implies, implies_true, and_true]
  exact ⟨fun h i j hj ↦ h j hj i, fun h j hj i ↦ h i j hj⟩

/-- The elements of the unipotent Bessel group `U` that fix each vector of the frame. -/
def besselU0 : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  besselU ϱ T ⊓ frameFixingSubgroup ϱ T

@[simp] theorem mem_besselU0 {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ besselU0 ϱ T ↔ g ∈ besselU ϱ T ∧ g ∈ frameFixingSubgroup ϱ T := (Iff.rfl)

/-- The group `H_l` of the isometries of the split form of `T` that fix every basis vector of
floor `< l`. -/
def floorFixingSubgroup (l : ℕ) : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (columnRowFixingSubgroup R {j | besselFloor j < l} ∅).subgroupOf _

@[simp] theorem mem_floorFixingSubgroup {l : ℕ} {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ floorFixingSubgroup ϱ T l ↔
      ∀ i j : BesselIndex ϱ κ, besselFloor j < l →
        ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
          (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j := by
  simp only [floorFixingSubgroup, Subgroup.mem_subgroupOf, mem_columnRowFixingSubgroup_iff,
    Set.mem_ofPred_eq, Set.notMem_empty, false_implies, implies_true, and_true]
  exact ⟨fun h i j hj ↦ h j hj i, fun h j hj i ↦ h i j hj⟩

theorem besselU0_le_besselU : besselU0 ϱ T ≤ besselU ϱ T := inf_le_left

theorem besselU0_le_frameFixingSubgroup : besselU0 ϱ T ≤ frameFixingSubgroup ϱ T := inf_le_right

theorem det_eq_one_of_mem_besselU {g : unitaryGroupOf (splitGram ϱ T)} (hg : g ∈ besselU ϱ T) :
    ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R).det = 1 :=
  ((mem_besselU ϱ T).mp hg).det_eq_one

end BesselSubgroups

end TauCeti
