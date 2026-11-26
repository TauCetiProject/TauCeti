/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup

/-!
# The split hermitian form, levels, floors and the Bessel subgroups

Let `R` be a commutative ring with involution, `ϱ` a natural number and `κ` a finite type. The
space `R^𝐁` has the basis `e₀, …, e_{ϱ-1}`, then a middle block `x_i` (`i ∈ κ`) and `z`, then
`e*₀, …, e*_{ϱ-1}`; the index type is `Matrix.BesselIndex ϱ κ`. For a matrix `T` on the
middle block, the **split form** `Matrix.splitGram ϱ T` pairs `e_a` with `e*_b` by
`δ_ab`, makes the hyperbolic pairs orthogonal to the middle block, and has Gram matrix `T` on the
middle block. Its unitary group is `Matrix.unitaryGroupOf (splitGram ϱ T)`.

The basis vectors carry a **level** (`a` for `e_a`, `ϱ` on the middle block, `2ϱ - a` for `e*_a`)
and a **floor** (`a` for `e_a` and `e*_a`, `ϱ` for `z`, `ϱ + 1` for `x_i`). The **frame** is
`(e₀, …, e_{ϱ-1}, z)`, and the **frame Gram matrix** of `γ` is the matrix of the products of the
frame with its image under `γ`.

The subgroups are cut out by conditions on entries.

* `Matrix.blockTriangularSubgroup lev`: the block upper triangular invertible matrices
  for a level function `lev`.
* `Matrix.agreeWithOneOn r`: the invertible matrices agreeing with `1` at the entries
  `(i, j)` with `r i j`, for a relation `r` such that `r i j` implies `r i k` or `r k j`.
* `Matrix.unitriangularSubgroup lev`: the block upper unitriangular matrices.
* `Matrix.besselU`, `Matrix.besselFixer`, `Matrix.besselU0`,
  `Matrix.floorFixer`: the unipotent Bessel group `𝖴` of isometries that are block
  unitriangular for the levels, the fixer of the frame, their intersection `𝖴⁰`, and the group
  `H_l` of isometries fixing every basis vector of floor `< l`.
* `Matrix.leviSubgroup τ`, `Matrix.parahoricSubgroup I τ`: the block diagonal
  matrices for a labelling `τ`, and the matrices whose entries below the blocks of `τ` lie in an
  ideal `I`; for the maximal ideal of a local ring this is the parahoric subgroup.

## Main results

* `Matrix.splitGram_isHermitian`: the split form of a hermitian `T` is hermitian.
* `Matrix.frameGram_one`: the frame Gram matrix of `1` has the single entry `T z z`.
* `Matrix.det_eq_one_of_mem_unitriangularSubgroup`: unitriangular matrices have det `1`.
* `Matrix.conj_mem_unitriangularSubgroup`: block triangular matrices normalize them.

## References

The definitions are adapted from the Lean project grh-lean, also called riemann-hypothesis
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/Groups/BesselGroups.lean` (declarations `New.Shape.Form.splitGram`,
`New.BesselIndex.level`, `New.parabolic`, `New.agreeWithOneOn`, `New.unitriangular`,
`New.Shape.Form.besselU`, `New.Shape.Form.besselU0`, `New.levi`, `New.parahoric`). Here the
Levi and parahoric subgroups are stated for any index type, commutative ring and ideal.
For the Bessel subgroups compare
* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical
  L-values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), Section 12.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-! ### Block triangular groups -/

section Triangular

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [LinearOrder α] (lev : n → α)

/-- The subgroup of `GL n R` of the block upper triangular matrices for the level function
`lev`. -/
def blockTriangularSubgroup : Subgroup (GL n R) where
  carrier := {g | (g : Matrix n n R).BlockTriangular lev}
  mul_mem' := BlockTriangular.mul
  one_mem' := blockTriangular_one
  inv_mem' := by simp_all [blockTriangular_inv_of_blockTriangular]

@[simp] theorem mem_blockTriangularSubgroup {g : GL n R} :
    g ∈ blockTriangularSubgroup lev ↔ (g : Matrix n n R).BlockTriangular lev := .rfl

open scoped Classical in
/-- For a relation `r` such that `r i j` implies `r i k` or `r k j` for every `k`, the subgroup
of the invertible matrices that agree with the identity matrix at every entry `(i, j)` with
`r i j`. -/
def agreeWithOneOn (r : n → n → Prop) (R : Type*) [CommRing R]
    (h_split : ∀ i k j : n, r i j → r i k ∨ r k j) : Subgroup (GL n R) :=
  Subgroup.ofDiv {u : GL n R | ∀ i j : n, r i j → u i j = (1 : Matrix n n R) i j} ⟨1, by simp⟩ <| by
    -- Compare `(x * y⁻¹) i j` with `(y * y⁻¹) i j` term by term. If `r i k` then `x i k = y i k`;
    -- otherwise `y⁻¹ k j = 0`, as `y` is block triangular for the level function that is `0`
    -- where `r i ·` holds and `1` elsewhere.
    intro x hx y hy i j hij
    have hy_inv : y⁻¹ ∈ blockTriangularSubgroup fun k : n ↦ if r i k then 0 else 1 := by
      refine (blockTriangularSubgroup _).inv_mem fun a b hab ↦ ?_
      obtain ⟨hib, hia⟩ : r i b ∧ ¬ r i a := by grind
      have hab_ne : a ≠ b := fun h_eq ↦ hia (by rwa [h_eq])
      exact (hy a b ((h_split i a b hib).resolve_left hia)).trans (one_apply_ne hab_ne)
    have h_term : ∀ k : n, x.val i k * y⁻¹.val k j = y.val i k * y⁻¹.val k j := fun k ↦ by
      by_cases hik : r i k
      · rw [hx i k hik, hy i k hik]
      · have h_zero : y⁻¹.val k j = 0 := hy_inv (by simp [hik, hij])
        rw [h_zero, mul_zero, mul_zero]
    calc (x.val * y⁻¹.val) i j = ∑ k : n, y.val i k * y⁻¹.val k j :=
          Finset.sum_congr rfl fun k _ ↦ h_term k
      _ = (1 : Matrix n n R) i j := by rw [← Matrix.mul_apply, y.mul_inv]

@[simp] theorem mem_agreeWithOneOn {r : n → n → Prop} {h_split : ∀ i k j : n, r i j → r i k ∨ r k j}
    {x : GL n R} :
    x ∈ agreeWithOneOn r R h_split ↔ ∀ i j : n, r i j → x i j = (1 : Matrix n n R) i j :=
  .rfl

/-- The subgroup of the block upper triangular matrices all of whose diagonal blocks are the
identity, for the level function `lev`. -/
abbrev unitriangularSubgroup (R : Type*) [CommRing R] : Subgroup (GL n R) :=
  agreeWithOneOn (fun i j : n ↦ lev j ≤ lev i) R fun i k _ hij ↦
    (le_total (lev k) (lev i)).imp_right hij.trans

theorem unitriangularSubgroup_le_blockTriangularSubgroup :
    unitriangularSubgroup lev R ≤ blockTriangularSubgroup lev := fun _ hu i j hij ↦
  (hu i j hij.le).trans (one_apply_ne fun h ↦ (h ▸ hij).false)

variable {lev}

/-- A matrix that agrees with the identity matrix at every entry `(i, j)` with
`lev j ≤ lev i` has determinant `1`. -/
theorem det_eq_one_of_mem_unitriangularSubgroup {u : GL n R}
    (hu : u ∈ unitriangularSubgroup lev R) : (u : Matrix n n R).det = 1 := by
  -- The determinant is the product of those of the diagonal blocks, which are `1`.
  have h_blocks : ∀ a : α, (u : Matrix n n R).toSquareBlock lev a = 1 := fun a ↦ by
    ext x y
    have hxy : lev y ≤ lev x := by rw [x.property, y.property]
    simp [toSquareBlock_def, hu x y hxy, Matrix.one_apply, Subtype.ext_iff]
  simp [(unitriangularSubgroup_le_blockTriangularSubgroup lev hu).det, h_blocks]

/-- If `d` is block upper triangular and `u` is block upper unitriangular for `lev`, then
`d⁻¹ * u * d` is block upper unitriangular for `lev`. -/
theorem conj_mem_unitriangularSubgroup {u d : GL n R} (hd : d ∈ blockTriangularSubgroup lev)
    (hu : u ∈ unitriangularSubgroup lev R) : d⁻¹ * u * d ∈ unitriangularSubgroup lev R := by
  -- In a nonzero term `d⁻¹ i k * u k l * d l j` we have `lev l ≤ lev j ≤ lev i ≤ lev k`, so
  -- that `u k l` is the entry of `1`.
  intro i j hij
  have hd_inv := (blockTriangularSubgroup lev).inv_mem hd
  have h_term : ∀ k l : n, d⁻¹.val i k * u.val k l * d.val l j =
      d⁻¹.val i k * (1 : Matrix n n R) k l * d.val l j := fun k l ↦ by
    grind [@hd_inv i k, @hd l j, hu k l, not_le]
  calc (d⁻¹ * u * d).val i j = (d⁻¹.val * (1 : Matrix n n R) * d.val) i j := by
        simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul, h_term]
    _ = (1 : Matrix n n R) i j := by simp

end Triangular

/-! ### Levi and parahoric subgroups -/

section Parahoric

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} (τ : n → α)

/-- The Levi subgroup of a labelling `τ`: the invertible matrices whose entry `(i, j)` vanishes
whenever `τ i ≠ τ j`. -/
def leviSubgroup (R : Type*) [CommRing R] : Subgroup (GL n R) :=
  (agreeWithOneOn (fun i j : n ↦ τ i ≠ τ j) R fun _ l _ hij ↦
      (hij.ne_or_ne (τ l)).imp_right Ne.symm).copy
    {g | ∀ i j : n, τ i ≠ τ j → (g : Matrix n n R) i j = 0} <| by
    ext g
    simp +contextual [ne_of_apply_ne τ]

@[simp] theorem mem_leviSubgroup {g : GL n R} :
    g ∈ leviSubgroup τ R ↔ ∀ i j : n, τ i ≠ τ j → (g : Matrix n n R) i j = 0 := .rfl

/-- The parahoric subgroup of a labelling `τ` relative to an ideal `I`: the invertible matrices
whose entry `(i, j)` lies in `I` whenever `τ i < τ j`. For the maximal ideal of a local ring
this is the parahoric subgroup of `τ`. -/
def parahoricSubgroup [LinearOrder α] (I : Ideal R) : Subgroup (GL n R) :=
  (blockTriangularSubgroup (OrderDual.toDual ∘ τ)).comap
    (GeneralLinearGroup.map (Ideal.Quotient.mk I))

theorem mem_parahoricSubgroup [LinearOrder α] (I : Ideal R) {g : GL n R} :
    g ∈ parahoricSubgroup τ I ↔ ∀ i j : n, τ i < τ j → (g : Matrix n n R) i j ∈ I := by
  simp [parahoricSubgroup, BlockTriangular, Ideal.Quotient.eq_zero_iff_mem]

theorem leviSubgroup_le_parahoricSubgroup [LinearOrder α] (I : Ideal R) :
    leviSubgroup τ R ≤ parahoricSubgroup τ I := fun _ hg ↦
  (mem_parahoricSubgroup τ I).2 fun i j hij ↦ hg i j hij.ne ▸ I.zero_mem

end Parahoric

/-! ### The basis, the split form, levels, floors and the frame -/

/-- The index set made of `ϱ` indices, a middle set `μ`, and `ϱ` further indices. -/
abbrev SplitIndex (ϱ : ℕ) (μ : Type*) : Type _ := Fin ϱ ⊕ μ ⊕ Fin ϱ

/-- The index set of the basis `e₀, …, e_{ϱ-1}, x_i (i ∈ κ), z, e*₀, …, e*_{ϱ-1}`. -/
abbrev BesselIndex (ϱ : ℕ) (κ : Type*) : Type _ := SplitIndex ϱ (κ ⊕ Unit)

/-- The index of the vector `z`. -/
abbrev BesselIndex.z (ϱ : ℕ) (κ : Type*) : BesselIndex ϱ κ := Sum.inr (Sum.inl (Sum.inr ()))

variable (ϱ : ℕ) {μ κ : Type*}

/-- The Gram matrix of `ϱ` hyperbolic planes and a middle block with Gram matrix `T`: identity
blocks pair the first and the last `ϱ` indices, `T` is the middle block, all else is zero. -/
def splitGram (T : Matrix μ μ R) : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (fromBlocks T 0 0 0)

variable {ϱ} (T : Matrix μ μ R)

@[simp] lemma splitGram_inl_inl (a b : Fin ϱ) : splitGram ϱ T (.inl a) (.inl b) = 0 := rfl
@[simp] lemma splitGram_inl_middle (a : Fin ϱ) (j : μ) :
    splitGram ϱ T (.inl a) (.inr (.inl j)) = 0 := rfl
@[simp] lemma splitGram_middle_inl (i : μ) (b : Fin ϱ) :
    splitGram ϱ T (.inr (.inl i)) (.inl b) = 0 := rfl
@[simp] lemma splitGram_middle_middle (i j : μ) :
    splitGram ϱ T (.inr (.inl i)) (.inr (.inl j)) = T i j := rfl
@[simp] lemma splitGram_inl_eStar (a b : Fin ϱ) :
    splitGram ϱ T (.inl a) (.inr (.inr b)) = (1 : Matrix (Fin ϱ) (Fin ϱ) R) a b := rfl
@[simp] lemma splitGram_eStar_inl (a b : Fin ϱ) :
    splitGram ϱ T (.inr (.inr a)) (.inl b) = (1 : Matrix (Fin ϱ) (Fin ϱ) R) a b := rfl
@[simp] lemma splitGram_middle_eStar (i : μ) (b : Fin ϱ) :
    splitGram ϱ T (.inr (.inl i)) (.inr (.inr b)) = 0 := rfl
@[simp] lemma splitGram_eStar_middle (a : Fin ϱ) (j : μ) :
    splitGram ϱ T (.inr (.inr a)) (.inr (.inl j)) = 0 := rfl
@[simp] lemma splitGram_eStar_eStar (a b : Fin ϱ) :
    splitGram ϱ T (.inr (.inr a)) (.inr (.inr b)) = 0 := rfl

/-- The split form of a hermitian matrix is hermitian. -/
theorem splitGram_isHermitian [StarRing R] {T : Matrix μ μ R} (hT : T.IsHermitian) :
    (splitGram ϱ T).IsHermitian := by
  ext (a | i | a) (b | j | b) <;>
    simp [hT.apply, (isHermitian_one (n := Fin ϱ) (α := R)).apply]

/-- The Gram matrix `diag(1_κ, -N)` on the middle block `κ ⊕ {z}`. -/
def middleGram [DecidableEq κ] (N : R) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R :=
  fromBlocks 1 0 0 (of fun _ _ ↦ -N)

theorem middleGram_isHermitian [StarRing R] [DecidableEq κ] {N : R} (hN : star N = N) :
    (middleGram (κ := κ) N).IsHermitian := by
  refine IsHermitian.fromBlocks isHermitian_one (by simp) ?_
  ext; simp [hN]

/-- The level of a basis index: `a` for `e_a`, `ϱ` on the middle block, `2ϱ - a` for `e*_a`. -/
def splitLevel : SplitIndex ϱ μ → ℕ :=
  Sum.elim (fun a ↦ a) (Sum.elim (fun _ ↦ ϱ) fun a ↦ 2 * ϱ - a)

@[simp] lemma splitLevel_inl (a : Fin ϱ) : splitLevel (μ := μ) (.inl a) = a := rfl
@[simp] lemma splitLevel_middle (i : μ) : splitLevel (ϱ := ϱ) (.inr (.inl i)) = ϱ := rfl
@[simp] lemma splitLevel_inr_inr (a : Fin ϱ) :
    splitLevel (μ := μ) (.inr (.inr a)) = 2 * ϱ - a := rfl

/-- The levels of the indices of the first block are below `ϱ`, those of the last block above. -/
lemma splitLevel_inl_lt (a : Fin ϱ) : splitLevel (μ := μ) (.inl a) < ϱ := a.isLt

lemma lt_splitLevel_inr_inr (a : Fin ϱ) : ϱ < splitLevel (μ := μ) (.inr (.inr a)) := by
  simp only [splitLevel_inr_inr]; omega

/-- The floor of a basis index: `a` for `e_a` and `e*_a`, `ϱ` for `z`, `ϱ + 1` for `x_i`. -/
def besselFloor : BesselIndex ϱ κ → ℕ :=
  Sum.elim (fun a ↦ a) (Sum.elim (Sum.elim (fun _ ↦ ϱ + 1) fun _ ↦ ϱ) fun a ↦ a)

/-- The indices of the frame `(e₀, …, e_{ϱ-1}, z)`. -/
def besselFrame : Fin (ϱ + 1) → BesselIndex ϱ κ := Fin.snoc Sum.inl (BesselIndex.z ϱ κ)

@[simp] lemma besselFrame_castSucc (a : Fin ϱ) : besselFrame (κ := κ) a.castSucc = .inl a := by
  simp [besselFrame]
@[simp] lemma besselFrame_last : besselFrame (κ := κ) (Fin.last ϱ) = BesselIndex.z ϱ κ := by
  simp [besselFrame]

variable [Fintype κ] [DecidableEq κ] (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)
  (γ : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)

/-- The matrix of the products of the frame with its image under `γ`, for the split form of
`T`. -/
def frameGram : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) R :=
  (splitGram ϱ T * γ).submatrix besselFrame besselFrame

/-- The frame Gram matrix of `1` has the single entry `T z z`, at the corner of `z`. -/
theorem frameGram_one :
    frameGram T 1 = single (Fin.last ϱ) (Fin.last ϱ) (T (.inr ()) (.inr ())) := by
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [frameGram, fun i : Fin ϱ ↦ (Fin.castSucc_lt_last i).ne']

/-! ### The Bessel subgroups -/

variable (ϱ) [StarRing R]

/-- The unipotent Bessel group `𝖴`: the isometries of the split form of `T` that are block
upper unitriangular for the levels. -/
def besselU : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (unitriangularSubgroup splitLevel R).subgroupOf _

/-- The isometries of the split form of `T` that fix each vector of the frame. -/
def besselFixer : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (agreeWithOneOn (fun _ j : BesselIndex ϱ κ ↦ j ∈ Set.range besselFrame) R
    fun _ _ _ hj ↦ Or.inr hj).subgroupOf _

/-- The elements of the unipotent Bessel group `𝖴` that fix each vector of the frame. -/
def besselU0 : Subgroup (unitaryGroupOf (splitGram ϱ T)) := besselU ϱ T ⊓ besselFixer ϱ T

/-- The group `H_l` of the isometries of the split form of `T` that fix every basis vector of
floor `< l`. -/
def floorFixer (l : ℕ) : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (agreeWithOneOn (fun _ j : BesselIndex ϱ κ ↦ besselFloor j < l) R
    fun _ _ _ hj ↦ Or.inr hj).subgroupOf _

theorem besselU0_le_besselU : besselU0 ϱ T ≤ besselU ϱ T := inf_le_left

theorem besselU0_le_besselFixer : besselU0 ϱ T ≤ besselFixer ϱ T := inf_le_right

theorem det_eq_one_of_mem_besselU {g : unitaryGroupOf (splitGram ϱ T)} (hg : g ∈ besselU ϱ T) :
    ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R).det = 1 :=
  det_eq_one_of_mem_unitriangularSubgroup hg

end Matrix
