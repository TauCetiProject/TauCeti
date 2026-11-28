/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Matched functions on complementary matrix blocks

An invertible matrix with columns indexed by `β ⊕ α` gives a column frame from its
`β`-columns and an annihilating row frame from the `α`-rows of its inverse. Functions on
these two frame spaces match if their values differ by the character of the determinant
of the completing matrix. Matching is the finite algebraic input for comparing theta
integrals on complementary spaces.

The matching relation and its use in a finite square law are from `grh-lean`,
`grh/src/New/Determinant/Chain/SquareLaw.lean`, at revision `72fead1`.
-/

public section

open Matrix MatrixGroups
open TauCeti (fromBlocksGL coe_fromBlocksGL)

namespace Matrix.GeneralLinearGroup

section Semiring

variable {R α β : Type*} [Semiring R] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The first column block of an invertible matrix in a sum decomposition. -/
def firstColumns (g : GL (β ⊕ α) R) : Matrix (β ⊕ α) β R :=
  (g : Matrix (β ⊕ α) (β ⊕ α) R).submatrix id Sum.inl

/-- The last row block of the inverse of an invertible matrix in a sum decomposition. -/
def invLastRows (g : GL (β ⊕ α) R) : Matrix α (β ⊕ α) R :=
  (↑g⁻¹ : Matrix (β ⊕ α) (β ⊕ α) R).submatrix Sum.inr id

/-- The entries of the first column block. -/
@[simp] theorem firstColumns_apply (g : GL (β ⊕ α) R) (i : β ⊕ α) (j : β) :
    g.firstColumns i j = (g : Matrix (β ⊕ α) (β ⊕ α) R) i (.inl j) := (rfl)

/-- The entries of the last row block of the inverse. -/
@[simp] theorem invLastRows_apply (g : GL (β ⊕ α) R) (i : α) (j : β ⊕ α) :
    g.invLastRows i j = (↑g⁻¹ : Matrix (β ⊕ α) (β ⊕ α) R) (.inr i) j := (rfl)

/-- Left multiplication transforms the column frame by the same matrix. -/
theorem firstColumns_mul (g k : GL (β ⊕ α) R) :
    (g * k).firstColumns = (g : Matrix (β ⊕ α) (β ⊕ α) R) * k.firstColumns := by
  simp only [firstColumns, Units.val_mul, submatrix_mul _ _ id id Sum.inl Function.bijective_id,
    submatrix_id_id]

/-- Left multiplication transforms the row frame by right multiplication by the inverse. -/
theorem invLastRows_mul (g k : GL (β ⊕ α) R) :
    (g * k).invLastRows = k.invLastRows * (↑g⁻¹ : Matrix (β ⊕ α) (β ⊕ α) R) := by
  have hinv : (g * k)⁻¹ = k⁻¹ * g⁻¹ := rfl
  unfold invLastRows
  rw [hinv, Units.val_mul, submatrix_mul _ _ Sum.inr id id Function.bijective_id, submatrix_id_id]

end Semiring

section Ring

variable {R α β : Type*} [Ring R] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Changing the basis in the first summand changes the column frame by that basis change. -/
theorem firstColumns_mul_fromBlocksGL (g : GL (β ⊕ α) R) (h : GL β R) (k : GL α R) :
    (g * fromBlocksGL (h, k)).firstColumns = g.firstColumns * (h : Matrix β β R) := by
  ext i j
  simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, coe_fromBlocksGL]

/-- Changing the basis in the first summand leaves the complementary inverse row block fixed. -/
@[simp] theorem invLastRows_mul_fromBlocksGL_one (g : GL (β ⊕ α) R) (h : GL β R) :
    (g * fromBlocksGL (h, 1)).invLastRows = g.invLastRows := by
  rw [invLastRows_mul]
  have hrow : (fromBlocksGL (h, 1)).invLastRows = (1 : GL (β ⊕ α) R).invLastRows := by
    unfold invLastRows
    rw [← map_inv]
    ext i j
    cases j <;> simp [coe_fromBlocksGL, Matrix.one_apply]
  rw [hrow]
  simp only [invLastRows, inv_one, Units.val_one]
  simpa using (one_submatrix_mul Sum.inr (Equiv.refl (β ⊕ α))
    (↑g⁻¹ : Matrix (β ⊕ α) (β ⊕ α) R))

end Ring

variable {R α β : Type*} [CommRing R] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Two completions of the same inverse row block have column frames related by a basis change.
The determinant of this basis change is the ratio of the completing determinants. -/
theorem exists_firstColumns_eq_mul_of_invLastRows_eq {g k : GL (β ⊕ α) R}
    (h : g.invLastRows = k.invLastRows) :
    ∃ u : GL β R, k.firstColumns = g.firstColumns * (u : Matrix β β R) ∧
      (k : Matrix (β ⊕ α) (β ⊕ α) R).det =
        (g : Matrix (β ⊕ α) (β ⊕ α) R).det * (u : Matrix β β R).det := by
  let t := g⁻¹ * k
  have ht : g * t = k := by simp [t]
  have hrow : ((t : Matrix (β ⊕ α) (β ⊕ α) R).submatrix Sum.inr id) =
      (1 : Matrix (β ⊕ α) (β ⊕ α) R).submatrix Sum.inr id := by
    rw [coe_mul, submatrix_mul _ _ Sum.inr id id Function.bijective_id, submatrix_id_id]
    rw [← invLastRows, h, invLastRows]
    have hcancel : (↑k⁻¹ : Matrix (β ⊕ α) (β ⊕ α) R) * (↑k : Matrix _ _ _) = 1 :=
      Units.inv_mul k
    simpa only [submatrix_mul _ _ Sum.inr id id Function.bijective_id, submatrix_id_id] using
      congrArg (fun a : Matrix (β ⊕ α) (β ⊕ α) R ↦ a.submatrix Sum.inr id) hcancel
  have h₂₁ : (t : Matrix (β ⊕ α) (β ⊕ α) R).toBlocks₂₁ = 0 := by
    ext i j
    simpa [Matrix.toBlocks₂₁, Matrix.one_apply] using congrFun (congrFun hrow i) (.inl j)
  have h₂₂ : (t : Matrix (β ⊕ α) (β ⊕ α) R).toBlocks₂₂ = 1 := by
    ext i j
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using congrFun (congrFun hrow i) (.inr j)
  let u := t.toBlocks₁₁GL h₂₁ h₂₂
  refine ⟨u, ?_, ?_⟩
  · rw [← ht, coe_toBlocks₁₁GL]
    ext i j
    have hz (i : α) (j : β) : (t : Matrix (β ⊕ α) (β ⊕ α) R) (.inr i) (.inl j) = 0 :=
      congrFun (congrFun h₂₁ i) j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, hz]
  · rw [← ht, coe_mul, det_mul]
    congr 1
    rw [coe_toBlocks₁₁GL, ← fromBlocks_toBlocks (t : Matrix (β ⊕ α) (β ⊕ α) R),
      h₂₁, h₂₂, det_fromBlocks_zero₂₁, det_one, mul_one, toBlocks_fromBlocks₁₁]

end Matrix.GeneralLinearGroup

namespace TauCeti

open Matrix.GeneralLinearGroup

variable {R α β C : Type*} [CommRing R] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [CommMonoidWithZero C]

/-- A matching for `χ` consists of a row function `Φ` and a column function `Ψ` vanishing
outside the complementary blocks of invertible matrices. On a common completion `g`,
the row value is `χ(det g)` times the column value. -/
structure AreMatched (χ : MulChar R C) (Φ : Matrix α (β ⊕ α) R → C)
    (Ψ : Matrix (β ⊕ α) β R → C) : Prop where
  /-- The row function vanishes outside the inverse row frames. -/
  row_eq_zero : ∀ x ∉ Set.range (invLastRows (R := R) (β := β) (α := α)), Φ x = 0
  /-- The column function vanishes outside the column frames. -/
  column_eq_zero : ∀ y ∉ Set.range (firstColumns (R := R) (β := β) (α := α)), Ψ y = 0
  /-- The matched values at each completion. -/
  apply_eq (g : GL (β ⊕ α) R) :
    Φ g.invLastRows = χ (g : Matrix (β ⊕ α) (β ⊕ α) R).det * Ψ g.firstColumns

variable {χ : MulChar R C} {Φ Φ' : Matrix α (β ⊕ α) R → C}
  {Ψ Ψ' : Matrix (β ⊕ α) β R → C}

/-- The column value transforms by the inverse determinant character under a basis change. -/
theorem AreMatched.column_mul (h : AreMatched χ Φ Ψ) (g : GL (β ⊕ α) R) (u : GL β R) :
    χ (u : Matrix β β R).det * Ψ (g.firstColumns * (u : Matrix β β R)) = Ψ g.firstColumns := by
  have hu : IsUnit (χ (g : Matrix (β ⊕ α) (β ⊕ α) R).det) :=
    (Matrix.GeneralLinearGroup.det g).isUnit.map χ
  apply hu.mul_left_cancel
  have h' := h.apply_eq (g * fromBlocksGL (u, 1))
  rw [invLastRows_mul_fromBlocksGL_one, firstColumns_mul_fromBlocksGL, coe_mul,
    coe_fromBlocksGL, det_mul, coe_one, det_fromBlocks_zero₂₁, det_one, mul_one, map_mul,
    mul_assoc, h.apply_eq g] at h'
  exact h'.symm

/-- Matching determines the row function uniquely. -/
theorem AreMatched.left_unique (h : AreMatched χ Φ Ψ) (h' : AreMatched χ Φ' Ψ) : Φ = Φ' := by
  funext x
  by_cases hx : x ∈ Set.range (invLastRows (R := R) (β := β) (α := α))
  · obtain ⟨g, rfl⟩ := hx
    exact (h.apply_eq g).trans (h'.apply_eq g).symm
  · rw [h.row_eq_zero x hx, h'.row_eq_zero x hx]

/-- Matching also determines the column function uniquely. -/
theorem AreMatched.right_unique (h : AreMatched χ Φ Ψ) (h' : AreMatched χ Φ Ψ') : Ψ = Ψ' := by
  funext y
  by_cases hy : y ∈ Set.range (firstColumns (R := R) (β := β) (α := α))
  · obtain ⟨g, rfl⟩ := hy
    exact ((Matrix.GeneralLinearGroup.det g).isUnit.map χ).mul_left_cancel
      ((h.apply_eq g).symm.trans (h'.apply_eq g))
  · rw [h.column_eq_zero y hy, h'.column_eq_zero y hy]

/-- A column function has a unique match if it is supported on column frames and transforms
by the inverse determinant character under basis changes of those frames. -/
theorem existsUnique_areMatched
    (hΨ : ∀ y ∉ Set.range (firstColumns (R := R) (β := β) (α := α)), Ψ y = 0)
    (hequiv : ∀ (g : GL (β ⊕ α) R) (u : GL β R),
      χ (u : Matrix β β R).det * Ψ (g.firstColumns * (u : Matrix β β R)) =
        Ψ g.firstColumns) :
    ∃! Φ, AreMatched χ Φ Ψ := by
  classical
  let Φ (x : Matrix α (β ⊕ α) R) :=
    if hx : x ∈ Set.range (invLastRows (R := R) (β := β) (α := α)) then
      χ (hx.choose : Matrix (β ⊕ α) (β ⊕ α) R).det * Ψ hx.choose.firstColumns else 0
  have hm : AreMatched χ Φ Ψ := by
    refine ⟨fun x hx ↦ dite_eq_right hx, hΨ, fun g ↦ ?_⟩
    have hg : g.invLastRows ∈ Set.range (invLastRows (R := R) (β := β) (α := α)) := ⟨g, rfl⟩
    obtain ⟨u, hu, hdet⟩ := exists_firstColumns_eq_mul_of_invLastRows_eq hg.choose_spec.symm
    simp only [Φ, dite_eq_left hg, hu, hdet, map_mul, mul_assoc, hequiv]
  exact ⟨Φ, hm, fun _ h' ↦ h'.left_unique hm⟩

/-- Support on the column frames and the determinant transformation law characterize
which column functions admit a match. -/
theorem exists_areMatched_iff :
    (∃ Φ, AreMatched χ Φ Ψ) ↔
      (∀ y ∉ Set.range (firstColumns (R := R) (β := β) (α := α)), Ψ y = 0) ∧
      ∀ (g : GL (β ⊕ α) R) (u : GL β R),
        χ (u : Matrix β β R).det * Ψ (g.firstColumns * (u : Matrix β β R)) =
          Ψ g.firstColumns :=
  ⟨fun ⟨_, h⟩ ↦ ⟨h.column_eq_zero, h.column_mul⟩,
    fun ⟨hs, he⟩ ↦ (existsUnique_areMatched (χ := χ) hs he).exists⟩

/-- Translating the column frame by the inverse of `k` corresponds to right translation on
row frames, with the row function multiplied by the character of `det k`. -/
theorem AreMatched.translate (h : AreMatched χ Φ Ψ) (k : GL (β ⊕ α) R) :
    AreMatched χ (fun x ↦ χ (k : Matrix (β ⊕ α) (β ⊕ α) R).det *
      Φ (x * (k : Matrix (β ⊕ α) (β ⊕ α) R)))
      (fun y ↦ Ψ ((↑k⁻¹ : Matrix (β ⊕ α) (β ⊕ α) R) * y)) := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_, fun g ↦ ?_⟩
  · rw [h.row_eq_zero _ (fun ⟨g, hg⟩ ↦ hx ⟨k * g, by
      rw [invLastRows_mul, hg, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]⟩), mul_zero]
  · exact h.column_eq_zero _ (fun ⟨g, hg⟩ ↦ hy ⟨k * g, by
      rw [firstColumns_mul, hg, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩)
  · have hr := invLastRows_mul k⁻¹ g
    have hc := firstColumns_mul k⁻¹ g
    simp only [inv_inv] at hr
    have hm : (k : Matrix (β ⊕ α) (β ⊕ α) R) * ((k⁻¹ * g : GL (β ⊕ α) R) :
        Matrix (β ⊕ α) (β ⊕ α) R) = (g : Matrix (β ⊕ α) (β ⊕ α) R) := by
      rw [← coe_mul, mul_inv_cancel_left]
    rw [← hr, ← hc, h.apply_eq (k⁻¹ * g), ← mul_assoc, ← map_mul, ← det_mul, hm]

end TauCeti
