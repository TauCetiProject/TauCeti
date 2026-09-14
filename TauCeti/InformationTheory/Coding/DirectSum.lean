module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.InformationTheory.Hamming

/-!
# Direct sums of linear codes

This file defines the direct sum of two linear codes on the disjoint union of their coordinate
types. A word belongs to the direct sum precisely when its restrictions to the two summands belong
to the respective codes.

The direct sum is identified linearly with the product of the two codes. Consequently its dimension
is the sum of the dimensions and its cardinality is the product of the cardinalities. Hamming weight
and distance are additive across the two coordinate summands. Canonical reindexings by the
commutativity and associativity equivalences for `Sum` give the corresponding code identities.

The construction follows the direct-sum convention in Huffman and Pless, *Fundamentals of
Error-Correcting Codes*, Section 1.6.
-/

@[expose] public section

namespace TauCeti

namespace LinearCode

variable {R ι κ ν : Type*}

section Semiring

variable [Semiring R]

/-- The direct sum of two linear codes, on the disjoint union of their coordinate types. -/
def directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    Submodule R (ι ⊕ κ → R) :=
  (C.prod D).map (LinearEquiv.sumArrowLequivProdArrow ι κ R R).symm.toLinearMap

/-- A word belongs to a direct sum exactly when each of its two restrictions belongs to the
corresponding code. -/
@[simp]
theorem mem_directSum_iff {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
    {x : ι ⊕ κ → R} :
    x ∈ directSum C D ↔ (fun i ↦ x (.inl i)) ∈ C ∧ (fun j ↦ x (.inr j)) ∈ D := by
  let e := LinearEquiv.sumArrowLequivProdArrow ι κ R R
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨e x, hx, ?_⟩
    exact e.symm_apply_apply x

/-- The direct sum is linearly equivalent to the product of its two constituent codes. -/
def directSumEquivProd (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    directSum C D ≃ₗ[R] C × D :=
  ((LinearEquiv.sumArrowLequivProdArrow ι κ R R).symm.submoduleMap (C.prod D)).symm.trans
    { toFun := fun x ↦ (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun x ↦ ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      map_add' := by simp
      map_smul' := by simp
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }

@[simp]
theorem directSumEquivProd_apply_fst (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    (x : directSum C D) (i : ι) :
    (directSumEquivProd C D x).1.1 i = x.1 (.inl i) :=
  rfl

@[simp]
theorem directSumEquivProd_apply_snd (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    (x : directSum C D) (j : κ) :
    (directSumEquivProd C D x).2.1 j = x.1 (.inr j) :=
  rfl

@[simp]
theorem directSumEquivProd_symm_apply_inl (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : C) (y : D) (i : ι) :
    ((directSumEquivProd C D).symm (x, y)).1 (.inl i) = x.1 i :=
  rfl

@[simp]
theorem directSumEquivProd_symm_apply_inr (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : C) (y : D) (j : κ) :
    ((directSumEquivProd C D).symm (x, y)).1 (.inr j) = y.1 j :=
  rfl

/-- Direct sum is monotone in both constituent codes. -/
@[gcongr]
theorem directSum_mono {C C' : Submodule R (ι → R)} {D D' : Submodule R (κ → R)}
    (hC : C ≤ C') (hD : D ≤ D') : directSum C D ≤ directSum C' D' := by
  intro x hx
  rw [mem_directSum_iff] at hx ⊢
  exact ⟨hC hx.1, hD hx.2⟩

/-- Reindexing a direct sum by swapping the coordinate summands swaps the two codes. -/
theorem map_directSum_sumComm (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    (directSum C D).map
        (LinearEquiv.funCongrLeft R R (Equiv.sumComm κ ι)).toLinearMap =
      directSum D C := by
  let e := LinearEquiv.funCongrLeft R R (Equiv.sumComm κ ι)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_directSum_iff.mpr
    exact (mem_directSum_iff.mp hy).symm
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_directSum_iff.mpr
    exact (mem_directSum_iff.mp hx).symm

/-- Reindexing an iterated direct sum by associating its coordinate summands associates the
three codes in the same way. -/
theorem map_directSum_sumAssoc (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    (E : Submodule R (ν → R)) :
    (directSum (directSum C D) E).map
        (LinearEquiv.funCongrLeft R R (Equiv.sumAssoc ι κ ν).symm).toLinearMap =
      directSum C (directSum D E) := by
  let e := LinearEquiv.funCongrLeft R R (Equiv.sumAssoc ι κ ν).symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_directSum_iff.mpr
    have hy' := mem_directSum_iff.mp hy
    have hyLeft := mem_directSum_iff.mp hy'.1
    exact ⟨hyLeft.1, mem_directSum_iff.mpr ⟨hyLeft.2, hy'.2⟩⟩
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_directSum_iff.mpr
    have hx' := mem_directSum_iff.mp hx
    have hxRight := mem_directSum_iff.mp hx'.2
    exact ⟨mem_directSum_iff.mpr ⟨hx'.1, hxRight.1⟩, hxRight.2⟩

end Semiring

section DivisionRing

variable [DivisionRing R]

/-- The dimension of a direct sum is the sum of the dimensions of its constituent codes. -/
@[simp]
theorem finrank_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    [Module.Finite R C] [Module.Finite R D] :
    Module.finrank R (directSum C D) = Module.finrank R C + Module.finrank R D := by
  rw [(directSumEquivProd C D).finrank_eq, Module.finrank_prod]

end DivisionRing

section Cardinality

variable [Semiring R]

/-- The cardinality of a direct sum is the product of the cardinalities of its constituent
codes. -/
@[simp]
theorem natCard_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    Nat.card { x : ι ⊕ κ → R //
      (fun i ↦ x (.inl i)) ∈ C ∧ (fun j ↦ x (.inr j)) ∈ D } =
      Nat.card C * Nat.card D := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_directSum_iff.symm),
    Nat.card_congr (directSumEquivProd C D).toEquiv, Nat.card_prod]

end Cardinality

section Hamming

variable [Semiring R] [DecidableEq R] [Fintype ι] [Fintype κ]

/-- Hamming weight is additive on words in a direct sum. -/
@[simp]
theorem hammingNorm_directSumEquivProd_symm (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : C) (y : D) :
    hammingNorm ((directSumEquivProd C D).symm (x, y) : ι ⊕ κ → R) =
      hammingNorm x.1 + hammingNorm y.1 := by
  rw [← hammingNorm_sumElim x.1 y.1]
  apply congrArg hammingNorm
  funext i
  cases i <;> simp

/-- Hamming distance is additive on pairs of words in a direct sum. -/
@[simp]
theorem hammingDist_directSumEquivProd_symm (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x x' : C) (y y' : D) :
    hammingDist ((directSumEquivProd C D).symm (x, y) : ι ⊕ κ → R)
        ((directSumEquivProd C D).symm (x', y') : ι ⊕ κ → R) =
      hammingDist x.1 x'.1 + hammingDist y.1 y'.1 := by
  rw [← hammingDist_sumElim x.1 x'.1 y.1 y'.1]
  apply congrArg₂ hammingDist
  · funext i
    cases i <;> simp
  · funext i
    cases i <;> simp

end Hamming

end LinearCode

end TauCeti
