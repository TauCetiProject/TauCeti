/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.InformationTheory.Hamming
public import TauCeti.LinearAlgebra.Submodule.Prod

/-!
# Direct sums of linear codes

This file defines the direct sum of two linear codes on the disjoint union of their coordinate
types. A word belongs to the direct sum precisely when its restrictions to the two summands belong
to the respective codes.

The direct sum is identified linearly with the product of the two codes. Consequently its dimension
is the sum of the dimensions and its cardinality is the product of the cardinalities. Hamming weight
and distance are additive across the two coordinate summands; consequently a natural number
divides all weights of a direct sum exactly when it divides all weights of both summands.
Canonical reindexings by the commutativity and associativity equivalences for `Sum` give the
corresponding code identities.

The construction follows the direct-sum convention in Huffman and Pless, *Fundamentals of
Error-Correcting Codes*, Section 1.6.
-/

public section

namespace Submodule

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
  rw [directSum, mem_map_equiv, LinearEquiv.symm_symm, mem_prod]
  rfl

/-- A word of the first code, extended by zeros, belongs to a direct sum. -/
theorem sumElim_zero_mem_directSum {C : Submodule R (ι → R)} (D : Submodule R (κ → R))
    {x : ι → R} (hx : x ∈ C) : Sum.elim x (0 : κ → R) ∈ directSum C D :=
  mem_directSum_iff.mpr ⟨hx, D.zero_mem⟩

/-- A word of the second code, extended by zeros, belongs to a direct sum. -/
theorem zero_sumElim_mem_directSum (C : Submodule R (ι → R)) {D : Submodule R (κ → R)}
    {y : κ → R} (hy : y ∈ D) : Sum.elim (0 : ι → R) y ∈ directSum C D :=
  mem_directSum_iff.mpr ⟨C.zero_mem, hy⟩

/-- The direct sum is linearly equivalent to the product of its two constituent codes. -/
def directSumEquivProd (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    directSum C D ≃ₗ[R] C × D :=
  ((LinearEquiv.sumArrowLequivProdArrow ι κ R R).symm.ofSubmodules (C.prod D) (directSum C D)
    (directSum.eq_1 C D).symm).symm.trans (prodEquiv C D)

private theorem directSumEquivProd_apply_eq (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : directSum C D) :
    directSumEquivProd C D x =
      (⟨fun i ↦ x.1 (.inl i), (mem_directSum_iff.mp x.2).1⟩,
        ⟨fun j ↦ x.1 (.inr j), (mem_directSum_iff.mp x.2).2⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    funext i
    simp only [directSumEquivProd, LinearEquiv.trans_apply, prodEquiv_apply,
      LinearEquiv.ofSubmodules_symm_apply, LinearEquiv.symm_symm,
      LinearEquiv.sumArrowLequivProdArrow_apply_fst]
  · apply Subtype.ext
    funext j
    simp only [directSumEquivProd, LinearEquiv.trans_apply, prodEquiv_apply,
      LinearEquiv.ofSubmodules_symm_apply, LinearEquiv.symm_symm,
      LinearEquiv.sumArrowLequivProdArrow_apply_snd]

@[simp]
theorem directSumEquivProd_apply_fst (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    (x : directSum C D) (i : ι) :
    (directSumEquivProd C D x).1.1 i = x.1 (.inl i) := by
  exact congrArg (fun y : C × D ↦ y.1.1 i) (directSumEquivProd_apply_eq C D x)

@[simp]
theorem directSumEquivProd_apply_snd (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    (x : directSum C D) (j : κ) :
    (directSumEquivProd C D x).2.1 j = x.1 (.inr j) := by
  exact congrArg (fun y : C × D ↦ y.2.1 j) (directSumEquivProd_apply_eq C D x)

@[simp]
theorem directSumEquivProd_symm_apply_inl (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : C) (y : D) (i : ι) :
    ((directSumEquivProd C D).symm (x, y)).1 (.inl i) = x.1 i := by
  have h := directSumEquivProd_apply_eq C D ((directSumEquivProd C D).symm (x, y))
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrArg (fun z : C × D ↦ z.1.1 i) h).symm

@[simp]
theorem directSumEquivProd_symm_apply_inr (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : C) (y : D) (j : κ) :
    ((directSumEquivProd C D).symm (x, y)).1 (.inr j) = y.1 j := by
  have h := directSumEquivProd_apply_eq C D ((directSumEquivProd C D).symm (x, y))
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrArg (fun z : C × D ↦ z.2.1 j) h).symm

/-- Direct sum is monotone in both constituent codes. -/
@[gcongr]
theorem directSum_mono {C C' : Submodule R (ι → R)} {D D' : Submodule R (κ → R)}
    (hC : C ≤ C') (hD : D ≤ D') : directSum C D ≤ directSum C' D' :=
  map_mono (prod_mono hC hD)

/-- Reindexing a direct sum by swapping the coordinate summands swaps the two codes. -/
@[simp]
theorem map_directSum_sumComm (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    (directSum C D).map
        (LinearEquiv.funCongrLeft R R (Equiv.sumComm κ ι)).toLinearMap =
      directSum D C := by
  ext x
  rw [mem_map_equiv, mem_directSum_iff, mem_directSum_iff]
  exact and_comm

/-- Reindexing an iterated direct sum by associating its coordinate summands associates the
three codes in the same way. -/
@[simp]
theorem map_directSum_sumAssoc (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    (E : Submodule R (ν → R)) :
    (directSum (directSum C D) E).map
        (LinearEquiv.funCongrLeft R R (Equiv.sumAssoc ι κ ν).symm).toLinearMap =
      directSum C (directSum D E) := by
  ext x
  simp only [mem_map_equiv, mem_directSum_iff]
  exact and_assoc

end Semiring

section Finrank

variable [Semiring R] [StrongRankCondition R]

/-- The dimension of a direct sum is the sum of the dimensions of its constituent codes. -/
@[simp]
theorem finrank_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R))
    [Module.Free R C] [Module.Free R D] [Module.Finite R C] [Module.Finite R D] :
    Module.finrank R (directSum C D) = Module.finrank R C + Module.finrank R D := by
  rw [(directSumEquivProd C D).finrank_eq, Module.finrank_prod]

end Finrank

section Cardinality

variable [Semiring R]

/-- The cardinality of a direct sum is the product of the cardinalities of its constituent
codes. -/
@[simp↓]
theorem natCard_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    Nat.card (directSum C D) = Nat.card C * Nat.card D := by
  rw [Nat.card_congr (directSumEquivProd C D).toEquiv, Nat.card_prod]

end Cardinality

section Hamming

variable [Semiring R] [DecidableEq R] [Fintype ι] [Fintype κ]

/-- Hamming weight is additive on words in a direct sum. -/
@[simp]
theorem hammingNorm_directSumEquivProd_symm (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x : C) (y : D) :
    hammingNorm ((directSumEquivProd C D).symm (x, y) : ι ⊕ κ → R) =
      hammingNorm x.1 + hammingNorm y.1 := by
  rw [← TauCeti.hammingNorm_sumElim x.1 y.1]
  apply congrArg hammingNorm
  funext i
  cases i <;> simp

/-- All weights of a direct sum are divisible by `k` exactly when this holds in both
constituent codes. -/
theorem forall_dvd_hammingNorm_directSum_iff (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (k : ℕ) :
    (∀ z ∈ directSum C D, k ∣ hammingNorm z) ↔
      (∀ x ∈ C, k ∣ hammingNorm x) ∧ ∀ y ∈ D, k ∣ hammingNorm y := by
  constructor
  · refine fun h ↦ ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · simpa using h _ (sumElim_zero_mem_directSum D hx)
    · simpa using h _ (zero_sumElim_mem_directSum C hy)
  · rintro ⟨hC, hD⟩ z hz
    rw [mem_directSum_iff] at hz
    rw [← Sum.elim_comp_inl_inr z, TauCeti.hammingNorm_sumElim]
    exact dvd_add (hC _ hz.1) (hD _ hz.2)

/-- Hamming distance is additive on pairs of words in a direct sum. -/
@[simp]
theorem hammingDist_directSumEquivProd_symm (C : Submodule R (ι → R))
    (D : Submodule R (κ → R)) (x x' : C) (y y' : D) :
    hammingDist ((directSumEquivProd C D).symm (x, y) : ι ⊕ κ → R)
        ((directSumEquivProd C D).symm (x', y') : ι ⊕ κ → R) =
      hammingDist x.1 x'.1 + hammingDist y.1 y'.1 := by
  rw [← TauCeti.hammingDist_sumElim x.1 x'.1 y.1 y'.1]
  apply congrArg₂ hammingDist
  · funext i
    cases i <;> simp
  · funext i
    cases i <;> simp

end Hamming

end Submodule
