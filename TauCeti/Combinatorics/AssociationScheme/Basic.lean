/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp

/-!
# Symmetric association schemes and the Bose–Mesner algebra

A symmetric association scheme with `d` classes on a finite type `X` is a class function
`rel : X → X → Fin (d + 1)` partitioning `X × X` into the diagonal class `0` and `d` nonempty
symmetric classes such that, for any classes `i`, `j` and any pair `(x, y)`, the number of `z`
with `rel x z = i` and `rel z y = j` depends only on `rel x y`.

The `0/1` adjacency matrices `adjMat rel i` (`A_i`) form a basis of the `(d + 1)`-dimensional
real subspace `bmAlgebra rel` (the Bose–Mesner algebra). It contains the identity `I` (`A_0`) and
the all-ones matrix `J` (`∑ i, A_i`), consists of symmetric matrices, is closed under both matrix
multiplication (`A_i * A_j = ∑ k, p^k_ij A_k`) and the entrywise Hadamard product
(`A_i ⊙ A_j = δ_ij A_i`), and is commutative.

The valencies `valency rel i` (`v_i`) and intersection numbers `intersectionNumber rel i j k`
(`p^k_ij`) are defined as global averages over pairs and triples so they are always well-defined,
and agree with the common local counts on any symmetric association scheme.

## Main definitions

* `TauCeti.IsAssocScheme`: axioms of a symmetric association scheme with `d` classes.
* `TauCeti.adjMat`: the `0/1` adjacency matrix `A_i` of class `i`.
* `TauCeti.bmAlgebra`: the Bose–Mesner algebra as a real subspace of matrices.
* `TauCeti.valency`: the averaged valency `v_i` of class `i`.
* `TauCeti.intersectionNumber`: the averaged intersection number `p^k_ij`.
* `TauCeti.IsAssocScheme.bmSubalgebra`: the Bose–Mesner algebra packaged as a real `Subalgebra`.
* `TauCeti.IsAssocScheme.adjMatBasis`: the basis of `bmAlgebra rel` given by the `adjMat rel i`.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012,
  §§11.1–11.2.
* C. Godsil, *Association Schemes*, lecture notes, 2010, §§1.1, 1.3.
-/

public section

namespace TauCeti

open Finset Matrix
open scoped Matrix

section General

variable {X : Type*} {d : ℕ}

/-- A symmetric association scheme with `d` classes, given by its class function: class `0`
is the diagonal, every class is symmetric and nonempty, and for all `i`, `j` the number of `z`
with `rel x z = i` and `rel z y = j` depends only on the class of `(x, y)`. -/
structure IsAssocScheme [Fintype X] (rel : X → X → Fin (d + 1)) : Prop where
  /-- Class `0` is the diagonal relation. -/
  rel_eq_zero_iff : ∀ x y, rel x y = 0 ↔ x = y
  /-- Every class is symmetric. -/
  rel_comm : ∀ x y, rel x y = rel y x
  /-- Every class is nonempty. -/
  exists_rel_eq : ∀ i, ∃ x y, rel x y = i
  /-- The number of intermediate vertices in classes `i` and `j` depends only on `rel x y`. -/
  card_eq : ∀ i j x y x' y', rel x y = rel x' y' →
    #{z | rel x z = i ∧ rel z y = j} = #{z | rel x' z = i ∧ rel z y' = j}

/-- The adjacency matrix `A_i` of class `i`: the real `0/1` matrix of the relation
`rel x y = i`. -/
def adjMat (rel : X → X → Fin (d + 1)) (i : Fin (d + 1)) : Matrix X X ℝ :=
  Matrix.of fun x y => if rel x y = i then 1 else 0

/-- The Bose–Mesner algebra: the real span of the adjacency matrices of the classes. -/
def bmAlgebra (rel : X → X → Fin (d + 1)) : Submodule ℝ (Matrix X X ℝ) :=
  Submodule.span ℝ (Set.range (adjMat rel))

/-- The valency `v_i` of class `i`: the number of ordered pairs in class `i` divided by
`|X|`. On a scheme it is the number of `y` with `rel x y = i`, for every `x`. -/
noncomputable def valency [Fintype X] (rel : X → X → Fin (d + 1)) (i : Fin (d + 1)) : ℝ :=
  (#{p : X × X | rel p.1 p.2 = i} : ℝ) / Fintype.card X

/-- The intersection number `p^k_(ij)`: the number of triples `(x, y, z)` with `(x, y)` in
class `k`, `(x, z)` in class `i` and `(z, y)` in class `j`, divided by the number of pairs in
class `k`. On a scheme it is the common number of such `z` for each pair in class `k`. -/
noncomputable def intersectionNumber [Fintype X] (rel : X → X → Fin (d + 1))
    (i j k : Fin (d + 1)) : ℝ :=
  (#{t : X × X × X | rel t.1 t.2.1 = k ∧ rel t.1 t.2.2 = i ∧ rel t.2.2 t.2.1 = j} : ℝ) /
    #{p : X × X | rel p.1 p.2 = k}

@[simp]
theorem adjMat_apply (rel : X → X → Fin (d + 1)) (i : Fin (d + 1)) (x y : X) :
    adjMat rel i x y = if rel x y = i then 1 else 0 :=
  (rfl)

theorem adjMat_nonneg (rel : X → X → Fin (d + 1)) (i : Fin (d + 1)) (x y : X) :
    0 ≤ adjMat rel i x y := by
  rw [adjMat_apply]
  split_ifs <;> norm_num

@[simp]
theorem adjMat_mem_bmAlgebra (rel : X → X → Fin (d + 1)) (i : Fin (d + 1)) :
    adjMat rel i ∈ bmAlgebra rel :=
  Submodule.subset_span ⟨i, rfl⟩

/-- An element lies in `bmAlgebra rel` iff it lies in the span of the adjacency matrices. -/
theorem mem_bmAlgebra_iff (rel : X → X → Fin (d + 1)) {M : Matrix X X ℝ} :
    M ∈ bmAlgebra rel ↔ M ∈ Submodule.span ℝ (Set.range (adjMat rel)) :=
  (Iff.rfl)

/-- The Bose–Mesner algebra equals the real span of the adjacency matrices. -/
theorem bmAlgebra_eq_span (rel : X → X → Fin (d + 1)) :
    bmAlgebra rel = Submodule.span ℝ (Set.range (adjMat rel)) := by
  exact (rfl)

/-- The adjacency matrices partition `X × X`, so their sum is the all-ones matrix `J`. -/
@[simp]
theorem sum_adjMat (rel : X → X → Fin (d + 1)) :
    ∑ i, adjMat rel i = Matrix.of fun _ _ => 1 := by
  ext x y
  simp

/-- The all-ones matrix `J` lies in the Bose–Mesner algebra. -/
theorem allOnes_mem_bmAlgebra (rel : X → X → Fin (d + 1)) :
    (Matrix.of fun _ _ : X => (1 : ℝ)) ∈ bmAlgebra rel := by
  rw [← sum_adjMat rel]
  exact Submodule.sum_mem _ fun i _ => adjMat_mem_bmAlgebra rel i

/-- The Hadamard product of two adjacency matrices is the diagonal delta:
`A_i ⊙ A_j = δ_ij A_i`. -/
theorem adjMat_hadamard (rel : X → X → Fin (d + 1)) (i j : Fin (d + 1)) :
    adjMat rel i ⊙ adjMat rel j = if i = j then adjMat rel i else 0 := by
  ext x y
  by_cases hij : i = j
  · subst hij
    by_cases hxy : rel x y = i <;> simp [hxy]
  · by_cases hxy : rel x y = i <;> simp [hxy, hij]

@[simp]
theorem adjMat_hadamard_self (rel : X → X → Fin (d + 1)) (i : Fin (d + 1)) :
    adjMat rel i ⊙ adjMat rel i = adjMat rel i := by
  simp [adjMat_hadamard]

theorem adjMat_hadamard_of_ne (rel : X → X → Fin (d + 1)) {i j : Fin (d + 1)} (hij : i ≠ j) :
    adjMat rel i ⊙ adjMat rel j = 0 := by
  simp [adjMat_hadamard, hij]

/-- The Bose–Mesner algebra is closed under the entrywise Hadamard product. -/
theorem hadamard_mem_bmAlgebra (rel : X → X → Fin (d + 1)) {M N : Matrix X X ℝ}
    (hM : M ∈ bmAlgebra rel) (hN : N ∈ bmAlgebra rel) : M ⊙ N ∈ bmAlgebra rel := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hN using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [adjMat_hadamard]
      split_ifs
      · exact adjMat_mem_bmAlgebra rel i
      · exact Submodule.zero_mem _
    | zero => simp
    | add _ _ _ _ h1 h2 => simpa [Matrix.hadamard_add] using Submodule.add_mem _ h1 h2
    | smul c _ _ h1 => simpa [Matrix.hadamard_smul] using Submodule.smul_mem _ c h1
  | zero => simp
  | add _ _ _ _ h1 h2 => simpa [Matrix.add_hadamard] using Submodule.add_mem _ h1 h2
  | smul c _ _ h1 => simpa [Matrix.smul_hadamard] using Submodule.smul_mem _ c h1

theorem adjMat_mul_apply [Fintype X] (rel : X → X → Fin (d + 1)) (i j : Fin (d + 1)) (x y : X) :
    (adjMat rel i * adjMat rel j) x y = (#{z | rel x z = i ∧ rel z y = j} : ℝ) := by
  rw [Matrix.mul_apply, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h1 : rel x z = i <;> by_cases h2 : rel z y = j <;> simp [h1, h2]

theorem sum_adjMat_mul_entry [Fintype X] (rel : X → X → Fin (d + 1)) (i j : Fin (d + 1)) :
    ∑ x, ∑ y, adjMat rel i x y * adjMat rel j x y =
      if i = j then (#{p : X × X | rel p.1 p.2 = i} : ℝ) else 0 := by
  have h : ∀ x y, adjMat rel i x y * adjMat rel j x y = (adjMat rel i ⊙ adjMat rel j) x y :=
    fun _ _ => rfl
  simp_rw [h, adjMat_hadamard]
  split_ifs with hij
  · rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases hp : rel x y = i <;> simp [hp]
  · simp

/-- The valencies of the classes sum to `|X|`. -/
theorem sum_valency [Fintype X] (rel : X → X → Fin (d + 1)) :
    ∑ i, valency rel i = Fintype.card X := by
  have hcard : ∑ i : Fin (d + 1), #{p : X × X | rel p.1 p.2 = i} =
      Fintype.card X * Fintype.card X := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    simp [Fintype.card_prod]
  simp_rw [valency, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hcard, Nat.cast_mul,
    ← div_eq_mul_inv]
  by_cases hX : (Fintype.card X : ℝ) = 0
  · simp [hX]
  · exact mul_div_cancel_right₀ _ hX

theorem intersectionNumber_nonneg [Fintype X] (rel : X → X → Fin (d + 1))
    (i j k : Fin (d + 1)) : 0 ≤ intersectionNumber rel i j k :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end General

namespace IsAssocScheme

variable {X : Type*} [Fintype X] {d : ℕ} {rel : X → X → Fin (d + 1)}

/-- A symmetric association scheme has a nonempty ground set (class `0` is nonempty). -/
theorem nonempty (h : IsAssocScheme rel) : Nonempty X :=
  let ⟨x, _, _⟩ := h.exists_rel_eq 0
  ⟨x⟩

theorem card_pos (h : IsAssocScheme rel) : 0 < Fintype.card X :=
  Fintype.card_pos_iff.mpr h.nonempty

theorem rel_self (h : IsAssocScheme rel) (x : X) : rel x x = 0 :=
  (h.rel_eq_zero_iff x x).mpr rfl

/-- The adjacency matrix of class `0` is the identity matrix. -/
theorem adjMat_zero [DecidableEq X] (h : IsAssocScheme rel) : adjMat rel 0 = 1 := by
  ext x y
  simp [Matrix.one_apply, h.rel_eq_zero_iff]

/-- The identity matrix lies in the Bose–Mesner algebra. -/
theorem one_mem_bmAlgebra [DecidableEq X] (h : IsAssocScheme rel) :
    (1 : Matrix X X ℝ) ∈ bmAlgebra rel := by
  rw [← h.adjMat_zero]
  exact adjMat_mem_bmAlgebra rel 0

/-- Every adjacency matrix of a symmetric association scheme is symmetric. -/
theorem adjMat_transpose (h : IsAssocScheme rel) (i : Fin (d + 1)) :
    (adjMat rel i)ᵀ = adjMat rel i := by
  ext x y
  simp [h.rel_comm x y]

/-- Every matrix in the Bose–Mesner algebra is symmetric. -/
theorem transpose_eq_of_mem_bmAlgebra (h : IsAssocScheme rel) {M : Matrix X X ℝ}
    (hM : M ∈ bmAlgebra rel) : Mᵀ = M := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h.adjMat_transpose i
  | zero => simp
  | add _ _ _ _ h1 h2 => simp [h1, h2]
  | smul c _ _ h1 => simp [h1]

/-- Every adjacency matrix of a symmetric association scheme is nonzero. -/
theorem adjMat_ne_zero (h : IsAssocScheme rel) (i : Fin (d + 1)) : adjMat rel i ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := h.exists_rel_eq i
  intro h0
  have := congrArg (fun M : Matrix X X ℝ => M x y) h0
  simp [hxy] at this

/-- The adjacency matrices of a symmetric association scheme are linearly independent. -/
theorem linearIndependent_adjMat (h : IsAssocScheme rel) : LinearIndependent ℝ (adjMat rel) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨x, y, hxy⟩ := h.exists_rel_eq i
  have hxy' := congrArg (fun M : Matrix X X ℝ => M x y) hc
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, adjMat_apply, Matrix.zero_apply]
    at hxy'
  rw [Finset.sum_eq_single i] at hxy'
  · simpa [hxy] using hxy'
  · intro j _ hji
    simp [hxy, hji.symm]
  · simp

/-- The adjacency matrices form a basis of the Bose–Mesner algebra. -/
noncomputable def adjMatBasis (h : IsAssocScheme rel) :
    Module.Basis (Fin (d + 1)) ℝ (bmAlgebra rel) :=
  Module.Basis.span h.linearIndependent_adjMat

@[simp]
theorem coe_adjMatBasis (h : IsAssocScheme rel) (i : Fin (d + 1)) :
    (h.adjMatBasis i : Matrix X X ℝ) = adjMat rel i :=
  congrArg Subtype.val (Module.Basis.span_apply h.linearIndependent_adjMat i)

/-- The Bose–Mesner algebra of a `d`-class scheme has dimension `d + 1`. -/
theorem finrank_bmAlgebra (h : IsAssocScheme rel) :
    Module.finrank ℝ (bmAlgebra rel) = d + 1 := by
  rw [Module.finrank_eq_card_basis h.adjMatBasis, Fintype.card_fin]

/-- In a symmetric association scheme, every vertex has the same number of class-`i` neighbours. -/
theorem card_filter_rel_eq (h : IsAssocScheme rel) (i : Fin (d + 1)) (x x' : X) :
    #{y | rel x y = i} = #{y | rel x' y = i} := by
  have h0 : rel x x = rel x' x' := by simp [h.rel_self]
  have hcard := h.card_eq i i x x x' x' h0
  simpa [h.rel_comm _ x, h.rel_comm _ x'] using hcard

private theorem card_pairs_rel_eq (h : IsAssocScheme rel) (i : Fin (d + 1)) (x : X) :
    #{p : X × X | rel p.1 p.2 = i} = Fintype.card X * #{y | rel x y = i} := by
  have hsplit : #{p : X × X | rel p.1 p.2 = i} = ∑ a : X, #{y | rel a y = i} := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  rw [hsplit]
  simp_rw [h.card_filter_rel_eq i _ x, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The number of `y` with `rel x y = i` equals the valency `valency rel i` for every `x`. -/
theorem card_filter_rel_eq_valency (h : IsAssocScheme rel) (i : Fin (d + 1)) (x : X) :
    (#{y | rel x y = i} : ℝ) = valency rel i := by
  unfold valency
  rw [h.card_pairs_rel_eq i x, Nat.cast_mul]
  have hpos : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.card_pos.ne'
  field_simp [hpos]

/-- Every row of `adjMat rel i` sums to `valency rel i`. -/
theorem sum_adjMat_row (h : IsAssocScheme rel) (i : Fin (d + 1)) (x : X) :
    ∑ y, adjMat rel i x y = valency rel i := by
  simp only [adjMat_apply, Finset.sum_boole]
  exact h.card_filter_rel_eq_valency i x

/-- Every column of `adjMat rel i` sums to `valency rel i`. -/
theorem sum_adjMat_col (h : IsAssocScheme rel) (i : Fin (d + 1)) (y : X) :
    ∑ x, adjMat rel i x y = valency rel i := by
  have hrow : ∀ x, adjMat rel i x y = adjMat rel i y x := fun x => by
    simp [h.rel_comm x y]
  simp_rw [hrow]
  exact h.sum_adjMat_row i y

/-- Every class of a symmetric association scheme has positive valency. -/
theorem valency_pos (h : IsAssocScheme rel) (i : Fin (d + 1)) : 0 < valency rel i := by
  obtain ⟨x, y, hxy⟩ := h.exists_rel_eq i
  rw [← h.card_filter_rel_eq_valency i x]
  exact_mod_cast Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hxy⟩⟩

@[simp]
theorem valency_zero (h : IsAssocScheme rel) : valency rel 0 = 1 := by
  obtain ⟨x⟩ := h.nonempty
  rw [← h.card_filter_rel_eq_valency 0 x]
  have hf : Finset.univ.filter (fun y => rel x y = 0) = {x} := by
    ext y
    simp [h.rel_eq_zero_iff, eq_comm]
  simp [hf]

private theorem card_triples_rel_eq (h : IsAssocScheme rel) (i j : Fin (d + 1)) (x y : X) :
    #{t : X × X × X | rel t.1 t.2.1 = rel x y ∧ rel t.1 t.2.2 = i ∧ rel t.2.2 t.2.1 = j} =
      #{p : X × X | rel p.1 p.2 = rel x y} * #{z | rel x z = i ∧ rel z y = j} := by
  have hsplit : #{t : X × X × X | rel t.1 t.2.1 = rel x y ∧ rel t.1 t.2.2 = i ∧
        rel t.2.2 t.2.1 = j} =
      ∑ p : X × X,
        if rel p.1 p.2 = rel x y then #{z | rel p.1 z = i ∧ rel z p.2 = j} else 0 := by
    rw [Finset.card_filter]
    have hprod : ∑ t : X × X × X, (if rel t.1 t.2.1 = rel x y ∧ rel t.1 t.2.2 = i ∧
        rel t.2.2 t.2.1 = j then 1 else 0) =
        ∑ a : X, ∑ b : X, ∑ z : X,
          (if rel a b = rel x y ∧ rel a z = i ∧ rel z b = j then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [hprod, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : rel a b = rel x y
    · rw [Finset.card_filter]
      simp [hab]
    · simp [hab]
  rw [hsplit]
  have hcon : ∀ p : X × X,
      (if rel p.1 p.2 = rel x y then #{z | rel p.1 z = i ∧ rel z p.2 = j} else 0) =
        if rel p.1 p.2 = rel x y then #{z | rel x z = i ∧ rel z y = j} else 0 := by
    intro p
    split_ifs with hp
    · exact h.card_eq i j p.1 p.2 x y hp
    · rfl
  simp_rw [hcon, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- For every pair `(x, y)` in class `k`, the number of `z` with `rel x z = i` and `rel z y = j`
equals `intersectionNumber rel i j k`. -/
theorem card_filter_rel_and_eq_intersectionNumber (h : IsAssocScheme rel) (i j : Fin (d + 1))
    (x y : X) :
    (#{z | rel x z = i ∧ rel z y = j} : ℝ) = intersectionNumber rel i j (rel x y) := by
  unfold intersectionNumber
  rw [h.card_triples_rel_eq i j x y, Nat.cast_mul]
  have hpos : 0 < #{p : X × X | rel p.1 p.2 = rel x y} :=
    Finset.card_pos.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hne : (#{p : X × X | rel p.1 p.2 = rel x y} : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  field_simp [hne]

/-- **Product of adjacency matrices.** In a symmetric association scheme,
`A_i * A_j = ∑ k, p^k_ij • A_k`. -/
theorem adjMat_mul_adjMat (h : IsAssocScheme rel) (i j : Fin (d + 1)) :
    adjMat rel i * adjMat rel j = ∑ k, intersectionNumber rel i j k • adjMat rel k := by
  ext x y
  rw [adjMat_mul_apply, h.card_filter_rel_and_eq_intersectionNumber i j x y]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, adjMat_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The Bose–Mesner algebra is closed under matrix multiplication. -/
theorem mul_mem_bmAlgebra (h : IsAssocScheme rel) {M N : Matrix X X ℝ}
    (hM : M ∈ bmAlgebra rel) (hN : N ∈ bmAlgebra rel) : M * N ∈ bmAlgebra rel := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hN using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [h.adjMat_mul_adjMat i j]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (adjMat_mem_bmAlgebra rel k)
    | zero => simp
    | add _ _ _ _ h1 h2 => simpa [Matrix.mul_add] using Submodule.add_mem _ h1 h2
    | smul c _ _ h1 => simpa [Matrix.mul_smul] using Submodule.smul_mem _ c h1
  | zero => simp
  | add _ _ _ _ h1 h2 => simpa [Matrix.add_mul] using Submodule.add_mem _ h1 h2
  | smul c _ _ h1 => simpa [Matrix.smul_mul] using Submodule.smul_mem _ c h1

/-- Any two adjacency matrices commute. -/
theorem adjMat_comm (h : IsAssocScheme rel) (i j : Fin (d + 1)) :
    adjMat rel i * adjMat rel j = adjMat rel j * adjMat rel i := by
  have hsym := h.transpose_eq_of_mem_bmAlgebra
    (h.mul_mem_bmAlgebra (adjMat_mem_bmAlgebra rel i) (adjMat_mem_bmAlgebra rel j))
  calc adjMat rel i * adjMat rel j
      = (adjMat rel i * adjMat rel j)ᵀ := hsym.symm
    _ = (adjMat rel j)ᵀ * (adjMat rel i)ᵀ := Matrix.transpose_mul _ _
    _ = adjMat rel j * adjMat rel i := by rw [h.adjMat_transpose i, h.adjMat_transpose j]

/-- The Bose–Mesner algebra is commutative under matrix multiplication. -/
theorem mul_comm_of_mem_bmAlgebra (h : IsAssocScheme rel) {M N : Matrix X X ℝ}
    (hM : M ∈ bmAlgebra rel) (hN : N ∈ bmAlgebra rel) : M * N = N * M := by
  have hsym := h.transpose_eq_of_mem_bmAlgebra (h.mul_mem_bmAlgebra hM hN)
  calc M * N = (M * N)ᵀ := hsym.symm
    _ = Nᵀ * Mᵀ := Matrix.transpose_mul M N
    _ = N * M := by rw [h.transpose_eq_of_mem_bmAlgebra hM, h.transpose_eq_of_mem_bmAlgebra hN]

/-- The Bose–Mesner algebra as a real subalgebra of matrices. -/
def bmSubalgebra [DecidableEq X] (h : IsAssocScheme rel) : Subalgebra ℝ (Matrix X X ℝ) where
  __ := bmAlgebra rel
  one_mem' := h.one_mem_bmAlgebra
  mul_mem' hM hN := h.mul_mem_bmAlgebra hM hN
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r h.one_mem_bmAlgebra

@[simp]
theorem mem_bmSubalgebra_iff [DecidableEq X] (h : IsAssocScheme rel) {M : Matrix X X ℝ} :
    M ∈ h.bmSubalgebra ↔ M ∈ bmAlgebra rel :=
  Iff.rfl

@[simp]
theorem toSubmodule_bmSubalgebra [DecidableEq X] (h : IsAssocScheme rel) :
    h.bmSubalgebra.toSubmodule = bmAlgebra rel :=
  SetLike.ext fun _ => h.mem_bmSubalgebra_iff

/-- Symmetry of the intersection numbers: `p^k_ij = p^k_ji`. -/
theorem intersectionNumber_comm (h : IsAssocScheme rel) (i j k : Fin (d + 1)) :
    intersectionNumber rel i j k = intersectionNumber rel j i k := by
  have heq : ∑ l, intersectionNumber rel i j l • adjMat rel l =
      ∑ l, intersectionNumber rel j i l • adjMat rel l := by
    rw [← h.adjMat_mul_adjMat i j, ← h.adjMat_mul_adjMat j i, h.adjMat_comm i j]
  have hli := linearIndependent_iff'.mp h.linearIndependent_adjMat Finset.univ
    (fun l => intersectionNumber rel i j l - intersectionNumber rel j i l)
    (by simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]) k (Finset.mem_univ k)
  exact sub_eq_zero.mp hli

/-- `p^k_0j = δ_jk`. -/
@[simp]
theorem intersectionNumber_zero_left (h : IsAssocScheme rel) (j k : Fin (d + 1)) :
    intersectionNumber rel 0 j k = if j = k then 1 else 0 := by
  obtain ⟨x, y, hxy⟩ := h.exists_rel_eq k
  rw [← hxy, ← h.card_filter_rel_and_eq_intersectionNumber 0 j x y]
  have hf : Finset.univ.filter (fun z => rel x z = 0 ∧ rel z y = j) =
      if j = rel x y then {x} else ∅ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h.rel_eq_zero_iff]
    split_ifs with hjk
    · subst hjk
      simp only [Finset.mem_singleton]
      exact ⟨fun ⟨hz, _⟩ => hz.symm, fun hz => ⟨hz.symm, hz ▸ rfl⟩⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro hxz
      rw [← hxz]
      exact Ne.symm hjk
  rw [hf, hxy]
  split_ifs <;> simp

/-- `p^k_i0 = δ_ik`. -/
@[simp]
theorem intersectionNumber_zero_right (h : IsAssocScheme rel) (i k : Fin (d + 1)) :
    intersectionNumber rel i 0 k = if i = k then 1 else 0 := by
  rw [h.intersectionNumber_comm, h.intersectionNumber_zero_left]

/-- `p^0_ij = δ_ij v_j`. -/
@[simp]
theorem intersectionNumber_eq_zero_right (h : IsAssocScheme rel) (i j : Fin (d + 1)) :
    intersectionNumber rel i j 0 = if i = j then valency rel j else 0 := by
  obtain ⟨x⟩ := h.nonempty
  have hxx : rel x x = 0 := h.rel_self x
  rw [← hxx, ← h.card_filter_rel_and_eq_intersectionNumber i j x x]
  split_ifs with hij
  · subst hij
    rw [← h.card_filter_rel_eq_valency i x]
    congr 2
    ext z
    simp [h.rel_comm z x]
  · have hempty : Finset.univ.filter (fun z => rel x z = i ∧ rel z x = j) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro h1 h2
      rw [h.rel_comm z x, h1] at h2
      exact hij h2
    simp [hempty]

/-- Double-counting triples gives `p^k_ij v_k = p^j_ik v_j`. -/
theorem intersectionNumber_mul_valency (h : IsAssocScheme rel) (i j k : Fin (d + 1)) :
    intersectionNumber rel i j k * valency rel k =
      intersectionNumber rel i k j * valency rel j := by
  have hkpos : (#{p : X × X | rel p.1 p.2 = k} : ℝ) ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := h.exists_rel_eq k
    exact_mod_cast (Finset.card_pos.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hxy⟩⟩).ne'
  have hjpos : (#{p : X × X | rel p.1 p.2 = j} : ℝ) ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := h.exists_rel_eq j
    exact_mod_cast (Finset.card_pos.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hxy⟩⟩).ne'
  have hXpos : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.card_pos.ne'
  unfold intersectionNumber valency
  have htriples :
      #{t : X × X × X | rel t.1 t.2.1 = k ∧ rel t.1 t.2.2 = i ∧ rel t.2.2 t.2.1 = j} =
      #{t : X × X × X | rel t.1 t.2.1 = j ∧ rel t.1 t.2.2 = i ∧ rel t.2.2 t.2.1 = k} := by
    refine Finset.card_bij (fun t _ => (t.2.2, t.2.1, t.1)) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      refine ⟨ht.2.2, ?_, ht.1⟩
      rw [h.rel_comm]
      exact ht.2.1
    · intro t₁ _ t₂ _ heq
      ext <;> simp_all
    · intro t ht
      refine ⟨(t.2.2, t.2.1, t.1), ?_, by ext <;> rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      refine ⟨ht.2.2, ?_, ht.1⟩
      rw [h.rel_comm]
      exact ht.2.1
  rw [htriples]
  field_simp [hkpos, hjpos, hXpos]

/-- Summing `p^k_ij` over `j` gives `v_i`. -/
theorem sum_intersectionNumber (h : IsAssocScheme rel) (i k : Fin (d + 1)) :
    ∑ j, intersectionNumber rel i j k = valency rel i := by
  obtain ⟨x, y, hxy⟩ := h.exists_rel_eq k
  simp_rw [← hxy, ← h.card_filter_rel_and_eq_intersectionNumber i _ x y,
    ← h.card_filter_rel_eq_valency i x, ← Nat.cast_sum]
  norm_cast
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hxz : rel x z = i
  · simp [hxz]
  · simp [hxz]

end IsAssocScheme

end TauCeti
