/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Block designs and symmetric designs

A `2`-`(v, k, ℓ)` design (`TauCeti.Design.IsTwoDesign`) is an incidence relation
`inc : P → L → Prop` between `v` points and a family of blocks such that every block is incident
with `k` points, every two distinct points lie together on `ℓ` blocks, and `2 ≤ k < v`, `0 < ℓ`.
Repeated blocks are permitted. Double counting shows that every point lies on
`r = ℓ (v - 1) / (k - 1)` blocks (`TauCeti.Design.replication`), that `b k = v r`, and that the
point-by-block incidence matrix `N` satisfies the Gram identity `N Nᵀ = (r - ℓ) I + ℓ J`, which
characterizes `2`-designs among uniform incidence relations with `2 ≤ k < v` and `0 < ℓ`.
Because `r > ℓ`, the real or rational Gram matrix is positive definite and hence `N` has full row
rank `v`.

A symmetric design (`TauCeti.Design.IsSymmetricDesign`) is a `2`-design with `b = v` blocks,
equivalently `r = k`. Its incidence matrix commutes with `J` and is invertible over `ℚ`, so
`Nᵀ N = N Nᵀ = (k - ℓ) I + ℓ J` and the dual incidence relation `flip inc` is again a symmetric
`2`-`(v, k, ℓ)` design.

## Main definitions

* `TauCeti.Design.IsTwoDesign`: a `2`-`(v, k, ℓ)` design for an incidence relation `inc`.
* `TauCeti.Design.IsSymmetricDesign`: a symmetric `2`-`(v, k, ℓ)` design (`Nat.card L = v`).
* `TauCeti.Design.replication`: the replication number `ℓ * (v - 1) / (k - 1)`.
* `TauCeti.Design.incMatrix`: the point-by-block `0`–`1` incidence matrix over a ring.

## Main results

* `TauCeti.Design.IsTwoDesign.card_blocks_through_eq_replication` and
  `TauCeti.Design.IsTwoDesign.replication_mul_sub_one`: every point lies on `r = replication v k ℓ`
  blocks and `r * (k - 1) = ℓ * (v - 1)`.
* `TauCeti.Design.IsTwoDesign.card_blocks_mul`: `Nat.card L * k = v * replication v k ℓ`.
* `TauCeti.Design.IsTwoDesign.incMatrix_mul_ones` and
  `TauCeti.Design.IsTwoDesign.ones_mul_incMatrix`: row and column sums of `incMatrix`.
* `TauCeti.Design.IsTwoDesign.incMatrix_mul_transpose`: the Gram identity
  `N * Nᵀ = (r - ℓ) • 1 + ℓ • J`.
* `TauCeti.Design.isTwoDesign_of_incMatrix_mul_transpose`: converse of the Gram identity over a
  semiring of characteristic zero.
* `TauCeti.Design.IsTwoDesign.rank_incMatrix`: the incidence matrix over a field of characteristic
  zero has rank `v`.
* `TauCeti.Design.IsTwoDesign.isSymmetricDesign_iff`: a `2`-design is symmetric iff `r = k`.
* `TauCeti.Design.IsSymmetricDesign.flip`: the dual of a symmetric design is a symmetric design
  with the same parameters.
* `TauCeti.Design.IsSymmetricDesign.incMatrix_transpose_mul`: `Nᵀ * N = (k - ℓ) • 1 + ℓ • J`.

## References

* C. Godsil and G. Royle, *Algebraic Graph Theory*, Graduate Texts in Mathematics 207,
  Springer, 2001, §5.10, pp. 94–96.
-/

public section

open Matrix

namespace TauCeti.Design

variable {P L : Type*} {inc : P → L → Prop} {v k ℓ : ℕ}

/-! ### Definitions and finiteness -/

variable (inc) in
/-- A `2`-`(v, k, ℓ)` design for the incidence relation `inc` between points `P` and blocks `L`:
there are `v` points, every block is incident with `k` points, every two distinct points are
together incident with exactly `ℓ` blocks, and `2 ≤ k < v`, `0 < ℓ`. Repeated blocks are allowed. -/
structure IsTwoDesign (v k ℓ : ℕ) : Prop where
  card_points : Nat.card P = v
  card_points_of_block : ∀ l, Nat.card {p // inc p l} = k
  card_pair : ∀ p q, p ≠ q → Nat.card {l // inc p l ∧ inc q l} = ℓ
  two_le : 2 ≤ k
  lt_card : k < v
  pos : 0 < ℓ

variable (inc) in
/-- A symmetric design: a `2`-design with as many blocks as points. -/
structure IsSymmetricDesign (v k ℓ : ℕ) : Prop extends IsTwoDesign inc v k ℓ where
  card_blocks_eq : Nat.card L = v

/-- The replication number `r = ℓ (v - 1) / (k - 1)` of a `2`-`(v, k, ℓ)` design. -/
def replication (v k ℓ : ℕ) : ℕ := ℓ * (v - 1) / (k - 1)

/-- The defining formula of `replication`. -/
theorem replication_def (v k ℓ : ℕ) : replication v k ℓ = ℓ * (v - 1) / (k - 1) := (rfl)

/-- A `2`-`(v, k, ℓ)` design has finitely many points. -/
theorem IsTwoDesign.finite_points (h : IsTwoDesign inc v k ℓ) : Finite P :=
  Nat.finite_of_card_ne_zero (h.card_points ▸ by have := h.two_le; have := h.lt_card; omega)

/-- A `2`-`(v, k, ℓ)` design has finitely many blocks: every block contains a pair of distinct
points, and each such pair lies on finitely many blocks. -/
theorem IsTwoDesign.finite_blocks (h : IsTwoDesign inc v k ℓ) : Finite L := by
  have := h.finite_points
  have hpair (l : L) :
      ∃ pq : {pq : P × P // pq.1 ≠ pq.2}, inc pq.val.1 l ∧ inc pq.val.2 l := by
    have hcard : Nat.card {p // inc p l} = k := h.card_points_of_block l
    have : Finite {p // inc p l} :=
      Nat.finite_of_card_ne_zero (hcard ▸ by have := h.two_le; omega)
    let := Fintype.ofFinite {p // inc p l}
    obtain ⟨p, q, hpq⟩ : ∃ p q : {p // inc p l}, p ≠ q :=
      Fintype.one_lt_card_iff.1 (by rw [← Nat.card_eq_fintype_card, hcard]; exact h.two_le)
    exact ⟨⟨(p.val, q.val), mt Subtype.ext hpq⟩, p.property, q.property⟩
  choose pq hpq using hpair
  have (x : {pq : P × P // pq.1 ≠ pq.2}) : Finite {l // inc x.val.1 l ∧ inc x.val.2 l} :=
    Nat.finite_of_card_ne_zero (h.card_pair x.val.1 x.val.2 x.property ▸ h.pos.ne')
  refine Finite.of_injective (fun l ↦ (⟨pq l, ⟨l, hpq l⟩⟩ :
    Σ x : {pq : P × P // pq.1 ≠ pq.2}, {l // inc x.val.1 l ∧ inc x.val.2 l}))
    fun l₁ l₂ heq ↦ ?_
  exact congrArg (fun x ↦ x.snd.val) heq

/-! ### Counting blocks and the replication number -/

private theorem IsTwoDesign.card_blocks_through_mul_sub_one (h : IsTwoDesign inc v k ℓ) (p : P) :
    Nat.card {l // inc p l} * (k - 1) = ℓ * (v - 1) := by
  have := h.finite_points
  have := h.finite_blocks
  let := Fintype.ofFinite P
  let := Fintype.ofFinite L
  classical
  let s : Finset P := {p}ᶜ
  let t : Finset L := Finset.univ.filter (inc p)
  have hst := Finset.card_mul_eq_card_mul inc (s := s) (t := t) (m := ℓ) (n := k - 1)
    (fun q hq ↦ by
      have hqp : p ≠ q := (Finset.mem_compl.1 hq |> Finset.notMem_singleton.1).symm
      rw [← h.card_pair p q hqp, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1; ext l
      simp [t, Finset.mem_bipartiteAbove])
    (fun l hl ↦ by
      have hpl : inc p l := (Finset.mem_filter.1 hl).2
      have hbelow : s.bipartiteBelow inc l = (Finset.univ.filter (inc · l)).erase p := by
        ext q
        simp [s, Finset.mem_bipartiteBelow, and_comm]
      rw [hbelow, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ p, hpl⟩),
        ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, h.card_points_of_block l])
  have hs : s.card = v - 1 := by
    simp [s, Finset.card_compl, ← Nat.card_eq_fintype_card, h.card_points]
  have ht : t.card = Nat.card {l // inc p l} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hs, ht, mul_comm _ ℓ] at hst
  exact hst.symm

/-- **The replication number.** Every point of a `2`-`(v, k, ℓ)` design lies on
`r = replication v k ℓ` blocks. -/
theorem IsTwoDesign.card_blocks_through_eq_replication (h : IsTwoDesign inc v k ℓ) (p : P) :
    Nat.card {l // inc p l} = replication v k ℓ :=
  Nat.eq_div_of_mul_eq_left (Nat.sub_pos_of_lt h.two_le).ne'
    (h.card_blocks_through_mul_sub_one p)

/-- The basic parameter identity `r * (k - 1) = ℓ * (v - 1)` of a `2`-`(v, k, ℓ)` design. -/
theorem IsTwoDesign.replication_mul_sub_one (h : IsTwoDesign inc v k ℓ) :
    replication v k ℓ * (k - 1) = ℓ * (v - 1) := by
  have := h.finite_points
  let := Fintype.ofFinite P
  obtain ⟨p⟩ : Nonempty P := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, h.card_points]
    have := h.two_le; have := h.lt_card; omega
  rw [← h.card_blocks_through_eq_replication p]
  exact h.card_blocks_through_mul_sub_one p

/-- In a `2`-`(v, k, ℓ)` design, `ℓ < replication v k ℓ`. -/
theorem IsTwoDesign.lt_replication (h : IsTwoDesign inc v k ℓ) : ℓ < replication v k ℓ := by
  have hlt : ℓ * (k - 1) < ℓ * (v - 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.sub_lt_sub_right (by have := h.two_le; omega) h.lt_card) h.pos
  rw [← h.replication_mul_sub_one] at hlt
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Counting blocks.** In a `2`-`(v, k, ℓ)` design, `b * k = v * r`. -/
theorem IsTwoDesign.card_blocks_mul (h : IsTwoDesign inc v k ℓ) :
    Nat.card L * k = v * replication v k ℓ := by
  have := h.finite_points
  have := h.finite_blocks
  let := Fintype.ofFinite P
  let := Fintype.ofFinite L
  classical
  have hmul := Finset.card_mul_eq_card_mul inc (s := (Finset.univ : Finset P))
    (t := (Finset.univ : Finset L)) (m := replication v k ℓ) (n := k)
    (fun p _ ↦ by
      rw [← h.card_blocks_through_eq_replication p, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [Finset.bipartiteAbove])
    (fun l _ ↦ by
      rw [← h.card_points_of_block l, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [Finset.bipartiteBelow])
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card_points] at hmul
  exact hmul.symm

/-! ### Incidence matrices and the Gram identity -/

/-- The point-by-block `0`–`1` incidence matrix of `inc : P → L → Prop` over `R`. -/
def incMatrix (R : Type*) [Zero R] [One R] (inc : P → L → Prop) [DecidableRel inc] :
    Matrix P L R :=
  Matrix.of fun p l ↦ if inc p l then 1 else 0

/-- Entries of the incidence matrix. -/
@[simp]
theorem incMatrix_apply [Zero R] [One R] [DecidableRel inc] (p : P) (l : L) :
    incMatrix R inc p l = if inc p l then 1 else 0 := (rfl)

/-- Mapping entrywise preserves the incidence matrix. -/
@[simp]
theorem incMatrix_map {R S F : Type*} [Zero R] [One R] [Zero S] [One S]
    [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S] [DecidableRel inc] (f : F) :
    (incMatrix R inc).map f = incMatrix S inc := by
  ext p l
  simp [apply_ite f]

/-- The transpose of the incidence matrix of `inc` is the incidence matrix of the flipped
relation `fun l p ↦ inc p l`. -/
@[simp]
theorem transpose_incMatrix {R : Type*} [Zero R] [One R] [DecidableRel inc] :
    (incMatrix R inc)ᵀ = incMatrix R fun l p ↦ inc p l := (rfl)

/-- Multiplying the incidence matrix on the right by an all-ones matrix multiplies it by the
replication number `r`. -/
theorem IsTwoDesign.incMatrix_mul_ones [Fintype L] [DecidableRel inc]
    {R α : Type*} [NonAssocSemiring R] (h : IsTwoDesign inc v k ℓ) :
    incMatrix R inc * (Matrix.of fun _ _ ↦ 1 : Matrix L α R) =
      (replication v k ℓ : R) • Matrix.of fun _ _ ↦ 1 := by
  ext p a
  simp only [Matrix.mul_apply, incMatrix_apply, Matrix.of_apply, mul_one, Finset.sum_boole,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, h.card_blocks_through_eq_replication,
    Matrix.smul_apply, smul_eq_mul]

/-- Multiplying the incidence matrix on the left by an all-ones matrix multiplies it by the
block size `k`. -/
theorem IsTwoDesign.ones_mul_incMatrix [Fintype P] [DecidableRel inc]
    {R α : Type*} [NonAssocSemiring R] (h : IsTwoDesign inc v k ℓ) :
    (Matrix.of fun _ _ ↦ 1 : Matrix α P R) * incMatrix R inc =
      (k : R) • Matrix.of fun _ _ ↦ 1 := by
  ext a l
  simp only [Matrix.mul_apply, Matrix.of_apply, one_mul, incMatrix_apply, Finset.sum_boole,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, h.card_points_of_block,
    Matrix.smul_apply, smul_eq_mul, mul_one]

/-- The `(p, q)` entry of `N * Nᵀ` counts the blocks incident with both `p` and `q`. -/
theorem incMatrix_mul_transpose_apply [Fintype L] [DecidableRel inc]
    {R : Type*} [NonAssocSemiring R] (p q : P) :
    (incMatrix R inc * (incMatrix R inc)ᵀ) p q = Fintype.card {l // inc p l ∧ inc q l} := by
  simp only [Matrix.mul_apply, transpose_apply, incMatrix_apply, boole_mul, ← ite_and,
    Finset.sum_boole, Fintype.card_subtype]

/-- **The Gram identity.** For a `2`-`(v, k, ℓ)` design over any ring,
`N * Nᵀ = (r - ℓ) • 1 + ℓ • J`. -/
theorem IsTwoDesign.incMatrix_mul_transpose [Fintype L] [DecidableEq P] [DecidableRel inc]
    {R : Type*} [NonAssocRing R] (h : IsTwoDesign inc v k ℓ) :
    incMatrix R inc * (incMatrix R inc)ᵀ =
      ((replication v k ℓ : R) - ℓ) • (1 : Matrix P P R) +
        (ℓ : R) • Matrix.of fun _ _ ↦ 1 := by
  ext p q
  rw [incMatrix_mul_transpose_apply, ← Nat.card_eq_fintype_card]
  rcases eq_or_ne p q with rfl | hpq
  · simp only [and_self]
    rw [h.card_blocks_through_eq_replication]
    simp [sub_add_cancel]
  · rw [h.card_pair p q hpq]
    simp [hpq]

/-- **The converse of the Gram identity.** Blocks of size `k` with `2 ≤ k < v`, `0 < ℓ`, and
`N * Nᵀ = d • 1 + ℓ • J` over a semiring of characteristic zero form a `2`-`(v, k, ℓ)`
design. -/
theorem isTwoDesign_of_incMatrix_mul_transpose [Fintype L] [DecidableEq P] [DecidableRel inc]
    {R : Type*} [NonAssocSemiring R] [CharZero R] {d : R}
    (hv : Nat.card P = v) (hk : ∀ l, Nat.card {p // inc p l} = k)
    (hk2 : 2 ≤ k) (hkv : k < v) (hℓ : 0 < ℓ)
    (hN : incMatrix R inc * (incMatrix R inc)ᵀ =
      d • (1 : Matrix P P R) + (ℓ : R) • Matrix.of fun _ _ ↦ 1) :
    IsTwoDesign inc v k ℓ where
  card_points := hv
  card_points_of_block := hk
  card_pair p q hpq := by
    have h := congr_fun₂ hN p q
    rw [incMatrix_mul_transpose_apply, ← Nat.card_eq_fintype_card] at h
    simpa [hpq, Nat.cast_inj] using h
  two_le := hk2
  lt_card := hkv
  pos := hℓ

/-- **The rank of the incidence matrix.** Over a field of characteristic zero, the incidence matrix
of a `2`-`(v, k, ℓ)` design has rank `v`. -/
theorem IsTwoDesign.rank_incMatrix [DecidableRel inc] {K : Type*} [Field K] [CharZero K]
    (h : IsTwoDesign inc v k ℓ) : (incMatrix K inc).rank = v := by
  have := h.finite_points
  have := h.finite_blocks
  let := Fintype.ofFinite P
  let := Fintype.ofFinite L
  classical
  have hgram : incMatrix ℚ inc * (incMatrix ℚ inc)ᵀ =
      ((replication v k ℓ : ℚ) - ℓ) • (1 : Matrix P P ℚ) +
        (ℓ : ℚ) • Matrix.of fun _ _ ↦ 1 :=
    h.incMatrix_mul_transpose
  have hdiag : (0 : ℚ) < (replication v k ℓ : ℚ) - ℓ :=
    sub_pos.2 (Nat.cast_lt.2 h.lt_replication)
  have hJ : ((ℓ : ℚ) • Matrix.of fun (_ _ : P) ↦ (1 : ℚ)).PosSemidef := by
    have hvec : (Matrix.of fun (_ _ : P) ↦ (1 : ℚ)) =
        vecMulVec (fun (_ : P) ↦ (1 : ℚ)) (star fun (_ : P) ↦ (1 : ℚ)) := by
      ext; simp [vecMulVec]
    exact hvec ▸ (posSemidef_vecMulVec_self_star _).smul (Nat.cast_nonneg ℓ)
  have hpos : (incMatrix ℚ inc * (incMatrix ℚ inc)ᵀ).PosDef := by
    rw [hgram]
    exact (Matrix.PosDef.one.smul hdiag).add_posSemidef hJ
  have hunit : IsUnit (incMatrix ℚ inc * (incMatrix ℚ inc)ᵀ) := hpos.isUnit
  have hrankQ : (incMatrix ℚ inc).rank = Fintype.card P := by
    rw [← rank_self_mul_transpose, rank_of_isUnit _ hunit]
  rw [← incMatrix_map (Rat.castHom K), Matrix.rank_map, hrankQ, ← Nat.card_eq_fintype_card,
    h.card_points]

/-! ### Symmetric designs -/

/-- **Fisher equality.** A `2`-design is symmetric if and only if `replication v k ℓ = k`. -/
theorem IsTwoDesign.isSymmetricDesign_iff (h : IsTwoDesign inc v k ℓ) :
    IsSymmetricDesign inc v k ℓ ↔ replication v k ℓ = k := by
  have hkpos : 0 < k := by have := h.two_le; omega
  have hvpos : 0 < v := by have := h.two_le; have := h.lt_card; omega
  refine ⟨fun hs ↦ ?_, fun hr ↦ ⟨h, ?_⟩⟩
  · have hmul := h.card_blocks_mul
    rw [hs.card_blocks_eq] at hmul
    exact (Nat.mul_left_cancel hvpos hmul).symm
  · have hmul := h.card_blocks_mul
    rw [hr] at hmul
    exact Nat.mul_right_cancel hkpos hmul

/-- For a symmetric design over `ℚ`, `Nᵀ * N` equals `(k - ℓ) • 1 + ℓ • J`. -/
private theorem IsSymmetricDesign.incMatrix_transpose_mul_rat [Fintype P] [DecidableEq L]
    [DecidableRel inc] (h : IsSymmetricDesign inc v k ℓ) :
    (incMatrix ℚ inc)ᵀ * incMatrix ℚ inc =
      ((k : ℚ) - ℓ) • (1 : Matrix L L ℚ) + (ℓ : ℚ) • Matrix.of fun _ _ ↦ 1 := by
  have := h.finite_blocks
  let := Fintype.ofFinite L
  classical
  have hr : replication v k ℓ = k := h.toIsTwoDesign.isSymmetricDesign_iff.1 h
  have hcard : Fintype.card P = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h.card_points, h.card_blocks_eq]
  let e : P ≃ L := Fintype.equivOfCardEq hcard
  let N : Matrix P L ℚ := incMatrix ℚ inc
  let N' : Matrix P P ℚ := N.submatrix (Equiv.refl P) e
  let J : Matrix P P ℚ := Matrix.of fun _ _ ↦ 1
  have hsub : N'ᵀ = Nᵀ.submatrix e (Equiv.refl P) :=
    Matrix.transpose_submatrix N (Equiv.refl P) e
  have hNN' : N' * N'ᵀ = ((k : ℚ) - ℓ) • (1 : Matrix P P ℚ) + (ℓ : ℚ) • J := by
    rw [hsub, submatrix_mul_equiv N Nᵀ (Equiv.refl P) e (Equiv.refl P), Equiv.coe_refl,
      submatrix_id_id]
    simpa only [hr] using h.toIsTwoDesign.incMatrix_mul_transpose (R := ℚ)
  have hunit : IsUnit N' := by
    rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.rank_eq_card_iff_mulVec_injective,
      Matrix.rank_submatrix N (Equiv.refl P) e, h.toIsTwoDesign.rank_incMatrix,
      ← Nat.card_eq_fintype_card, h.card_points]
  have hrow : N' * J = (k : ℚ) • J := by
    have hJ : J = (Matrix.of fun _ _ ↦ 1 : Matrix L P ℚ).submatrix e (Equiv.refl P) := by
      ext; simp [J]
    conv_lhs => rhs; rw [hJ]
    rw [submatrix_mul_equiv N _ (Equiv.refl P) e (Equiv.refl P),
      h.toIsTwoDesign.incMatrix_mul_ones, hr, Equiv.coe_refl, submatrix_id_id]
  have hcol : J * N' = (k : ℚ) • J := by
    conv_lhs => lhs; rw [← submatrix_id_id J]
    rw [← Equiv.coe_refl, submatrix_mul_equiv J N (Equiv.refl P) (Equiv.refl P) e,
      h.toIsTwoDesign.ones_mul_incMatrix]
    ext; simp [J]
  have hcomm : N' * N'ᵀ * N' = N' * (N' * N'ᵀ) := by
    rw [hNN']
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hrow, hcol]
  have hNtN' : N'ᵀ * N' = ((k : ℚ) - ℓ) • (1 : Matrix P P ℚ) + (ℓ : ℚ) • J :=
    hunit.mul_left_cancel (by rw [← Matrix.mul_assoc, hcomm, ← hNN'])
  have hsub' : N'ᵀ * N' = (Nᵀ * N).submatrix e e := by
    rw [hsub, submatrix_mul_equiv Nᵀ N e (Equiv.refl P) e]
  have hres := congrArg (fun M : Matrix P P ℚ ↦ M.submatrix e.symm e.symm) hNtN'
  rw [hsub', submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at hres
  rw [hres]
  ext l₁ l₂
  simp [J, Matrix.one_apply]

/-- **The dual of a symmetric design** is a symmetric design with the same parameters; in
particular, any two distinct blocks meet in `ℓ` points. -/
theorem IsSymmetricDesign.flip (h : IsSymmetricDesign inc v k ℓ) :
    IsSymmetricDesign (_root_.flip inc) v k ℓ := by
  have := h.finite_points
  have := h.finite_blocks
  let := Fintype.ofFinite P
  let := Fintype.ofFinite L
  classical
  have hr : replication v k ℓ = k := h.toIsTwoDesign.isSymmetricDesign_iff.1 h
  have hcard : ∀ p, Nat.card {l // inc p l} = k := fun p ↦
    (h.toIsTwoDesign.card_blocks_through_eq_replication p).trans hr
  have hNtN := h.incMatrix_transpose_mul_rat
  rw [← Matrix.transpose_transpose (incMatrix ℚ inc), transpose_incMatrix] at hNtN
  rw [Function.flip_def]
  exact ⟨isTwoDesign_of_incMatrix_mul_transpose (R := ℚ) (d := (k : ℚ) - ℓ) h.card_blocks_eq
    hcard h.two_le h.lt_card h.pos hNtN, h.card_points⟩

/-- For a symmetric `2`-`(v, k, ℓ)` design over any ring, `Nᵀ * N = (k - ℓ) • 1 + ℓ • J`. -/
theorem IsSymmetricDesign.incMatrix_transpose_mul [Fintype P] [DecidableEq L] [DecidableRel inc]
    {R : Type*} [NonAssocRing R] (h : IsSymmetricDesign inc v k ℓ) :
    (incMatrix R inc)ᵀ * incMatrix R inc =
      ((k : R) - ℓ) • (1 : Matrix L L R) + (ℓ : R) • Matrix.of fun _ _ ↦ 1 := by
  have hr : replication v k ℓ = k := h.toIsTwoDesign.isSymmetricDesign_iff.1 h
  have hflip : IsSymmetricDesign (fun l p ↦ inc p l) v k ℓ := by
    simpa only [Function.flip_def] using h.flip
  conv_lhs => rhs; rw [← Matrix.transpose_transpose (incMatrix R inc)]
  rw [transpose_incMatrix]
  simpa only [hr] using hflip.toIsTwoDesign.incMatrix_mul_transpose (R := R)

end TauCeti.Design
