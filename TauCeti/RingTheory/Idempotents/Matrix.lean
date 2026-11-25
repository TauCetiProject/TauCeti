/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RingTheory.Idempotents.Corner.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Idempotents in matrix rings and the corner of a diagonal matrix unit

For a ring `α` and an index `i`, the diagonal matrix unit `Eᵢᵢ = Matrix.single i i 1` is an
idempotent of `Matrix n n α`. Its corner `Eᵢᵢ · Matrix n n α · Eᵢᵢ` consists of the matrices
supported on the entry `(i, i)`, so it is a copy of `α`; and `Eᵢᵢ` is **full**, generating the
whole matrix ring as a two-sided ideal, because `1 = ∑ⱼ Eⱼᵢ Eᵢᵢ Eᵢⱼ`.

Together these say that `α` is a full idempotent corner of `Matrix n n α`, the standard instance of
Morita equivalence. In a product of matrix rings over division rings, one such unit per factor
selects a full idempotent whose corner is a product of division rings.

Over a domain `K` satisfying `StrongRankCondition` (for instance any commutative integral domain or
division ring), any finite family of pairwise orthogonal nonzero idempotents in `Matrix n n K` has
cardinality at most `Fintype.card n` (`OrthogonalIdempotents.card_le_of_matrix`), because choosing
one nonzero row from each idempotent yields a left `K`-linearly independent family in `n → K`.

## Main definitions

* `Matrix.cornerSingleOneEquiv`: the corner of `Eᵢᵢ` is isomorphic to the coefficient ring.

## Main results

* `Matrix.isIdempotentElem_single_one`: the diagonal matrix unit `Eᵢᵢ` is idempotent.
* `Matrix.orthogonalIdempotents_map_single`: the images of the diagonal matrix units under a
  homomorphism out of `Mₙ(α)` are orthogonal idempotents.
* `Matrix.single_apply_eq_of_mem_corner`: a matrix in the corner of `Eᵢᵢ` is supported on the
  entry `(i, i)`.
* `Matrix.twoSidedIdeal_span_single_one_eq_top`: the diagonal matrix unit `Eᵢᵢ` is full.
* `OrthogonalIdempotents.card_le_of_matrix`: a family of pairwise orthogonal nonzero idempotents in
  `Matrix n n K` over a domain `K` satisfying `StrongRankCondition` has size at most
  `Fintype.card n`.
-/

public section

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal matrix unit `Eᵢᵢ` is idempotent. -/
@[simp]
theorem isIdempotentElem_single_one [NonAssocSemiring α] (i : n) :
    IsIdempotentElem (single i i (1 : α)) := by
  simp [IsIdempotentElem]

section Map

variable {B F : Type*} [NonAssocSemiring α] [FunLike F (Matrix n n α) B]

/-- The images of the diagonal matrix units are orthogonal idempotents. -/
theorem orthogonalIdempotents_map_single [Semiring B] [NonUnitalRingHomClass F (Matrix n n α) B]
    (f : F) : OrthogonalIdempotents fun i : n => f (single i i 1) :=
  ⟨fun i => (isIdempotentElem_single_one i).map f, fun i j hij => by simp [← map_mul, hij]⟩

end Map

section Semiring

variable [Semiring α]

/-- A matrix in the corner of `Eᵢᵢ` is supported on the entry `(i, i)`. -/
theorem single_apply_eq_of_mem_corner {i : n} {x : Matrix n n α}
    (hx : x ∈ Subsemigroup.corner (single i i (1 : α))) : single i i (x i i) = x := by
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff (isIdempotentElem_single_one i)).mp hx
  calc single i i (x i i) = single i i (1 : α) * x * single i i 1 := by
        rw [single_mul_mul_single, one_mul, mul_one]
    _ = x := by rw [hl, hr]

/-- **The corner of the diagonal matrix unit `Eᵢᵢ` is the coefficient ring**, through the
`(i, i)` entry. -/
def cornerSingleOneEquiv (i : n) : (isIdempotentElem_single_one (α := α) i).Corner ≃+* α where
  toFun x := x.val i i
  invFun a := ⟨single i i a, (Subsemigroup.mem_corner_iff (isIdempotentElem_single_one i)).mpr
    ⟨by simp, by simp⟩⟩
  left_inv x := Subtype.ext (single_apply_eq_of_mem_corner x.property)
  right_inv a := by simp
  map_mul' x y := by
    rw [IsIdempotentElem.Corner.val_mul]
    conv_lhs => rw [← single_apply_eq_of_mem_corner x.property, ← single_apply_eq_of_mem_corner
        y.property]
    simp
  map_add' _ _ := rfl

@[simp]
theorem cornerSingleOneEquiv_apply (i : n) (x : (isIdempotentElem_single_one (α := α) i).Corner) :
    cornerSingleOneEquiv i x = x.val i i :=
  (rfl)

@[simp]
theorem val_cornerSingleOneEquiv_symm_apply (i : n) (a : α) :
    ((cornerSingleOneEquiv i).symm a).val = single i i a :=
  (rfl)

end Semiring

/-- **The diagonal matrix unit `Eᵢᵢ` is full**: it generates `Matrix n n α` as a two-sided ideal,
since `1 = ∑ⱼ Eⱼᵢ Eᵢᵢ Eᵢⱼ`. -/
theorem twoSidedIdeal_span_single_one_eq_top [NonAssocRing α] (i : n) :
    TwoSidedIdeal.span {single i i (1 : α)} = ⊤ := by
  refine (TwoSidedIdeal.one_mem_iff _).mp ?_
  rw [← sum_single_one]
  refine sum_mem fun j _ ↦ ?_
  have h : single j i (1 : α) * single i i 1 * single i j 1 = single j j 1 := by simp
  rw [← h]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))

end Matrix

/-- Over a domain `K` satisfying `StrongRankCondition` (for instance any commutative integral
domain or division ring), a finite family of pairwise orthogonal nonzero idempotents in
`Matrix n n K` has cardinality at most `Fintype.card n`. -/
theorem OrthogonalIdempotents.card_le_of_matrix {K ι n : Type*} [Ring K] [IsDomain K]
    [StrongRankCondition K] [Fintype ι] [Fintype n] [DecidableEq n] {e : ι → Matrix n n K}
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0) : Fintype.card ι ≤ Fintype.card n := by
  classical
  have hex (i : ι) : ∃ r : n, e i r ≠ 0 := Function.ne_iff.mp (hne i)
  let r (i : ι) : n := (hex i).choose
  let w (i : ι) : n → K := e i (r i)
  have hw_ne (i : ι) : w i ≠ 0 := (hex i).choose_spec
  have hw_mul (i j : ι) : Matrix.vecMul (w i) (e j) = if i = j then w i else 0 := by
    rw [← Matrix.mul_apply_eq_vecMul, he.mul_eq]
    ext c
    by_cases hij : i = j <;> simp [hij, w]
  have hli : LinearIndependent K w := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    have h0 : Matrix.vecMul (∑ i ∈ s, c i • w i) (e j) = 0 := by rw [hc, Matrix.zero_vecMul]
    have hsum : Matrix.vecMul (∑ i ∈ s, c i • w i) (e j) = c j • w j := by
      simp [Matrix.sum_vecMul, Matrix.smul_vecMul, hw_mul, hj]
    obtain ⟨col, hcol⟩ := Function.ne_iff.mp (hw_ne j)
    have hmul : c j * w j col = 0 := by
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
        congrFun (hsum.symm.trans h0) col
    exact (mul_eq_zero.mp hmul).resolve_right hcol
  simpa only [Module.finrank_fintype_fun_eq_card] using hli.fintype_card_le_finrank
