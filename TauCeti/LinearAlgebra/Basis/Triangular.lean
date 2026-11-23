/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Flags of triangular bases

Let `e` and `b` be bases of a module indexed by `Fin n` over a semiring. If `b` is triangular with
respect to `e`, so that each `b l` is a combination of `e 0, …, e l`, and the semiring is
Dedekind-finite (for instance a division ring or a commutative semiring), then `b` and `e` define
the same flag of submodules in the sense of `Module.Basis.flag`. Over a stably finite semiring,
the `k`-th steps of the two flags already agree as soon as one contains the other. Combined with
`Module.Basis.mem_flag_iff_repr_eq_zero`, a vector in the span of `e 0, …, e (j - 1)` has
vanishing `b`-coordinates from the `j`-th on.

For a finite index type with a map `f` into a preorder, a family `v` is triangular with respect to
a basis `b` with diagonal coefficients `c` when each `v i - c i • b i` is a combination of the
`b j` with `f j < f i`. Its matrix in `b` is then upper triangular for a linear order refining
`f j < f i`, so its determinant in `b` is the product of the `c i`. Taking `f = id` gives the
same for a preordered index type and the `b j` with `j < i`.

## Main results

* `Module.Basis.flag_eq_of_flag_le`: over a stably finite semiring, if the `k`-th step of the
  flag of a basis `b` lies in that of a basis `e`, then the two are equal.
* `Module.Basis.flag_eq_of_triangular`: over a Dedekind-finite semiring, a basis triangular with
  respect to `e` has the same flag as `e`.
* `Module.Basis.det_eq_prod_of_sub_smul_mem_span_image_apply_lt`: the determinant of a family
  triangular along a map `f` into a preorder is the product of its diagonal coefficients.
* `Module.Basis.det_pos_of_sub_smul_mem_span_image_apply_lt`: over an ordered ring in which
  products of positive elements are positive, such a family with positive diagonal coefficients
  has positive determinant.
-/

public section

open Finset Submodule

namespace Module.Basis

variable {K E : Type*} [Semiring K] [AddCommMonoid E] [Module K E] {n : ℕ}

/-- Over a stably finite semiring, such as a division ring or a commutative semiring, if the
`k`-th step `b.flag k` of the flag of a basis `b` lies in the `k`-th step of the flag of a basis
`e`, then the two are equal: `b 0, …, b (k - 1)` and `e 0, …, e (k - 1)` span the same submodule.
Stable finiteness enters because a square matrix with a one-sided inverse is invertible. -/
theorem flag_eq_of_flag_le [IsStablyFiniteRing K] (b : Basis (Fin n) K E)
    {e : Basis (Fin n) K E} {k : Fin (n + 1)} (h : b.flag k ≤ e.flag k) : b.flag k = e.flag k := by
  refine le_antisymm h <| e.flag_le_iff.2 fun i hi ↦ b.mem_flag_iff_repr_eq_zero.2 fun m hm ↦ ?_
  -- The indices from the `k`-th on, where the transition matrices have square blocks.
  let S := {l : Fin n // k ≤ l.castSucc}
  -- Expand `e j` in `b` and then in `e`: at an index `l ∈ S`, only the `b m` with `m ∈ S`
  -- contribute, since the other `b m` lie in `b.flag k ≤ e.flag k`.
  have hexp (j : Fin n) (l : S) :
      ∑ m : S, b.repr (e j) m * e.repr (b m) l = if j = l then 1 else 0 := by
    have h' := congrArg (fun x ↦ e.repr x l) (b.sum_repr (e j))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      repr_self, Finsupp.single_apply] at h'
    have h0 : ∑ m : {m : Fin n // ¬k ≤ m.castSucc}, b.repr (e j) m * e.repr (b m) l = 0 :=
      Finset.sum_eq_zero fun m _ ↦ by
        rw [e.mem_flag_iff_repr_eq_zero.1 (h (b.self_mem_flag (not_le.1 m.property))) l
          l.property, mul_zero]
    rwa [← Fintype.sum_subtype_add_sum_subtype (fun m ↦ k ≤ m.castSucc), h0, add_zero] at h'
  -- The block `W` of `b` in `e` on `S` is a left inverse of the block `D` of `e` in `b`, hence
  -- also a right inverse since `K` is stably finite.
  let D : Matrix S S K := .of fun m l ↦ e.repr (b m) l
  let W : Matrix S S K := .of fun j m ↦ b.repr (e j) m
  have hDW : D * W = 1 := mul_eq_one_comm.1 <| by
    ext j l
    simp [W, D, Matrix.mul_apply, Matrix.one_apply, hexp, Subtype.val_inj]
  -- The `b`-coordinates of `e i` on `S` form a row vector `z` with `z ᵥ* D = 0`, as `i ∉ S`;
  -- then `z = z ᵥ* (D * W) = (z ᵥ* D) ᵥ* W = 0`.
  let z : S → K := fun m ↦ b.repr (e i) m
  have hzD : Matrix.vecMul z D = 0 := by
    ext l
    have hil : i ≠ l := fun h ↦ (hi.trans_le l.property).ne (congrArg Fin.castSucc h)
    simp [Matrix.vecMul, dotProduct, z, D, hexp, hil]
  calc b.repr (e i) m = z ⟨m, hm⟩ := rfl
    _ = Matrix.vecMul (Matrix.vecMul z D) W ⟨m, hm⟩ := by
      rw [Matrix.vecMul_vecMul, hDW, Matrix.vecMul_one]
    _ = 0 := by rw [hzD, Matrix.zero_vecMul, Pi.zero_apply]

/-- A basis `b` that is triangular with respect to a basis `e` (each `b l` is a combination of
`e 0, …, e l`) has the same flag as `e`: `b 0, …, b (k - 1)` and `e 0, …, e (k - 1)` span the
same submodule. This holds over any Dedekind-finite semiring, such as a division ring or a
commutative semiring, where an element with a one-sided inverse is invertible. -/
theorem flag_eq_of_triangular [IsDedekindFiniteMonoid K] (b : Basis (Fin n) K E)
    {e : Basis (Fin n) K E} (htri : ∀ l i, l < i → e.repr (b l) i = 0) (k : Fin (n + 1)) :
    b.flag k = e.flag k := by
  -- A basis triangular with respect to another one has a smaller flag.
  have hle {b e : Basis (Fin n) K E} (h : ∀ l i, l < i → e.repr (b l) i = 0) :
      b.flag k ≤ e.flag k :=
    b.flag_le_iff.2 fun l hl ↦ e.mem_flag_iff_repr_eq_zero.2
      fun i hi ↦ h l i (Fin.castSucc_lt_castSucc_iff.1 (hl.trans_le hi))
  refine le_antisymm (hle htri) (hle fun l i hli ↦ ?_)
  -- `e` is triangular with respect to `b` too; show it column by column, from the last one on.
  induction i using WellFoundedGT.induction generalizing l with | _ i ih
  -- Expand `e j` in `b` and then in `e`, and read off the `i`-th coordinate: for `j ≤ i`, only
  -- `b i` contributes, by triangularity of `b` and of the columns of `e` after the `i`-th.
  have hexp (j : Fin n) (hji : j ≤ i) :
      b.repr (e j) i * e.repr (b i) i = if j = i then 1 else 0 := by
    have h := congrArg (fun x ↦ e.repr x i) (b.sum_repr (e j))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      repr_self, Finsupp.single_apply] at h
    rwa [Finset.sum_eq_single i (fun m _ hmi ↦ ?_) (by simp)] at h
    rcases hmi.lt_or_gt with hmi | hmi
    · rw [htri m i hmi, mul_zero]
    · rw [ih m hmi j (hji.trans_lt hmi), zero_mul]
  -- The diagonal coefficient `e.repr (b i) i` has the right inverse `b.repr (e i) i`, since `K` is
  -- Dedekind-finite, so the other coefficients `b.repr (e l) i` with `l < i` vanish.
  have hinv : e.repr (b i) i * b.repr (e i) i = 1 :=
    mul_eq_one_comm.1 <| by simpa using hexp i le_rfl
  rw [← mul_one (b.repr (e l) i), ← hinv, ← mul_assoc, hexp l hli.le]
  simp [hli.ne]

section Det

variable {ι α R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A finite type with a map `f` into a preorder carries a linear order in which `f i < f j`
implies `i < j`: order by the number of indices below along `f`, breaking ties along `Fin`. -/
private theorem exists_linearOrder_lt_of_apply_lt [Finite ι] [Preorder α] (f : ι → α) :
    ∃ _ : LinearOrder ι, ∀ i j, f i < f j → i < j := by
  classical
  have := Fintype.ofFinite ι
  -- The number of indices below `i` along `f` grows strictly along `f i < f j`.
  let h (i : ι) : ℕ := #{j | f j < f i}
  have hh {i j : ι} (hij : f i < f j) : h i < h j := card_lt_card <|
    ssubset_iff_of_subset (monotone_filter_right _ fun _ _ hk ↦ hk.trans hij) |>.2
      ⟨i, by simpa using hij, by simp⟩
  let g (i : ι) : Lex (ℕ × Fin (Fintype.card ι)) := toLex (h i, Fintype.equivFin ι i)
  exact ⟨LinearOrder.lift' g fun i j hij ↦
      (Fintype.equivFin ι).injective (Prod.ext_iff.1 (toLex.injective hij)).2,
    fun i j hij ↦ Prod.Lex.toLex_lt_toLex.2 (.inl (hh hij))⟩

/-- The determinant of a family `v` that is triangular with respect to a basis `b` along a map
`f` into a preorder, in the sense that each `v i - c i • b i` is a combination of the `b j` with
`f j < f i`, is the product of the diagonal coefficients `c i`. For instance, `f = id` compares
the indices for a preorder on `ι`, and `f = Prod.fst` compares only the first coordinates of a
family indexed by a product. -/
theorem det_eq_prod_of_sub_smul_mem_span_image_apply_lt [Preorder α] (b : Basis ι R M)
    (f : ι → α) {v : ι → M} {c : ι → R}
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' {j | f j < f i})) : b.det v = ∏ i, c i := by
  -- The coordinates of `v i` at the indices `j` with `¬f j < f i` are those of `c i • b i`.
  have hrepr (i j : ι) (hij : ¬f j < f i) : b.repr (v i) j = c i * Finsupp.single i 1 j := by
    have h0 : b.repr (v i - c i • b i) j = 0 := by
      by_contra h
      exact hij (b.mem_span_image.1 (hv i) (Finsupp.mem_support_iff.2 h))
    rwa [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_self, smul_eq_mul,
      sub_eq_zero] at h0
  -- The matrix of `v` in `b` is upper triangular for a linear order on `ι` refining `f`.
  obtain ⟨_, hlt⟩ := exists_linearOrder_lt_of_apply_lt f
  -- The determinant does not depend on the `DecidableEq ι` instance.
  obtain rfl : ‹DecidableEq ι› = LinearOrder.toDecidableEq := Subsingleton.elim _ _
  rw [det_apply, Matrix.det_of_isUpperTriangular]
  · simp [toMatrix_apply, hrepr _ _ (lt_irrefl _)]
  · intro i j (hji : j < i)
    rw [toMatrix_apply, hrepr _ _ fun hij ↦ (hlt i j hij).not_gt hji,
      Finsupp.single_eq_of_ne hji.ne', mul_zero]

/-- Over an ordered ring in which products of positive elements are positive, a family `v` that
is triangular with respect to a basis `b` along a map `f` into a preorder with positive diagonal
coefficients `c i`, in the sense of `Module.Basis.det_eq_prod_of_sub_smul_mem_span_image_apply_lt`,
has positive determinant in `b`. -/
theorem det_pos_of_sub_smul_mem_span_image_apply_lt [PartialOrder R] [ZeroLEOneClass R]
    [PosMulStrictMono R] [Nontrivial R] [Preorder α] (b : Basis ι R M) (f : ι → α) {v : ι → M}
    {c : ι → R} (hc : ∀ i, 0 < c i)
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' {j | f j < f i})) : 0 < b.det v := by
  rw [b.det_eq_prod_of_sub_smul_mem_span_image_apply_lt f hv]
  exact prod_pos fun i _ ↦ hc i

end Det

end Module.Basis
