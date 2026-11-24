/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Order.Preorder.Finite

/-!
# Flags of triangular bases

Let `e` and `b` be bases of a module indexed by `Fin n` over a semiring. If `b` is triangular with
respect to `e`, so that each `b l` is a combination of `e 0, …, e l`, and the semiring is
Dedekind-finite (for instance a division ring or a commutative semiring), then `b` and `e` define
the same flag of submodules in the sense of `Module.Basis.flag`. At a single flag step `k`,
`b.flag k ≤ e.flag k` already implies `b.flag k = e.flag k` whenever square matrices over the
semiring of size `min k (n - k)` are Dedekind-finite (in particular, over any stably finite
semiring). Combined with `Module.Basis.mem_flag_iff_repr_eq_zero`, a vector in the span of
`e 0, …, e (j - 1)` has vanishing `b`-coordinates from the `j`-th on.

For a finite index type with a map `f` into a preorder, a family `v` is triangular with respect to
a basis `b` with diagonal coefficients `c` when each `v i - c i • b i` is a combination of the
`b j` with `f j < f i`. Its matrix in `b` is then block triangular for an injective ranking into
`ℕ` refining `f j < f i`, so its determinant in `b` is the product of the `c i`. Taking `f = id`
gives the same for a preordered index type and the `b j` with `j < i`. In the same way, an
endomorphism `f` with each `f (b j) - c j • b j` in the span of the earlier basis vectors has an
upper-triangular matrix in `b` with diagonal `c`.

## Main results

* `Module.Basis.flag_eq_of_flag_le`: if the `k`-th step of the flag of a basis `b` lies in that of
  a basis `e` and square matrices of size `min k (n - k)` over `K` are Dedekind-finite, then the
  two steps are equal.
* `Module.Basis.flag_eq_of_triangular`: over a Dedekind-finite semiring, a basis triangular with
  respect to `e` has the same flag as `e`.
* `Module.Basis.det_eq_prod_of_sub_smul_mem_span_image_apply_lt`: the determinant of a family
  triangular along a map `f` into a preorder is the product of its diagonal coefficients.
* `Module.Basis.det_pos_of_sub_smul_mem_span_image_apply_lt`: for a relation `<` on the ring
  with `0 < 1` under which products of positive elements are positive, such a family with
  positive diagonal coefficients has positive determinant.
* `Module.Basis.linearMap_toMatrix_isUpperTriangular_of_sub_smul_mem_flag` and
  `Module.Basis.linearMap_toMatrix_apply_self_of_sub_smul_mem_flag`: an endomorphism that is
  triangular with respect to the flag of a basis has an upper-triangular matrix in that basis,
  with the given diagonal.
-/

public section

open Finset Submodule

namespace Module.Basis

variable {K E : Type*} [Semiring K] [AddCommMonoid E] [Module K E] {n : ℕ}

/-- If `b` has vanishing `e`-coordinates from `p` to `¬p` and the `p`-block matrix ring is
Dedekind-finite, then `e` also has vanishing `b`-coordinates from `p` to `¬p`. -/
private theorem repr_eq_zero_of_block_zero_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b e : Basis ι K E) {p : ι → Prop} [DecidablePred p]
    [IsDedekindFiniteMonoid (Matrix {l // p l} {l // p l} K)]
    (h : ∀ j l, p j → ¬p l → e.repr (b j) l = 0) {i m : ι} (hi : p i) (hm : ¬p m) :
    b.repr (e i) m = 0 := by
  let P := {l : ι // p l}
  have hexp (j : P) (l : ι) :
      ∑ r : P, e.repr (b j) r * b.repr (e r) l = if (j : ι) = l then 1 else 0 := by
    rw [Fintype.sum_of_injective Subtype.val Subtype.val_injective _
      (fun r ↦ e.repr (b j) r * b.repr (e r) l)
      (fun r hr ↦ by rw [h j r j.property fun hpr ↦ hr ⟨⟨r, hpr⟩, rfl⟩, zero_mul]) (fun _ ↦ rfl)]
    simpa [repr_self, Finsupp.single_apply] using b.sum_repr_mul_repr' e (b j) l
  let A : Matrix P P K := .of fun j r ↦ e.repr (b j) r
  let B : Matrix P P K := .of fun r l ↦ b.repr (e r) l
  have hBA : B * A = 1 := mul_eq_one_comm.1 <| by
    ext j l; simp [A, B, Matrix.mul_apply, Matrix.one_apply, hexp, Subtype.val_inj]
  have hAz : A.mulVec (fun r : P ↦ b.repr (e r) m) = 0 := by
    ext j
    have hjm : (j : ι) ≠ m := fun h ↦ hm (h ▸ j.property)
    simp [Matrix.mulVec, dotProduct, A, hexp, hjm]
  simpa [hBA, hAz] using
    (congrFun (Matrix.mulVec_mulVec (fun r : P ↦ b.repr (e r) m) B A) ⟨i, hi⟩).symm

/-- If `b` has vanishing `e`-coordinates from `p` to `¬p` and the `¬p`-block matrix ring is
Dedekind-finite, then `e` also has vanishing `b`-coordinates from `p` to `¬p`. -/
private theorem repr_eq_zero_of_block_zero_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b e : Basis ι K E) {p : ι → Prop} [DecidablePred p]
    [IsDedekindFiniteMonoid (Matrix {l // ¬p l} {l // ¬p l} K)]
    (h : ∀ j l, p j → ¬p l → e.repr (b j) l = 0) {i m : ι} (hi : p i) (hm : ¬p m) :
    b.repr (e i) m = 0 := by
  let S := {l : ι // ¬p l}
  have hexp (j : ι) (l : S) :
      ∑ r : S, b.repr (e j) r * e.repr (b r) l = if j = l then 1 else 0 := by
    rw [Fintype.sum_of_injective Subtype.val Subtype.val_injective _
      (fun r ↦ b.repr (e j) r * e.repr (b r) l)
      (fun r hr ↦ by rw [h r l (not_not.1 fun hpr ↦ hr ⟨⟨r, hpr⟩, rfl⟩) l.property, mul_zero])
      (fun _ ↦ rfl)]
    simpa [repr_self, Finsupp.single_apply] using e.sum_repr_mul_repr' b (e j) l
  let D : Matrix S S K := .of fun r l ↦ e.repr (b r) l
  let W : Matrix S S K := .of fun j r ↦ b.repr (e j) r
  have hDW : D * W = 1 := mul_eq_one_comm.1 <| by
    ext j l; simp [W, D, Matrix.mul_apply, Matrix.one_apply, hexp, Subtype.val_inj]
  have hzD : Matrix.vecMul (fun r : S ↦ b.repr (e i) r) D = 0 := by
    ext l
    have hil : i ≠ l := fun h ↦ l.property (h ▸ hi)
    simp [Matrix.vecMul, dotProduct, D, hexp, hil]
  simpa [hDW, hzD] using
    (congrFun (Matrix.vecMul_vecMul (fun r : S ↦ b.repr (e i) r) D W) ⟨m, hm⟩).symm

/-- If the `k`-th step `b.flag k` of the flag of a basis `b` lies in the `k`-th step of the flag
of a basis `e`, and square matrices over `K` of size `min k (n - k)` are Dedekind-finite (for
instance when `K` is a stably finite semiring, such as a division ring or a commutative semiring,
or at `k = 1` or `k = n - 1` when `K` itself is Dedekind-finite), then `b.flag k = e.flag k`:
`b 0, …, b (k - 1)` and `e 0, …, e (k - 1)` span the same submodule. -/
theorem flag_eq_of_flag_le (b : Basis (Fin n) K E) {e : Basis (Fin n) K E} {k : Fin (n + 1)}
    [IsDedekindFiniteMonoid
      (Matrix (Fin (min (k : ℕ) (n - k))) (Fin (min (k : ℕ) (n - k))) K)]
    (h : b.flag k ≤ e.flag k) : b.flag k = e.flag k := by
  refine le_antisymm h <| e.flag_le_iff.2 fun i hi ↦ b.mem_flag_iff_repr_eq_zero.2 fun m hm ↦ ?_
  have hzero (j l : Fin n) (hj : j.castSucc < k) (hl : ¬l.castSucc < k) : e.repr (b j) l = 0 :=
    e.mem_flag_iff_repr_eq_zero.1 (h (b.self_mem_flag hj)) l (not_lt.1 hl)
  -- Invert whichever diagonal block of the transition matrix has the smaller size `min k (n - k)`.
  rcases le_total (k : ℕ) (n - k) with hkn | hkn
  · let eP : {l : Fin n // l.castSucc < k} ≃ Fin (min (k : ℕ) (n - k)) :=
      (Fin.castLEquiv (Nat.le_of_lt_succ k.isLt)).symm.trans (finCongr (min_eq_left hkn).symm)
    have : IsDedekindFiniteMonoid (Matrix {l : Fin n // l.castSucc < k} _ K) :=
      (MulEquivClass.isDedekindFiniteMonoid_iff (Matrix.reindexRingEquiv K eP)).2 inferInstance
    exact repr_eq_zero_of_block_zero_left b e hzero hi (not_lt.2 hm)
  · let eS : {l : Fin n // ¬l.castSucc < k} ≃ Fin (min (k : ℕ) (n - k)) :=
      (Equiv.subtypeEquiv Fin.revPerm fun l ↦ by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.revPerm_apply, Fin.val_rev]; omega).trans <|
        (Fin.castLEquiv (Nat.sub_le n k)).symm.trans (finCongr (min_eq_right hkn).symm)
    have : IsDedekindFiniteMonoid (Matrix {l : Fin n // ¬l.castSucc < k} _ K) :=
      (MulEquivClass.isDedekindFiniteMonoid_iff (Matrix.reindexRingEquiv K eS)).2 inferInstance
    exact repr_eq_zero_of_block_zero_right b e hzero hi (not_lt.2 hm)

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
    have h := e.sum_repr_mul_repr' b (e j) i
    rw [Finset.sum_eq_single i (fun m _ hmi ↦ ?_) (by simp)] at h
    · simpa [repr_self, Finsupp.single_apply] using h
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
  -- The matrix of `v` in `b` is block triangular for an injective ranking refining `f`.
  obtain ⟨g, hg_inj, hlt⟩ := TauCeti.exists_injective_nat_lt_of_apply_lt f
  have htri : (b.toMatrix v).BlockTriangular g := by
    intro i j (hji : g j < g i)
    rw [toMatrix_apply, hrepr _ _ fun hij ↦ (hlt i j hij).not_gt hji,
      Finsupp.single_eq_of_ne (fun h ↦ hji.ne (congrArg g h.symm)), mul_zero]
  rw [det_apply, htri.det_eq_prod_diag hg_inj]
  simp [toMatrix_apply, hrepr _ _ (lt_irrefl _)]

/-- Let `<` be a relation on the ring `R` with `0 < 1` under which products of positive elements
are positive, as in an ordered ring. A family `v` that is triangular with respect to a basis `b`
along a map `f` into a preorder with positive diagonal coefficients `c i`, in the sense of
`Module.Basis.det_eq_prod_of_sub_smul_mem_span_image_apply_lt`, has positive determinant in `b`.
-/
theorem det_pos_of_sub_smul_mem_span_image_apply_lt [LT R] [Preorder α] (b : Basis ι R M)
    (f : ι → α) {v : ι → M} {c : ι → R} (h1 : (0 : R) < 1)
    (hmul : ∀ x y : R, 0 < x → 0 < y → 0 < x * y) (hc : ∀ i, 0 < c i)
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' {j | f j < f i})) : 0 < b.det v := by
  rw [b.det_eq_prod_of_sub_smul_mem_span_image_apply_lt f hv]
  exact prod_induction _ (0 < ·) hmul h1 fun i _ ↦ hc i

end Det

section Flag

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
  (b : Basis (Fin n) R M) {f : M →ₗ[R] M} {c : Fin n → R}

/-- On and below the diagonal, the matrix of an endomorphism `f` that is triangular with respect to
the flag of `b`, with diagonal coefficients `c`, is that of `j ↦ c j • b j`. -/
private theorem linearMap_toMatrix_apply_of_sub_smul_mem_flag
    (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) {i j : Fin n} (hji : j ≤ i) :
    LinearMap.toMatrix b b f i j = c j * Finsupp.single j 1 i := by
  have h0 := b.mem_flag_iff_repr_eq_zero.1 (h j) i (Fin.castSucc_le_castSucc_iff.2 hji)
  rw [LinearMap.toMatrix_apply]
  rwa [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_self, smul_eq_mul,
    sub_eq_zero] at h0

/-- The matrix of an endomorphism `f` in a basis `b` is upper triangular when each `f (b j)` is a
multiple of `b j` modulo the span `b.flag j.castSucc` of the earlier basis vectors. -/
theorem linearMap_toMatrix_isUpperTriangular_of_sub_smul_mem_flag
    (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) :
    (LinearMap.toMatrix b b f).IsUpperTriangular := by
  -- `IsUpperTriangular` is `BlockTriangular · id`, so its hypothesis `id j < id i` is `j < i`
  intro i j (hji : j < i)
  rw [linearMap_toMatrix_apply_of_sub_smul_mem_flag b h hji.le, Finsupp.single_eq_of_ne hji.ne',
    mul_zero]

/-- The diagonal of the matrix of an endomorphism `f` in a basis `b` is `c` when each
`f (b j) - c j • b j` lies in the span `b.flag j.castSucc` of the earlier basis vectors. -/
theorem linearMap_toMatrix_apply_self_of_sub_smul_mem_flag
    (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) (i : Fin n) :
    LinearMap.toMatrix b b f i i = c i := by
  rw [linearMap_toMatrix_apply_of_sub_smul_mem_flag b h le_rfl, Finsupp.single_eq_same, mul_one]

end Flag

end Module.Basis
