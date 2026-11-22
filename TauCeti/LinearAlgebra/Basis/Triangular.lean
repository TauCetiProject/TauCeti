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

Let `e` and `b` be bases of a module indexed by `Fin n` over a stably finite semiring (for
instance a division ring or a commutative semiring), with `b` triangular with respect to `e`:
each `b l` is a combination of `e 0, …, e l`. Then `b` and `e` define the same flag of
submodules in the sense of `Module.Basis.flag`. Combined with
`Module.Basis.mem_flag_iff_repr_eq_zero`, a vector in the span of `e 0, …, e (j - 1)` has
vanishing `b`-coordinates from the `j`-th on.

For a linearly ordered index type, a family `v` is triangular with respect to a basis `b` with
diagonal coefficients `c` when each `v i - c i • b i` is a combination of the `b j` with `j < i`.
Its matrix in `b` is then upper triangular, so its determinant in `b` is the product of the `c i`.

## Main results

* `Module.Basis.flag_eq_of_triangular`: a basis triangular with respect to `e` has the same flag
  as `e`.
* `Module.Basis.det_eq_prod_of_sub_smul_mem_span`: the determinant of a triangular family is the
  product of its diagonal coefficients.
* `Module.Basis.det_pos_of_sub_smul_mem_span`: over an ordered ring, a triangular family with
  positive diagonal coefficients has positive determinant.
* `Module.Basis.det_pos_of_sub_smul_mem_span_image_apply_lt`: the same for a family triangular
  with respect to the relation `f r < f p` for a map `f` into a preorder, such as the projection
  `Prod.fst` from a product index type.
-/

public section

open Finset Submodule

namespace Module.Basis

variable {K E : Type*} [Semiring K] [IsStablyFiniteRing K] [AddCommMonoid E] [Module K E] {n : ℕ}

/-- A basis `b` that is triangular with respect to a basis `e` (each `b l` is a combination of
`e 0, …, e l`) has the same flag as `e`: `b 0, …, b (k - 1)` and `e 0, …, e (k - 1)` span the
same submodule. This holds over any stably finite semiring, such as a division ring or a
commutative semiring, where a square matrix with a one-sided inverse is invertible. -/
theorem flag_eq_of_triangular (b : Basis (Fin n) K E) {e : Basis (Fin n) K E}
    (htri : ∀ l i, l < i → e.repr (b l) i = 0) (k : Fin (n + 1)) : b.flag k = e.flag k := by
  refine le_antisymm (b.flag_le_iff.2 fun l hl ↦ e.mem_flag_iff_repr_eq_zero.2
    fun i hi ↦ htri l i (Fin.castSucc_lt_castSucc_iff.1 (hl.trans_le hi))) ?_
  refine e.flag_le_iff.2 fun i hi ↦ b.mem_flag_iff_repr_eq_zero.2 fun m hm ↦ ?_
  -- The indices from the `k`-th on, where the transition matrices have square blocks.
  let S := {l : Fin n // k ≤ l.castSucc}
  -- Expand `e j` in `b` and then in `e`: at an index `l ∈ S`, only the `b m` with `m ∈ S`
  -- contribute, by triangularity.
  have hexp (j : Fin n) (l : S) :
      ∑ m : S, b.repr (e j) m * e.repr (b m) l = if j = l then 1 else 0 := by
    have h := congrArg (fun x ↦ e.repr x l) (b.sum_repr (e j))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      repr_self, Finsupp.single_apply] at h
    have h0 : ∑ m : {m : Fin n // ¬k ≤ m.castSucc}, b.repr (e j) m * e.repr (b m) l = 0 :=
      Finset.sum_eq_zero fun m _ ↦ by
        rw [htri m l (Fin.castSucc_lt_castSucc_iff.1 ((not_le.1 m.property).trans_le l.property)),
          mul_zero]
    rwa [← Fintype.sum_subtype_add_sum_subtype (fun m ↦ k ≤ m.castSucc), h0, add_zero] at h
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

section Det

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  [LinearOrder ι]

/-- The determinant of a family `v` that is triangular with respect to a basis `b`, in the sense
that each `v i - c i • b i` is a combination of the `b j` with `j < i`, is the product of the
diagonal coefficients `c i`. -/
theorem det_eq_prod_of_sub_smul_mem_span (b : Basis ι R M) {v : ι → M} {c : ι → R}
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' Set.Iio i)) : b.det v = ∏ i, c i := by
  -- The coordinates of `v i` at the indices `j ≥ i` are those of `c i • b i`.
  have hrepr (i j : ι) (hij : i ≤ j) : b.repr (v i) j = c i * Finsupp.single i 1 j := by
    have h0 : b.repr (v i - c i • b i) j = 0 := by
      by_contra h
      exact not_lt.2 hij (b.mem_span_image.1 (hv i) (Finsupp.mem_support_iff.2 h))
    rwa [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_self, smul_eq_mul,
      sub_eq_zero] at h0
  rw [det_apply, Matrix.det_of_isUpperTriangular]
  · simp [toMatrix_apply, hrepr _ _ le_rfl]
  · intro i j (hji : j < i)
    rw [toMatrix_apply, hrepr _ _ hji.le, Finsupp.single_eq_of_ne hji.ne', mul_zero]

/-- Over an ordered ring, a family `v` that is triangular with respect to a basis `b` with positive
diagonal coefficients `c i`, in the sense of `Module.Basis.det_eq_prod_of_sub_smul_mem_span`, has
positive determinant in `b`. -/
theorem det_pos_of_sub_smul_mem_span [PartialOrder R] [IsStrictOrderedRing R] (b : Basis ι R M)
    {v : ι → M} {c : ι → R} (hc : ∀ i, 0 < c i)
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' Set.Iio i)) : 0 < b.det v := by
  rw [b.det_eq_prod_of_sub_smul_mem_span hv]
  exact prod_pos fun i _ ↦ hc i

end Det

section Comp

variable {ι η R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype η] [DecidableEq η]
  [Preorder ι] [PartialOrder R] [IsStrictOrderedRing R]

/-- Over an ordered ring, a family `v` that is triangular with respect to a basis `b` with positive
diagonal coefficients `c p`, in the sense that each `v p - c p • b p` is a combination of the `b r`
with `f r < f p` for a map `f` into a preorder, has positive determinant in `b`. This is
`Module.Basis.det_pos_of_sub_smul_mem_span` for an order on the index type refining the one pulled
back along `f`; for instance, `f = Prod.fst` compares only the first coordinates of a family
indexed by a product. -/
theorem det_pos_of_sub_smul_mem_span_image_apply_lt (b : Basis η R M) (f : η → ι) {v : η → M}
    {c : η → R} (hc : ∀ p, 0 < c p)
    (hv : ∀ p, v p - c p • b p ∈ span R (b '' {r | f r < f p})) : 0 < b.det v := by
  classical
  -- The number of indices below `p` along `f` grows strictly along `f r < f p`.
  let h (p : η) : ℕ := #{r | f r < f p}
  have hh {r p : η} (hr : f r < f p) : h r < h p := card_lt_card <|
    ssubset_iff_of_subset (monotone_filter_right _ fun _ _ hs ↦ hs.trans hr) |>.2
      ⟨r, by simpa using hr, by simp⟩
  -- Refine the order by `h` to a linear order on `η`, breaking ties along `Fin`.
  let : LinearOrder η := LinearOrder.lift' (fun p ↦ toLex (h p, Fintype.equivFin η p))
    fun p q hpq ↦ (Fintype.equivFin η).injective (Prod.ext_iff.1 (toLex.injective hpq)).2
  -- `convert` identifies the `DecidableEq η` instance of the statement with that of the order.
  convert b.det_pos_of_sub_smul_mem_span hc fun p ↦
    span_mono (Set.image_mono fun r hr ↦ Prod.Lex.toLex_lt_toLex.2 (.inl (hh hr))) (hv p)

end Comp

end Module.Basis
