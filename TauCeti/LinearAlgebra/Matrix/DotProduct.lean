/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Dot products

A family of `n` linear forms on `K ^ n`, written as coefficient vectors `l i` so that the `i`-th
form sends `x` to `l i ⬝ᵥ x`, is linearly independent exactly when the square matrix with rows
`l i` is invertible. Its kernel is then trivial, so the forms cannot all vanish at a nonzero point.

Relabelling the indices of a square matrix `M` along `e : I ≃ J` is an isometry of the pairing
`(u, v) ↦ u ⬝ᵥ M *ᵥ v`, and the sesquilinear form of a compression `Aᴴ * M * A` is that of `M`
pulled back along `A`.

When `A` scales `x` to a multiple of `x'` and `Aᵀ` scales `y'` to a multiple of `y`, the scalars
transform the dot products `x' ⬝ᵥ y'` and `x ⬝ᵥ y` into each other. For the character-lattice
matrix of a special isogeny acting on roots and coroots, this is the rule by which the Cartan
integers transform (R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, §11).

Over a ring, the bilinear form of a matrix with its diagonal removed is the sum over
ordered off-diagonal index pairs.

For a matrix `J`, a vector orthogonal under `(u, v) ↦ u ⬝ᵥ J *ᵥ v`, or under the sesquilinear
`(u, v) ↦ star u ⬝ᵥ J *ᵥ v`, to every element of a set is orthogonal to its span.

## Main results

* `Matrix.apply_last_eq_of_dotProduct_eq_zero`: if `w ⬝ᵥ v = 0` and the last coordinate of `w` is
  a unit, then the last coordinate of `v` is determined by its other coordinates.
* `Module.Dual.apply_prod_eq_dotProduct_add_mul`: a linear functional on `(ι → R) × R` is
  `(v, t) ↦ v ⬝ᵥ u + t * s`.
* `LinearIndependent.exists_dotProduct_ne_zero`: `n` linearly independent forms on `K ^ n` do not
  all vanish at a nonzero point.
* `Matrix.comp_equiv_symm_dotProduct_reindex_mulVec`: relabelling the indices is an isometry.
* `Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec`: the sesquilinear form of a compression
  `Aᴴ * M * A` is that of `M` pulled back along `A`.
* `Matrix.dotProduct_self_nonneg`: over an ordered ring `v ⬝ᵥ v` is nonnegative.
* `TauCeti.mul_dotProduct_eq_of_mulVec_eq_smul`: if `A *ᵥ x = a • x'` and `Aᵀ *ᵥ y' = b • y`,
  then `a * (x' ⬝ᵥ y') = b * (x ⬝ᵥ y)`.
* `TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero`: over a field in which `2 ≠ 0`,
  every unit vector of `K³` has an orthogonal unit vector.
* `Matrix.dotProduct_mulVec_eq_zero_of_mem_span`,
  `Matrix.star_dotProduct_mulVec_eq_zero_of_mem_span`: orthogonality to a set extends to its span.
-/

public section

open Matrix

/-- The zero-diagonal part of a matrix bilinear form is its sum over ordered off-diagonal pairs. -/
theorem Matrix.dotProduct_mulVec_sub_diagonal_eq_sum_offDiag {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Ring 𝕜] (A : Matrix n n 𝕜) (u v : n → 𝕜) :
    u ⬝ᵥ (A - diagonal A.diag) *ᵥ v =
      ∑ p ∈ (Finset.univ : Finset n).offDiag, u p.1 * A p.1 p.2 * v p.2 := by
  let f (p : n × n) := u p.1 * (A - diagonal A.diag) p.1 p.2 * v p.2
  have he : u ⬝ᵥ (A - diagonal A.diag) *ᵥ v =
      ∑ p ∈ (Finset.univ : Finset n) ×ˢ (Finset.univ : Finset n), f p := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm, Finset.sum_product]
  rw [he, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _),
    Finset.sum_diag]
  simp only [f, Matrix.sub_apply, diagonal_apply_eq, diag_apply, sub_self, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr rfl fun _ hp ↦ by
    rw [diagonal_apply_ne _ (Finset.mem_offDiag.mp hp).2.2, sub_zero]


/-- `n` linearly independent linear forms on `K ^ n` do not all vanish at a nonzero point. -/
theorem LinearIndependent.exists_dotProduct_ne_zero {K ι : Type*} [Field K] [Fintype ι]
    {l : ι → ι → K} (hl : LinearIndependent K l) {x : ι → K} (hx : x ≠ 0) :
    ∃ i, l i ⬝ᵥ x ≠ 0 := by
  classical
  have hinj : Function.Injective (Matrix.of l).mulVec := mulVec_injective_iff_isUnit.mpr <|
    (linearIndependent_row_iff_isUnit (A := Matrix.of l)).mp hl
  by_contra! h
  exact hx <| hinj <| by ext i; simpa [mulVec] using h i

/-- **Relabelling the vertices is an isometry**: for a relabelling `e : I ≃ J` of the indices of a
square matrix `M`, the vectors `u ∘ e.symm` and `v ∘ e.symm` pair under `M.reindex e e` as `u`
and `v` do under `M`. -/
theorem Matrix.comp_equiv_symm_dotProduct_reindex_mulVec {I J α : Type*} [Fintype I] [Fintype J]
    [NonUnitalNonAssocSemiring α] (e : I ≃ J) (M : Matrix I I α) (u v : I → α) :
    u ∘ e.symm ⬝ᵥ M.reindex e e *ᵥ (v ∘ e.symm) = u ⬝ᵥ M *ᵥ v := by
  simp [submatrix_mulVec_equiv, Function.comp_assoc]

/-- The sesquilinear form of a compression `Aᴴ * M * A` is the form of `M` pulled back along `A`:
`star x ⬝ᵥ (Aᴴ * M * A) *ᵥ y = star (A *ᵥ x) ⬝ᵥ M *ᵥ (A *ᵥ y)`. -/
theorem Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec {k l α : Type*} [Fintype k]
    [Fintype l] [NonUnitalSemiring α] [StarRing α] (A : Matrix k l α) (M : Matrix k k α)
    (x y : l → α) : star x ⬝ᵥ (Aᴴ * M * A) *ᵥ y = star (A *ᵥ x) ⬝ᵥ M *ᵥ (A *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, star_mulVec, dotProduct_mulVec]

/-- Over an ordered ring the dot product `v ⬝ᵥ v`, a sum of squares, is nonnegative. -/
@[simp]
theorem Matrix.dotProduct_self_nonneg {n R : Type*} [Fintype n] [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] (v : n → R) : 0 ≤ v ⬝ᵥ v :=
  Fintype.sum_nonneg fun i ↦ mul_self_nonneg (v i)

/-- **Scaling by a matrix and by its transpose transforms the dot product.** If `A` sends `x` to
`a • x'` and `Aᵀ` sends `y'` to `b • y`, then `a * (x' ⬝ᵥ y') = b * (x ⬝ᵥ y)`. For the
character-lattice matrix of a special isogeny, with `x = α_i`, `x' = α_{σ i}`, `y' = α_{σ j}^∨`,
`y = α_j^∨`, `a = ℓ i` and `b = ℓ j`, this is the rule
`ℓ i ⟨α_{σ i}, α_{σ j}^∨⟩ = ℓ j ⟨α_i, α_j^∨⟩` by which the Cartan integers transform. -/
theorem TauCeti.mul_dotProduct_eq_of_mulVec_eq_smul {m n R : Type*} [Fintype m] [Fintype n]
    [NonUnitalCommSemiring R] {A : Matrix m n R} {x y : n → R} {x' y' : m → R} {a b : R}
    (hx : A *ᵥ x = a • x') (hy : Aᵀ *ᵥ y' = b • y) :
    a * (x' ⬝ᵥ y') = b * (x ⬝ᵥ y) := by
  have key := dotProduct_transpose_mulVec A x y'
  rwa [hx, hy, dotProduct_comm x, dotProduct_comm y', smul_dotProduct, smul_dotProduct,
    dotProduct_comm y, eq_comm] at key

/-- If `w ⬝ᵥ v = 0` and `w (Fin.last n)` is a unit, then `v (Fin.last n)` is
`-(w (last))⁻¹ * ∑ i, w i.castSucc * v i.castSucc`. -/
theorem Matrix.apply_last_eq_of_dotProduct_eq_zero {n : ℕ} {R : Type*} [Ring R]
    {w v : Fin (n + 1) → R} (hv : w ⬝ᵥ v = 0)
    (hwunit : IsUnit (w (Fin.last n))) :
    v (Fin.last n) =
      -((hwunit.unit⁻¹ : Rˣ) : R) * ∑ i : Fin n, w i.castSucc * v i.castSucc := by
  simp only [dotProduct, Fin.sum_univ_castSucc] at hv
  calc v (Fin.last n) =
      ((hwunit.unit⁻¹ : Rˣ) : R) * (w (Fin.last n) * v (Fin.last n)) := by
        rw [← mul_assoc, hwunit.val_inv_mul, one_mul]
    _ = _ := by rw [eq_neg_of_add_eq_zero_right hv, mul_neg, neg_mul]

/-- Over a field in which `2 ≠ 0`, **every unit vector of the three-dimensional space has an
orthogonal unit vector**: the reflection exchanging a suitable standard basis vector `eᵢ` with `p`
carries another standard basis vector to one. -/
theorem TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero {K : Type*} [Field K]
    [NeZero (2 : K)] {p : Fin 3 → K} (hp : p ⬝ᵥ p = 1) : ∃ u, u ⬝ᵥ u = 1 ∧ p ⬝ᵥ u = 0 := by
  -- Some coordinate satisfies `p i ≠ 1`, as otherwise `p ⬝ᵥ p = 3`.
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 1 := by
    by_contra! h
    rw [dotProduct, Fin.sum_univ_three, h 0, h 1, h 2] at hp
    exact two_ne_zero (by linear_combination hp : (2 : K) = 0)
  obtain ⟨j, hj⟩ := exists_ne i
  have hi' : 1 - p i ≠ 0 := sub_ne_zero.mpr hi.symm
  -- The reflection exchanging `eᵢ` and `p` sends `eⱼ` to a unit vector orthogonal to `p`.
  refine ⟨Pi.single j 1 + (p j / (1 - p i)) • (Pi.single i 1 - p), ?_, ?_⟩
  · simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_sub,
      sub_dotProduct]
    simp only [single_one_dotProduct, dotProduct_single_one, Pi.single_eq_same,
      Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj.symm, hp, smul_eq_mul]
    field_simp
    ring
  · simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, dotProduct_single_one, hp,
      smul_eq_mul]
    field_simp
    ring

/-- A linear functional on `(ι → R) × R` is `(v, t) ↦ v ⬝ᵥ u + t * s`, where `u k` is its value at
`(Pi.single k 1, 0)` and `s` its value at `(0, 1)`. -/
theorem Module.Dual.apply_prod_eq_dotProduct_add_mul {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring R] (f : Module.Dual R ((ι → R) × R)) (v : ι → R) (t : R) :
    f (v, t) = v ⬝ᵥ (fun k => f (Pi.single k 1, 0)) + t * f (0, 1) := by
  have hsplit : (v, t) = (v, 0) + t • ((0 : ι → R), (1 : R)) := by ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul]
  congr 1
  have := LinearMap.pi_apply_eq_sum_univ (f.comp (LinearMap.inl R (ι → R) R)) v
  simp only [LinearMap.comp_apply, LinearMap.inl_apply] at this
  rw [this, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul]
  congr 3
  ext l
  simp [Pi.single_apply, eq_comm]

/-- **Orthogonality extends to the span, on the right**: if `w ⬝ᵥ J *ᵥ v = 0` for every `v ∈ s`,
then `w ⬝ᵥ J *ᵥ u = 0` for every `u` in the span of `s`. -/
theorem Matrix.dotProduct_mulVec_eq_zero_of_mem_span {n R : Type*} [Fintype n] [CommSemiring R]
    {J : Matrix n n R} {s : Set (n → R)} {w u : n → R} (h : ∀ v ∈ s, w ⬝ᵥ J *ᵥ v = 0)
    (hu : u ∈ Submodule.span R s) : w ⬝ᵥ J *ᵥ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [mulVec_add, dotProduct_add, hx, hy]
  | smul c x _ hx => simp [mulVec_smul, dotProduct_smul, hx]

/-- **Orthogonality extends to the span, on the left**: if `star v ⬝ᵥ J *ᵥ w = 0` for every
`v ∈ s`, then `star u ⬝ᵥ J *ᵥ w = 0` for every `u` in the span of `s`. -/
theorem Matrix.star_dotProduct_mulVec_eq_zero_of_mem_span {n R : Type*} [Fintype n]
    [CommSemiring R] [StarRing R] {J : Matrix n n R} {s : Set (n → R)} {w u : n → R}
    (h : ∀ v ∈ s, star v ⬝ᵥ J *ᵥ w = 0) (hu : u ∈ Submodule.span R s) :
    star u ⬝ᵥ J *ᵥ w = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [add_dotProduct, hx, hy]
  | smul c x _ hx => simp [star_smul, smul_dotProduct, hx]

/-- If `w` is orthogonal to every element of `s`, then the form `star u ⬝ᵥ J *ᵥ w` takes the same
value at any two vectors `u` and `u'` that differ by an element of the span of `s`. -/
theorem Matrix.star_dotProduct_mulVec_eq_of_sub_mem_span {n R : Type*} [Fintype n] [CommRing R]
    [StarRing R] {J : Matrix n n R} {s : Set (n → R)} {w u u' : n → R}
    (h : ∀ v ∈ s, star v ⬝ᵥ J *ᵥ w = 0) (hu : u - u' ∈ Submodule.span R s) :
    star u ⬝ᵥ J *ᵥ w = star u' ⬝ᵥ J *ᵥ w := by
  have h0 := star_dotProduct_mulVec_eq_zero_of_mem_span h hu
  rwa [star_sub, sub_dotProduct, sub_eq_zero] at h0
