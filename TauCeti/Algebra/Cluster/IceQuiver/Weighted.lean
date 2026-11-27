/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation.Basic
public import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Tactic.FieldSimp

/-!
# Weighted ice quivers and their full matrices

A *weighted ice quiver* along `row : K ↪ I` is an exchange matrix `B` (rows `I`, mutable columns
`K`, with a symmetrizer `s_k`) together with positive integer weights `s_f` on the frozen
vertices `f ∉ Set.range row` and a rational block `C` of arrow weights between frozen vertices,
such that `s_f C_fg = -s_g C_gf` and `s_k ∣ s_f B_fk`. Its *full matrix* `M : Matrix I I ℚ` is

* `M i (row k) = B i k`,
* `M (row k) f = -s_f B_fk / s_k` for frozen `f`,
* `M f g = C f g` for frozen `f` and `g`.

Every vertex now carries a positive weight `s_i`, these weights skew-symmetrize `M`, and every
entry of `M` in a mutable row or column is an integer. Conversely, for a fixed mutable embedding
`row`, a pair of positive integer weights `s` and a rational matrix `M` that `s` skew-symmetrizes
and that is integral in the mutable rows and columns comes from exactly one weighted ice quiver,
whose weights are `s` and whose full matrix is `M` (`WeightedIceQuiver.weightFullMatrixEquiv`).
The matrix alone does not determine the weights. The entries between frozen vertices are
arbitrary rationals, subject only to weighted skew-symmetry; the motivating special case is the
half-arrows of Fock and Goncharov, which appear when quivers are glued along frozen vertices.

Mutation at a mutable vertex applies `TauCeti.matrixMutation` to the whole full matrix, keeps
the weights, and projects to mutation of the exchange matrix
(`WeightedIceQuiver.toExchangeMatrix_mutation`). Freezing and defrosting change the mutable
embedding and keep the full matrix and weights. A frozen vertex can be defrosted when its row and
column in the full matrix are integral (`WeightedIceQuiver.IsIntegralAt`); mutation at a mutable
vertex preserves this condition and commutes with defrosting and with freezing.

## Main definitions

* `TauCeti.WeightedIceQuiver row`: an exchange matrix with frozen weights and a frozen block.
* `TauCeti.WeightedIceQuiver.weight`, `TauCeti.WeightedIceQuiver.fullMatrix`: the weights of all
  vertices and the full skew-symmetrizable rational matrix.
* `TauCeti.WeightedIceQuiver.IsFullMatrix row s M`: the conditions characterizing full matrices.
* `TauCeti.WeightedIceQuiver.weightFullMatrixEquiv`: weighted ice quivers are equivalent to their
  weights together with their full matrices.
* `TauCeti.WeightedIceQuiver.mutation`, `TauCeti.WeightedIceQuiver.freeze`,
  `TauCeti.WeightedIceQuiver.defrost`: mutation, freezing and defrosting.

## Main results

* `TauCeti.WeightedIceQuiver.fullMatrix_mutation`: the full matrix of the mutation at `k` is the
  matrix mutation of the full matrix at `row k`.
* `TauCeti.WeightedIceQuiver.toExchangeMatrix_mutation`: full matrix mutation projects to
  `TauCeti.ExchangeMatrix.mutation`.
* `TauCeti.WeightedIceQuiver.mutation_mutation`: mutation is an involution.
* `TauCeti.WeightedIceQuiver.isIntegralAt_mutation_iff`: mutation preserves integrality at every
  vertex.
* `TauCeti.WeightedIceQuiver.defrost_mutation`, `TauCeti.WeightedIceQuiver.freeze_mutation`:
  mutation commutes with defrosting and with freezing.

## Implementation notes

The rational full matrix reuses the matrix-level theory of `ExchangeMatrix/Basic.lean` and
`ExchangeMatrix/Mutation/Basic.lean`, which is stated over any linearly ordered ring: the weights
form a `Matrix.IsSkewSymmetrizer` of the full matrix, mutation is `TauCeti.matrixMutation` along
`Function.Embedding.refl I`, its involutivity is `TauCeti.matrixMutation_matrixMutation`,
preservation of the skew-symmetrizer is `Matrix.IsSkewSymmetrizer.matrixMutation`, and preservation
of integrality at a vertex is `TauCeti.forall_matrixMutation_refl_mem_iff` for the subring of
integers.

## References

* V. V. Fock and A. B. Goncharov, *Cluster X-varieties, amalgamation, and Poisson–Lie groups*,
  in *Algebraic Geometry and Number Theory*, Progr. Math. 253, Birkhäuser (2006), §§2.1–2.2,
  for seeds with multipliers, rational exchange matrices between frozen vertices, mutation and
  defrosting.
-/

public section

open Matrix

namespace TauCeti

variable {I K K' : Type*}

/-- A *weighted ice quiver* along the embedding `row : K ↪ I` of the mutable vertices: an
exchange matrix together with positive integer weights on the frozen vertices
`f ∉ Set.range row` and a rational matrix of arrow weights between frozen vertices. The weights
skew-symmetrize the frozen block, and the symmetrizer `s_k` of a mutable vertex divides the
weighted entry `s_f B_fk`, so that the entries of the mutable rows of the full matrix are
integers. -/
@[ext]
structure WeightedIceQuiver (row : K ↪ I) extends ExchangeMatrix row where
  /-- The weights of the frozen vertices. -/
  frozenWeight : ↥(Set.range row)ᶜ → ℤ
  /-- The weights of the frozen vertices are positive. -/
  frozenWeight_pos : ∀ f, 0 < frozenWeight f
  /-- The arrow weights between frozen vertices. -/
  frozenBlock : Matrix ↥(Set.range row)ᶜ ↥(Set.range row)ᶜ ℚ
  /-- The frozen weights skew-symmetrize the frozen block. -/
  frozenWeight_mul_frozenBlock : ∀ f g,
    (frozenWeight f : ℚ) * frozenBlock f g = -((frozenWeight g : ℚ) * frozenBlock g f)
  /-- The symmetrizer of a mutable vertex divides the weighted entries of its column in the
  frozen rows. -/
  symmetrizer_dvd : ∀ f k, symmetrizer k ∣ frozenWeight f * matrix f k

namespace WeightedIceQuiver

variable {row : K ↪ I} (q : WeightedIceQuiver row)

/-! ### Weights and the full matrix -/

/-- The weight of a vertex: the symmetrizer at a mutable vertex and the frozen weight at a frozen
vertex. -/
noncomputable def weight : I → ℤ :=
  Function.extend row q.symmetrizer (Function.extend Subtype.val q.frozenWeight 0)

@[simp]
theorem weight_row (k : K) : q.weight (row k) = q.symmetrizer k :=
  row.injective.extend_apply _ _ k

@[simp]
theorem weight_frozen (f : ↥(Set.range row)ᶜ) : q.weight f = q.frozenWeight f := by
  rw [weight, Function.extend_apply' _ _ _ f.property]
  exact Subtype.val_injective.extend_apply _ _ f

/-- Every vertex weight is positive. -/
theorem weight_pos (i : I) : 0 < q.weight i := by
  by_cases hi : i ∈ Set.range row
  · obtain ⟨k, rfl⟩ := hi
    simpa using q.symmetrizer_pos k
  · lift i to ↥(Set.range row)ᶜ using hi
    simpa using q.frozenWeight_pos i

/-- The entries of the full matrix in a frozen column. -/
private noncomputable def frozenColumn (j : I) : I → ℚ :=
  Function.extend row (fun k ↦ -((q.weight j : ℚ) * q.matrix j k) / q.symmetrizer k)
    (Function.extend Subtype.val
      (fun f ↦ Function.extend Subtype.val (q.frozenBlock f) 0 j) 0)

/-- The *full matrix* of a weighted ice quiver, a square rational matrix on all vertices. Its
mutable columns are the columns of the exchange matrix, its entry in a mutable row `row k` and
a frozen column `f` is `-s_f B_fk / s_k`, and its frozen entries form the frozen block. -/
noncomputable def fullMatrix : Matrix I I ℚ :=
  of fun i j ↦ Function.extend row (fun k ↦ (q.matrix i k : ℚ)) (fun j ↦ q.frozenColumn j i) j

@[simp]
theorem fullMatrix_apply_col (i : I) (k : K) : q.fullMatrix i (row k) = q.matrix i k := by
  rw [fullMatrix, of_apply, row.injective.extend_apply]

@[simp]
theorem fullMatrix_apply_row_frozen (k : K) (f : ↥(Set.range row)ᶜ) :
    q.fullMatrix (row k) f = -((q.frozenWeight f : ℚ) * q.matrix f k) / q.symmetrizer k := by
  rw [fullMatrix, of_apply, Function.extend_apply' _ _ _ f.property, frozenColumn,
    row.injective.extend_apply, weight_frozen]

@[simp]
theorem fullMatrix_apply_frozen (f g : ↥(Set.range row)ᶜ) :
    q.fullMatrix f g = q.frozenBlock f g := by
  rw [fullMatrix, of_apply, Function.extend_apply' _ _ _ g.property, frozenColumn,
    Function.extend_apply' _ _ _ f.property, Subtype.val_injective.extend_apply,
    Subtype.val_injective.extend_apply]

/-- The vertex weights skew-symmetrize the full matrix. -/
theorem weight_mul_fullMatrix (i j : I) :
    (q.weight i : ℚ) * q.fullMatrix i j = -((q.weight j : ℚ) * q.fullMatrix j i) := by
  have hs (k : K) : (q.symmetrizer k : ℚ) ≠ 0 := by exact_mod_cast (q.symmetrizer_pos k).ne'
  by_cases hi : i ∈ Set.range row <;> by_cases hj : j ∈ Set.range row
  · obtain ⟨a, rfl⟩ := hi
    obtain ⟨b, rfl⟩ := hj
    simp only [weight_row, fullMatrix_apply_col]
    exact_mod_cast q.symmetrizer_mul_matrix a b
  · obtain ⟨a, rfl⟩ := hi
    lift j to ↥(Set.range row)ᶜ using hj
    simp only [weight_row, weight_frozen, fullMatrix_apply_row_frozen, fullMatrix_apply_col]
    field_simp [hs a]
  · obtain ⟨b, rfl⟩ := hj
    lift i to ↥(Set.range row)ᶜ using hi
    simp only [weight_row, weight_frozen, fullMatrix_apply_row_frozen, fullMatrix_apply_col]
    field_simp [hs b]
  · lift i to ↥(Set.range row)ᶜ using hi
    lift j to ↥(Set.range row)ᶜ using hj
    simpa only [weight_frozen, fullMatrix_apply_frozen] using q.frozenWeight_mul_frozenBlock i j

/-- The vertex weights form a skew-symmetrizer of the full matrix. -/
theorem isSkewSymmetrizer_fullMatrix :
    q.fullMatrix.IsSkewSymmetrizer fun i ↦ (q.weight i : ℚ) :=
  ⟨fun i ↦ by exact_mod_cast q.weight_pos i, q.weight_mul_fullMatrix⟩

/-- The diagonal of the full matrix vanishes. -/
@[simp]
theorem fullMatrix_apply_self (i : I) : q.fullMatrix i i = 0 :=
  q.isSkewSymmetrizer_fullMatrix.apply_self i

/-- The entries of the full matrix in a mutable row are integers. -/
theorem exists_intCast_eq_fullMatrix_row (k : K) (j : I) :
    ∃ n : ℤ, (n : ℚ) = q.fullMatrix (row k) j := by
  by_cases hj : j ∈ Set.range row
  · obtain ⟨b, rfl⟩ := hj
    exact ⟨q.matrix (row k) b, (q.fullMatrix_apply_col _ b).symm⟩
  lift j to ↥(Set.range row)ᶜ using hj
  have hd := (Rat.den_div_intCast_eq_one_iff _ _ (q.symmetrizer_pos k).ne').2
    (q.symmetrizer_dvd j k)
  refine ⟨-(((q.frozenWeight j * q.matrix j k : ℤ) : ℚ) / q.symmetrizer k).num, ?_⟩
  rw [Int.cast_neg, (Rat.den_eq_one_iff _).1 hd, fullMatrix_apply_row_frozen, neg_div,
    Int.cast_mul]

/-- The entries of the full matrix in a mutable column are integers. -/
theorem exists_intCast_eq_fullMatrix_col (i : I) (k : K) :
    ∃ n : ℤ, (n : ℚ) = q.fullMatrix i (row k) :=
  ⟨q.matrix i k, (q.fullMatrix_apply_col i k).symm⟩

/-! ### Full matrices -/

/-- The rational matrix `M` with vertex weights `s` is the *full matrix* of a weighted ice quiver
along `row`: the weights form a skew-symmetrizer of `M`, and every entry of `M` in a mutable row
or a mutable column is an integer. -/
structure IsFullMatrix (row : K ↪ I) (s : I → ℤ) (M : Matrix I I ℚ) : Prop where
  /-- The weights skew-symmetrize the matrix. -/
  isSkewSymmetrizer : M.IsSkewSymmetrizer fun i ↦ (s i : ℚ)
  /-- The entries in a mutable row are integers. -/
  exists_intCast_eq_row : ∀ k j, ∃ n : ℤ, (n : ℚ) = M (row k) j
  /-- The entries in a mutable column are integers. -/
  exists_intCast_eq_col : ∀ i k, ∃ n : ℤ, (n : ℚ) = M i (row k)

/-- The full matrix and the weights of a weighted ice quiver satisfy the defining conditions of a
full matrix. -/
theorem isFullMatrix : IsFullMatrix row q.weight q.fullMatrix :=
  ⟨q.isSkewSymmetrizer_fullMatrix, q.exists_intCast_eq_fullMatrix_row,
    q.exists_intCast_eq_fullMatrix_col⟩

namespace IsFullMatrix

variable {s : I → ℤ} {M : Matrix I I ℚ}

/-- The weights of a full matrix are positive. -/
theorem weight_pos (h : IsFullMatrix row s M) (i : I) : 0 < s i :=
  Int.cast_pos.mp (h.isSkewSymmetrizer.pos i)

/-- The weights of a full matrix skew-symmetrize it. -/
theorem weight_mul (h : IsFullMatrix row s M) (i j : I) :
    (s i : ℚ) * M i j = -((s j : ℚ) * M j i) :=
  h.isSkewSymmetrizer.mul_apply i j

/-- The row and the column of a full matrix at a mutable vertex lie in the subring of integers. -/
private theorem mem_bot (h : IsFullMatrix row s M) (k : K) (j : I) :
    M (row k) j ∈ (⊥ : Subring ℚ) ∧ M j (row k) ∈ (⊥ : Subring ℚ) :=
  ⟨Subring.mem_bot.2 (h.exists_intCast_eq_row k j), Subring.mem_bot.2 (h.exists_intCast_eq_col j k)⟩

/-- The integer value of a mutable column entry is its numerator. -/
private theorem num_col (h : IsFullMatrix row s M) (i : I) (k : K) :
    ((M i (row k)).num : ℚ) = M i (row k) := by
  obtain ⟨n, hn⟩ := h.exists_intCast_eq_col i k
  rw [← hn, Rat.num_intCast]

/-- Restricting the mutable vertices to a subset keeps a full matrix full. -/
theorem of_range_subset {row' : K' ↪ I} (h : IsFullMatrix row s M)
    (hr : Set.range row' ⊆ Set.range row) : IsFullMatrix row' s M :=
  have H (k : K') (j : I) : M (row' k) j ∈ (⊥ : Subring ℚ) ∧ M j (row' k) ∈ (⊥ : Subring ℚ) := by
    obtain ⟨l, hl⟩ := hr ⟨k, rfl⟩
    rw [← hl]
    exact h.mem_bot l j
  ⟨h.isSkewSymmetrizer, fun k j ↦ Subring.mem_bot.1 (H k j).1,
    fun i k ↦ Subring.mem_bot.1 (H k i).2⟩

end IsFullMatrix

/-- The weighted ice quiver with a given full matrix and weights. -/
noncomputable def ofFullMatrix (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M) :
    WeightedIceQuiver row where
  matrix := of fun i k ↦ (M i (row k)).num
  symmetrizer k := s (row k)
  isSkewSymmetrizer :=
    ⟨fun _ ↦ h.weight_pos _, fun a b ↦ by
      have hab := h.weight_mul (row a) (row b)
      rw [← h.num_col (row a) b, ← h.num_col (row b) a] at hab
      simp only [submatrix_apply, of_apply, id_eq]
      exact_mod_cast hab⟩
  frozenWeight f := s f
  frozenWeight_pos f := h.weight_pos f
  frozenBlock f g := M f g
  frozenWeight_mul_frozenBlock f g := h.weight_mul f g
  symmetrizer_dvd f k := by
    obtain ⟨n, hn⟩ := h.exists_intCast_eq_row k f
    have hs : (s (row k) : ℚ) ≠ 0 := by exact_mod_cast (h.weight_pos _).ne'
    have hq : ((s f * (M f (row k)).num : ℤ) : ℚ) / s (row k) = -n := by
      rw [Int.cast_mul, h.num_col, h.weight_mul, hn, neg_div, mul_div_cancel_left₀ _ hs]
    exact (Rat.den_div_intCast_eq_one_iff _ _ (h.weight_pos _).ne').1 (by
      rw [of_apply, hq, Rat.den_neg_eq_den, Rat.den_intCast])

section ofFullMatrix

variable (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M)

@[simp]
theorem ofFullMatrix_matrix (i : I) (k : K) :
    (ofFullMatrix s M h).matrix i k = (M i (row k)).num :=
  (rfl)

@[simp]
theorem ofFullMatrix_symmetrizer (k : K) : (ofFullMatrix s M h).symmetrizer k = s (row k) :=
  (rfl)

@[simp]
theorem ofFullMatrix_frozenWeight (f : ↥(Set.range row)ᶜ) :
    (ofFullMatrix s M h).frozenWeight f = s f :=
  (rfl)

@[simp]
theorem ofFullMatrix_frozenBlock (f g : ↥(Set.range row)ᶜ) :
    (ofFullMatrix s M h).frozenBlock f g = M f g :=
  (rfl)

end ofFullMatrix

/-- The weighted ice quiver built from the weights `s` and the full matrix `M` has the weights
`s`. -/
@[simp]
theorem weight_ofFullMatrix (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M) :
    (ofFullMatrix s M h).weight = s := by
  funext i
  by_cases hi : i ∈ Set.range row
  · obtain ⟨k, rfl⟩ := hi
    simp
  · lift i to ↥(Set.range row)ᶜ using hi
    simp

/-- The weighted ice quiver built from the weights `s` and the full matrix `M` has the full
matrix `M`. -/
@[simp]
theorem fullMatrix_ofFullMatrix (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M) :
    (ofFullMatrix s M h).fullMatrix = M := by
  have hs (k : K) : (s (row k) : ℚ) ≠ 0 := by exact_mod_cast (h.weight_pos _).ne'
  ext i j
  by_cases hj : j ∈ Set.range row
  · obtain ⟨b, rfl⟩ := hj
    exact (fullMatrix_apply_col _ i b).trans (h.num_col i b)
  lift j to ↥(Set.range row)ᶜ using hj
  by_cases hi : i ∈ Set.range row
  · obtain ⟨a, rfl⟩ := hi
    have hga := h.weight_mul j (row a)
    rw [fullMatrix_apply_row_frozen, ofFullMatrix_frozenWeight, ofFullMatrix_matrix,
      ofFullMatrix_symmetrizer, h.num_col, hga, neg_neg, mul_div_cancel_left₀ _ (hs a)]
  · lift i to ↥(Set.range row)ᶜ using hi
    rw [fullMatrix_apply_frozen, ofFullMatrix_frozenBlock]

/-- A weighted ice quiver is recovered from its full matrix and its weights. -/
@[simp]
theorem ofFullMatrix_fullMatrix : ofFullMatrix q.weight q.fullMatrix q.isFullMatrix = q := by
  ext i k
  · rw [ofFullMatrix_matrix, fullMatrix_apply_col, Rat.num_intCast]
  all_goals simp

/-- Weighted ice quivers along `row` correspond bijectively to pairs of positive integer vertex
weights and rational matrices that these weights skew-symmetrize and that are integral in the
mutable rows and columns. -/
noncomputable def weightFullMatrixEquiv :
    WeightedIceQuiver row ≃ {p : (I → ℤ) × Matrix I I ℚ // IsFullMatrix row p.1 p.2} where
  toFun q := ⟨(q.weight, q.fullMatrix), q.isFullMatrix⟩
  invFun p := ofFullMatrix p.val.1 p.val.2 p.property
  left_inv q := q.ofFullMatrix_fullMatrix
  right_inv p := by
    apply Subtype.ext
    ext : 1 <;> simp

@[simp]
theorem weightFullMatrixEquiv_apply :
    weightFullMatrixEquiv q = ⟨(q.weight, q.fullMatrix), q.isFullMatrix⟩ := (rfl)

@[simp]
theorem weightFullMatrixEquiv_symm_apply
    (p : {p : (I → ℤ) × Matrix I I ℚ // IsFullMatrix row p.1 p.2}) :
    weightFullMatrixEquiv.symm p = ofFullMatrix p.val.1 p.val.2 p.property := (rfl)

/-- A weighted ice quiver is determined by its weights and its full matrix. -/
theorem ext_weight_fullMatrix {q q' : WeightedIceQuiver row} (hs : q.weight = q'.weight)
    (hM : q.fullMatrix = q'.fullMatrix) : q = q' :=
  weightFullMatrixEquiv.injective (Subtype.ext (Prod.ext hs hM))

/-! ### Integrality at a vertex -/

/-- The row and the column of the full matrix at the vertex `i` are integral. Mutable vertices
have this property, and a frozen vertex can be made mutable exactly when it has it. -/
def IsIntegralAt (i : I) : Prop :=
  ∀ j, (∃ n : ℤ, (n : ℚ) = q.fullMatrix i j) ∧ ∃ n : ℤ, (n : ℚ) = q.fullMatrix j i

theorem isIntegralAt_iff {i : I} : q.IsIntegralAt i ↔
    ∀ j, (∃ n : ℤ, (n : ℚ) = q.fullMatrix i j) ∧ ∃ n : ℤ, (n : ℚ) = q.fullMatrix j i :=
  Iff.rfl

/-- The full matrix is integral at every mutable vertex. -/
@[simp]
theorem isIntegralAt_row (k : K) : q.IsIntegralAt (row k) :=
  fun j ↦ ⟨q.exists_intCast_eq_fullMatrix_row k j, q.exists_intCast_eq_fullMatrix_col j k⟩

/-! ### Mutation -/

section Mutation

variable [DecidableEq I]

namespace IsFullMatrix

variable {s : I → ℤ} {M : Matrix I I ℚ}

/-- Mutation at a mutable vertex keeps a full matrix full, with the same weights. -/
protected theorem matrixMutation (h : IsFullMatrix row s M) (k : K) :
    IsFullMatrix row s (matrixMutation (Function.Embedding.refl I) M (row k)) :=
  have H (l : K) (j : I) :
      matrixMutation (Function.Embedding.refl I) M (row k) (row l) j ∈ (⊥ : Subring ℚ) ∧
        matrixMutation (Function.Embedding.refl I) M (row k) j (row l) ∈ (⊥ : Subring ℚ) :=
    (forall_matrixMutation_refl_mem_iff (h.mem_bot k) (row l)).2 (h.mem_bot l) j
  ⟨h.isSkewSymmetrizer.matrixMutation (row k), fun l j ↦ Subring.mem_bot.1 (H l j).1,
    fun i l ↦ Subring.mem_bot.1 (H l i).2⟩

end IsFullMatrix

/-- The *mutation* of a weighted ice quiver at a mutable vertex `k`: the full matrix is mutated
at `row k` by the usual formula and the weights are kept. -/
noncomputable def mutation (k : K) : WeightedIceQuiver row :=
  ofFullMatrix q.weight (matrixMutation (Function.Embedding.refl I) q.fullMatrix (row k))
    (q.isFullMatrix.matrixMutation k)

/-- Mutation keeps all vertex weights. -/
@[simp]
theorem weight_mutation (k : K) : (q.mutation k).weight = q.weight :=
  weight_ofFullMatrix _ _ _

/-- The full matrix of a mutated weighted ice quiver is the mutation of the full matrix. -/
@[simp]
theorem fullMatrix_mutation (k : K) :
    (q.mutation k).fullMatrix = matrixMutation (Function.Embedding.refl I) q.fullMatrix (row k) :=
  fullMatrix_ofFullMatrix _ _ _

/-- The entries of the full matrix of a mutated weighted ice quiver. -/
theorem fullMatrix_mutation_apply (k : K) (i j : I) :
    (q.mutation k).fullMatrix i j = if i = row k ∨ j = row k then -q.fullMatrix i j
      else q.fullMatrix i j + (q.fullMatrix i (row k))⁺ * (q.fullMatrix (row k) j)⁺ -
        (q.fullMatrix i (row k))⁻ * (q.fullMatrix (row k) j)⁻ := by
  rw [fullMatrix_mutation, matrixMutation_apply, Function.Embedding.refl_apply]

/-- Mutation at `k` negates the row of `row k`. -/
theorem fullMatrix_mutation_apply_row (k : K) (j : I) :
    (q.mutation k).fullMatrix (row k) j = -q.fullMatrix (row k) j := by
  simp [fullMatrix_mutation_apply]

/-- Mutation at `k` negates the column of `row k`. This is not a `simp` lemma, since
`fullMatrix_apply_col` already rewrites its left-hand side. -/
theorem fullMatrix_mutation_apply_col (k : K) (i : I) :
    (q.mutation k).fullMatrix i (row k) = -q.fullMatrix i (row k) := by
  rw [fullMatrix_mutation, matrixMutation_apply_col]

/-- The entries of the mutated full matrix away from the row and the column of `row k`. -/
theorem fullMatrix_mutation_apply_of_ne (k : K) {i j : I} (hi : i ≠ row k) (hj : j ≠ row k) :
    (q.mutation k).fullMatrix i j =
      q.fullMatrix i j + (q.fullMatrix i (row k))⁺ * (q.fullMatrix (row k) j)⁺ -
        (q.fullMatrix i (row k))⁻ * (q.fullMatrix (row k) j)⁻ := by
  simp [fullMatrix_mutation_apply, hi, hj]

/-- Mutating twice at the same vertex gives back the weighted ice quiver. -/
@[simp]
theorem mutation_mutation (k : K) : (q.mutation k).mutation k = q :=
  ext_weight_fullMatrix (by simp) (by simp)

/-- Mutation at a fixed vertex is an involution. -/
theorem mutation_involutive (k : K) :
    Function.Involutive fun q : WeightedIceQuiver row ↦ q.mutation k :=
  fun q ↦ q.mutation_mutation k

/-- Mutation of a weighted ice quiver projects to mutation of its exchange matrix. -/
@[simp]
theorem toExchangeMatrix_mutation [DecidableEq K] (k : K) :
    (q.mutation k).toExchangeMatrix = q.toExchangeMatrix.mutation k := by
  have hB : q.fullMatrix.submatrix id row = q.matrix.map (Int.castRingHom ℚ) := by
    ext
    simp
  have h := (matrixMutation_submatrix (row := Function.Embedding.refl I) (row' := row) (f := id)
    (g := row) Function.injective_id (fun _ ↦ rfl) q.fullMatrix k).symm
  rw [hB, matrixMutation_map _ Int.cast_mono] at h
  ext i j
  · apply Int.cast_injective (α := ℚ)
    rw [ExchangeMatrix.mutation_matrix, ← fullMatrix_apply_col, fullMatrix_mutation]
    simpa using congrFun₂ h i j
  · rw [ExchangeMatrix.mutation_symmetrizer, ← weight_row, weight_mutation, weight_row]

/-- Mutation preserves integrality of the full matrix at every vertex. -/
@[simp]
theorem isIntegralAt_mutation_iff (k : K) {i : I} :
    (q.mutation k).IsIntegralAt i ↔ q.IsIntegralAt i := by
  simpa only [isIntegralAt_iff, fullMatrix_mutation, ← Subring.mem_bot] using
    forall_matrixMutation_refl_mem_iff (q.isFullMatrix.mem_bot k) i

end Mutation

/-! ### Freezing and defrosting -/

/-- *Freeze* the mutable vertices outside the range of `ι : K' ↪ K`. The full matrix and the
weights are kept. -/
noncomputable def freeze (ι : K' ↪ K) : WeightedIceQuiver (ι.trans row) :=
  ofFullMatrix q.weight q.fullMatrix (q.isFullMatrix.of_range_subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨ι k, rfl⟩))

/-- Freezing keeps all vertex weights. -/
@[simp]
theorem weight_freeze (ι : K' ↪ K) : (q.freeze ι).weight = q.weight :=
  weight_ofFullMatrix _ _ _

/-- Freezing keeps the entire full matrix, although fewer vertices are mutable. -/
@[simp]
theorem fullMatrix_freeze (ι : K' ↪ K) : (q.freeze ι).fullMatrix = q.fullMatrix :=
  fullMatrix_ofFullMatrix _ _ _

/-- Integrality at a vertex only depends on the full matrix, so it is unchanged by freezing. -/
@[simp]
theorem isIntegralAt_freeze_iff (ι : K' ↪ K) {i : I} :
    (q.freeze ι).IsIntegralAt i ↔ q.IsIntegralAt i := by
  simp [isIntegralAt_iff]

/-- Freezing deletes the columns of the frozen vertices from the exchange matrix. -/
@[simp]
theorem toExchangeMatrix_freeze (ι : K' ↪ K) :
    (q.freeze ι).toExchangeMatrix =
      q.toExchangeMatrix.submatrix id ι (Function.Embedding.trans_apply ι row) := by
  ext i k
  · rw [ExchangeMatrix.submatrix_matrix, submatrix_apply, id_eq]
    exact_mod_cast ((q.freeze ι).fullMatrix_apply_col i k).symm.trans
      ((congrFun₂ (q.fullMatrix_freeze ι) i _).trans (q.fullMatrix_apply_col i (ι k)))
  · rw [ExchangeMatrix.submatrix_symmetrizer, Function.comp_apply, ← weight_row (q.freeze ι),
      weight_freeze, Function.Embedding.trans_apply, weight_row]

/-- *Defrost* along `ι : K ↪ K'`: the new mutable embedding `row'` extends `row` along `ι`, so
every old mutable vertex stays mutable. The full matrix must be integral at each new mutable vertex
outside the range of `ι`; the full matrix and the weights are kept. -/
noncomputable def defrost (ι : K ↪ K') (row' : K' ↪ I) (hι : ∀ k, row' (ι k) = row k)
    (h : ∀ k, k ∉ Set.range ι → q.IsIntegralAt (row' k)) : WeightedIceQuiver row' :=
  ofFullMatrix q.weight q.fullMatrix <|
    have H (k : K') : q.IsIntegralAt (row' k) := by
      by_cases hk : k ∈ Set.range ι
      · obtain ⟨l, rfl⟩ := hk
        rw [hι]
        exact q.isIntegralAt_row l
      · exact h k hk
    ⟨q.isSkewSymmetrizer_fullMatrix, fun k j ↦ (H k j).1, fun i k ↦ (H k i).2⟩

/-- Defrosting keeps all vertex weights. -/
@[simp]
theorem weight_defrost (ι : K ↪ K') (row' : K' ↪ I) (hι : ∀ k, row' (ι k) = row k)
    (h : ∀ k, k ∉ Set.range ι → q.IsIntegralAt (row' k)) :
    (q.defrost ι row' hι h).weight = q.weight :=
  weight_ofFullMatrix _ _ _

/-- Defrosting keeps the entire full matrix, although more vertices are mutable. -/
@[simp]
theorem fullMatrix_defrost (ι : K ↪ K') (row' : K' ↪ I) (hι : ∀ k, row' (ι k) = row k)
    (h : ∀ k, k ∉ Set.range ι → q.IsIntegralAt (row' k)) :
    (q.defrost ι row' hι h).fullMatrix = q.fullMatrix :=
  fullMatrix_ofFullMatrix _ _ _

/-- Integrality at a vertex only depends on the full matrix, so it is unchanged by defrosting. -/
@[simp]
theorem isIntegralAt_defrost_iff (ι : K ↪ K') (row' : K' ↪ I) (hι : ∀ k, row' (ι k) = row k)
    (h : ∀ k, k ∉ Set.range ι → q.IsIntegralAt (row' k)) {i : I} :
    (q.defrost ι row' hι h).IsIntegralAt i ↔ q.IsIntegralAt i := by
  simp [isIntegralAt_iff]

section Mutation

variable [DecidableEq I]

/-- Mutation at an old mutable vertex commutes with defrosting. -/
theorem defrost_mutation (ι : K ↪ K') (row' : K' ↪ I) (hι : ∀ k, row' (ι k) = row k)
    (h : ∀ k, k ∉ Set.range ι → q.IsIntegralAt (row' k)) (k : K) :
    (q.mutation k).defrost ι row' hι (fun l hl ↦ (q.isIntegralAt_mutation_iff k).2 (h l hl)) =
      (q.defrost ι row' hι h).mutation (ι k) := by
  apply ext_weight_fullMatrix (by simp)
  simp [hι]

/-- Mutation at a vertex that stays mutable commutes with freezing. -/
theorem freeze_mutation (ι : K' ↪ K) (k : K') :
    (q.mutation (ι k)).freeze ι = (q.freeze ι).mutation k := by
  exact ext_weight_fullMatrix (by simp) (by simp)

end Mutation

end WeightedIceQuiver

end TauCeti
