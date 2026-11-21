/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
entry of `M` in a mutable row or column is an integer. Conversely, a rational matrix with a
positive integer skew-symmetrizer that is integral in the mutable rows and columns is the full
matrix of exactly one weighted ice quiver (`WeightedIceQuiver.fullMatrixEquiv`). The entries
between frozen vertices may be fractions: these are the half-arrows of Fock and Goncharov, which
appear when quivers are glued along frozen vertices.

Mutation at a mutable vertex applies the usual mutation formula to the whole full matrix, keeps
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
* `TauCeti.WeightedIceQuiver.fullMatrixEquiv`: weighted ice quivers are equivalent to their full
  matrices and weights.
* `TauCeti.WeightedIceQuiver.mutation`, `TauCeti.WeightedIceQuiver.freeze`,
  `TauCeti.WeightedIceQuiver.defrost`: mutation, freezing and defrosting.

## Main results

* `TauCeti.WeightedIceQuiver.toExchangeMatrix_mutation`: full matrix mutation projects to
  `TauCeti.ExchangeMatrix.mutation`.
* `TauCeti.WeightedIceQuiver.mutation_mutation`: mutation is an involution.
* `TauCeti.WeightedIceQuiver.isIntegralAt_mutation_iff`: mutation preserves integrality at every
  vertex.
* `TauCeti.WeightedIceQuiver.defrost_mutation`, `TauCeti.WeightedIceQuiver.freeze_mutation`:
  mutation commutes with defrosting and with freezing.

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

omit q in
/-- Every vertex is mutable or frozen. -/
private theorem row_or_frozen (i : I) : (∃ k, row k = i) ∨ ∃ f : ↥(Set.range row)ᶜ, f.val = i := by
  by_cases hi : i ∈ Set.range row
  · exact Or.inl hi
  · exact Or.inr ⟨⟨i, hi⟩, rfl⟩

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
  obtain ⟨k, rfl⟩ | ⟨f, rfl⟩ := row_or_frozen (row := row) i
  · simpa using q.symmetrizer_pos k
  · simpa using q.frozenWeight_pos f

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
  obtain ⟨a, rfl⟩ | ⟨f, rfl⟩ := row_or_frozen (row := row) i <;>
    obtain ⟨b, rfl⟩ | ⟨g, rfl⟩ := row_or_frozen (row := row) j
  · simp only [weight_row, fullMatrix_apply_col]
    exact_mod_cast q.symmetrizer_mul_matrix a b
  · simp only [weight_row, weight_frozen, fullMatrix_apply_row_frozen, fullMatrix_apply_col]
    field_simp [hs a]
  · simp only [weight_row, weight_frozen, fullMatrix_apply_row_frozen, fullMatrix_apply_col]
    field_simp [hs b]
  · simpa only [weight_frozen, fullMatrix_apply_frozen] using q.frozenWeight_mul_frozenBlock f g

/-- The diagonal of the full matrix vanishes. -/
@[simp]
theorem fullMatrix_apply_self (i : I) : q.fullMatrix i i = 0 := by
  have h := q.weight_mul_fullMatrix i i
  have hs : (q.weight i : ℚ) ≠ 0 := by exact_mod_cast (q.weight_pos i).ne'
  have h2 : (q.weight i : ℚ) * q.fullMatrix i i = 0 := by linarith
  exact (mul_eq_zero.mp h2).resolve_left hs

/-- The entries of the full matrix in a mutable row are integers. -/
theorem exists_intCast_eq_fullMatrix_row (k : K) (j : I) :
    ∃ n : ℤ, (n : ℚ) = q.fullMatrix (row k) j := by
  obtain ⟨b, rfl⟩ | ⟨f, rfl⟩ := row_or_frozen (row := row) j
  · exact ⟨q.matrix (row k) b, (q.fullMatrix_apply_col _ b).symm⟩
  obtain ⟨c, hc⟩ := q.symmetrizer_dvd f k
  have hs : (q.symmetrizer k : ℚ) ≠ 0 := by exact_mod_cast (q.symmetrizer_pos k).ne'
  have hc' : (q.frozenWeight f : ℚ) * q.matrix f k = q.symmetrizer k * c := by exact_mod_cast hc
  refine ⟨-c, ?_⟩
  rw [fullMatrix_apply_row_frozen, hc']
  field_simp
  push_cast
  ring

/-- The entries of the full matrix in a mutable column are integers. -/
theorem exists_intCast_eq_fullMatrix_col (i : I) (k : K) :
    ∃ n : ℤ, (n : ℚ) = q.fullMatrix i (row k) :=
  ⟨q.matrix i k, (q.fullMatrix_apply_col i k).symm⟩

/-! ### Full matrices -/

/-- The rational matrix `M` with vertex weights `s` is the *full matrix* of a weighted ice quiver
along `row`: the weights are positive and skew-symmetrize `M`, and every entry of `M` in a
mutable row or a mutable column is an integer. -/
structure IsFullMatrix (row : K ↪ I) (s : I → ℤ) (M : Matrix I I ℚ) : Prop where
  /-- The weights are positive. -/
  weight_pos : ∀ i, 0 < s i
  /-- The weights skew-symmetrize the matrix. -/
  weight_mul : ∀ i j, (s i : ℚ) * M i j = -((s j : ℚ) * M j i)
  /-- The entries in a mutable row are integers. -/
  exists_intCast_eq_row : ∀ k j, ∃ n : ℤ, (n : ℚ) = M (row k) j
  /-- The entries in a mutable column are integers. -/
  exists_intCast_eq_col : ∀ i k, ∃ n : ℤ, (n : ℚ) = M i (row k)

/-- The full matrix and the weights of a weighted ice quiver satisfy the defining conditions of a
full matrix. -/
theorem isFullMatrix : IsFullMatrix row q.weight q.fullMatrix :=
  ⟨q.weight_pos, q.weight_mul_fullMatrix, q.exists_intCast_eq_fullMatrix_row,
    q.exists_intCast_eq_fullMatrix_col⟩

namespace IsFullMatrix

variable {s : I → ℤ} {M : Matrix I I ℚ}

/-- The integer value of a mutable column entry is its numerator. -/
private theorem num_col (h : IsFullMatrix row s M) (i : I) (k : K) :
    ((M i (row k)).num : ℚ) = M i (row k) := by
  obtain ⟨n, hn⟩ := h.exists_intCast_eq_col i k
  rw [← hn, Rat.num_intCast]

/-- Restricting the mutable vertices to a subset keeps a full matrix full. -/
theorem of_range_subset {row' : K' ↪ I} (h : IsFullMatrix row s M)
    (hr : Set.range row' ⊆ Set.range row) : IsFullMatrix row' s M where
  weight_pos := h.weight_pos
  weight_mul := h.weight_mul
  exists_intCast_eq_row k j := by
    obtain ⟨l, hl⟩ := hr ⟨k, rfl⟩
    exact hl ▸ h.exists_intCast_eq_row l j
  exists_intCast_eq_col i k := by
    obtain ⟨l, hl⟩ := hr ⟨k, rfl⟩
    exact hl ▸ h.exists_intCast_eq_col i l

/-- A positive weight times the positive part of an entry is the weight of the column vertex
times the negative part of the transposed entry. -/
private theorem weight_mul_posPart (h : IsFullMatrix row s M) (i j : I) :
    (s i : ℚ) * (M i j)⁺ = (s j : ℚ) * (M j i)⁻ := by
  have hi : (0 : ℚ) ≤ s i := by exact_mod_cast (h.weight_pos i).le
  have hj : (0 : ℚ) ≤ s j := by exact_mod_cast (h.weight_pos j).le
  rw [posPart_def, negPart_def, mul_max_of_nonneg _ _ hi, mul_max_of_nonneg _ _ hj,
    h.weight_mul, mul_neg, mul_zero, mul_zero]

end IsFullMatrix

/-- The weighted ice quiver with a given full matrix and weights. -/
noncomputable def ofFullMatrix (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M) :
    WeightedIceQuiver row where
  matrix := of fun i k ↦ (M i (row k)).num
  symmetrizer k := s (row k)
  isSkewSymmetrizer :=
    ⟨fun k ↦ h.weight_pos _, fun a b ↦ by
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
    refine ⟨-n, ?_⟩
    have hf := h.weight_mul f (row k)
    rw [← h.num_col, ← hn] at hf
    have hf' : ((s f * (M f (row k)).num : ℤ) : ℚ) = ((s (row k) * -n : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hf'

section ofFullMatrix

variable (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M)

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

@[simp]
theorem weight_ofFullMatrix (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M) :
    (ofFullMatrix s M h).weight = s := by
  funext i
  obtain ⟨k, rfl⟩ | ⟨f, rfl⟩ := row_or_frozen (row := row) i <;> simp

@[simp]
theorem fullMatrix_ofFullMatrix (s : I → ℤ) (M : Matrix I I ℚ) (h : IsFullMatrix row s M) :
    (ofFullMatrix s M h).fullMatrix = M := by
  have hs (k : K) : (s (row k) : ℚ) ≠ 0 := by exact_mod_cast (h.weight_pos _).ne'
  ext i j
  obtain ⟨b, rfl⟩ | ⟨g, rfl⟩ := row_or_frozen (row := row) j
  · exact (fullMatrix_apply_col _ i b).trans (h.num_col i b)
  obtain ⟨a, rfl⟩ | ⟨f, rfl⟩ := row_or_frozen (row := row) i
  · have hga := h.weight_mul g (row a)
    rw [fullMatrix_apply_row_frozen, ofFullMatrix_frozenWeight, ofFullMatrix_matrix,
      ofFullMatrix_symmetrizer, h.num_col, hga, neg_neg, mul_div_cancel_left₀ _ (hs a)]
  · rw [fullMatrix_apply_frozen, ofFullMatrix_frozenBlock]

/-- A weighted ice quiver is recovered from its full matrix and its weights. -/
@[simp]
theorem ofFullMatrix_fullMatrix : ofFullMatrix q.weight q.fullMatrix q.isFullMatrix = q := by
  ext i k
  · rw [ofFullMatrix_matrix, fullMatrix_apply_col, Rat.num_intCast]
  all_goals simp

/-- A weighted ice quiver is determined by its weights and its full matrix. -/
theorem ext_fullMatrix {q q' : WeightedIceQuiver row} (hs : q.weight = q'.weight)
    (hM : q.fullMatrix = q'.fullMatrix) : q = q' := by
  ext i k
  · exact_mod_cast (q.fullMatrix_apply_col i k).symm.trans
      ((congrFun₂ hM i (row k)).trans (q'.fullMatrix_apply_col i k))
  · rw [← weight_row, hs, weight_row]
  · rw [← weight_frozen, hs, weight_frozen]
  · rw [← fullMatrix_apply_frozen, hM, fullMatrix_apply_frozen]

/-- Weighted ice quivers along `row` correspond bijectively to pairs of positive integer vertex
weights and rational matrices that these weights skew-symmetrize and that are integral in the
mutable rows and columns. -/
noncomputable def fullMatrixEquiv :
    WeightedIceQuiver row ≃ {p : (I → ℤ) × Matrix I I ℚ // IsFullMatrix row p.1 p.2} where
  toFun q := ⟨(q.weight, q.fullMatrix), q.isFullMatrix⟩
  invFun p := ofFullMatrix p.val.1 p.val.2 p.property
  left_inv q := q.ofFullMatrix_fullMatrix
  right_inv p := by
    apply Subtype.ext
    ext : 1 <;> simp

@[simp]
theorem fullMatrixEquiv_apply :
    fullMatrixEquiv q = ⟨(q.weight, q.fullMatrix), q.isFullMatrix⟩ := (rfl)

@[simp]
theorem fullMatrixEquiv_symm_apply
    (p : {p : (I → ℤ) × Matrix I I ℚ // IsFullMatrix row p.1 p.2}) :
    fullMatrixEquiv.symm p = ofFullMatrix p.val.1 p.val.2 p.property := (rfl)

/-! ### Integrality at a vertex -/

/-- The row and the column of the full matrix at the vertex `i` are integral. Mutable vertices
have this property, and a frozen vertex can be made mutable exactly when it has it. -/
def IsIntegralAt (i : I) : Prop :=
  ∀ j, (∃ n : ℤ, (n : ℚ) = q.fullMatrix i j) ∧ ∃ n : ℤ, (n : ℚ) = q.fullMatrix j i

theorem isIntegralAt_iff {i : I} : q.IsIntegralAt i ↔
    ∀ j, (∃ n : ℤ, (n : ℚ) = q.fullMatrix i j) ∧ ∃ n : ℤ, (n : ℚ) = q.fullMatrix j i :=
  Iff.rfl

/-- The full matrix is integral at every mutable vertex. -/
theorem isIntegralAt_row (k : K) : q.IsIntegralAt (row k) :=
  fun j ↦ ⟨q.exists_intCast_eq_fullMatrix_row k j, q.exists_intCast_eq_fullMatrix_col j k⟩

/-! ### Mutation -/

section Mutation

variable [DecidableEq I]

/-- The mutation of a square rational matrix at the vertex `k`. -/
private def mutatedMatrix (M : Matrix I I ℚ) (k : I) : Matrix I I ℚ :=
  of fun i j ↦ if i = k ∨ j = k then -M i j
    else M i j + (M i k)⁺ * (M k j)⁺ - (M i k)⁻ * (M k j)⁻

private theorem mutatedMatrix_apply (M : Matrix I I ℚ) (k i j : I) :
    mutatedMatrix M k i j = if i = k ∨ j = k then -M i j
      else M i j + (M i k)⁺ * (M k j)⁺ - (M i k)⁻ * (M k j)⁻ :=
  (rfl)

private theorem mutatedMatrix_mutatedMatrix (M : Matrix I I ℚ) (k : I) :
    mutatedMatrix (mutatedMatrix M k) k = M := by
  ext i j
  by_cases hik : i = k
  · simp [mutatedMatrix_apply, hik]
  by_cases hjk : j = k
  · simp [mutatedMatrix_apply, hjk]
  simp only [mutatedMatrix_apply, hik, hjk, or_self, ↓reduceIte, or_true, true_or,
    posPart_neg, negPart_neg]
  ring

/-- A mutated entry is an integer if the entry and the two entries in the mutation row and column
that it involves are integers. -/
private theorem exists_intCast_eq_mutatedMatrix {M : Matrix I I ℚ} {k i j : I}
    (hij : ∃ n : ℤ, (n : ℚ) = M i j) (hik : ∃ n : ℤ, (n : ℚ) = M i k)
    (hkj : ∃ n : ℤ, (n : ℚ) = M k j) : ∃ n : ℤ, (n : ℚ) = mutatedMatrix M k i j := by
  obtain ⟨a, ha⟩ := hij
  obtain ⟨b, hb⟩ := hik
  obtain ⟨c, hc⟩ := hkj
  refine ⟨if i = k ∨ j = k then -a else a + b⁺ * c⁺ - b⁻ * c⁻, ?_⟩
  rw [mutatedMatrix_apply, ← ha, ← hb, ← hc]
  split_ifs <;> simp [posPart_def, negPart_def, Int.cast_max]

namespace IsFullMatrix

variable {s : I → ℤ} {M : Matrix I I ℚ}

/-- Mutation at a mutable vertex keeps a full matrix full, with the same weights. -/
private theorem mutatedMatrix (h : IsFullMatrix row s M) (k : K) :
    IsFullMatrix row s (mutatedMatrix M (row k)) where
  weight_pos := h.weight_pos
  weight_mul i j := by
    by_cases hc : i = row k ∨ j = row k
    · have hc' : j = row k ∨ i = row k := hc.symm
      simp only [mutatedMatrix_apply, hc, hc', ↓reduceIte]
      linear_combination -h.weight_mul i j
    · have hc' : ¬(j = row k ∨ i = row k) := fun h' ↦ hc h'.symm
      simp only [mutatedMatrix_apply, hc, hc', ↓reduceIte]
      linear_combination h.weight_mul i j + (M (row k) j)⁺ * h.weight_mul_posPart i (row k) +
        (M (row k) j)⁻ * h.weight_mul_posPart (row k) i +
        (M (row k) i)⁻ * h.weight_mul_posPart (row k) j +
        (M (row k) i)⁺ * h.weight_mul_posPart j (row k)
  exists_intCast_eq_row l j := exists_intCast_eq_mutatedMatrix (h.exists_intCast_eq_row l j)
    (h.exists_intCast_eq_row l (row k)) (h.exists_intCast_eq_row k j)
  exists_intCast_eq_col i l := exists_intCast_eq_mutatedMatrix (h.exists_intCast_eq_col i l)
    (h.exists_intCast_eq_col i k) (h.exists_intCast_eq_row k (row l))

end IsFullMatrix

/-- The *mutation* of a weighted ice quiver at a mutable vertex `k`: the full matrix is mutated
at `row k` by the usual formula and the weights are kept. -/
noncomputable def mutation (k : K) : WeightedIceQuiver row :=
  ofFullMatrix q.weight (mutatedMatrix q.fullMatrix (row k)) (q.isFullMatrix.mutatedMatrix k)

@[simp]
theorem weight_mutation (k : K) : (q.mutation k).weight = q.weight :=
  weight_ofFullMatrix _ _ _

/-- The full matrix of a mutated weighted ice quiver. -/
theorem fullMatrix_mutation_apply (k : K) (i j : I) :
    (q.mutation k).fullMatrix i j = if i = row k ∨ j = row k then -q.fullMatrix i j
      else q.fullMatrix i j + (q.fullMatrix i (row k))⁺ * (q.fullMatrix (row k) j)⁺ -
        (q.fullMatrix i (row k))⁻ * (q.fullMatrix (row k) j)⁻ := by
  rw [mutation, fullMatrix_ofFullMatrix, mutatedMatrix_apply]

/-- Mutation at `k` negates the row of `row k`. -/
@[simp]
theorem fullMatrix_mutation_apply_row (k : K) (j : I) :
    (q.mutation k).fullMatrix (row k) j = -q.fullMatrix (row k) j := by
  simp [fullMatrix_mutation_apply]

/-- Mutation at `k` negates the column of `row k`. This is not a `simp` lemma, since
`fullMatrix_apply_col` already rewrites its left-hand side. -/
theorem fullMatrix_mutation_apply_col (k : K) (i : I) :
    (q.mutation k).fullMatrix i (row k) = -q.fullMatrix i (row k) := by
  rw [fullMatrix_mutation_apply]
  simp

/-- The entries of the mutated full matrix away from the row and the column of `row k`. -/
theorem fullMatrix_mutation_apply_of_ne (k : K) {i j : I} (hi : i ≠ row k) (hj : j ≠ row k) :
    (q.mutation k).fullMatrix i j =
      q.fullMatrix i j + (q.fullMatrix i (row k))⁺ * (q.fullMatrix (row k) j)⁺ -
        (q.fullMatrix i (row k))⁻ * (q.fullMatrix (row k) j)⁻ := by
  simp [fullMatrix_mutation_apply, hi, hj]

/-- Mutating twice at the same vertex gives back the weighted ice quiver. -/
@[simp]
theorem mutation_mutation (k : K) : (q.mutation k).mutation k = q := by
  apply ext_fullMatrix (by simp)
  simp only [mutation, fullMatrix_ofFullMatrix, mutatedMatrix_mutatedMatrix]

/-- Mutation at a fixed vertex is an involution. -/
theorem mutation_involutive (k : K) :
    Function.Involutive fun q : WeightedIceQuiver row ↦ q.mutation k :=
  fun q ↦ q.mutation_mutation k

/-- Mutation of a weighted ice quiver projects to mutation of its exchange matrix. -/
@[simp]
theorem toExchangeMatrix_mutation [DecidableEq K] (k : K) :
    (q.mutation k).toExchangeMatrix = q.toExchangeMatrix.mutation k := by
  ext i j
  · have h := (q.mutation k).fullMatrix_apply_col i j
    rw [fullMatrix_mutation_apply] at h
    simp only [fullMatrix_apply_col, row.injective.eq_iff] at h
    rw [ExchangeMatrix.mutation_matrix, matrixMutation_apply]
    apply Int.cast_injective (α := ℚ)
    rw [← h]
    split_ifs <;> simp [posPart_def, negPart_def, Int.cast_max]
  · rw [ExchangeMatrix.mutation_symmetrizer, ← weight_row, weight_mutation, weight_row]

/-- Mutation preserves integrality of the full matrix at every vertex. -/
theorem isIntegralAt_mutation_iff (k : K) {i : I} :
    (q.mutation k).IsIntegralAt i ↔ q.IsIntegralAt i := by
  suffices H : ∀ q : WeightedIceQuiver row, q.IsIntegralAt i → (q.mutation k).IsIntegralAt i from
    ⟨fun h ↦ by simpa using H _ h, H q⟩
  intro q h j
  have hk := q.isIntegralAt_row k
  simp only [fullMatrix_mutation_apply]
  exact ⟨by simpa [mutatedMatrix_apply] using
      exists_intCast_eq_mutatedMatrix (h j).1 (hk i).2 (hk j).1,
    by simpa [mutatedMatrix_apply] using
      exists_intCast_eq_mutatedMatrix (h j).2 (hk j).2 (hk i).1⟩

end Mutation

/-! ### Freezing and defrosting -/

/-- *Freeze* the mutable vertices outside the range of `ι : K' ↪ K`. The full matrix and the
weights are kept. -/
noncomputable def freeze (ι : K' ↪ K) : WeightedIceQuiver (ι.trans row) :=
  ofFullMatrix q.weight q.fullMatrix (q.isFullMatrix.of_range_subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨ι k, rfl⟩))

@[simp]
theorem weight_freeze (ι : K' ↪ K) : (q.freeze ι).weight = q.weight :=
  weight_ofFullMatrix _ _ _

@[simp]
theorem fullMatrix_freeze (ι : K' ↪ K) : (q.freeze ι).fullMatrix = q.fullMatrix :=
  fullMatrix_ofFullMatrix _ _ _

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

/-- *Defrost* the vertices in the range of a new mutable embedding `row'`. The full matrix must be
integral at each new mutable vertex that was frozen before; the full matrix and the weights are
kept. -/
noncomputable def defrost (row' : K' ↪ I)
    (h : ∀ k, row' k ∉ Set.range row → q.IsIntegralAt (row' k)) : WeightedIceQuiver row' :=
  ofFullMatrix q.weight q.fullMatrix
    { weight_pos := q.weight_pos
      weight_mul := q.weight_mul_fullMatrix
      exists_intCast_eq_row k j := by
        by_cases hk : row' k ∈ Set.range row
        · obtain ⟨l, hl⟩ := hk
          simpa [hl] using q.exists_intCast_eq_fullMatrix_row l j
        · exact (h k hk j).1
      exists_intCast_eq_col i k := by
        by_cases hk : row' k ∈ Set.range row
        · obtain ⟨l, hl⟩ := hk
          simpa [hl] using q.exists_intCast_eq_fullMatrix_col i l
        · exact (h k hk i).2 }

@[simp]
theorem weight_defrost (row' : K' ↪ I)
    (h : ∀ k, row' k ∉ Set.range row → q.IsIntegralAt (row' k)) :
    (q.defrost row' h).weight = q.weight :=
  weight_ofFullMatrix _ _ _

@[simp]
theorem fullMatrix_defrost (row' : K' ↪ I)
    (h : ∀ k, row' k ∉ Set.range row → q.IsIntegralAt (row' k)) :
    (q.defrost row' h).fullMatrix = q.fullMatrix :=
  fullMatrix_ofFullMatrix _ _ _

/-- Integrality at a vertex only depends on the full matrix, so it is unchanged by defrosting. -/
@[simp]
theorem isIntegralAt_defrost_iff (row' : K' ↪ I)
    (h : ∀ k, row' k ∉ Set.range row → q.IsIntegralAt (row' k)) {i : I} :
    (q.defrost row' h).IsIntegralAt i ↔ q.IsIntegralAt i := by
  simp [isIntegralAt_iff]

section Mutation

variable [DecidableEq I]

/-- Mutation at a vertex that is mutable before and after defrosting commutes with defrosting. -/
theorem defrost_mutation (row' : K' ↪ I)
    (h : ∀ k, row' k ∉ Set.range row → q.IsIntegralAt (row' k)) {k : K} {k' : K'}
    (hk : row' k' = row k) :
    (q.mutation k).defrost row' (fun l hl ↦ (q.isIntegralAt_mutation_iff k).2 (h l hl)) =
      (q.defrost row' h).mutation k' := by
  apply ext_fullMatrix (by simp)
  ext i j
  simp [fullMatrix_mutation_apply, hk]

/-- Mutation at a vertex that stays mutable commutes with freezing. -/
theorem freeze_mutation (ι : K' ↪ K) (k : K') :
    (q.mutation (ι k)).freeze ι = (q.freeze ι).mutation k := by
  apply ext_fullMatrix (by simp)
  ext i j
  simp [fullMatrix_mutation_apply]

end Mutation

end WeightedIceQuiver

end TauCeti
