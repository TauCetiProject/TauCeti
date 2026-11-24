/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility

/-!
# Degree mutation and column-annihilating gradings

Given an extended integer matrix `B : Matrix I K ℤ` along `row : K ↪ I` on a finite row type `I`
and a family of degrees `g : I → G` in an additive commutative group, a column-annihilating grading
satisfies `∑ i, B i j • g i = 0` for every mutable column `j`, or more generally
`∑ i, (B i j / r j) • g i = 0` when positive exchange degrees `r j` divide their columns. Column
annihilation makes binary and degree-`r` polynomial cluster exchange relations homogeneous, so
`degreeMutation` tracks the degrees of cluster variables across seed mutations, including principal
`g`-vectors.

Mutating `g` in direction `k` replaces `g (row k)` by
`-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i` and fixes all other coordinates.
When `B (row k) k = 0` and column `k` has degree zero, replacing `(-B i k)⁺` by `(B i k)⁺` gives
the same mutated family, and mutating twice in direction `k` recovers `g`. When `B (row k) k = 0`,
simultaneous matrix and degree mutation preserves and reflects both divided-column and ordinary
column annihilation.

Iterating along finite mutation words propagates any initial grading while keeping all coordinates
outside `Set.range row` fixed.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compositio Mathematica 143
  (2007), §6, Proposition 6.1, for homogeneity and degree mutation.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195 (2005),
  §3, equations (3.2)–(3.4), for the signed mutation factors.
* J. E. Grabowski and S. Launois, *Graded quantum cluster algebras and an application to quantum
  Grassmannians*, Proceedings of the London Mathematical Society (3) 109 (2014), §3, for
  column-annihilating gradings on quantum cluster algebras.
* Bai, Chen, Ding and Xu, *Generalized quantum cluster algebras: the Laurent phenomenon and upper
  bounds*, §2, and T. Nakanishi and D. Rupel, *Companion cluster algebras to a generalized cluster
  algebra*, §3, for divided-column exchange degrees.
-/

public section

namespace TauCeti

open Matrix

section DegreeMutation

variable {I K I' K' G H : Type*} [DecidableEq I] [Fintype I] [AddCommGroup G] [AddCommGroup H]

/-- Mutate a grading `g : I → G` in direction `k` along `B`: coordinate `row k` becomes
`-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i` and all other coordinates
are unchanged. -/
def degreeMutation (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (g : I → G) : I → G :=
  Function.update g (row k)
    (-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i)

variable (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (g g₁ g₂ : I → G)

/-- Definitional presentation of degree mutation via `Function.update`. -/
theorem degreeMutation_def : degreeMutation row B k g =
    Function.update g (row k) (-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i) :=
  (rfl)

/-- Entrywise formula for degree mutation. -/
theorem degreeMutation_apply (j : I) : degreeMutation row B k g j =
    if j = row k then -g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i else g j := by
  simp [degreeMutation, Function.update_apply]

/-- Formula for `degreeMutation` at the mutated coordinate `row k`. -/
theorem degreeMutation_apply_row :
    degreeMutation row B k g (row k) =
      -g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i := by simp [degreeMutation]

@[simp]
theorem degreeMutation_apply_of_ne {j : I} (hj : j ≠ row k) : degreeMutation row B k g j = g j := by
  simp [degreeMutation, hj]

/-- Coordinates outside the mutable rows are fixed by every degree mutation. -/
@[simp]
theorem degreeMutation_apply_of_notMem_range {j : I} (hj : j ∉ Set.range row) :
    degreeMutation row B k g j = g j :=
  degreeMutation_apply_of_ne row B k g fun h ↦ hj ⟨k, h.symm⟩

/-- When `B (row k) k = 0`, the sum in `degreeMutation` extends over all row indices. -/
theorem degreeMutation_apply_row_of_eq_zero (hkk : B (row k) k = 0) :
    degreeMutation row B k g (row k) = -g (row k) + ∑ i, (-B i k)⁺ • g i := by
  rw [degreeMutation_apply_row, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp [hkk]

/-- Degree mutation acts by the columns of the positive-sign left mutation factor `E₁`. -/
theorem degreeMutation_eq_sum_matrixMutationLeft_smul (j : I) :
    degreeMutation row B k g j = ∑ i, matrixMutationLeft row B k 1 i j • g i := by
  by_cases hj : j = row k
  · subst j
    rw [degreeMutation_apply_row, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
    simp only [matrixMutationLeft_apply_col, ite_true, neg_one_smul, neg_mul, one_mul]
    exact congrArg _ (Finset.sum_congr rfl fun i hi ↦ by simp [(Finset.mem_erase.mp hi).1])
  · simp [hj, Matrix.one_apply]

private theorem sum_matrixMutationLeft_smul_sum_matrixMutationLeft_smul (ε : ℤ) (l : I) :
    (∑ j, matrixMutationLeft row B k ε j l • ∑ i, matrixMutationLeft row B k ε i j • g i) =
      g l := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, mul_comm (matrixMutationLeft row B k ε _ l)]
  have hmul (i : I) :
      (∑ j, matrixMutationLeft row B k ε i j * matrixMutationLeft row B k ε j l) =
        (1 : Matrix I I ℤ) i l := by
    simpa only [Matrix.mul_apply] using
      congrFun (congrFun (matrixMutationLeft_mul_self row B k ε) i) l
  simp [hmul, Matrix.one_apply]

/-- Applying `degreeMutation` twice with the same matrix and direction is the identity. -/
@[simp]
theorem degreeMutation_self : degreeMutation row B k (degreeMutation row B k g) = g := by
  ext l; simp_rw [degreeMutation_eq_sum_matrixMutationLeft_smul]
  exact sum_matrixMutationLeft_smul_sum_matrixMutationLeft_smul row B k g 1 l

@[simp]
theorem degreeMutation_zero : degreeMutation row B k (0 : I → G) = 0 := by
  ext j; simp [degreeMutation_eq_sum_matrixMutationLeft_smul]

theorem degreeMutation_add :
    degreeMutation row B k (g₁ + g₂) = degreeMutation row B k g₁ + degreeMutation row B k g₂ := by
  ext j; simp [degreeMutation_eq_sum_matrixMutationLeft_smul, smul_add, Finset.sum_add_distrib]

@[simp]
theorem degreeMutation_neg : degreeMutation row B k (-g) = -degreeMutation row B k g := by
  ext j; simp [degreeMutation_eq_sum_matrixMutationLeft_smul, Finset.sum_neg_distrib]

theorem degreeMutation_sub :
    degreeMutation row B k (g₁ - g₂) = degreeMutation row B k g₁ - degreeMutation row B k g₂ := by
  simp only [sub_eq_add_neg, degreeMutation_add, degreeMutation_neg]

/-- Additive group homomorphisms commute with degree mutation. -/
theorem comp_degreeMutation (φ : G →+ H) :
    φ ∘ degreeMutation row B k g = degreeMutation row B k (φ ∘ g) := by
  ext j; simp [degreeMutation_eq_sum_matrixMutationLeft_smul, map_sum, map_zsmul]

/-- Evaluating an additive homomorphism on a mutated degree equals mutating the mapped degrees. -/
theorem map_degreeMutation_apply (φ : G →+ H) (j : I) :
    φ (degreeMutation row B k g j) = degreeMutation row B k (φ ∘ g) j :=
  congrFun (comp_degreeMutation row B k g φ) j

/-- When `B (row k) k = 0` and column `k` has total degree zero, either signed left factor `Eε`
(`ε = ±1`) computes degree mutation. -/
theorem degreeMutation_eq_sum_matrixMutationLeft_smul_of_sum_smul_eq_zero
    (hkk : B (row k) k = 0) (hcol : ∑ i, B i k • g i = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (j : I) :
    degreeMutation row B k g j = ∑ i, matrixMutationLeft row B k ε i j • g i := by
  rcases hε with rfl | rfl
  · exact degreeMutation_eq_sum_matrixMutationLeft_smul row B k g j
  · rw [degreeMutation_eq_sum_matrixMutationLeft_smul]
    by_cases hj : j = row k
    · subst j
      apply sub_eq_zero.mp
      rw [← Finset.sum_sub_distrib]
      simp_rw [← sub_smul, matrixMutationLeft_apply_col_one_sub_neg_one row B k hkk, neg_smul]
      rw [Finset.sum_neg_distrib, hcol, neg_zero]
    · simp [matrixMutationLeft_apply_of_ne _ _ _ _ _ hj]

/-- When `B (row k) k = 0` and column `k` has total degree zero, degree mutation in direction `k`
uses `(B i k)⁺` interchangeably with `(-B i k)⁺`. -/
theorem degreeMutation_apply_row_posPart (hkk : B (row k) k = 0)
    (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row B k g (row k) =
      -g (row k) + ∑ i ∈ Finset.univ.erase (row k), (B i k)⁺ • g i := by
  rw [degreeMutation_eq_sum_matrixMutationLeft_smul_of_sum_smul_eq_zero row B k g hkk hcol
    (Or.inr rfl), ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp only [matrixMutationLeft_apply_col, ite_true, neg_one_smul, neg_neg, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp [(Finset.mem_erase.mp hi).1]

/-- Full-sum positive-part formula for degree mutation when `B (row k) k = 0` and column `k`
has total degree zero. -/
theorem degreeMutation_apply_row_posPart_univ (hkk : B (row k) k = 0)
    (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row B k g (row k) = -g (row k) + ∑ i, (B i k)⁺ • g i := by
  rw [degreeMutation_apply_row_posPart row B k g hkk hcol,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp [hkk]

/-- Negating the matrix fixes degree mutation in direction `k` when `B (row k) k = 0` and
column `k` has total degree zero. -/
theorem degreeMutation_neg_left (hkk : B (row k) k = 0) (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row (-B) k g = degreeMutation row B k g := by
  ext j
  by_cases hj : j = row k
  · simp [hj, degreeMutation_apply_row, degreeMutation_apply_row_posPart row B k g hkk hcol]
  · simp [hj]

/-- Mutating along `B` and then along `matrixMutation row B k` in the same direction recovers `g`
whenever `B (row k) k = 0` and column `k` has total degree zero. -/
@[simp]
theorem degreeMutation_degreeMutation [DecidableEq K] (hkk : B (row k) k = 0)
    (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row (matrixMutation row B k) k (degreeMutation row B k g) = g := by
  ext l
  rw [degreeMutation_eq_sum_matrixMutationLeft_smul, matrixMutationLeft_matrixMutation]
  simp_rw [degreeMutation_eq_sum_matrixMutationLeft_smul_of_sum_smul_eq_zero row B k g hkk hcol
    (Or.inr rfl)]
  exact sum_matrixMutationLeft_smul_sum_matrixMutationLeft_smul row B k g (-1) l

/-- Degree mutation commutes with bijective relabelling of all rows and any compatible map of
mutable columns. -/
theorem degreeMutation_submatrix [DecidableEq I'] [Fintype I'] {row' : K' ↪ I'}
    {f : I' → I} {hK : K' → K} (hf : Function.Bijective f)
    (h : ∀ a, f (row' a) = row (hK a)) (k : K') :
    degreeMutation row' (B.submatrix f hK) k (g ∘ f) = degreeMutation row B (hK k) g ∘ f := by
  let e : I' ≃ I := Equiv.ofBijective f hf
  ext j
  have hrow : j = row' k ↔ f j = row (hK k) := by rw [← h, hf.injective.eq_iff]
  by_cases hj : j = row' k
  · subst j
    simp only [Function.comp_apply, degreeMutation_apply_row, h,
      Finset.sum_erase_eq_sub (Finset.mem_univ _), submatrix_apply]
    exact congrArg (-g (row (hK k)) + ·)
      (congrArg (· - _) (e.sum_comp fun i ↦ (-B i (hK k))⁺ • g i))
  · simp [hj, mt hrow.mpr hj]

section Preservation

variable [DecidableEq K]

/-- Exact transformation of divided-column pairings under simultaneous matrix and degree
mutation. -/
theorem sum_matrixMutation_ediv_smul_degreeMutation {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0) (j : K) :
    ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i =
      if j = k then -∑ i, (B i k / r k) • g i
      else ∑ i, (B i j / r j) • g i +
        (r k * (B (row k) j / r j)⁺) • ∑ i, (B i k / r k) • g i := by
  let : Fintype K := Fintype.ofInjective row row.injective
  set β : Matrix I K ℤ := of fun i l ↦ B i l / r l
  have hstep :
      ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i =
        ∑ a, (β * matrixMutationRight row β k (r k * 1)) a j • g a := by
    simp_rw [degreeMutation_eq_sum_matrixMutationLeft_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_smul]
    congr 1
    simp_rw [mul_comm (matrixMutation row B k _ j / r j)]
    simpa only [Matrix.mul_apply, β, of_apply] using congrFun (congrFun
      (matrixMutationLeft_mul_of_matrixMutation_ediv row B r k 1 hr hdvd hkk (Or.inl rfl)) a) j
  rw [hstep]
  by_cases hj : j = k
  · subst j; simp [mul_matrixMutationRight_apply, β, Finset.sum_neg_distrib]
  · have hrk : ((r k * 1) * β (row k) j)⁺ = r k * (B (row k) j / r j)⁺ := by
      simp only [mul_one, β, of_apply, posPart_def, mul_max_of_nonneg _ _ (hr k).le, mul_zero]
    simp only [hj, ite_false, mul_matrixMutationRight_apply, hrk, add_smul]
    simp only [β, of_apply]
    rw [Finset.sum_add_distrib, Finset.smul_sum]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun a _ ↦ by simp [smul_smul, mul_comm])

/-- Along the mutation column `k`, the mutated matrix pairs with the mutated degrees by the
negative of the original pairing whenever `B (row k) k = 0`. -/
theorem sum_matrixMutation_col_smul_degreeMutation (hkk : B (row k) k = 0) :
    ∑ i, matrixMutation row B k i k • degreeMutation row B k g i = -∑ i, B i k • g i := by
  simpa using sum_matrixMutation_ediv_smul_degreeMutation row B k g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) hkk k

/-- Simultaneous matrix and degree mutation preserves divided-column annihilation
`∑ i, (B i j / r j) • g i = 0` when `B (row k) k = 0` and positive degrees `r j` divide every
column. -/
theorem sum_matrixMutation_ediv_smul_degreeMutation_eq_zero {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0)
    (hg : ∀ j, ∑ i, (B i j / r j) • g i = 0) (j : K) :
    ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i = 0 := by
  simp [sum_matrixMutation_ediv_smul_degreeMutation row B k g hr hdvd hkk j, hg]

/-- Divided-column annihilation is preserved and reflected by simultaneous matrix and degree
mutation when `B (row k) k = 0` and positive degrees divide every column. -/
theorem forall_sum_matrixMutation_ediv_smul_degreeMutation_eq_zero_iff {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0) :
    (∀ j, ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i = 0) ↔
      ∀ j, ∑ i, (B i j / r j) • g i = 0 := by
  refine ⟨fun h' ↦ ?_, sum_matrixMutation_ediv_smul_degreeMutation_eq_zero row B k g hr hdvd hkk⟩
  have hk : ∑ i, (B i k / r k) • g i = 0 := by
    have hk' := h' k
    rw [sum_matrixMutation_ediv_smul_degreeMutation row B k g hr hdvd hkk k] at hk'
    simpa using hk'
  intro j
  by_cases hj : j = k
  · exact hj ▸ hk
  · have hj' := h' j
    rw [sum_matrixMutation_ediv_smul_degreeMutation row B k g hr hdvd hkk j] at hj'
    simpa [hj, hk] using hj'

/-- Simultaneous matrix and degree mutation preserves ordinary column annihilation
`∑ i, B i j • g i = 0` when `B (row k) k = 0`. -/
theorem sum_matrixMutation_smul_degreeMutation_eq_zero (hkk : B (row k) k = 0)
    (hg : ∀ j, ∑ i, B i j • g i = 0) (j : K) :
    ∑ i, matrixMutation row B k i j • degreeMutation row B k g i = 0 := by
  simpa using sum_matrixMutation_ediv_smul_degreeMutation_eq_zero row B k g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) hkk (by simpa using hg) j

/-- Ordinary column annihilation is preserved and reflected by simultaneous matrix and degree
mutation when `B (row k) k = 0`. -/
theorem forall_sum_matrixMutation_smul_degreeMutation_eq_zero_iff (hkk : B (row k) k = 0) :
    (∀ j, ∑ i, matrixMutation row B k i j • degreeMutation row B k g i = 0) ↔
      ∀ j, ∑ i, B i j • g i = 0 := by
  simpa using forall_sum_matrixMutation_ediv_smul_degreeMutation_eq_zero_iff row B k g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) hkk

end Preservation

end DegreeMutation

section BlockSum

variable {I₁ I₂ K₁ K₂ G : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [Fintype I₁] [Fintype I₂] [AddCommGroup G]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)
  (g₁ : I₁ → G) (g₂ : I₂ → G)

/-- Mutating a block-diagonal matrix in the first summand mutates the first degree family and
fixes the second. -/
@[simp]
theorem degreeMutation_fromBlocks_inl (k : K₁) :
    degreeMutation (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.inl k) (Sum.elim g₁ g₂) =
      Sum.elim (degreeMutation row₁ B₁ k g₁) g₂ := by
  have hrow : (row₁.sumMap row₂) (Sum.inl k) = Sum.inl (row₁ k) := by simp
  ext (i | i)
  · by_cases hi : i = row₁ k
    · subst i
      rw [Sum.elim_inl, ← hrow, degreeMutation_apply_row, degreeMutation_apply_row, hrow]
      simp [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fintype.sum_sum_type]
    · simp [degreeMutation_apply, hi]
  · simp [degreeMutation_apply]

/-- Mutating a block-diagonal matrix in the second summand mutates the second degree family and
fixes the first. -/
@[simp]
theorem degreeMutation_fromBlocks_inr (k : K₂) :
    degreeMutation (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.inr k) (Sum.elim g₁ g₂) =
      Sum.elim g₁ (degreeMutation row₂ B₂ k g₂) := by
  have hrow : (row₁.sumMap row₂) (Sum.inr k) = Sum.inr (row₂ k) := by simp
  ext (i | i)
  · simp [degreeMutation_apply]
  · by_cases hi : i = row₂ k
    · subst i
      rw [Sum.elim_inr, ← hrow, degreeMutation_apply_row, degreeMutation_apply_row, hrow]
      simp [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fintype.sum_sum_type]
    · simp [degreeMutation_apply, hi]

end BlockSum

section Word

variable {I K I' K' G H : Type*} [DecidableEq I] [DecidableEq K] [Fintype I]
  [AddCommGroup G] [AddCommGroup H]

/-- Propagate a grading `g : I → G` along a finite mutation word in reading order, mutating the
underlying matrix simultaneously at each step. -/
def degreeMutationWord (row : K ↪ I) (B : Matrix I K ℤ) (g : I → G) : List K → I → G
  | [] => g
  | k :: w => degreeMutationWord row (matrixMutation row B k) (degreeMutation row B k g) w

variable (row : K ↪ I) (B : Matrix I K ℤ) (g g₁ g₂ : I → G)

@[simp]
theorem degreeMutationWord_nil : degreeMutationWord row B g [] = g := (rfl)

@[simp]
theorem degreeMutationWord_cons (k : K) (w : List K) :
    degreeMutationWord row B g (k :: w) =
      degreeMutationWord row (matrixMutation row B k) (degreeMutation row B k g) w := (rfl)

theorem degreeMutationWord_singleton (k : K) :
    degreeMutationWord row B g [k] = degreeMutation row B k g := (rfl)

/-- Concatenation applies the left word to both the matrix and the grading, followed by the
right word. -/
@[simp]
theorem degreeMutationWord_append (u v : List K) :
    degreeMutationWord row B g (u ++ v) =
      degreeMutationWord row (matrixMutationWord row B u) (degreeMutationWord row B g u) v := by
  induction u generalizing B g with
  | nil => simp
  | cons k u ih =>
    simpa only [List.cons_append, degreeMutationWord_cons, matrixMutationWord_cons] using
      ih (matrixMutation row B k) (degreeMutation row B k g)

/-- Coordinates outside `Set.range row` are fixed along every mutation word. -/
@[simp]
theorem degreeMutationWord_apply_of_notMem_range {j : I} (hj : j ∉ Set.range row) (w : List K) :
    degreeMutationWord row B g w j = g j := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih =>
    rw [degreeMutationWord_cons, ih, degreeMutation_apply_of_notMem_range row B k g hj]

@[simp]
theorem degreeMutationWord_zero (w : List K) : degreeMutationWord row B (0 : I → G) w = 0 := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih => simp [ih]

theorem degreeMutationWord_add (w : List K) :
    degreeMutationWord row B (g₁ + g₂) w =
      degreeMutationWord row B g₁ w + degreeMutationWord row B g₂ w := by
  induction w generalizing B g₁ g₂ with
  | nil => rfl
  | cons k w ih => rw [degreeMutationWord_cons, degreeMutation_add, ih]; rfl

@[simp]
theorem degreeMutationWord_neg (w : List K) :
    degreeMutationWord row B (-g) w = -degreeMutationWord row B g w := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih => rw [degreeMutationWord_cons, degreeMutation_neg, ih]; rfl

theorem degreeMutationWord_sub (w : List K) :
    degreeMutationWord row B (g₁ - g₂) w =
      degreeMutationWord row B g₁ w - degreeMutationWord row B g₂ w := by
  simp [sub_eq_add_neg, degreeMutationWord_add]

/-- Additive group homomorphisms commute with `degreeMutationWord`. -/
theorem comp_degreeMutationWord (φ : G →+ H) (w : List K) :
    φ ∘ degreeMutationWord row B g w = degreeMutationWord row B (φ ∘ g) w := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih => rw [degreeMutationWord_cons, degreeMutationWord_cons, ← comp_degreeMutation, ih]

/-- Evaluating an additive homomorphism on a word-mutated degree equals mutating the mapped
degrees. -/
theorem map_degreeMutationWord_apply (φ : G →+ H) (w : List K) (j : I) :
    φ (degreeMutationWord row B g w j) = degreeMutationWord row B (φ ∘ g) w j :=
  congrFun (comp_degreeMutationWord row B g φ w) j

/-- Bijective row relabelling and compatible mutable-column mapping commute with
`degreeMutationWord`. -/
theorem degreeMutationWord_submatrix [DecidableEq I'] [DecidableEq K'] [Fintype I']
    {row' : K' ↪ I'} {f : I' → I} {hK : K' → K} (hf : Function.Bijective f)
    (h : ∀ a, f (row' a) = row (hK a)) (w : List K') :
    degreeMutationWord row' (B.submatrix f hK) (g ∘ f) w =
      degreeMutationWord row B g (w.map hK) ∘ f := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih =>
    simp only [List.map_cons, degreeMutationWord_cons]
    rw [matrixMutation_submatrix hf.injective h B k,
      degreeMutation_submatrix row B g hf h k, ih]

section BlockSumWord

variable {I₁ I₂ K₁ K₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq K₁] [DecidableEq K₂] [Fintype I₁] [Fintype I₂]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)
  (h₁ : I₁ → G) (h₂ : I₂ → G)

/-- An interleaved word on a block-diagonal matrix acts independently on each degree family by its
projected subword. -/
theorem degreeMutationWord_fromBlocks (w : List (K₁ ⊕ K₂)) :
    degreeMutationWord (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.elim h₁ h₂) w =
      Sum.elim (degreeMutationWord row₁ B₁ h₁ (w.filterMap Sum.getLeft?))
        (degreeMutationWord row₂ B₂ h₂ (w.filterMap Sum.getRight?)) := by
  induction w generalizing B₁ B₂ h₁ h₂ with
  | nil => rfl
  | cons k w ih =>
    cases k with
    | inl k =>
      simpa only [degreeMutationWord_cons, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, matrixMutation_fromBlocks_inl, degreeMutation_fromBlocks_inl] using
        ih (matrixMutation row₁ B₁ k) B₂ (degreeMutation row₁ B₁ k h₁) h₂
    | inr k =>
      simpa only [degreeMutationWord_cons, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, matrixMutation_fromBlocks_inr, degreeMutation_fromBlocks_inr] using
        ih B₁ (matrixMutation row₂ B₂ k) h₁ (degreeMutation row₂ B₂ k h₂)

/-- A word in the first block mutates the first degree family and fixes the second. -/
@[simp]
theorem degreeMutationWord_fromBlocks_inl (w : List K₁) :
    degreeMutationWord (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.elim h₁ h₂) (w.map Sum.inl) =
      Sum.elim (degreeMutationWord row₁ B₁ h₁ w) h₂ := by
  simpa [Function.comp_def] using
    degreeMutationWord_fromBlocks row₁ row₂ B₁ B₂ h₁ h₂ (w.map Sum.inl)

/-- A word in the second block mutates the second degree family and fixes the first. -/
@[simp]
theorem degreeMutationWord_fromBlocks_inr (w : List K₂) :
    degreeMutationWord (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.elim h₁ h₂) (w.map Sum.inr) =
      Sum.elim h₁ (degreeMutationWord row₂ B₂ h₂ w) := by
  simpa [Function.comp_def] using
    degreeMutationWord_fromBlocks row₁ row₂ B₁ B₂ h₁ h₂ (w.map Sum.inr)

end BlockSumWord

/-- Equal adjacent directions cancel in `degreeMutationWord` whenever the mutable diagonal entry
and total column degree at `k` vanish after the prefix `u`. -/
theorem degreeMutationWord_append_cons_cons_self (u v : List K) (k : K)
    (hkk : matrixMutationWord row B u (row k) k = 0)
    (hcol : ∑ i, matrixMutationWord row B u i k • degreeMutationWord row B g u i = 0) :
    degreeMutationWord row B g (u ++ k :: k :: v) = degreeMutationWord row B g (u ++ v) := by
  rw [degreeMutationWord_append, degreeMutationWord_cons, degreeMutationWord_cons,
    matrixMutation_matrixMutation, degreeMutation_degreeMutation _ _ _ _ hkk hcol,
    ← degreeMutationWord_append]

omit [Fintype I] in
private theorem hdiag_cons {B : Matrix I K ℤ} {k : K} {w : List K}
    (hdiag : ∀ u l v, k :: w = u ++ l :: v → matrixMutationWord row B u (row l) l = 0) :
    ∀ u l v, w = u ++ l :: v → matrixMutationWord row (matrixMutation row B k) u (row l) l = 0 :=
  fun u l v hw ↦ by simpa only [matrixMutationWord_cons] using hdiag (k :: u) l v (by simp [hw])

/-- Divided-column annihilation persists along any word whose prefix matrices have zero diagonal
at each step's mutation direction. -/
theorem sum_matrixMutationWord_ediv_smul_degreeMutationWord_eq_zero {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0)
    (hg : ∀ j, ∑ i, (B i j / r j) • g i = 0) (j : K) :
    ∑ i, (matrixMutationWord row B w i j / r j) • degreeMutationWord row B g w i = 0 := by
  induction w generalizing B g with
  | nil => simpa using hg j
  | cons k w ih =>
    have hkk : B (row k) k = 0 := by simpa using hdiag [] k w rfl
    simp only [matrixMutationWord_cons, degreeMutationWord_cons]
    exact ih (matrixMutation row B k) (degreeMutation row B k g)
      (fun i l ↦ dvd_matrixMutation (hdvd · l) k i) (hdiag_cons row hdiag)
      (sum_matrixMutation_ediv_smul_degreeMutation_eq_zero row B k g hr hdvd hkk hg)

/-- Divided-column annihilation is preserved and reflected along any word whose prefix matrices
have zero diagonal at each step's mutation direction. -/
theorem forall_sum_matrixMutationWord_ediv_smul_degreeMutationWord_eq_zero_iff {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0) :
    (∀ j, ∑ i, (matrixMutationWord row B w i j / r j) • degreeMutationWord row B g w i = 0) ↔
      ∀ j, ∑ i, (B i j / r j) • g i = 0 := by
  induction w generalizing B g with
  | nil => simp
  | cons k w ih =>
    have hkk : B (row k) k = 0 := by simpa using hdiag [] k w rfl
    simp only [matrixMutationWord_cons, degreeMutationWord_cons]
    exact (ih (matrixMutation row B k) (degreeMutation row B k g)
      (fun i l ↦ dvd_matrixMutation (hdvd · l) k i) (hdiag_cons row hdiag)).trans
      (forall_sum_matrixMutation_ediv_smul_degreeMutation_eq_zero_iff row B k g hr hdvd hkk)

/-- Ordinary column annihilation persists along any word whose prefix matrices have zero diagonal
at each step's mutation direction. -/
theorem sum_matrixMutationWord_smul_degreeMutationWord_eq_zero (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0)
    (hg : ∀ j, ∑ i, B i j • g i = 0) (j : K) :
    ∑ i, matrixMutationWord row B w i j • degreeMutationWord row B g w i = 0 := by
  simpa using sum_matrixMutationWord_ediv_smul_degreeMutationWord_eq_zero row B g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) w hdiag (by simpa using hg) j

/-- Ordinary column annihilation is preserved and reflected along any word whose prefix matrices
have zero diagonal at each step's mutation direction. -/
theorem forall_sum_matrixMutationWord_smul_degreeMutationWord_eq_zero_iff (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0) :
    (∀ j, ∑ i, matrixMutationWord row B w i j • degreeMutationWord row B g w i = 0) ↔
      ∀ j, ∑ i, B i j • g i = 0 := by
  simpa using forall_sum_matrixMutationWord_ediv_smul_degreeMutationWord_eq_zero_iff row B g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) w hdiag

/-- Reversing a mutation word undoes its action on any column-annihilating grading when each
step's mutable diagonal entry vanishes. -/
theorem degreeMutationWord_degreeMutationWord_reverse (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0)
    (hg : ∀ j, ∑ i, B i j • g i = 0) :
    degreeMutationWord row (matrixMutationWord row B w) (degreeMutationWord row B g w)
      w.reverse = g := by
  induction w generalizing B g with
  | nil => simp
  | cons k w ih =>
    have hkk : B (row k) k = 0 := by simpa using hdiag [] k w rfl
    rw [List.reverse_cons, degreeMutationWord_append]
    simp only [matrixMutationWord_cons, degreeMutationWord_cons]
    rw [ih _ _ (hdiag_cons row hdiag)
        (sum_matrixMutation_smul_degreeMutation_eq_zero row B k g hkk hg),
      matrixMutationWord_matrixMutationWord_reverse, degreeMutationWord_nil,
      degreeMutation_degreeMutation row B k g hkk (hg k)]

end Word

namespace ExchangeMatrix

variable {I K G : Type*} [DecidableEq I] [DecidableEq K] [Fintype I]
  [AddCommGroup G] {row : K ↪ I} (B : ExchangeMatrix row)

omit [Fintype I] in
private theorem matrixMutationWord_row_self (w : List K) :
    ∀ u k v, w = u ++ k :: v → matrixMutationWord row B.matrix u (row k) k = 0 := by
  intro u k _ _
  rw [← B.mutationWord_matrix]
  exact (B.mutationWord u).matrix_row_self k

/-- Every mutation word on a bundled exchange matrix preserves divided-column annihilation of
positive exchange degrees. -/
theorem sum_mutationWord_ediv_smul_degreeMutationWord_eq_zero {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B.matrix i j) {g : I → G}
    (hg : ∀ j, ∑ i, (B.matrix i j / r j) • g i = 0) (w : List K) (j : K) :
    ∑ i, ((B.mutationWord w).matrix i j / r j) • degreeMutationWord row B.matrix g w i = 0 := by
  rw [B.mutationWord_matrix]
  exact sum_matrixMutationWord_ediv_smul_degreeMutationWord_eq_zero row B.matrix g hr hdvd w
    (B.matrixMutationWord_row_self w) hg j

/-- Every mutation word on a bundled exchange matrix preserves and reflects divided-column
annihilation of positive exchange degrees. -/
theorem forall_sum_mutationWord_ediv_smul_degreeMutationWord_eq_zero_iff {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B.matrix i j) (g : I → G) (w : List K) :
    (∀ j, ∑ i, ((B.mutationWord w).matrix i j / r j) • degreeMutationWord row B.matrix g w i = 0) ↔
      ∀ j, ∑ i, (B.matrix i j / r j) • g i = 0 := by
  simp_rw [B.mutationWord_matrix]
  exact forall_sum_matrixMutationWord_ediv_smul_degreeMutationWord_eq_zero_iff row B.matrix g
    hr hdvd w (B.matrixMutationWord_row_self w)

/-- Every mutation word on a bundled exchange matrix preserves ordinary column annihilation. -/
theorem sum_mutationWord_smul_degreeMutationWord_eq_zero {g : I → G}
    (hg : ∀ j, ∑ i, B.matrix i j • g i = 0) (w : List K) (j : K) :
    ∑ i, (B.mutationWord w).matrix i j • degreeMutationWord row B.matrix g w i = 0 := by
  rw [B.mutationWord_matrix]
  exact sum_matrixMutationWord_smul_degreeMutationWord_eq_zero row B.matrix g w
    (B.matrixMutationWord_row_self w) hg j

/-- Every mutation word on a bundled exchange matrix preserves and reflects ordinary column
annihilation. -/
theorem forall_sum_mutationWord_smul_degreeMutationWord_eq_zero_iff (g : I → G) (w : List K) :
    (∀ j, ∑ i, (B.mutationWord w).matrix i j • degreeMutationWord row B.matrix g w i = 0) ↔
      ∀ j, ∑ i, B.matrix i j • g i = 0 := by
  simp_rw [B.mutationWord_matrix]
  exact forall_sum_matrixMutationWord_smul_degreeMutationWord_eq_zero_iff row B.matrix g w
    (B.matrixMutationWord_row_self w)

/-- Equal adjacent directions cancel in `degreeMutationWord` on a bundled exchange matrix for any
initial column-annihilating grading. -/
theorem degreeMutationWord_append_cons_cons_self {g : I → G}
    (hg : ∀ j, ∑ i, B.matrix i j • g i = 0) (u v : List K) (k : K) :
    degreeMutationWord row B.matrix g (u ++ k :: k :: v) =
      degreeMutationWord row B.matrix g (u ++ v) := by
  refine TauCeti.degreeMutationWord_append_cons_cons_self row B.matrix g u v k
    (B.matrixMutationWord_row_self (u ++ [k]) u k [] rfl) ?_
  rw [← B.mutationWord_matrix]
  exact B.sum_mutationWord_smul_degreeMutationWord_eq_zero hg u k

/-- Reversing a word on a bundled exchange matrix inverts its action on any column-annihilating
grading. -/
theorem degreeMutationWord_degreeMutationWord_reverse {g : I → G}
    (hg : ∀ j, ∑ i, B.matrix i j • g i = 0) (w : List K) :
    degreeMutationWord row (B.mutationWord w).matrix
        (degreeMutationWord row B.matrix g w) w.reverse = g := by
  rw [B.mutationWord_matrix]
  exact TauCeti.degreeMutationWord_degreeMutationWord_reverse row B.matrix g w
    (B.matrixMutationWord_row_self w) hg

end ExchangeMatrix

/-- For unequal column degrees `(3, 2)` on an extended `3 × 2` matrix, divided-column annihilation
holds initially for `g = ![0, 1, 1]` and persists after mutating in direction `0`, where `g`
updates to `![3, 1, 1]`. -/
example : degreeMutation (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0
    (![0, 1, 1] : Fin 3 → ℤ) = ![3, 1, 1] := by decide

example : ∀ j : Fin 2, ∑ i : Fin 3,
    (matrixMutation (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0 i j /
      (![3, 2] : Fin 2 → ℤ) j) •
      degreeMutation (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0
        (![0, 1, 1] : Fin 3 → ℤ) i = 0 :=
  sum_matrixMutation_ediv_smul_degreeMutation_eq_zero
    (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0 ![0, 1, 1]
    (by decide) (fun a b ↦ by fin_cases a <;> fin_cases b <;> decide) (by decide) (by decide)

end TauCeti
