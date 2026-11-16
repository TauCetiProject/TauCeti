/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.GroupTheory.Coxeter.Parabolic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
import TauCeti.GroupTheory.Coxeter.Dihedral

/-!
# Coxeter matrix and reflection representation of a generalized Cartan matrix

Let `A` be a generalized Cartan matrix (`Matrix.IsGeneralizedCartan`): an integer matrix with `2`
on the diagonal, nonpositive off-diagonal entries, and symmetric zero pattern (`A i j = 0` iff
`A j i = 0`). Neither finiteness of the index set, invertibility, nor symmetrizability is assumed.

From any integer matrix `A` we read off its **Cartan Coxeter matrix**
`Matrix.cartanCoxeterMatrix`: on the diagonal its entries are `1`; off the diagonal, when the
Cartan product `c = A i j * A j i` lies in `{0, 1, 2, 3}`, its entry is the dihedral order
`2, 3, 4, 6` (`TauCeti.coxeterOrder`), and when `c ≥ 4` (including the affine value `c = 4`, where
`TauCeti.coxeterOrder 4 = 1` would collapse two independent simple reflections) it is `0`, Mathlib's
encoding of an infinite order. Defining `Matrix.cartanCoxeterMatrix` totally on all integer matrices
keeps its carrier and Coxeter group free of proof parameters.

Given vectors `x : I → X` and linear forms `f : I → Module.Dual R X` over a commutative ring `R`
pairing by `f i (x j) = A i j` for a generalized Cartan matrix `A`, the reflections
`Module.reflection` satisfy all braid relations of `A.cartanCoxeterMatrix`
(`Matrix.IsGeneralizedCartan.isLiftable_reflection`).

Specializing to the finitely-supported free `ℤ`-module `I →₀ ℤ` — which, unlike
`Matrix.columnReflection` on `κ → ℤ`, requires neither `[Fintype I]` nor `[DecidableEq I]` and
follows Kac's convention `A i j = αⱼ(hᵢ)` — gives the integral root-lattice representation
`CoxeterSystem.cartanRepresentation` (and, via `Aᵀ`, the integral coroot-lattice representation
`CoxeterSystem.dualCartanRepresentation`) of any Coxeter system of type `A.cartanCoxeterMatrix`:

* **Kac's Lemma 3.11** (`CoxeterSystem.cartanRepresentation_single_pos_iff` and
  `CoxeterSystem.cartanRepresentation_single_neg_iff`): the image of the `i`-th basis root under
  `w` is positive iff `i` is not a right descent of `w`, and negative iff `i` is a right descent.
* **Kac's Proposition 3.13** (`CoxeterSystem.cartanRepresentation_injective` and
  `CoxeterSystem.dualCartanRepresentation_injective`): both integral lattice representations are
  faithful, supplying the Coxeter presentation for the Weyl group of any Cartan realization over a
  characteristic-zero field.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1, Lemma 3.11, and
  Proposition 3.13.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), §5.4.
-/

public section

open Function Polynomial.Chebyshev Set
open scoped Matrix

/-! ### Generalized Cartan matrices -/

/-- The proposition that an integer matrix is a **generalized Cartan matrix**: its diagonal entries
are `2`, its off-diagonal entries are nonpositive, and its zero pattern is symmetric. Neither
finiteness of the index type nor symmetrizability is required. -/
structure Matrix.IsGeneralizedCartan {I : Type*} (A : Matrix I I ℤ) : Prop where
  /-- Every diagonal entry equals `2`. -/
  diag : ∀ i, A i i = 2
  /-- Off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- Off-diagonal zeros are symmetric. -/
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

namespace Matrix.IsGeneralizedCartan

variable {I : Type*} {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan)
include hA

/-- Every Cartan product `A i j * A j i` of a generalized Cartan matrix is nonnegative. -/
theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- The Cartan product `A i j * A j i` vanishes iff both `A i j` and `A j i` vanish. -/
theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 ∧ A j i = 0 := by
  rw [mul_eq_zero]
  exact ⟨fun h ↦ h.elim (fun h₁ ↦ ⟨h₁, (hA.zero_comm i j).mp h₁⟩)
    (fun h₂ ↦ ⟨(hA.zero_comm i j).mpr h₂, h₂⟩), fun h ↦ Or.inl h.1⟩

/-- The diagonal entries of the cast of `A` to any ring with `1` equal `2`. -/
theorem diag_map (R : Type*) [AddGroupWithOne R] (i : I) :
    A.map (Int.cast : ℤ → R) i i = 2 := by
  simp [hA.diag]

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose : Aᵀ.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

omit hA in
@[simp]
protected theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ h.transpose, IsGeneralizedCartan.transpose⟩

/-- Any principal submatrix of a generalized Cartan matrix along an embedding is a generalized
Cartan matrix. -/
protected theorem submatrix {J : Type*} (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

/-- Reindexing a generalized Cartan matrix gives a generalized Cartan matrix. -/
protected theorem reindex {J : Type*} (e : I ≃ J) : (A.reindex e e).IsGeneralizedCartan :=
  hA.submatrix e.symm.toEmbedding

end Matrix.IsGeneralizedCartan

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem Matrix.IsFiniteCartan.isGeneralizedCartan {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan :=
  ⟨hA.diag, hA.offDiag_nonpos, hA.zero_comm⟩

namespace CartanMatrix

theorem isGeneralizedCartan_A (n : ℕ) : (CartanMatrix.A n).IsGeneralizedCartan where
  diag i := by simpa using congrFun (A_diag n) i
  offDiag_nonpos := A_apply_le_zero_of_ne n
  zero_comm i j := by
    have h : CartanMatrix.A n j i = CartanMatrix.A n i j := by
      simpa [Matrix.transpose_apply] using congrArg (fun M ↦ M i j) (A_transpose n)
    rw [h]

theorem isGeneralizedCartan_B (n : ℕ) : (CartanMatrix.B n).IsGeneralizedCartan where
  diag := B_diag n
  offDiag_nonpos := B_off_diag_nonpos n
  zero_comm i j := by
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> simp_all

theorem isGeneralizedCartan_C (n : ℕ) : (CartanMatrix.C n).IsGeneralizedCartan := by
  rw [← B_transpose]
  exact (isGeneralizedCartan_B n).transpose

end CartanMatrix

/-! ### The Coxeter matrix of an integer Cartan matrix -/

namespace Matrix

/-- **The Coxeter matrix read off an integer matrix `A`**, in the generalized Cartan convention:
`1` on the diagonal; off the diagonal, `2, 3, 4, 6` (`TauCeti.coxeterOrder`) when the Cartan
product `A i j * A j i` lies in `{0, 1, 2, 3}`, and `0` (`∞`) otherwise.

Unlike `TauCeti.coxeterMatrixOfCartanMatrix`, off-diagonal pairs with `A i j * A j i = 4` (such as
affine `A₁⁽¹⁾` or `A₂⁽²⁾`) receive the infinite-order entry `0` rather than `1`, and no hypotheses
on `A` are baked into the definition. -/
noncomputable def cartanCoxeterMatrix {I : Type*} (A : Matrix I I ℤ) : CoxeterMatrix I :=
  open scoped Classical in
  { M := .of fun i j ↦
      if i = j then 1
      else if 0 ≤ A i j * A j i ∧ A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i)
      else 0
    isSymm := by
      ext i j
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [hij, hij.symm, mul_comm (A j i) (A i j)]
    diagonal i := by simp
    off_diagonal i j hij := by
      simp only [of_apply, hij, ↓reduceIte]
      split_ifs with h
      · have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
          simp only [mem_insert_iff, mem_singleton_iff]
          omega
        have := TauCeti.two_le_coxeterOrder hmem
        omega
      · decide }

section CartanCoxeterMatrix

variable {I : Type*} (A : Matrix I I ℤ)

/-- Entry formula for `Matrix.cartanCoxeterMatrix`. -/
theorem cartanCoxeterMatrix_apply [DecidableEq I] (i j : I) :
    A.cartanCoxeterMatrix i j =
      if i = j then 1
      else if 0 ≤ A i j * A j i ∧ A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [cartanCoxeterMatrix]
  · simp [cartanCoxeterMatrix, hij]

theorem cartanCoxeterMatrix_diag (i : I) : A.cartanCoxeterMatrix i i = 1 :=
  A.cartanCoxeterMatrix.diagonal i

/-- Off-diagonal entry formula for `Matrix.cartanCoxeterMatrix`, requiring no `DecidableEq`
instance on `I`. -/
theorem cartanCoxeterMatrix_apply_of_ne {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j =
      if 0 ≤ A i j * A j i ∧ A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i)
      else 0 := by
  classical
  simp [cartanCoxeterMatrix_apply, hij]

/-- Off the diagonal, for a generalized Cartan matrix, `A.cartanCoxeterMatrix i j` is
`TauCeti.coxeterOrder (A i j * A j i)` when `A i j * A j i ≤ 3`, and `0` otherwise. -/
theorem IsGeneralizedCartan.cartanCoxeterMatrix_apply_of_ne {A : Matrix I I ℤ}
    (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j =
      if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0 := by
  simp [A.cartanCoxeterMatrix_apply_of_ne hij, hA.mul_nonneg i j]

@[simp]
theorem cartanCoxeterMatrix_transpose : Aᵀ.cartanCoxeterMatrix = A.cartanCoxeterMatrix := by
  classical
  ext i j
  simp only [cartanCoxeterMatrix_apply, transpose_apply, mul_comm (A j i) (A i j)]

theorem cartanCoxeterMatrix_eq_two_of_mul_eq_zero {i j : I} (hij : i ≠ j)
    (h : A i j * A j i = 0) : A.cartanCoxeterMatrix i j = 2 := by
  simp [A.cartanCoxeterMatrix_apply_of_ne hij, h]

theorem cartanCoxeterMatrix_eq_three_of_mul_eq_one {i j : I} (hij : i ≠ j)
    (h : A i j * A j i = 1) : A.cartanCoxeterMatrix i j = 3 := by
  simp [A.cartanCoxeterMatrix_apply_of_ne hij, h]

theorem cartanCoxeterMatrix_eq_four_of_mul_eq_two {i j : I} (hij : i ≠ j)
    (h : A i j * A j i = 2) : A.cartanCoxeterMatrix i j = 4 := by
  simp [A.cartanCoxeterMatrix_apply_of_ne hij, h]

theorem cartanCoxeterMatrix_eq_six_of_mul_eq_three {i j : I} (hij : i ≠ j)
    (h : A i j * A j i = 3) : A.cartanCoxeterMatrix i j = 6 := by
  simp [A.cartanCoxeterMatrix_apply_of_ne hij, h]

theorem cartanCoxeterMatrix_eq_zero_of_four_le_mul {i j : I} (hij : i ≠ j)
    (h : 4 ≤ A i j * A j i) : A.cartanCoxeterMatrix i j = 0 := by
  have hnot : ¬(0 ≤ A i j * A j i ∧ A i j * A j i ≤ 3) := by omega
  simp [A.cartanCoxeterMatrix_apply_of_ne hij, hnot]

/-- When every off-diagonal Cartan product lies in `{0, 1, 2, 3}`, `Matrix.cartanCoxeterMatrix`
agrees with `TauCeti.coxeterMatrixOfCartanMatrix`. -/
theorem cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    A.cartanCoxeterMatrix = TauCeti.coxeterMatrixOfCartanMatrix A hdiag hmem := by
  classical
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hm := hmem i j hij
    have hbounds : 0 ≤ A i j * A j i ∧ A i j * A j i ≤ 3 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hm
      omega
    simp [cartanCoxeterMatrix_apply, hij, hbounds, TauCeti.coxeterMatrixOfCartanMatrix_apply]

end CartanCoxeterMatrix

end Matrix

namespace CartanMatrix

/-- The `2 × 2` generalized Cartan matrix `!![2, -2; -2, 2]` of untwisted affine type `A₁⁽¹⁾`. -/
abbrev affineA₁ : Matrix (Fin 2) (Fin 2) ℤ := !![2, -2; -2, 2]

/-- `CartanMatrix.affineA₁` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_affineA₁ : affineA₁.IsGeneralizedCartan where
  diag i := by fin_cases i <;> decide
  offDiag_nonpos i j hij := by fin_cases i <;> fin_cases j <;> simp_all [affineA₁]
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

/-- The off-diagonal Coxeter entry of `CartanMatrix.B 2` is `4`. -/
theorem cartanCoxeterMatrix_B_two : (CartanMatrix.B 2).cartanCoxeterMatrix 0 1 = 4 := by
  apply Matrix.cartanCoxeterMatrix_eq_four_of_mul_eq_two _ (by decide)
  rw [CartanMatrix.B_two]
  decide

/-- The off-diagonal Coxeter entry of `CartanMatrix.affineA₁` is `0` (`∞`). -/
theorem cartanCoxeterMatrix_affineA₁ : affineA₁.cartanCoxeterMatrix 0 1 = 0 :=
  Matrix.cartanCoxeterMatrix_eq_zero_of_four_le_mul _ (by decide) (by decide)

end CartanMatrix

namespace Matrix

/-! ### Braid relations for linear reflections -/

namespace IsGeneralizedCartan

/-- **Braid relations for reflections realizing a generalized Cartan matrix.** Let `X` be any
module over a commutative ring `R`, with vectors `x : I → X` and linear forms `f : I → Dual R X`
satisfying `f i (x j) = A i j`. Then the reflections `Module.reflection` satisfy
`(s_i * s_j) ^ (A.cartanCoxeterMatrix i j) = 1`. -/
theorem isLiftable_reflection {I R X : Type*} [CommRing R] [AddCommGroup X]
    [Module R X] {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan) {x : I → X}
    {f : I → Module.Dual R X} (hpair : ∀ i j, f i (x j) = A i j)
    {hf : ∀ i, f i (x i) = 2} :
    A.cartanCoxeterMatrix.IsLiftable (fun i ↦ Module.reflection (hf i)) := by
  classical
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · rw [cartanCoxeterMatrix_diag, pow_one]
    ext z
    exact Module.involutive_reflection (hf i) z
  · rw [hA.cartanCoxeterMatrix_apply_of_ne hij]
    split_ifs with hle
    · have hnonneg := hA.mul_nonneg i j
      have hcases : A i j * A j i = 0 ∨ A i j * A j i = 1 ∨
          A i j * A j i = 2 ∨ A i j * A j i = 3 := by omega
      have ht (c : ℤ) (hc : A i j * A j i = c) :
          ((c - 2 : ℤ) : R) = f i (x j) * f j (x i) - 2 := by
        rw [hpair, hpair, ← Int.cast_mul, hc]
        push_cast
        ring
      rcases hcases with hc | hc | hc | hc
      · obtain ⟨hij0, hji0⟩ := (hA.mul_eq_zero_iff i j).mp hc
        rw [hc, TauCeti.coxeterOrder_zero, sq]
        ext z
        simp only [mul_apply_eq_comp, one_apply_eq_self, Module.reflection_apply, map_sub,
          map_smul, hf, hpair, hij0, hji0, Int.cast_zero, zero_smul, sub_zero]
        module
      · rw [hc, TauCeti.coxeterOrder_one]
        ext z
        rw [Module.reflection_mul_reflection_pow_apply (hf i) (hf j) 3 z (-1 : R)
          (by simpa using ht 1 hc)]
        norm_num [S_zero, S_one]
      · rw [hc, TauCeti.coxeterOrder_two]
        ext z
        rw [Module.reflection_mul_reflection_pow_apply (hf i) (hf j) 4 z (0 : R)
          (by simpa using ht 2 hc)]
        norm_num [S_zero, S_one]
      · rw [hc, TauCeti.coxeterOrder_three]
        ext z
        rw [Module.reflection_mul_reflection_pow_apply (hf i) (hf j) 6 z (1 : R)
          (by simpa using ht 3 hc)]
        norm_num [S_two]
    · exact pow_zero _

end IsGeneralizedCartan

/-! ### Reflections on the free root lattice `I →₀ ℤ` -/

/-- The `i`-th simple reflection on the free root lattice `I →₀ ℤ` associated to an integer matrix
`A` with diagonal `2`: it sends `z` to `z - (∑ j, z j * A i j) • single i 1`, so the `j`-th basis
vector maps to `single j 1 - A i j • single i 1`. -/
noncomputable def cartanRootReflection {I : Type*} (A : Matrix I I ℤ) (hdiag : ∀ i, A i i = 2)
    (i : I) : (I →₀ ℤ) ≃ₗ[ℤ] (I →₀ ℤ) :=
  Module.reflection (x := Finsupp.single i (1 : ℤ)) (f := Finsupp.linearCombination ℤ (A i))
    (by simp [hdiag i])

/-- Explicit formula for `Matrix.cartanRootReflection`. -/
theorem cartanRootReflection_apply {I : Type*} (A : Matrix I I ℤ) (hdiag : ∀ i, A i i = 2)
    (i : I) (z : I →₀ ℤ) :
    A.cartanRootReflection hdiag i z =
      z - (Finsupp.linearCombination ℤ (A i) z) • Finsupp.single i 1 :=
  Module.reflection_apply z _

@[simp]
theorem cartanRootReflection_single {I : Type*} (A : Matrix I I ℤ) (hdiag : ∀ i, A i i = 2)
    (i j : I) :
    A.cartanRootReflection hdiag i (Finsupp.single j 1) =
      Finsupp.single j 1 - A i j • Finsupp.single i 1 := by
  simp [cartanRootReflection_apply]

theorem cartanRootReflection_single_self {I : Type*} (A : Matrix I I ℤ) (hdiag : ∀ i, A i i = 2)
    (i : I) :
    A.cartanRootReflection hdiag i (Finsupp.single i 1) = -Finsupp.single i 1 :=
  Module.reflection_apply_self _

end Matrix

/-! ### The integral root-lattice representation of `CoxeterSystem A.cartanCoxeterMatrix W` -/

namespace CoxeterSystem

section ChebyshevHelpers

/-- For `t ≥ 2`, the Chebyshev `S`-polynomials at `t` satisfy `S_{n-1}(t) < S_n(t)` and
`1 ≤ S_n(t)` for every `n : ℕ`. -/
private theorem chebyshev_S_pos_and_strictMono {t : ℤ} (ht : 2 ≤ t) :
    ∀ n : ℕ, (S ℤ ((n : ℤ) - 1)).eval t < (S ℤ n).eval t ∧ 1 ≤ (S ℤ n).eval t := by
  intro n
  induction n with
  | zero => simp [S_zero]
  | succ n ih =>
    obtain ⟨hlt, hpos⟩ := ih
    have hrec : (S ℤ ((n : ℤ) + 1)).eval t =
        t * (S ℤ n).eval t - (S ℤ ((n : ℤ) - 1)).eval t := by
      have h := congrArg (Polynomial.eval t) (S_add_two ℤ ((n : ℤ) - 1))
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
      ring_nf at h ⊢
      exact h
    have hstep : (S ℤ n).eval t < (S ℤ ((n : ℤ) + 1)).eval t := by
      rw [hrec]
      nlinarith
    push_cast
    exact ⟨by simpa using hstep, by omega⟩

private theorem chebyshev_S_sub_one_nonneg {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    0 ≤ (S ℤ ((n : ℤ) - 1)).eval t := by
  rcases n with _ | n
  · simp
  · have := (chebyshev_S_pos_and_strictMono ht n).2
    push_cast
    simpa using le_trans zero_le_one this

/-- Nonnegativity of the two Chebyshev factors appearing in a rank-two alternating product of
length `m` below the dihedral order (`m < coxeterOrder c` when `0 ≤ c ≤ 3`, arbitrary `m` when
`4 ≤ c`). -/
private theorem chebyshev_rankTwo_nonneg_pair {c : ℤ} (hc0 : 0 ≤ c) (m : ℕ)
    (hm : c ≤ 3 → m < TauCeti.coxeterOrder c) :
    0 ≤ (S ℤ (m / 2 : ℕ)).eval (c - 2) + (S ℤ ((m / 2 : ℕ) - 1 : ℤ)).eval (c - 2) ∧
      0 ≤ (if Even m then (S ℤ ((m / 2 : ℕ) - 1 : ℤ)).eval (c - 2)
        else (S ℤ (m / 2 : ℕ)).eval (c - 2)) := by
  classical
  set k : ℕ := m / 2
  set t : ℤ := c - 2
  rcases le_or_gt 4 c with hc4 | hc4
  · have ht2 : 2 ≤ t := by omega
    have hk1 := (chebyshev_S_pos_and_strictMono ht2 k).2
    have hk0 := chebyshev_S_sub_one_nonneg ht2 k
    refine ⟨by omega, ?_⟩
    split_ifs
    · exact hk0
    · exact le_trans zero_le_one hk1
  · have hmlt : m < TauCeti.coxeterOrder c := hm (by omega)
    have hcases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases hcases with hc | hc | hc | hc
    · rw [hc, TauCeti.coxeterOrder_zero] at hmlt
      have hk0 : k = 0 := by omega
      exact ⟨by simp [hk0], by split_ifs <;> norm_num [hk0, S_zero]⟩
    · rw [hc, TauCeti.coxeterOrder_one] at hmlt
      have hm012 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm012 with rfl | rfl | rfl <;> norm_num [k, t, hc, S_zero, S_one]
    · rw [hc, TauCeti.coxeterOrder_two] at hmlt
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with hk | hk <;>
        exact ⟨by norm_num [hk, t, hc, S_zero, S_one],
          by split_ifs <;> norm_num [hk, t, hc, S_zero, S_one]⟩
    · rw [hc, TauCeti.coxeterOrder_three] at hmlt
      have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk012 with hk | hk | hk <;>
        exact ⟨by norm_num [hk, t, hc, S_zero, S_one, S_two],
          by split_ifs <;> norm_num [hk, t, hc, S_zero, S_one, S_two]⟩

end ChebyshevHelpers

variable {I W : Type*} [Group W] {A : Matrix I I ℤ}
  (cs : CoxeterSystem A.cartanCoxeterMatrix W) (hA : A.IsGeneralizedCartan)

/-- **The integral root-lattice representation** of a Coxeter system of type
`A.cartanCoxeterMatrix`, acting on `I →₀ ℤ` by `s_i(e_j) = e_j - A i j • e_i`. -/
noncomputable def cartanRepresentation : W →* ((I →₀ ℤ) ≃ₗ[ℤ] (I →₀ ℤ)) :=
  cs.lift ⟨A.cartanRootReflection hA.diag,
    hA.isLiftable_reflection (x := fun i ↦ Finsupp.single i (1 : ℤ))
      (f := fun i ↦ Finsupp.linearCombination ℤ (A i)) (fun i j ↦ by simp)⟩

@[simp]
theorem cartanRepresentation_simple (i : I) :
    cs.cartanRepresentation hA (cs.simple i) = A.cartanRootReflection hA.diag i :=
  cs.lift_apply_simple _ i

theorem cartanRepresentation_simple_single (i j : I) :
    cs.cartanRepresentation hA (cs.simple i) (Finsupp.single j 1) =
      Finsupp.single j 1 - A i j • Finsupp.single i 1 := by
  simp

/-- Right-multiplying `w` by `s_i` negates the `w`-image of `single i 1`. -/
theorem cartanRepresentation_mul_simple_single (w : W) (i : I) :
    cs.cartanRepresentation hA (w * cs.simple i) (Finsupp.single i 1) =
      -cs.cartanRepresentation hA w (Finsupp.single i 1) := by
  rw [map_mul, mul_apply_eq_comp, cartanRepresentation_simple,
    A.cartanRootReflection_single_self, map_neg]

/-- **Rank-two nonnegativity on the root lattice.** For an alternating word of length `m` strictly
below the braid length `A.cartanCoxeterMatrix i j` (or of arbitrary length when
`A.cartanCoxeterMatrix i j = 0`), the image of `single i 1` is a nonnegative integer combination of
`single i 1` and `single j 1`. -/
private theorem rankTwo_cartanRepresentation_nonneg (i j : I) {m : ℕ}
    (hm : m < A.cartanCoxeterMatrix i j ∨ A.cartanCoxeterMatrix i j = 0) :
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧
      cs.cartanRepresentation hA (cs.wordProd (alternatingWord i j m)) (Finsupp.single i 1) =
        a • Finsupp.single i 1 + b • Finsupp.single j 1 := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · have hm0 : m = 0 := by simp at hm; omega
    exact ⟨1, 0, zero_le_one, le_rfl, by simp [hm0, alternatingWord]⟩
  set k : ℕ := m / 2
  set c : ℤ := A i j * A j i
  set t : ℤ := c - 2
  have hq : 0 ≤ -A j i := neg_nonneg.mpr (hA.offDiag_nonpos j i hij.symm)
  have hf (r : I) : Finsupp.linearCombination ℤ (A r) (Finsupp.single r 1) = 2 := by
    simp [hA.diag r]
  have ht : t = Finsupp.linearCombination ℤ (A i) (Finsupp.single j 1) *
      Finsupp.linearCombination ℤ (A j) (Finsupp.single i 1) - 2 := by simp [t, c]
  have hword :
      cs.cartanRepresentation hA (cs.wordProd (alternatingWord i j m)) (Finsupp.single i 1) =
        ((S ℤ k).eval t + (S ℤ ((k : ℤ) - 1)).eval t) • Finsupp.single i 1 +
          ((if Even m then (S ℤ ((k : ℤ) - 1)).eval t else (S ℤ k).eval t) * -A j i) •
            Finsupp.single j 1 := by
    rw [cs.prod_alternatingWord_eq_mul_pow]
    by_cases he : Even m
    · simp only [he, ↓reduceIte, one_mul, map_pow, map_mul, cartanRepresentation_simple]
      simpa [Matrix.cartanRootReflection, k] using
        Module.reflection_mul_reflection_pow_apply_self (hf i) (hf j) k t ht
    · simp only [he, ↓reduceIte, map_mul, map_pow, cartanRepresentation_simple]
      simpa [Matrix.cartanRootReflection, k] using
        Module.reflection_mul_reflection_mul_reflection_pow_apply_self (hf i) (hf j) k t ht
  obtain ⟨ha, hb⟩ := chebyshev_rankTwo_nonneg_pair (hA.mul_nonneg i j) m fun hle3 ↦ by
    have hM : A.cartanCoxeterMatrix i j = TauCeti.coxeterOrder c := by
      simp [hA.cartanCoxeterMatrix_apply_of_ne hij, hle3, c]
    have hMpos : A.cartanCoxeterMatrix i j ≠ 0 := by
      rw [hM]
      have hmem : c ∈ ({0, 1, 2, 3} : Set ℤ) := by
        have := hA.mul_nonneg i j
        simp only [mem_insert_iff, mem_singleton_iff]
        omega
      have := TauCeti.two_le_coxeterOrder hmem
      omega
    exact hM ▸ hm.resolve_right hMpos
  exact ⟨_, _, ha, mul_nonneg hb hq, hword⟩

/-- An element `v` of the rank-two parabolic subgroup on `{i, j}` without right descent at `i`
sends `single i 1` to a nonnegative integer combination of `single i 1` and `single j 1`. -/
theorem exists_nonneg_cartanRepresentation_of_mem_parabolic_pair {i j : I} {v : W}
    (hv : v ∈ cs.parabolic {i, j}) (hvi : ¬cs.IsRightDescent v i) :
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧
      cs.cartanRepresentation hA v (Finsupp.single i 1) =
        a • Finsupp.single i 1 + b • Finsupp.single j 1 := by
  have hlen := cs.not_isRightDescent_iff.mp hvi
  have hword : cs.wordProd (alternatingWord i j (cs.length v)) = v := by
    refine (cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair hv).elim id fun h ↦ ?_
    rcases hk : cs.length v with _ | k
    · simp [cs.length_eq_zero_iff.mp hk, alternatingWord]
    · rw [hk, alternatingWord_succ, wordProd_concat] at h
      have hle := cs.length_wordProd_le (alternatingWord i j k)
      rw [length_alternatingWord] at hle
      rw [← h, cs.simple_mul_simple_cancel_right, h] at hlen
      omega
  have hred : cs.IsReduced (alternatingWord j i (cs.length v + 1)) := by
    rw [IsReduced, alternatingWord_succ, wordProd_concat, hword, hlen, List.concat_eq_append,
      List.length_append, length_alternatingWord, List.length_singleton]
  have hk : cs.length v < A.cartanCoxeterMatrix i j ∨ A.cartanCoxeterMatrix i j = 0 := by
    by_contra hcon
    rw [not_or, not_lt, ← A.cartanCoxeterMatrix.symmetric j i] at hcon
    exact cs.not_isReduced_alternatingWord j i hcon.2 (by omega) hred
  rw [← hword]
  exact cs.rankTwo_cartanRepresentation_nonneg hA i j hk

private theorem cartanRepresentation_single_nonneg {w : W} {i : I}
    (h : ¬cs.IsRightDescent w i) : 0 ≤ cs.cartanRepresentation hA w (Finsupp.single i 1) := by
  classical
  induction hn : cs.length w using Nat.strong_induction_on generalizing w i with
  | _ n ih =>
    rcases eq_or_ne w 1 with rfl | hw
    · simp
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul {i, j} w
    dsimp only at hu hv huv
    subst huv
    have hu' := cs.isMinimalCosetRep_iff.mp hu
    have hlen := cs.length_mul_of_isMinimalCosetRep hu hv
    have hv₁ : v ≠ 1 := by
      rintro rfl
      exact hu' j (by simp) (by simpa using hj)
    have hvpos : 0 < cs.length v := Nat.pos_of_ne_zero (mt cs.length_eq_zero_iff.mp hv₁)
    have hvi : ¬cs.IsRightDescent v i := fun hd ↦ h <| by
      rw [IsRightDescent] at hd ⊢
      rw [mul_assoc, cs.length_mul_of_isMinimalCosetRep hu
        (mul_mem hv (cs.simple_mem_parabolic (by simp))), hlen]
      omega
    obtain ⟨a, b, ha, hb, hab⟩ :=
      cs.exists_nonneg_cartanRepresentation_of_mem_parabolic_pair hA hv hvi
    rw [map_mul, mul_apply_eq_comp, hab, map_add, map_smul, map_smul]
    exact add_nonneg (smul_nonneg ha (ih _ (by omega) (hu' i (by simp)) rfl))
      (smul_nonneg hb (ih _ (by omega) (hu' j (by simp)) rfl))

private theorem cartanRepresentation_single_pos {w : W} {i : I}
    (h : ¬cs.IsRightDescent w i) : 0 < cs.cartanRepresentation hA w (Finsupp.single i 1) :=
  lt_of_le_of_ne (cs.cartanRepresentation_single_nonneg hA h)
    ((map_ne_zero_iff _ (cs.cartanRepresentation hA w).injective).mpr
      (Finsupp.single_ne_zero.mpr one_ne_zero)).symm

private theorem cartanRepresentation_single_neg {w : W} {i : I}
    (h : cs.IsRightDescent w i) : cs.cartanRepresentation hA w (Finsupp.single i 1) < 0 := by
  have hpos := cs.cartanRepresentation_single_pos hA
    (cs.isRightDescent_iff_not_isRightDescent_mul.mp h)
  rwa [cs.cartanRepresentation_mul_simple_single, neg_pos] at hpos

/-- **Kac's Lemma 3.11, positive case.** In the root-lattice representation of a generalized Cartan
matrix, `w(e_i) > 0` iff `i` is not a right descent of `w` (`ℓ(w s_i) = ℓ(w) + 1`). -/
theorem cartanRepresentation_single_pos_iff (w : W) (i : I) :
    0 < cs.cartanRepresentation hA w (Finsupp.single i 1) ↔ ¬cs.IsRightDescent w i :=
  ⟨fun hpos hd ↦ lt_asymm hpos (cs.cartanRepresentation_single_neg hA hd),
    cs.cartanRepresentation_single_pos hA⟩

/-- **Kac's Lemma 3.11, negative case.** In the root-lattice representation of a generalized Cartan
matrix, `w(e_i) < 0` iff `i` is a right descent of `w` (`ℓ(w s_i) + 1 = ℓ(w)`). -/
theorem cartanRepresentation_single_neg_iff (w : W) (i : I) :
    cs.cartanRepresentation hA w (Finsupp.single i 1) < 0 ↔ cs.IsRightDescent w i :=
  ⟨fun hneg ↦ by_contra fun hd ↦ lt_asymm hneg (cs.cartanRepresentation_single_pos hA hd),
    cs.cartanRepresentation_single_neg hA⟩

/-- **Kac's Proposition 3.13 (faithfulness on the root lattice).** The integral root-lattice
representation of `CoxeterSystem A.cartanCoxeterMatrix W` is injective. -/
theorem cartanRepresentation_injective : Function.Injective (cs.cartanRepresentation hA) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ by_contra fun hw₁ ↦ ?_
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw₁
  have hneg := cs.cartanRepresentation_single_neg hA hi
  rw [hw, one_apply_eq_self] at hneg
  exact (Finsupp.single_nonneg.mpr zero_le_one).not_gt hneg

private theorem isLiftable_transpose_cartanRootReflection :
    A.cartanCoxeterMatrix.IsLiftable (Aᵀ.cartanRootReflection hA.transpose.diag) := by
  rw [← A.cartanCoxeterMatrix_transpose]
  exact hA.transpose.isLiftable_reflection (x := fun i ↦ Finsupp.single i (1 : ℤ))
    (f := fun i ↦ Finsupp.linearCombination ℤ (Aᵀ i)) (fun i j ↦ by simp)

/-- **The integral coroot-lattice representation** of a Coxeter system of type
`A.cartanCoxeterMatrix`, acting on `I →₀ ℤ` via `Aᵀ` (`s_i^∨(e_j) = e_j - A j i • e_i`). -/
noncomputable def dualCartanRepresentation : W →* ((I →₀ ℤ) ≃ₗ[ℤ] (I →₀ ℤ)) :=
  cs.lift ⟨Aᵀ.cartanRootReflection hA.transpose.diag,
    isLiftable_transpose_cartanRootReflection hA⟩

@[simp]
theorem dualCartanRepresentation_simple (i : I) :
    cs.dualCartanRepresentation hA (cs.simple i) = Aᵀ.cartanRootReflection hA.transpose.diag i :=
  cs.lift_apply_simple _ i

theorem dualCartanRepresentation_simple_single (i j : I) :
    cs.dualCartanRepresentation hA (cs.simple i) (Finsupp.single j 1) =
      Finsupp.single j 1 - A j i • Finsupp.single i 1 := by
  simp [Matrix.transpose_apply]

private theorem dualCartanRepresentation_eq_cartanRepresentation :
    cs.dualCartanRepresentation hA =
      (A.cartanCoxeterMatrix_transpose.symm ▸ cs).cartanRepresentation hA.transpose := by
  have hsimple {M' : CoxeterMatrix I} (h : A.cartanCoxeterMatrix = M') (i : I) :
      (h ▸ cs).simple i = cs.simple i := by cases h; rfl
  refine cs.ext_simple fun i ↦ ?_
  rw [dualCartanRepresentation_simple, ← hsimple A.cartanCoxeterMatrix_transpose.symm i,
    cartanRepresentation_simple]

/-- **Kac's Lemma 3.11 for coroots, positive case:** `w(e_i^∨) > 0` iff `¬cs.IsRightDescent w i`. -/
theorem dualCartanRepresentation_single_pos_iff (w : W) (i : I) :
    0 < cs.dualCartanRepresentation hA w (Finsupp.single i 1) ↔ ¬cs.IsRightDescent w i := by
  have hdesc {M' : CoxeterMatrix I} (h : A.cartanCoxeterMatrix = M') :
      (h ▸ cs).IsRightDescent w i ↔ cs.IsRightDescent w i := by cases h; rfl
  rw [cs.dualCartanRepresentation_eq_cartanRepresentation hA,
    cartanRepresentation_single_pos_iff, hdesc A.cartanCoxeterMatrix_transpose.symm]

/-- **Kac's Lemma 3.11 for coroots, negative case:** `w(e_i^∨) < 0` iff `cs.IsRightDescent w i`. -/
theorem dualCartanRepresentation_single_neg_iff (w : W) (i : I) :
    cs.dualCartanRepresentation hA w (Finsupp.single i 1) < 0 ↔ cs.IsRightDescent w i := by
  have hdesc {M' : CoxeterMatrix I} (h : A.cartanCoxeterMatrix = M') :
      (h ▸ cs).IsRightDescent w i ↔ cs.IsRightDescent w i := by cases h; rfl
  rw [cs.dualCartanRepresentation_eq_cartanRepresentation hA,
    cartanRepresentation_single_neg_iff, hdesc A.cartanCoxeterMatrix_transpose.symm]

/-- **Kac's Proposition 3.13 for coroots:** `CoxeterSystem.dualCartanRepresentation` is
injective. -/
theorem dualCartanRepresentation_injective :
    Function.Injective (cs.dualCartanRepresentation hA) := by
  rw [cs.dualCartanRepresentation_eq_cartanRepresentation hA]
  exact (A.cartanCoxeterMatrix_transpose.symm ▸ cs).cartanRepresentation_injective hA.transpose

end CoxeterSystem

end
