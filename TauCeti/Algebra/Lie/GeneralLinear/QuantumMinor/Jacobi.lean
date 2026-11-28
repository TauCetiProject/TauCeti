/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Centrality
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Polynomial
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Row
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Polynomial

/-!
# The quantum Jacobi identity

The two-by-two complementary-minor identity for a Capelli determinant uses consecutive
spectral parameters. Expand along the last row, then use right cancellation after adjoining
a central indeterminate. The columns can be any permutation of the rows, so the identity
applies to any pair of deleted columns and any pair of deleted rows after reordering.

This is the complementary-minor identity of L. Alpöge (`Formalism.FourierDecayAlt.Qr.QJacobi`).
-/

public section

open Polynomial

namespace Matrix

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

-- A last-row expansion vanishes if its appended row duplicates one of the preceding rows.
private theorem quantumMinor_snoc_eq_zero_of_mem_range (E : Matrix ι ι A) (u : K)
    (a : Fin n → ι) (b : Fin (n + 1) → ι) {x : ι} (hx : x ∈ Set.range a) :
    E.quantumMinor u (Fin.snoc a x) b = 0 := by
  rw [E.quantumMinor_eq_zero_of_not_injective_left]
  simp [Fin.snoc_injective_iff, hx]

private theorem quantumMinor_jacobi_row (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (v : K) (a : Fin n → ι) (r s : ι) (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 2)) :
    let R : Fin (n + 2) → ι := Fin.snoc (Fin.snoc a r) s
    let C := R ∘ σ
    let M (y : ι) := E.quantumMinor v (Fin.snoc a y) (Fin.init C)
    M r * E.quantumMinor v (Fin.snoc (Fin.snoc a s) (R i)) C -
      M s * E.quantumMinor v (Fin.snoc (Fin.snoc a r) (R i)) C =
      -(E.quantumMinor v R C * M (R i)) := by
  intro R C M
  let D := E.quantumMinor v R C
  have hcomm (y : ι) (hy : y = r ∨ y = s) : Commute (M y) D := by
    have hrow : Set.range (Fin.snoc a y) ⊆ Set.range R := by
      rw [Fin.range_snoc]
      refine Set.insert_subset_iff.mpr ⟨?_, ?_⟩
      · rcases hy with rfl | rfl
        · exact ⟨(Fin.last n).castSucc, by simp [R]⟩
        · exact ⟨Fin.last _, by simp [R]⟩
      · rintro _ ⟨k, rfl⟩
        exact ⟨k.castSucc.castSucc, by simp [R]⟩
    have hcol : Set.range (Fin.init C) ⊆ Set.range R := by
      rintro _ ⟨j, rfl⟩
      exact ⟨σ j.castSucc, rfl⟩
    have h := (E.commute_quantumMinor_self_quantumMinor_of_range_subset hE v v R
      (Fin.snoc a y) (Fin.init C) hrow hcol).symm
    dsimp only [D, C]
    rw [E.quantumMinor_comp_perm_right hE, Units.smul_def, Commute, SemiconjBy]
    simp only [mul_smul_comm, smul_mul_assoc]
    exact congrArg _ h.eq
  have hswap : E.quantumMinor v (Fin.snoc (Fin.snoc a s) r) C = -D := by
    let τ := Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1))
    have hτ : Fin.snoc (Fin.snoc a s) r = R ∘ τ := by
      funext j
      refine Fin.lastCases (by simp [R, τ]) (fun k ↦ ?_) j
      refine Fin.lastCases (by simp [R, τ]) (fun l ↦ ?_) k
      have hl : l.castSucc.castSucc ≠ (Fin.last n).castSucc :=
        fun h ↦ l.castSucc_lt_last.ne (Fin.castSucc_injective _ h)
      simp [R, τ, Equiv.swap_apply_of_ne_of_ne hl (Fin.castSucc_lt_last _).ne]
    rw [hτ, E.quantumMinor_comp_perm_left]
    simp [D, τ, Equiv.Perm.sign_swap (Fin.castSucc_lt_last _).ne]
  -- An interior index repeats a row in every determinant; otherwise exactly one survives.
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [R, Fin.snoc_last]
    rw [E.quantumMinor_snoc_eq_zero_of_mem_range v _ _ ⟨Fin.last _, by simp⟩,
      mul_zero, zero_sub, (hcomm s (Or.inr rfl)).eq]
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [R, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hswap, E.quantumMinor_snoc_eq_zero_of_mem_range v _ _ ⟨Fin.last _, by simp⟩,
        mul_zero, sub_zero, mul_neg, (hcomm r (Or.inl rfl)).eq]
    · simp only [R, Fin.snoc_castSucc]
      rw [E.quantumMinor_snoc_eq_zero_of_mem_range v _ _ ⟨k.castSucc, by simp⟩,
        E.quantumMinor_snoc_eq_zero_of_mem_range v _ _ ⟨k.castSucc, by simp⟩]
      simp [M, E.quantumMinor_snoc_eq_zero_of_mem_range v a _ (Set.mem_range_self k)]

-- Multiplication by the transposed matrix of shifted entries identifies the two rows of
-- cofactor expressions. The matrices here may be over a ring with zero divisors.
private theorem quantumMinor_jacobi_of_vecMul_injective [HasUniqueDiv A]
    (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (u : K) (a : Fin n → ι) (r s : ι) (σ : Equiv.Perm (Fin (n + 2))) :
    let R : Fin (n + 2) → ι := Fin.snoc (Fin.snoc a r) s
    let C := R ∘ σ
    Function.Injective (fun x ↦ x ᵥ* (of fun p i ↦
      (if R i = C p then algebraMap K A (u + 1) else 0) + E (R i) (C p))) →
    ∀ p : Fin (n + 2),
    E.quantumMinor (u + 1) (Fin.snoc a r) (Fin.init C) *
        E.quantumMinor u (Fin.snoc a s) (p.removeNth C) -
      E.quantumMinor (u + 1) (Fin.snoc a s) (Fin.init C) *
        E.quantumMinor u (Fin.snoc a r) (p.removeNth C) =
      @Fin.snoc (n + 1) (fun _ ↦ A) (fun j ↦ E.quantumMinor (u + 1) R C *
        E.quantumMinor u a (j.removeNth (Fin.init C))) 0 p := by
  intro R C hT p
  let T : Matrix (Fin (n + 2)) (Fin (n + 2)) A := of fun j i ↦
    (if R i = C j then algebraMap K A (u + 1) else 0) + E (R i) (C j)
  let D := E.quantumMinor (u + 1) R C
  let M (y : ι) := E.quantumMinor (u + 1) (Fin.snoc a y) (Fin.init C)
  let f (j : Fin (n + 2)) := (-1 : ℤ) ^ (n + 1 - j.val) •
    (M r * E.quantumMinor u (Fin.snoc a s) (j.removeNth C) -
      M s * E.quantumMinor u (Fin.snoc a r) (j.removeNth C))
  let g : Fin (n + 2) → A := Fin.snoc (fun j ↦ (-1 : ℤ) ^ (n + 1 - j.val) •
    (D * E.quantumMinor u a (j.removeNth (Fin.init C)))) 0
  have hexpand (b : Fin (n + 1) → ι) (i : Fin (n + 2)) :
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ (n + 1 - j.val) •
        (E.quantumMinor u b (j.removeNth C) * T j i)) =
        E.quantumMinor (u + 1) (Fin.snoc b (R i)) C := by
    rw [E.quantumMinor_succ_row_last hE]
    simp [T]
  have hf (i : Fin (n + 2)) : (f ᵥ* T) i = -(D * M (R i)) := by
    simp only [vecMul, dotProduct, f, sub_mul, smul_sub, Finset.sum_sub_distrib,
      smul_mul_assoc, mul_assoc, ← mul_smul_comm _ (M r), ← mul_smul_comm _ (M s),
      ← Finset.mul_sum, hexpand]
    exact E.quantumMinor_jacobi_row hE (u + 1) a r s σ i
  have hg (i : Fin (n + 2)) : (g ᵥ* T) i = -(D * M (R i)) := by
    have hsign (j : Fin (n + 1)) : (-1 : ℤ) ^ (n + 1 - j.val) = -((-1) ^ (n - j.val)) := by
      rw [show n + 1 - j.val = (n - j.val) + 1 by omega, pow_succ, mul_neg_one]
    have hsmall : (∑ j : Fin (n + 1), (-1 : ℤ) ^ (n - j.val) •
        (E.quantumMinor u a (j.removeNth (Fin.init C)) * T j.castSucc i)) = M (R i) := by
      dsimp only [M]
      rw [E.quantumMinor_succ_row_last hE]
      simp [T, Fin.init]
    rw [vecMul, dotProduct, Fin.sum_univ_castSucc]
    simp only [g, Fin.snoc_last, zero_mul, add_zero, Fin.snoc_castSucc, hsign, neg_smul,
      neg_mul, smul_mul_assoc, mul_assoc, ← mul_smul_comm _ D]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hsmall]
  have hfg := hT (funext fun i ↦ (hf i).trans (hg i).symm)
  refine Fin.lastCases ?_ (fun j ↦ ?_) p
  · simpa [f, g, D, M] using congrFun hfg (Fin.last (n + 1))
  · have hj := congrFun hfg j.castSucc
    simp only [f, g, Fin.snoc_castSucc, Fin.val_castSucc] at hj
    rcases neg_one_pow_eq_or ℤ (n + 1 - j.val) with h | h <;>
      simpa only [Fin.snoc_castSucc, h, one_smul, neg_one_smul, neg_inj, M, D] using hj

-- The row permutation arises because the test matrix has columns indexed by R and
-- rows indexed by C = R ∘ σ. Before this permutation its leading coefficient is the identity.
private theorem vecMul_injective_quantumMinor_polynomial (E : Matrix ι ι A) (v : K)
    (R : Fin n → ι) (hR : Function.Injective R) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun x ↦ x ᵥ* (of fun j i ↦
      (if R i = R (σ j) then algebraMap K A[X] v else 0) +
        (E.map Polynomial.C + diagonal (fun _ ↦ X) : Matrix ι ι A[X]) (R i) (R (σ j)))) := by
  let B : Matrix (Fin n) (Fin n) A := of fun j i ↦
    (if i = j then algebraMap K A v else 0) + E (R i) (R j)
  let P := B.map C + diagonal (fun _ ↦ (X : A[X]))
  have hP : Function.Injective (fun x ↦ x ᵥ* P) :=
    isRightRegular_iff_vecMul_injective.mp (isRightRegular_map_C_add_diagonal_X B)
  have hmat : (of fun (j i : Fin n) ↦
      (if R i = R (σ j) then algebraMap K A[X] v else 0) +
        (E.map Polynomial.C + diagonal (fun _ ↦ X) : Matrix ι ι A[X]) (R i) (R (σ j))) =
      P.submatrix σ id := by
    apply Matrix.ext
    intro j i
    by_cases h : i = σ j <;>
      simp [P, B, diagonal_apply, hR.eq_iff, h, eq_comm (a := σ j), add_assoc, algebraMap_apply]
  intro x y hxy
  simp only [hmat, submatrix_vecMul_equiv, Function.comp_id] at hxy
  funext j
  simpa only [Function.comp_apply, σ.symm_apply_apply] using congrFun (hP hxy) (σ j)

/-- Quantum Jacobi identity in oriented tuple form. Move the two row labels to be deleted to
the end (`r`, `s`), and move the first column label to be deleted to the end of the column
tuple `C`. The other deleted column is `p`. If `p` is the last position, the two columns
coincide and the answer is zero; otherwise the answer is the full determinant times the
minor with both rows and both columns deleted. The tuple order absorbs the orientation signs. -/
theorem quantumMinor_jacobi [HasUniqueDiv A]
    (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (u : K) (a : Fin n → ι) (r s : ι) (σ : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 2)) :
    let R : Fin (n + 2) → ι := Fin.snoc (Fin.snoc a r) s
    let C := R ∘ σ
    E.quantumMinor (u + 1) (Fin.snoc a r) (Fin.init C) *
        E.quantumMinor u (Fin.snoc a s) (p.removeNth C) -
      E.quantumMinor (u + 1) (Fin.snoc a s) (Fin.init C) *
        E.quantumMinor u (Fin.snoc a r) (p.removeNth C) =
      @Fin.snoc (n + 1) (fun _ ↦ A) (fun j ↦ E.quantumMinor (u + 1) R C *
        E.quantumMinor u a (j.removeNth (Fin.init C))) 0 p := by
  dsimp only
  by_cases hR : Function.Injective (Fin.snoc (Fin.snoc a r) s : Fin (n + 2) → ι)
  · let F : Matrix ι ι A[X] := E.map Polynomial.C + diagonal (fun _ ↦ X)
    let coeffs : A[X] ≃+ (ℕ →₀ A) := AddMonoidAlgebra.coeffAddEquiv
    let : HasUniqueDiv A[X] := coeffs.injective.hasUniqueDiv coeffs.toAddMonoidHom
    have hF : F.HasMatrixUnitLieRelations := hE.map_C_add_diagonal_X
    have hT := E.vecMul_injective_quantumMinor_polynomial (u + 1)
      (Fin.snoc (Fin.snoc a r) s) hR σ
    have h := F.quantumMinor_jacobi_of_vecMul_injective hF u a r s σ hT
    let e : A[X] →+* A := constantCoeff
    have he {k : ℕ} (v : K) (b c : Fin k → ι) :
        e (F.quantumMinor v b c) = E.quantumMinor v b c := by
      simpa only [e, F, constantCoeff_apply, coeff_zero_eq_eval_zero, map_zero, add_zero] using
        E.eval_quantumMinor_map_C_add_diagonal_X v 0 b c
    refine Fin.lastCases ?_ (fun j ↦ ?_) p
    · simpa only [Fin.snoc_last, map_sub, map_mul, he, map_zero] using
        congrArg e (h (Fin.last (n + 1)))
    · simpa only [Fin.snoc_castSucc, map_sub, map_mul, he] using congrArg e (h j.castSucc)
  · have hfull (b : Fin (n + 2) → ι) := E.quantumMinor_eq_zero_of_not_injective_left (u + 1) _ b hR
    have hz (j : Fin (n + 2)) : @Fin.snoc (n + 1) (fun _ ↦ A) (fun k ↦
        E.quantumMinor (u + 1) (Fin.snoc (Fin.snoc a r) s) (Fin.snoc (Fin.snoc a r) s ∘ σ) *
        E.quantumMinor u a (k.removeNth (Fin.init (Fin.snoc (Fin.snoc a r) s ∘ σ))))
        (0 : A) j = 0 := by
      refine Fin.lastCases (by simp) (fun k ↦ ?_) j
      simp [hfull]
    rw [hz]
    simp only [Fin.snoc_injective_iff, Fin.range_snoc] at hR
    by_cases hrs : r = s
    · subst s
      simp
    · have h : ¬ Function.Injective (Fin.snoc a r) ∨ ¬ Function.Injective (Fin.snoc a s) := by
        by_contra! hinj
        simp only [Fin.snoc_injective_iff, Set.mem_insert_iff, not_or] at hinj hR
        exact hR ⟨hinj.1, Ne.symm hrs, hinj.2.2⟩
      rcases h with hr | hs
      · simp [E.quantumMinor_eq_zero_of_not_injective_left _ _ _ hr]
      · simp [E.quantumMinor_eq_zero_of_not_injective_left _ _ _ hs]

end Matrix
