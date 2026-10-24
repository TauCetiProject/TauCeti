/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import TauCeti.Data.Matrix.Permutation

/-!
# Total support of square matrices

A square matrix has total support if it is nonzero and every nonzero entry belongs to a
permutation diagonal consisting of nonzero entries. For a nonnegative matrix this is the
usual positive-diagonal condition. On a nonempty finite index type, it is equivalent to
having the same zero pattern as a doubly stochastic matrix.

The forward construction averages the permutation matrices supported by the matrix.
The converse uses Mathlib's Birkhoff decomposition
`exists_eq_sum_perm_of_mem_doublyStochastic`. This characterization turns a combinatorial
condition on the support into the feasibility condition for doubly stochastic scaling.

## References

* R. Sinkhorn and P. Knopp, *Concerning nonnegative matrices and doubly stochastic matrices*,
  Pacific J. Math. 21 (1967), 343–348, definition on p. 343 and theorem on p. 344.
-/

public section

namespace Matrix

variable {n R : Type*}

section Zero

variable [Zero R] {K L : Matrix n n R}

/-- A square matrix has total support if it is nonzero and every nonzero entry lies on a
permutation diagonal of nonzero entries. The zero matrix is excluded, including on an empty
index type, as in the classical definition. -/
def HasTotalSupport (K : Matrix n n R) : Prop :=
  K ≠ 0 ∧ ∀ i j, K i j ≠ 0 →
    ∃ σ : Equiv.Perm n, σ i = j ∧ ∀ k, K k (σ k) ≠ 0

/-- The nonzero-matrix and permutation-diagonal conditions defining total support. -/
theorem hasTotalSupport_iff : HasTotalSupport K ↔
    K ≠ 0 ∧ ∀ i j, K i j ≠ 0 →
      ∃ σ : Equiv.Perm n, σ i = j ∧ ∀ k, K k (σ k) ≠ 0 := Iff.rfl

/-- The zero matrix does not have total support. -/
@[simp]
theorem not_hasTotalSupport_zero : ¬HasTotalSupport (0 : Matrix n n R) := by
  simp [hasTotalSupport_iff]

/-- Total support depends only on the zero pattern. -/
theorem hasTotalSupport_congr (h : ∀ i j, K i j = 0 ↔ L i j = 0) :
    HasTotalSupport K ↔ HasTotalSupport L := by
  have hz : K = 0 ↔ L = 0 := by
    simp only [← Matrix.ext_iff, zero_apply, h]
  simp only [hasTotalSupport_iff, ne_eq, hz, h]

end Zero

section OrderedField

variable [Fintype n] [DecidableEq n] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {K : Matrix n n R}

/-- Every nonzero entry of a doubly stochastic matrix lies on a positive permutation
diagonal. This is the support consequence of Birkhoff's decomposition. -/
theorem exists_perm_ne_zero_of_mem_doublyStochastic (hK : K ∈ doublyStochastic R n)
    {i j : n} (hij : K i j ≠ 0) :
    ∃ σ : Equiv.Perm n, σ i = j ∧ ∀ k, K k (σ k) ≠ 0 := by
  obtain ⟨w, hw, -, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hK
  have hentry (i j : n) : ∑ σ, w σ * σ.permMatrix R i j = K i j := by
    simpa only [Matrix.sum_apply, smul_apply, smul_eq_mul] using
      congrArg (fun M : Matrix n n R ↦ M i j) hsum
  have hpos : 0 < ∑ σ, w σ * σ.permMatrix R i j := by
    rw [hentry]
    exact lt_of_le_of_ne (nonneg_of_mem_doublyStochastic hK) (Ne.symm hij)
  obtain ⟨σ, -, hσ⟩ := Finset.sum_pos_iff_of_nonneg
    (fun σ _ ↦ mul_nonneg (hw σ) (by
      simp only [PEquiv.toMatrix_toPEquiv_apply]
      exact (Pi.single_nonneg (α := fun _ : n ↦ R)).2 zero_le_one _)) |>.1 hpos
  have hσij : σ i = j := by
    by_contra hne
    simp only [PEquiv.toMatrix_toPEquiv_apply] at hσ
    simp [hne] at hσ
  refine ⟨σ, hσij, fun k ↦ ne_of_gt ?_⟩
  have hwσ : 0 < w σ := by
    simpa [PEquiv.toMatrix_toPEquiv_apply, hσij] using hσ
  calc
    0 < w σ := hwσ
    _ ≤ (∑ τ, w τ • τ.permMatrix R) k (σ k) :=
      weight_le_sum_permMatrix Finset.univ w (fun τ _ ↦ hw τ) (Finset.mem_univ σ) k
    _ = K k (σ k) := congrArg (fun M : Matrix n n R ↦ M k (σ k)) hsum

/-- A doubly stochastic matrix of positive order has total support. -/
theorem hasTotalSupport_of_mem_doublyStochastic [Nonempty n]
    (hK : K ∈ doublyStochastic R n) : HasTotalSupport K := by
  refine ⟨?_, fun _ _ hij ↦ exists_perm_ne_zero_of_mem_doublyStochastic hK hij⟩
  intro hzero
  have hrow := sum_row_of_mem_doublyStochastic hK (Classical.arbitrary n)
  simp [hzero] at hrow

/-- A matrix with total support has the same zero pattern as a doubly stochastic matrix.
No sign condition on the original entries is needed: only their support matters. -/
theorem HasTotalSupport.exists_mem_doublyStochastic (hK : HasTotalSupport K) :
    ∃ P ∈ doublyStochastic R n, ∀ i j, P i j = 0 ↔ K i j = 0 := by
  classical
  let s : Finset (Equiv.Perm n) := Finset.univ.filter fun σ ↦ ∀ k, K k (σ k) ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, j, hij⟩ : ∃ i j, K i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hK.1 (Matrix.ext h)
    obtain ⟨σ, -, hσ⟩ := hK.2 i j hij
    exact ⟨σ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩⟩
  have hcard : (s.card : R) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  let P : Matrix n n R := ∑ σ ∈ s, (s.card : R)⁻¹ • σ.permMatrix R
  have hP : P ∈ doublyStochastic R n :=
    convex_doublyStochastic.sum_mem (fun _ _ ↦ by positivity)
      (by simp [hcard]) (fun _ _ ↦ permMatrix_mem_doublyStochastic)
  refine ⟨P, hP, fun i j ↦ ?_⟩
  have hentry : P i j = ∑ σ ∈ s, (s.card : R)⁻¹ * σ.permMatrix R i j := by
    simp only [P, Matrix.sum_apply, smul_apply, smul_eq_mul]
  constructor
  · intro hzero
    by_contra hij
    obtain ⟨σ, hσij, hσ⟩ := hK.2 i j hij
    have hσmem : σ ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩
    have hle : (s.card : R)⁻¹ ≤ P i j := by
      simpa only [hσij] using
        weight_le_sum_permMatrix s (fun _ ↦ (s.card : R)⁻¹)
          (fun _ _ ↦ by positivity) hσmem i
    have hpos : 0 < (s.card : R)⁻¹ := inv_pos.2 (by exact_mod_cast hs.card_pos)
    have hposP : 0 < P i j := hpos.trans_le hle
    exact hposP.ne' hzero
  · intro hij
    rw [hentry]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hσij : σ i ≠ j := by
      intro heq
      exact (Finset.mem_filter.1 hσ).2 i (heq ▸ hij)
    simp only [PEquiv.toMatrix_toPEquiv_apply]
    simp [hσij]

/-- Total support is equivalent to a doubly stochastic realization of the same zero pattern.
The nonempty index type is necessary because the classical definition excludes the zero
matrix, whereas the empty matrix is doubly stochastic. -/
theorem hasTotalSupport_iff_exists_mem_doublyStochastic [Nonempty n] :
    HasTotalSupport K ↔ ∃ P ∈ doublyStochastic R n, ∀ i j, P i j = 0 ↔ K i j = 0 := by
  refine ⟨HasTotalSupport.exists_mem_doublyStochastic, ?_⟩
  rintro ⟨P, hP, hPK⟩
  exact (hasTotalSupport_congr hPK).1 (hasTotalSupport_of_mem_doublyStochastic hP)

end OrderedField

end Matrix
