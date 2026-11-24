/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Lift
public import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Lifting symplectic matrices along an adically complete quotient

Let `R` be a commutative ring which is `I`-adically complete. Every symplectic matrix over `R ⧸ I`
lifts to a symplectic matrix over `R`
(`TauCeti.GLSymplectic.map_quotient_mk_surjective_of_isAdicComplete`). In every characteristic:
`2` need not be invertible.

The proof is Newton's method. A matrix `M` whose symplectic defect `M * J * Mᵀ - J` has entries in
`I ^ k` is corrected to `(1 + X) * M`, where `X` has entries in `I ^ k` and solves the linearized
equation `E + X * J + J * Xᵀ = 0`
(`Matrix.exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero`, which needs no division by two);
the new defect is quadratic in `X` and `E` (`Matrix.one_add_mul_mul_J_mul_transpose_sub_J`), so
lies in `I ^ (2 k) ⊆ I ^ (k + 1)`. The corrections converge `I`-adically
(`TauCeti.exists_forall_sub_mem_pow`), and the limit has defect in every `I ^ n`, hence zero. This
is the square-zero lifting of `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`,
iterated.

If moreover `I ≤ 𝔫`, a matrix congruent to `1` modulo the image of `𝔫` lifts to one congruent to
`1` modulo `𝔫` (`TauCeti.GLSymplectic.exists_map_eq_and_sub_one_mem`). For a local ring that is
`I`-adically complete and `𝔫` its maximal ideal `𝔪`, a reduction congruent to `1` modulo `𝔪 / I`
lifts to `g ≡ 1 mod 𝔪`.

## Main results

* `TauCeti.GLSymplectic.exists_sub_mem_pow_and_mul_J_mul_transpose_sub_J_mem_pow_succ`: the
  Newton step.
* `TauCeti.GLSymplectic.exists_mem_symplecticGroup_sub_mem`: a matrix that is symplectic modulo
  `I` is congruent modulo `I` to a symplectic matrix.
* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_isAdicComplete`: reduction modulo `I` is
  surjective on symplectic groups.
* `TauCeti.GLSymplectic.exists_map_eq_and_sub_one_mem`: lifts congruent to `1`.
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

noncomputable section

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type*} [CommRing R]

/-- **The Newton step.** If the symplectic defect `M * J * Mᵀ - J` of `M` has entries in `I ^ k`,
then there is a matrix `M'` congruent to `M` modulo `I ^ k` whose defect has entries in
`I ^ (k + 1)`. -/
theorem exists_sub_mem_pow_and_mul_J_mul_transpose_sub_J_mem_pow_succ (I : Ideal R) {k : ℕ}
    (M : Matrix (l ⊕ l) (l ⊕ l) R) (hM : ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I ^ k) :
    ∃ M' : Matrix (l ⊕ l) (l ⊕ l) R, (∀ i j, (M' - M) i j ∈ I ^ k) ∧
      ∀ i j, (M' * J l R * M'ᵀ - J l R) i j ∈ I ^ (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun i j ↦ by simp, fun i j ↦ ?_⟩
    simp
  set E := M * J l R * Mᵀ - J l R with hE
  obtain ⟨X, hX_mem, hX⟩ := exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero (I ^ k) E hM
    (transpose_mul_J_mul_transpose_sub_J M) (mul_J_mul_transpose_sub_J_apply_self M)
  have hle : I ^ k * I ^ k ≤ I ^ (k + 1) := by
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (by omega)
  have hXt : ∀ i j, Xᵀ i j ∈ I ^ k := fun i j ↦ hX_mem j i
  refine ⟨(1 + X) * M, fun i j ↦ ?_, fun i j ↦ ?_⟩
  · rw [add_mul, one_mul, add_sub_cancel_left]
    exact mul_apply_mem_right hX_mem M i j
  rw [one_add_mul_mul_J_mul_transpose_sub_J hE.symm hX]
  simp only [Matrix.add_apply]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_
  · exact hle (mul_apply_mem_mul hX_mem hM i j)
  · exact hle (mul_apply_mem_mul hM hXt i j)
  · exact hle (mul_apply_mem_mul (mul_apply_mem_right hX_mem (J l R)) hXt i j)
  · exact hle (mul_apply_mem_mul (mul_apply_mem_right hX_mem E) hXt i j)

/-- A matrix over an `I`-adically complete ring that is symplectic modulo `I` is congruent modulo
`I` to a symplectic matrix. -/
theorem exists_mem_symplecticGroup_sub_mem (I : Ideal R) [IsAdicComplete I R]
    (M : Matrix (l ⊕ l) (l ⊕ l) R) (hM : ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I) :
    ∃ L ∈ symplecticGroup l R, ∀ i j, (L - M) i j ∈ I := by
  -- Newton's method: a sequence with defect in `I ^ (n + 1)` and steps in `I ^ (n + 1)`.
  let P : ℕ → Matrix (l ⊕ l) (l ⊕ l) R → Prop :=
    fun n M ↦ ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I ^ (n + 1)
  have hstep (n : ℕ) (M : Matrix (l ⊕ l) (l ⊕ l) R) (hM : P n M) :
      ∃ M', (∀ i j, (M' - M) i j ∈ I ^ (n + 1)) ∧ P (n + 1) M' :=
    exists_sub_mem_pow_and_mul_J_mul_transpose_sub_J_mem_pow_succ I M hM
  let seq : (n : ℕ) → {M // P n M} := fun n ↦ Nat.rec ⟨M, by simpa [P] using hM⟩
    (fun n M ↦ ⟨(hstep n M.val M.property).choose,
      (hstep n M.val M.property).choose_spec.2⟩) n
  have hsucc (n : ℕ) (i j : l ⊕ l) : ((seq (n + 1)).val - (seq n).val) i j ∈ I ^ (n + 1) :=
    (hstep n (seq n).val (seq n).property).choose_spec.1 i j
  obtain ⟨L, hL⟩ := exists_forall_sub_mem_pow I (fun n (p : (l ⊕ l) × (l ⊕ l)) ↦
    (seq n).val p.1 p.2) fun n p ↦ Ideal.pow_le_pow_right n.le_succ (hsucc n p.1 p.2)
  have hLn (n : ℕ) (i j : l ⊕ l) : (Matrix.of (fun i j ↦ L (i, j)) - (seq n).val) i j ∈ I ^ n :=
    hL n (i, j)
  refine ⟨Matrix.of fun i j ↦ L (i, j), ?_, fun i j ↦ ?_⟩
  · rw [SymplecticGroup.mem_iff, ← sub_eq_zero]
    ext i j
    refine IsHausdorff.haus (I := I) inferInstance _ fun n ↦
      (Ideal.smodEq_smul_top_iff_sub_mem _ _ _).mpr ?_
    simpa using mul_J_mul_transpose_sub_J_mem_of_sub_mem (hLn n)
      (fun i j ↦ Ideal.pow_le_pow_right (by omega) ((seq n).property i j)) i j
  · have h0 : (seq 0).val = M := rfl
    have := Ideal.add_mem _ (hLn 1 i j) (by simpa using hsucc 0 i j)
    simpa [h0] using this

/-- **Symplectic matrices lift along an adically complete quotient.** If `R` is `I`-adically
complete, reduction modulo `I` is surjective on symplectic groups. -/
theorem map_quotient_mk_surjective_of_isAdicComplete (I : Ideal R) [IsAdicComplete I R] :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) :=
  map_quotient_mk_surjective_of_exists_mem_symplecticGroup_sub_mem I
    (exists_mem_symplecticGroup_sub_mem I)

/-- **Lifts congruent to the identity.** If `R` is `I`-adically complete and `I ≤ 𝔫`, a symplectic
matrix over `R ⧸ I` congruent to `1` modulo the image of `𝔫` lifts to a symplectic matrix over `R`
congruent to `1` modulo `𝔫`. For an `I`-adically complete local ring and `𝔫` its maximal ideal
`𝔪`, a lift of a matrix that is `1` modulo `𝔪 / I` is `1` modulo `𝔪`. -/
theorem exists_map_eq_and_sub_one_mem (I : Ideal R) [IsAdicComplete I R] {𝔫 : Ideal R}
    (hI : I ≤ 𝔫) (g : GLSymplectic l (R ⧸ I))
    (hg : ∀ i j, (((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) - 1) i j ∈
      𝔫.map (Ideal.Quotient.mk I)) :
    ∃ G : GLSymplectic l R, GLSymplectic.map l (Ideal.Quotient.mk I) G = g ∧
      ∀ i j, (((G : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) - 1) i j ∈ 𝔫 := by
  obtain ⟨G, rfl⟩ := map_quotient_mk_surjective_of_isAdicComplete I g
  refine ⟨G, rfl, fun i j ↦ ?_⟩
  have h : Ideal.Quotient.mk I ((((G : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) - 1) i j) ∈
      𝔫.map (Ideal.Quotient.mk I) := by
    simpa [coe_map, Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using hg i j
  rwa [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_eq_left.mpr hI] at h

end

end TauCeti.GLSymplectic
