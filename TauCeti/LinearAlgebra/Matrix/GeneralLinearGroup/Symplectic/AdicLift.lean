/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Lift
public import Mathlib.RingTheory.AdicCompletion.Basic

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
the new defect is quadratic in `X` and `E`, so lies in `I ^ (2 k) ⊆ I ^ (k + 1)`. The corrections
converge `I`-adically, and the limit has defect in every `I ^ n`, hence zero. This is the
square-zero lifting of `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`, iterated.

If moreover `I ≤ 𝔫`, a matrix congruent to `1` modulo the image of `𝔫` lifts to one congruent to
`1` modulo `𝔫` (`TauCeti.GLSymplectic.exists_map_eq_and_sub_one_mem`). For a complete local ring
and `𝔫` its maximal ideal, a reduction congruent to `1` modulo `𝔪 / I` lifts to `g ≡ 1 mod 𝔪`.

## Main results

* `TauCeti.GLSymplectic.exists_sub_mem_pow_and_defect_mem_pow_succ`: the Newton step.
* `TauCeti.GLSymplectic.exists_mem_symplecticGroup_sub_mem`: a matrix that is symplectic modulo
  `I` is congruent modulo `I` to a symplectic matrix.
* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_isAdicComplete`: reduction modulo `I` is
  surjective on symplectic groups.
* `TauCeti.GLSymplectic.exists_map_eq_and_sub_one_mem`: lifts congruent to `1`.

## References

* TauCetiRoadmap, `ArithmeticGaloisRepresentations/README.md`, §5.10 (symplectic forms and gluing).
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

noncomputable section

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type*} [CommRing R]

private theorem mul_apply_mem_mul {m n o : Type*} [Fintype n] {I K : Ideal R}
    {A : Matrix m n R} {B : Matrix n o R} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ K)
    (i : m) (j : o) : (A * B) i j ∈ I * K := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_mul (hA i k) (hB k j)

private theorem smodEq_iff (I : Ideal R) (x y : R) (n : ℕ) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/-- **The Newton step.** If the symplectic defect `M * J * Mᵀ - J` of `M` has entries in `I ^ k`,
then a matrix congruent to `M` modulo `I ^ k` has defect in `I ^ (k + 1)`. For `k ≥ 1` it is
`(1 + X) * M`, with `X` solving the linearized equation, and no division by two is needed. -/
theorem exists_sub_mem_pow_and_defect_mem_pow_succ (I : Ideal R) {k : ℕ}
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
  have hXJ : ∀ i j, (X * J l R) i j ∈ I ^ k := fun i j ↦ by
    simpa using mul_mul_apply_mem hX_mem 1 (J l R) i j
  refine ⟨(1 + X) * M, fun i j ↦ ?_, fun i j ↦ ?_⟩
  · rw [add_mul, one_mul, add_sub_cancel_left]
    simpa using mul_mul_apply_mem hX_mem 1 M i j
  · have hdef : (1 + X) * M * J l R * ((1 + X) * M)ᵀ - J l R =
        X * E + E * Xᵀ + X * J l R * Xᵀ + X * E * Xᵀ := by
      have hJ : M * J l R * Mᵀ = J l R + E := by rw [hE, add_sub_cancel]
      have hX' : X * J l R + J l R * Xᵀ = -E := by
        rw [eq_neg_iff_add_eq_zero, add_comm, ← add_assoc]
        exact hX
      calc (1 + X) * M * J l R * ((1 + X) * M)ᵀ - J l R
          = (1 + X) * (M * J l R * Mᵀ) * (1 + Xᵀ) - J l R := by
            rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
            noncomm_ring
        _ = E + (X * J l R + J l R * Xᵀ) + X * E + E * Xᵀ + X * J l R * Xᵀ + X * E * Xᵀ := by
            rw [hJ]
            noncomm_ring
        _ = _ := by rw [hX']; noncomm_ring
    rw [hdef]
    simp only [Matrix.add_apply]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_
    · exact hle (mul_apply_mem_mul hX_mem hM i j)
    · exact hle (mul_apply_mem_mul hM hXt i j)
    · exact hle (mul_apply_mem_mul hXJ hXt i j)
    · have hXE : ∀ i j, (X * E) i j ∈ I ^ k := fun i j ↦ by
        simpa using mul_mul_apply_mem hX_mem 1 E i j
      exact hle (mul_apply_mem_mul hXE hXt i j)

/-- The defect of a matrix congruent entrywise to one with small defect. -/
private theorem defect_mem_of_sub_mem {I : Ideal R} {n : ℕ} {L M : Matrix (l ⊕ l) (l ⊕ l) R}
    (hLM : ∀ i j, (L - M) i j ∈ I ^ n) (hM : ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I ^ n)
    (i j : l ⊕ l) : (L * J l R * Lᵀ - J l R) i j ∈ I ^ n := by
  set D := L - M
  have hL : L = M + D := by simp [D]
  have hD : ∀ i j, (D * J l R) i j ∈ I ^ n := fun i j ↦ by
    simpa using mul_mul_apply_mem hLM 1 (J l R) i j
  have hDt : ∀ i j, Dᵀ i j ∈ I ^ n := fun i j ↦ hLM j i
  have h : L * J l R * Lᵀ - J l R = (M * J l R * Mᵀ - J l R) + D * J l R * Mᵀ +
      M * J l R * Dᵀ + D * J l R * Dᵀ := by
    rw [hL, Matrix.transpose_add]
    noncomm_ring
  rw [h]
  simp only [Matrix.add_apply]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (hM i j) ?_) ?_) ?_
  · simpa using mul_mul_apply_mem hD 1 Mᵀ i j
  · simpa [Matrix.mul_assoc] using mul_mul_apply_mem hDt (M * J l R) 1 i j
  · simpa using mul_mul_apply_mem hDt (D * J l R) 1 i j

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
    exists_sub_mem_pow_and_defect_mem_pow_succ I M hM
  let seq : (n : ℕ) → {M // P n M} := fun n ↦ Nat.rec ⟨M, by simpa [P] using hM⟩
    (fun n M ↦ ⟨(hstep n M.val M.property).choose,
      (hstep n M.val M.property).choose_spec.2⟩) n
  have hsucc (n : ℕ) (i j : l ⊕ l) : ((seq (n + 1)).val - (seq n).val) i j ∈ I ^ (n + 1) :=
    (hstep n (seq n).val (seq n).property).choose_spec.1 i j
  have hcauchy (m : ℕ) : ∀ n, m ≤ n → ∀ i j, ((seq n).val - (seq m).val) i j ∈ I ^ m := by
    intro n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      intro i j
      have := Ideal.pow_le_pow_right (I := I) (by omega : m ≤ n + 1) (hsucc n i j)
      simpa [sub_add_sub_cancel'] using Ideal.add_mem _ this (ih i j)
  choose L hL using fun i j ↦ IsPrecomplete.prec (I := I) inferInstance
    (f := fun n ↦ (seq n).val i j) fun {m n} hmn ↦ by
      rw [smodEq_iff, ← neg_sub]
      simpa using neg_mem (hcauchy m n hmn i j)
  have hLn (n : ℕ) (i j : l ⊕ l) : (Matrix.of L - (seq n).val) i j ∈ I ^ n := by
    have := neg_mem ((smodEq_iff I _ _ n).mp (hL i j n))
    rwa [neg_sub] at this
  refine ⟨Matrix.of L, ?_, fun i j ↦ ?_⟩
  · rw [SymplecticGroup.mem_iff, ← sub_eq_zero]
    ext i j
    refine IsHausdorff.haus (I := I) inferInstance _ fun n ↦ (smodEq_iff I _ _ n).mpr ?_
    simpa using defect_mem_of_sub_mem (hLn n)
      (fun i j ↦ Ideal.pow_le_pow_right (by omega) ((seq n).property i j)) i j
  · have h0 : (seq 0).val = M := rfl
    have := Ideal.add_mem _ (hLn 1 i j) (by simpa using hsucc 0 i j)
    simpa [h0] using this

/-- **Symplectic matrices lift along an adically complete quotient.** If `R` is `I`-adically
complete, reduction modulo `I` is surjective on symplectic groups. -/
theorem map_quotient_mk_surjective_of_isAdicComplete (I : Ideal R) [IsAdicComplete I R] :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) := by
  classical
  intro g
  choose m hm using fun i j ↦ Ideal.Quotient.mk_surjective
    (((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) i j)
  let M : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.of m
  have hM_map : M.map (Ideal.Quotient.mk I) =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) := by
    ext i j
    exact hm i j
  have hE : ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I := by
    rw [← Ideal.mk_ker (I := I), forall_mem_ker_iff_map_eq_zero]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM_map,
      Matrix.map_J, (GLSymplectic.mem_iff).mp g.property, sub_self]
  obtain ⟨L, hL, hLM⟩ := exists_mem_symplecticGroup_sub_mem I M hE
  refine ⟨⟨ofSymplecticGroup l R ⟨L, hL⟩, ofSymplecticGroup_mem l R ⟨L, hL⟩⟩, ?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [← hm i j]
  simpa [M, coe_map, Matrix.GeneralLinearGroup.map_apply, coe_ofSymplecticGroup,
    Ideal.Quotient.eq] using hLM i j

/-- **Lifts congruent to the identity.** If `R` is `I`-adically complete and `I ≤ 𝔫`, a symplectic
matrix over `R ⧸ I` congruent to `1` modulo the image of `𝔫` lifts to a symplectic matrix over `R`
congruent to `1` modulo `𝔫`. For a local ring and `𝔫` its maximal ideal, a lift of a matrix that
is `1` modulo `𝔪 / I` is `1` modulo `𝔪`. -/
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
