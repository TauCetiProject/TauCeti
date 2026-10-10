/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.Basic

import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Rank factorization through a finite intermediate space

A matrix over a field factors through an intermediate vector space whose dimension is
its rank. Factoring through `Fin r` is equivalent to the inequality `rank M ≤ r`.
Exact-rank factorizations are unique up to an invertible change of basis.

## Main results

* `Matrix.exists_eq_mul_rank`: factor through `Fin M.rank`.
* `Matrix.exists_eq_mul_of_rank_le`: factor through `Fin r` when `M.rank ≤ r`.
* `Matrix.rank_le_iff_exists_eq_mul`: characterize rank by factorization.
* `Matrix.exists_unit_eq_mul_of_rank_factorization`: uniqueness under an invertible
  change of basis at exact rank.

## Provenance

Ported from `ForTauCeti/LinearAlgebra/Matrix/RankFactorization.lean` in
[Kitware's DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
originally developed by Jon Crall and Claude Fable 5 (Apache-2.0).
-/

public section

namespace Matrix

open Module (finrank)

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n]

/--
**Rank factorization (exact).** Every matrix factors as `M = L * R` with inner
dimension `Fin M.rank`: `L` lists a basis of the column space of `M` and `R` the
coordinates of each column of `M` in that basis.
-/
theorem exists_eq_mul_rank (M : Matrix m n 𝕜) :
    ∃ (L : Matrix m (Fin M.rank) 𝕜) (R : Matrix (Fin M.rank) n 𝕜), M = L * R := by
  -- `Pi.single` below needs `DecidableEq n`, which the statement does not.
  classical
  -- A basis of the column space, indexed by `Fin M.rank`.
  have hdim : finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank := by
    rw [Matrix.rank]
  let b : Module.Basis (Fin M.rank) 𝕜 (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq 𝕜 _ hdim
  -- Each column of `M` lies in the column space.
  have hcol : ∀ j : n, (fun i => M i j) ∈ LinearMap.range M.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨Matrix.of fun i k => (b k : m → 𝕜) i, Matrix.of fun k j => b.repr ⟨_, hcol j⟩ k, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  -- Expand column `j` in the basis and evaluate the resulting identity at row `i`.
  have hrepr := congrArg Subtype.val (b.sum_repr ⟨_, hcol j⟩)
  rw [Submodule.coe_sum] at hrepr
  have := congrFun hrepr i
  simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Finset.sum_congr rfl fun k _ => mul_comm ((b k : m → 𝕜) i) (b.repr ⟨_, hcol j⟩ k)]
  exact this.symm

/--
**Rank factorization (padded).** A matrix `M` with `M.rank ≤ r` factors as
`M = L * R` with `L : Matrix m (Fin r) 𝕜` and `R : Matrix (Fin r) n 𝕜`
(the exact factorization, zero-padded to inner dimension `r`).
-/
theorem exists_eq_mul_of_rank_le (M : Matrix m n 𝕜) {r : ℕ} (h : M.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  obtain ⟨L₀, R₀, hM⟩ := exists_eq_mul_rank M
  refine ⟨Matrix.of fun i k => if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0,
    Matrix.of fun k j => if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0, ?_⟩
  ext i j
  -- Reduce the padded sum over `Fin r` to the exact sum over `Fin M.rank`.
  set f : ℕ → 𝕜 := fun k => if hk : k < M.rank then L₀ i ⟨k, hk⟩ * R₀ ⟨k, hk⟩ j else 0 with hf
  have hpad : ∀ k : Fin r,
      (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
        * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0) = f (k : ℕ) := by
    intro k
    by_cases hk : (k : ℕ) < M.rank <;> simp [hf, hk]
  have hexact : ∀ k : Fin M.rank, L₀ i k * R₀ k j = f (k : ℕ) := by
    intro k
    simp [hf, k.isLt]
  have hsum : (∑ k : Fin r,
        (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
          * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0))
      = ∑ k : Fin M.rank, L₀ i k * R₀ k j := by
    rw [Finset.sum_congr rfl fun k _ => hpad k, Fin.sum_univ_eq_sum_range f r,
      Finset.sum_congr rfl fun k _ => hexact k, Fin.sum_univ_eq_sum_range f M.rank]
    -- The padding terms vanish above `M.rank`.
    refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le h))
      fun k _ hk => dite_eq_right (by simpa using hk)).symm
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [hsum, ← Matrix.mul_apply, ← hM]

/--
**Rank-`r` factorization characterization.** A matrix has rank at most `r` if
and only if it factors through `Fin r`: `M.rank ≤ r ↔ ∃ L R, M = L * R`.
-/
theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  refine ⟨exists_eq_mul_of_rank_le M, ?_⟩
  rintro ⟨L, R, rfl⟩
  calc (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card (Fin r) := L.rank_le_card_width
    _ = r := Fintype.card_fin r

/-! ### Uniqueness of a rank factorization

For factorizations through a space whose dimension is the rank, the left factors have
identical ranges and are injective. Their change of basis is therefore invertible. -/

section Uniqueness

/-- If `M = L * R` has rank equal to the number of columns of `L`, then `L`
has full column rank. The intermediate index may be any finite type. -/
theorem rank_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n 𝕜} {L : Matrix m ι 𝕜}
    {R : Matrix ι n 𝕜} (hM : M.rank = Fintype.card ι)
    (h : M = L * R) : L.rank = Fintype.card ι := by
  refine le_antisymm (by simpa using L.rank_le_card_width) ?_
  calc Fintype.card ι = M.rank := hM.symm
    _ = (L * R).rank := by rw [h]
    _ ≤ L.rank := Matrix.rank_mul_le_left L R

/-- An exact-rank left factor spans the column space of the factored matrix. -/
theorem range_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n 𝕜} {L : Matrix m ι 𝕜}
    {R : Matrix ι n 𝕜} (hM : M.rank = Fintype.card ι) (h : M = L * R) :
    LinearMap.range L.mulVecLin = LinearMap.range M.mulVecLin := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [h, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hL := rank_left_factor_eq hM h
    rw [Matrix.rank] at hM hL
    exact hM.trans hL.symm

omit [Fintype n] in
/-- If each column of `L'` belongs to the range of `L`, then `L'` factors
through `L`. The column index type `κ` need not be finite: a preimage is
chosen independently for each of its columns. -/
theorem exists_mul_eq_of_range_le {ι κ : Type*} [Fintype ι]
    {L : Matrix m ι 𝕜} {L' : Matrix m κ 𝕜}
    (h : ∀ j : κ, L'.col j ∈ LinearMap.range L.mulVecLin) :
    ∃ G : Matrix ι κ 𝕜, L * G = L' := by
  classical
  have hpre (j : κ) : ∃ v : ι → 𝕜, L.mulVec v = L'.col j := h j
  choose v hv using hpre
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hv j) i

/-- Two factorizations of the same matrix through any finite intermediate type `ι`,
when the rank equals `Fintype.card ι`, differ by an invertible change of basis.
The decidable equality instance supplies the identity matrix and square-matrix units. -/
theorem exists_unit_eq_mul_of_rank_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix m n 𝕜} (hM : M.rank = Fintype.card ι)
    {L L' : Matrix m ι 𝕜} {R R' : Matrix ι n 𝕜}
    (h : M = L * R) (h' : M = L' * R') :
    ∃ g : (Matrix ι ι 𝕜)ˣ,
      L' = L * (g : Matrix ι ι 𝕜) ∧
        R' = ((g⁻¹ : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) * R := by
  classical
  have hrange : LinearMap.range L'.mulVecLin = LinearMap.range L.mulVecLin := by
    rw [range_left_factor_eq hM h', range_left_factor_eq hM h]
  have hcols : ∀ j : ι, L'.col j ∈ LinearMap.range L.mulVecLin := by
    intro j
    rw [← hrange, Matrix.range_mulVecLin]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hcols' : ∀ j : ι, L.col j ∈ LinearMap.range L'.mulVecLin := by
    intro j
    rw [hrange, Matrix.range_mulVecLin]
    exact Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_le (L := L) (L' := L') hcols
  obtain ⟨G', hG'⟩ := exists_mul_eq_of_range_le (L := L') (L' := L) hcols'
  have hLinj : Function.Injective L.mulVec :=
    (rank_eq_card_iff_mulVec_injective L).mp (rank_left_factor_eq hM h)
  have hL'inj : Function.Injective L'.mulVec :=
    (rank_eq_card_iff_mulVec_injective L').mp (rank_left_factor_eq hM h')
  have hGG' : G * G' = 1 := by
    rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
    · apply Matrix.ext
      intro i j
      exact (hEmpty.false i).elim
    · let : Inhabited ι := ⟨Classical.choice hNonempty⟩
      apply (mul_right_injective_iff_mulVec_injective.mpr hLinj)
      exact calc
        L * (G * G') = (L * G) * G' := (Matrix.mul_assoc L G G').symm
        _ = L := by rw [hG, hG']
        _ = L * 1 := (Matrix.mul_one L).symm
  have hG'G : G' * G = 1 := by
    rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
    · apply Matrix.ext
      intro i j
      exact (hEmpty.false i).elim
    · let : Inhabited ι := ⟨Classical.choice hNonempty⟩
      apply (mul_right_injective_iff_mulVec_injective.mpr hL'inj)
      exact calc
        L' * (G' * G) = (L' * G') * G := (Matrix.mul_assoc L' G' G).symm
        _ = L' := by rw [hG', hG]
        _ = L' * 1 := (Matrix.mul_one L').symm
  refine ⟨⟨G, G', hGG', hG'G⟩, hG.symm, ?_⟩
  have hR : R = G * R' := by
    rcases isEmpty_or_nonempty n with hEmpty | hNonempty
    · apply Matrix.ext
      intro i j
      exact (hEmpty.false j).elim
    · let : Inhabited n := ⟨Classical.choice hNonempty⟩
      apply (mul_right_injective_iff_mulVec_injective.mpr hLinj)
      exact calc
        L * R = M := h.symm
        _ = L' * R' := h'
        _ = (L * G) * R' := by rw [hG]
        _ = L * (G * R') := Matrix.mul_assoc L G R'
  rw [hR, ← Matrix.mul_assoc]
  simp [hG'G]

end Uniqueness

end Matrix
