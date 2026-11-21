/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.MatrixUnits
public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar
import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Unitary conjugacy of nearby systems of matrix units in a C⋆-algebra

To make nearby finite-dimensional `⋆`-homomorphisms and C⋆-subalgebras inner-conjugate by a unitary
close to `1` (feeding AF local structure and approximate intertwining), we polar-normalize
`matrixUnitIntertwiner ℝ e f` when `‖f r i j - e r i j‖ ≤ δ` and `6 * (∑ r, card (n r)) * δ ≤ 1`:
the resulting unitary `u` has `Joined 1 u`, conjugates `e` to `f`, satisfies
`‖(u : A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`, lies in any closed unital `𝕜'`-`⋆`-subalgebra
containing `e` and `f`, and has scalar part `1` in `Unitization ℂ A`.

## Main results

* `TauCeti.IsMatrixUnitSystem.norm_matrixUnitIntertwiner_sub_one_le`,
  `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate_mem`,
  `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate`,
  `TauCeti.IsMatrixUnitSystem.exists_unitization_unitary_conjugate`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23; *K-Theory for Operator
  Algebras*, 2nd ed., Cambridge Univ. Press (1998), Ch. III, §7.
-/

public section

namespace TauCeti.IsMatrixUnitSystem
/-- Bound `‖matrixUnitIntertwiner 𝕜 e f - 1‖ ≤ 2 * (∑ r, card (n r)) * δ` when
`‖f r i j - e r i j‖ ≤ δ`. -/
theorem norm_matrixUnitIntertwiner_sub_one_le {κ A : Type*} {n : κ → Type*} [Fintype κ]
    [∀ r, Fintype (n r)] [NormedRing A] [StarRing A] [CStarRing A] (𝕜 : Type*) [RCLike 𝕜]
    [NormedAlgebra 𝕜 A] {e f : ∀ r : κ, n r → n r → A} (he : IsMatrixUnitSystem e)
    {δ : ℝ} (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ‖matrixUnitIntertwiner 𝕜 e f - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  rw [← he.matrixUnitIntertwiner_self (𝕜 := 𝕜), matrixUnitIntertwiner_def,
    matrixUnitIntertwiner_def, add_sub_add_comm, ← sub_mul,
    show (1 - matrixUnitSupport f) - (1 - matrixUnitSupport e) =
      matrixUnitSupport e - matrixUnitSupport f by abel]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, ← sub_mul]
  set S : ℝ := (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ
  refine (norm_add_le _ _).trans <|
    (add_le_add (b := S) (d := S) ?_ ?_).trans_eq (by dsimp [S]; ring)
  · refine (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (he.isStarProjection_support.one_sub.norm_le _)).trans ?_)
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, S, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦ (norm_sum_le _ _).trans <|
      (Finset.sum_le_sum fun i _ ↦ (norm_sub_rev _ _).le.trans (hdist r i i)).trans (by simp)
  · dsimp [S]; rw [Finset.sum_mul]; refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦ ?_
    by_cases hcard : Fintype.card (n r) = 0; · simp [hcard]
    have hpos : (0 : ℝ) < Fintype.card (n r) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    rw [norm_smul, norm_inv, RCLike.norm_natCast,
      ← inv_mul_cancel_left₀ hpos.ne' ((Fintype.card (n r) : ℝ) * δ)]; gcongr
    exact (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun a _ ↦
      (norm_sum_le _ _).trans <| Finset.sum_le_sum fun b _ ↦ (norm_mul_le _ _).trans <|
        (mul_le_of_le_one_right (norm_nonneg _) (he.isPartialIsometry r b a).norm_le_one).trans
          (hdist r a b)).trans (by simp)

section
variable {κ A : Type*} {n : κ → Type*} [Fintype κ] [∀ r, Fintype (n r)] [CStarAlgebra A]
  {e f : ∀ r : κ, n r → n r → A}
private lemma exists_polarUnitary_intertwiner [PartialOrder A] [StarOrderedRing A]
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    {δ : ℝ} (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ a : Aˣ, (a : A) = matrixUnitIntertwiner ℝ e f ∧ Joined 1 a.polarUnitary ∧
      (∀ r i j, (a.polarUnitary : A) * e r i j * star (a.polarUnitary : A) = f r i j) ∧
      ‖(a.polarUnitary : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  have hz_le := he.norm_matrixUnitIntertwiner_sub_one_le ℝ hdist
  have hz_unit : IsUnit (matrixUnitIntertwiner ℝ e f) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one
      (show ‖1 - matrixUnitIntertwiner ℝ e f‖ < 1 by rw [norm_sub_rev]; linarith)
  set a : Aˣ := hz_unit.unit; have ha : (a : A) = matrixUnitIntertwiner ℝ e f := hz_unit.unit_spec
  have ha_half : ‖(a : A) - 1‖ ≤ 1 / 2 := by rw [ha]; linarith
  exact ⟨a, ha, Units.joined_one_polarUnitary ha_half, fun r i j ↦ a.conjugate_polarUnitary
      (ha ▸ he.mul_matrixUnitIntertwiner_eq_matrixUnitIntertwiner_mul ℝ hf r i j)
      (ha ▸ he.star_matrixUnitIntertwiner_mul_eq_mul_star_matrixUnitIntertwiner ℝ hf r i j),
    by linarith [Units.norm_polarUnitary_sub_one_le (ha_half.trans (by norm_num)), ha ▸ hz_le]⟩
/-- **Unitary conjugacy of nearby matrix-unit systems in a closed unital `𝕜'`-`⋆`-subalgebra**
(`‖f r i j - e r i j‖ ≤ δ`, `6 * (∑ r, card (n r)) * δ ≤ 1`), with `u ∈ s`, `Joined 1 u`,
and `‖(u : A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`. -/
theorem exists_unitary_conjugate_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [SubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A] [StarMemClass S A]
    {s : S} [IsClosed (s : Set A)] (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    (he_mem : ∀ r i j, e r i j ∈ s) (hf_mem : ∀ r i j, f r i j ∈ s)
    {δ : ℝ} (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, (u : A) ∈ s ∧ Joined 1 u ∧
      (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  obtain ⟨a, ha, h⟩ := exists_polarUnitary_intertwiner he hf hsmall hdist
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜' A
  exact ⟨a.polarUnitary,
    a.polarUnitary_mem (𝕜' := ℝ) (ha ▸ matrixUnitIntertwiner_mem ℝ he_mem hf_mem), h⟩
/-- **Unitary conjugacy of nearby matrix-unit systems**: `‖f r i j - e r i j‖ ≤ δ`,
`6 * (∑ r, card (n r)) * δ ≤ 1` gives `u` with `Joined 1 u`, `‖(u : A) - 1‖ ≤ 8 * (∑ ...) * δ`. -/
theorem exists_unitary_conjugate (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    {δ : ℝ} (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, Joined 1 u ∧ (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  obtain ⟨a, -, h⟩ := exists_polarUnitary_intertwiner he hf hsmall hdist; exact ⟨a.polarUnitary, h⟩
end
/-- **Unitary conjugacy of nearby matrix-unit systems (non-unital)**: gives
`u : unitary (Unitization ℂ A)` with `fst = 1`, `Joined 1 u`, conjugating `e` to `f`. -/
theorem exists_unitization_unitary_conjugate {κ A : Type*} {n : κ → Type*} [Fintype κ]
    [∀ r, Fintype (n r)] [NonUnitalCStarAlgebra A] {e f : ∀ r : κ, n r → n r → A}
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f) {δ : ℝ}
    (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary (Unitization ℂ A), (u : Unitization ℂ A).fst = 1 ∧ Joined 1 u ∧
      (∀ r i j, (u : Unitization ℂ A) * (e r i j : Unitization ℂ A) *
        star (u : Unitization ℂ A) = (f r i j : Unitization ℂ A)) ∧
      ‖(u : Unitization ℂ A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  obtain ⟨a, ha, h⟩ := exists_polarUnitary_intertwiner (he.map ι) (hf.map ι) hsmall fun r i j ↦ by
    simpa only [ι, Unitization.inrNonUnitalStarAlgHom_apply, ← Unitization.inr_sub,
      Unitization.norm_inr] using hdist r i j
  have ha_fst : (a : Unitization ℂ A).fst = 1 := by
    rw [← Unitization.fstHom_apply ℂ A, ← AlgHom.restrictScalars_apply ℝ, ha,
      map_matrixUnitIntertwiner]; simp [ι, matrixUnitIntertwiner_def, matrixUnitSupport_def]
  exact ⟨a.polarUnitary, Units.fst_polarUnitary_eq_one ha_fst, h⟩
end TauCeti.IsMatrixUnitSystem
