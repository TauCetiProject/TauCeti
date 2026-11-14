/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.MatrixUnits
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar

/-!
# Unitary conjugacy of nearby systems of matrix units in a C⋆-algebra

To show that nearby embeddings of a finite-dimensional C⋆-algebra `⨁ᵣ M_{n(r)}(ℂ)` into an ambient
C⋆-algebra are inner-conjugate—a key step in Bratteli's local characterization of AF algebras and
in uniqueness of inductive-limit maps—one compares two finite multi-block systems of matrix units
`e, f` of the same shape via the averaging intertwiner `matrixUnitIntertwiner ℂ e f`.

In any C⋆-algebra, partial isometry entries have norm at most `1`, so entrywise closeness
`‖f r i j - e r i j‖ ≤ δ` forces `‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r, card (n r)) * δ`.
When `6 * (∑ r, card (n r)) * δ ≤ 1`, this intertwiner lies within `1 / 3` of `1` and is therefore
invertible; passing to its polar unitary `u = z.polarUnitary` produces a unitary `u` close to `1`
(`‖(u : A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`) in the path component of `1` (`Joined 1 u`) that
conjugates `e` entrywise to `f`, preserves any closed unital `ℂ`-`⋆`-subalgebra containing `e` and
`f`, and in `Unitization ℂ A` has scalar part `(u : Unitization ℂ A).fst = 1`.

## Main results

* `TauCeti.IsMatrixUnitSystem.norm_matrixUnitIntertwiner_sub_one_le`: quantitative distance of
  `matrixUnitIntertwiner ℂ e f` to `1`.
* `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate_mem`,
  `TauCeti.IsMatrixUnitSystem.exists_unitary_conjugate`,
  `TauCeti.IsMatrixUnitSystem.exists_unitization_unitary_conjugate`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge Univ. Press (1998),
  Chapter III, §7.
-/

public section

namespace TauCeti.IsMatrixUnitSystem

section Unital

variable {κ A : Type*} {n : κ → Type*} [Fintype κ] [∀ r, Fintype (n r)] [CStarAlgebra A]
  {e f : ∀ r : κ, n r → n r → A}

/-- Quantitative estimate `‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r, card (n r)) * δ` whenever
`e` is a system of matrix units and `‖f r i j - e r i j‖ ≤ δ` for all `r, i, j`. -/
theorem norm_matrixUnitIntertwiner_sub_one_le (he : IsMatrixUnitSystem e)
    {δ : ℝ} (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ‖matrixUnitIntertwiner ℂ e f - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  rw [← he.matrixUnitIntertwiner_self (𝕜 := ℂ), matrixUnitIntertwiner_def,
    matrixUnitIntertwiner_def, add_sub_add_comm, ← sub_mul,
    show (1 - matrixUnitSupport f) - (1 - matrixUnitSupport e) =
      matrixUnitSupport e - matrixUnitSupport f by abel]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, ← sub_mul]
  refine (norm_add_le _ _).trans ?_
  have hpart1 : ‖(matrixUnitSupport e - matrixUnitSupport f) * (1 - matrixUnitSupport e)‖ ≤
      (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
    refine (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (he.isStarProjection_support.one_sub.norm_le _)).trans ?_)
    simp only [matrixUnitSupport_def, ← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦
      (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦
        (norm_sub_rev (e r i i) (f r i i)).le.trans (hdist r i i)).trans (by simp)
  have hpart2 : ‖∑ r : κ, (Fintype.card (n r) : ℂ)⁻¹ •
      ∑ a : n r, ∑ b : n r, (f r a b - e r a b) * e r b a‖ ≤
      (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ ↦ ?_
    by_cases hcard : Fintype.card (n r) = 0
    · simp [hcard]
    · have hpos : (0 : ℝ) < Fintype.card (n r) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
      rw [norm_smul, norm_inv, Complex.norm_natCast,
        ← inv_mul_cancel_left₀ hpos.ne' ((Fintype.card (n r) : ℝ) * δ)]
      gcongr
      have hb (a b : n r) : ‖(f r a b - e r a b) * e r b a‖ ≤ δ :=
        (norm_mul_le _ _).trans <|
          (mul_le_of_le_one_right (norm_nonneg _) (he.isPartialIsometry r b a).norm_le_one).trans
            (hdist r a b)
      exact (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun a _ ↦
        (norm_sum_le _ _).trans <| Finset.sum_le_sum fun b _ ↦ hb a b).trans (by simp)
  linarith

/-- **Unitary conjugacy of nearby systems of matrix units in a closed unital `ℂ`-`⋆`-subalgebra**:
if finite systems `e, f` in `s` satisfy `‖f r i j - e r i j‖ ≤ δ` with
`6 * (∑ r, card (n r)) * δ ≤ 1`, there exists `u : unitary A` with `(u : A) ∈ s`, `Joined 1 u`,
`(u : A) * e r i j * star (u : A) = f r i j` for all `r, i, j`, and
`‖(u : A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`. -/
theorem exists_unitary_conjugate_mem {S : Type*} [SetLike S A] [SubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    (he_mem : ∀ r i j, e r i j ∈ s) (hf_mem : ∀ r i j, f r i j ∈ s)
    {δ : ℝ} (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, (u : A) ∈ s ∧ Joined 1 u ∧
      (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  set z : A := matrixUnitIntertwiner ℂ e f
  have hz_le : ‖z - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ :=
    he.norm_matrixUnitIntertwiner_sub_one_le hdist
  have hz_third : ‖z - 1‖ ≤ 1 / 3 := by linarith
  have hz_unit : IsUnit z := sub_sub_cancel 1 z ▸
    isUnit_one_sub_of_norm_lt_one (show ‖1 - z‖ < 1 by rw [norm_sub_rev]; linarith)
  set a : Aˣ := hz_unit.unit
  have ha_val : (a : A) = z := IsUnit.unit_spec hz_unit
  have ha_third : ‖(a : A) - 1‖ ≤ 1 / 3 := ha_val ▸ hz_third
  exact ⟨a.polarUnitary,
    a.polarUnitary_mem (𝕜' := ℂ) (ha_val ▸ matrixUnitIntertwiner_mem ℂ he_mem hf_mem),
    Units.joined_one_polarUnitary (ha_third.trans (by norm_num)),
    fun r i j ↦ a.conjugate_polarUnitary
      (by rw [ha_val]; exact he.mul_matrixUnitIntertwiner_eq_matrixUnitIntertwiner_mul ℂ hf r i j)
      (by rw [ha_val]
          exact he.star_matrixUnitIntertwiner_mul_eq_mul_star_matrixUnitIntertwiner ℂ hf r i j),
    by linarith [Units.norm_polarUnitary_sub_one_le (ha_third.trans (by norm_num)),
      ha_val ▸ hz_le]⟩

/-- **Unitary conjugacy of nearby systems of matrix units** in a unital C⋆-algebra: if finite
systems `e, f` satisfy `‖f r i j - e r i j‖ ≤ δ` with `6 * (∑ r, card (n r)) * δ ≤ 1`, there exists
`u : unitary A` with `Joined 1 u`, `(u : A) * e r i j * star (u : A) = f r i j` for all `r, i, j`,
and `‖(u : A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`. -/
theorem exists_unitary_conjugate (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f)
    {δ : ℝ} (hsmall : 6 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ ≤ 1)
    (hdist : ∀ r i j, ‖f r i j - e r i j‖ ≤ δ) :
    ∃ u : unitary A, Joined 1 u ∧ (∀ r i j, (u : A) * e r i j * star (u : A) = f r i j) ∧
      ‖(u : A) - 1‖ ≤ 8 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ := by
  have : IsClosed ((⊤ : StarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨u, -, hjoined, hconj, hnorm⟩ :=
    he.exists_unitary_conjugate_mem (s := (⊤ : StarSubalgebra ℂ A)) hf
      (fun _ _ _ ↦ trivial) (fun _ _ _ ↦ trivial) hsmall hdist
  exact ⟨u, hjoined, hconj, hnorm⟩

end Unital

/-- **Unitary conjugacy of nearby systems of matrix units in a non-unital C⋆-algebra**: if finite
systems `e, f` in a non-unital C⋆-algebra `A` satisfy `‖f r i j - e r i j‖ ≤ δ` with
`6 * (∑ r, card (n r)) * δ ≤ 1`, there exists `u : unitary (Unitization ℂ A)` with
`(u : Unitization ℂ A).fst = 1`, `Joined 1 u`,
`(u : Unitization ℂ A) * e r i j * star (u : Unitization ℂ A) = f r i j` for all `r, i, j`, and
`‖(u : Unitization ℂ A) - 1‖ ≤ 8 * (∑ r, card (n r)) * δ`. -/
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
  set e' : ∀ r : κ, n r → n r → Unitization ℂ A := fun r i j ↦ e r i j
  set f' : ∀ r : κ, n r → n r → Unitization ℂ A := fun r i j ↦ f r i j
  have he' : IsMatrixUnitSystem e' := he.map ι
  have hf' : IsMatrixUnitSystem f' := hf.map ι
  have hdist' : ∀ r i j, ‖f' r i j - e' r i j‖ ≤ δ := fun r i j ↦ by
    simpa only [e', f', ← Unitization.inr_sub, Unitization.norm_inr] using hdist r i j
  set z : Unitization ℂ A := matrixUnitIntertwiner ℂ e' f'
  have hz_le : ‖z - 1‖ ≤ 2 * (∑ r : κ, (Fintype.card (n r) : ℝ)) * δ :=
    he'.norm_matrixUnitIntertwiner_sub_one_le hdist'
  have hz_third : ‖z - 1‖ ≤ 1 / 3 := by linarith
  have hz_unit : IsUnit z := sub_sub_cancel 1 z ▸
    isUnit_one_sub_of_norm_lt_one (show ‖1 - z‖ < 1 by rw [norm_sub_rev]; linarith)
  set a : (Unitization ℂ A)ˣ := hz_unit.unit
  have ha_val : (a : Unitization ℂ A) = z := IsUnit.unit_spec hz_unit
  have ha_third : ‖(a : Unitization ℂ A) - 1‖ ≤ 1 / 3 := ha_val ▸ hz_third
  have ha_fst : (a : Unitization ℂ A).fst = 1 := by
    have he0 : (fun r i j ↦ Unitization.fstHom ℂ A (e' r i j)) = 0 := by ext; simp [e']
    have hf0 : (fun r i j ↦ Unitization.fstHom ℂ A (f' r i j)) = 0 := by ext; simp [f']
    rw [ha_val, ← Unitization.fstHom_apply ℂ A, map_matrixUnitIntertwiner, he0, hf0]
    simp
  exact ⟨a.polarUnitary, Units.fst_polarUnitary ha_fst,
    Units.joined_one_polarUnitary (ha_third.trans (by norm_num)),
    fun r i j ↦ a.conjugate_polarUnitary
      (by rw [ha_val]
          exact he'.mul_matrixUnitIntertwiner_eq_matrixUnitIntertwiner_mul ℂ hf' r i j)
      (by rw [ha_val]
          exact he'.star_matrixUnitIntertwiner_mul_eq_mul_star_matrixUnitIntertwiner ℂ hf' r i j),
    by linarith [Units.norm_polarUnitary_sub_one_le (ha_third.trans (by norm_num)),
      ha_val ▸ hz_le]⟩

end TauCeti.IsMatrixUnitSystem
