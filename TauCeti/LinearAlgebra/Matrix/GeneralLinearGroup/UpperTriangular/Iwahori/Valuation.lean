/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori.Basic

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Transvection
import TauCeti.RingTheory.Valuation.Basic

/-!
# Valuation characterization and normaliser of pro-`p` Iwahori subgroups

Let `K` be a field with a valuation subring `A`, and let `I₁ ⊆ GL_m(K)` be the image of the
pro-`p` Iwahori subgroup `TauCeti.iwahoriOne m A` of `GL_m(A)`. This file characterizes membership
in `I₁` through the valuation of `A` and establishes diagonal conjugation, normaliser, and
transvection membership properties:

* `TauCeti.mem_map_iwahoriOne_iff`: membership in `I₁` via entrywise valuation bounds.
* `TauCeti.diagGL_mem_map_iwahoriOne_iff`: membership of a diagonal matrix in `I₁`.
* `TauCeti.diagGL_mul_mul_inv_mem_map_iwahoriOne_of_isUpperTriangular` and
  `TauCeti.diagGL_inv_mul_mul_mem_map_iwahoriOne_of_isLowerTriangular`: conjugation of upper- and
  lower-triangular elements of `I₁` by dominant diagonal matrices.
* `ValuationSubring.valuation_diag_eq_one_of_mem_map_iwahoriOne`: every diagonal entry of `g ∈ I₁`
  has valuation `1`.
* `ValuationSubring.diagGL_mem_normalizer_map_iwahoriOne`: diagonal matrices whose entries share a
  common valuation normalise `I₁`.
* `ValuationSubring.transvectionUnit_mem_map_iwahoriOne_iff`: a transvection `1 + c E_{ij}`
  (`i ≠ j`) lies in `I₁` iff `v(c) ≤ 1` when `i < j`, and `v(c) < 1` when `j < i`.

## References

* Adapted from `src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.v_diag_eq_one_of_mem_proIwahori`, `New.diagGL_conj_mem_proIwahori_of_v_eq_one`, and
  `New.transvectionGL_mem_proIwahori`.
-/

public section

namespace TauCeti

open Matrix

variable {K : Type*} [Field K] (A : ValuationSubring K) {m : Type*} [Fintype m] [LinearOrder m]

/-- **Membership in the pro-`p` Iwahori subgroup of `GL_m(K)`.** An invertible matrix over `K`
comes from the pro-`p` Iwahori subgroup of `GL_m(𝒪)` exactly when all its entries are integral,
its entries below the diagonal lie in the maximal ideal, and its diagonal entries are congruent
to `1` modulo the maximal ideal, all measured by the valuation of `𝒪`. -/
theorem mem_map_iwahoriOne_iff {g : GL m K} :
    g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ↔
      (∀ i j, A.valuation (g i j) ≤ 1) ∧ (∀ ⦃i j⦄, j < i → A.valuation (g i j) < 1) ∧
        ∀ i, A.valuation (g i i - 1) < 1 := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hklow, hkdiag⟩ := mem_upperUnitriangularCongruenceSubgroup_iff.mp hk
    refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
    · rw [GeneralLinearGroup.map_apply]
      exact A.valuation_le_one _
    · rw [GeneralLinearGroup.map_apply]
      exact (A.valuation_lt_one_iff _).mp (hklow hji)
    · rw [GeneralLinearGroup.map_apply, ← map_one (algebraMap A K), ← map_sub]
      exact (A.valuation_lt_one_iff _).mp (hkdiag i)
  · rintro ⟨h1, hlow, hdiag⟩
    let M : Matrix m m A := of fun i j ↦ ⟨g i j, (A.valuation_le_one_iff _).mp (h1 i j)⟩
    have hlowM : ∀ ⦃i j⦄, j < i → M i j ∈ IsLocalRing.maximalIdeal A := fun _ _ hji ↦
      (A.valuation_lt_one_iff _).mpr (hlow hji)
    have hdiagM : ∀ i, M i i - 1 ∈ IsLocalRing.maximalIdeal A := fun i ↦
      (A.valuation_lt_one_iff _).mpr (hdiag i)
    -- Modulo the maximal ideal, `M` is upper unitriangular, so its determinant is a unit.
    have hdet : IsUnit M.det := by
      refine isUnit_det_of_isUpperTriangular_map (f := IsLocalRing.residue A)
        (fun _ _ hji ↦ (IsLocalRing.residue_eq_zero_iff _).mpr (hlowM hji)) fun i ↦ ?_
      have hdiag_res : IsLocalRing.residue A (M i i) = 1 := by
        simpa [sub_eq_zero] using (IsLocalRing.residue_eq_zero_iff _).mpr (hdiagM i)
      simp [hdiag_res]
    refine ⟨GeneralLinearGroup.mk'' M hdet, ?_, ?_⟩
    · exact mem_upperUnitriangularCongruenceSubgroup_iff.mpr ⟨hlowM, hdiagM⟩
    · ext i j
      rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.val_mk'']
      simp [M, ValuationSubring.algebraMap_apply]

/-- A diagonal matrix lies in the pro-`p` Iwahori subgroup of `GL m K` exactly when every diagonal
entry satisfies `v (t i - 1) < 1`. -/
theorem diagGL_mem_map_iwahoriOne_iff {t : m → Kˣ} :
    diagGL t ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ↔
      ∀ i : m, A.valuation ((t i : K) - 1) < 1 := by
  rw [mem_map_iwahoriOne_iff]
  constructor
  · rintro ⟨-, -, hdiag⟩
    simpa [diagGL_coe] using hdiag
  · intro hdiag
    refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ by simpa [diagGL_coe] using hdiag i⟩
    · simp only [diagGL_coe, diagonal_apply]
      split_ifs with hij
      · subst hij
        have h1 : A.valuation ((t i : K) - 1 + 1) = A.valuation (1 : K) :=
          Valuation.map_add_eq_of_lt_right A.valuation (by simpa using hdiag i)
        simpa using h1.le
      · simp
    · simp [hji.ne']

/-- Conjugating an upper-triangular element of `I₁` by a dominant diagonal matrix keeps it in
`I₁`. -/
theorem diagGL_mul_mul_inv_mem_map_iwahoriOne_of_isUpperTriangular {t : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K)) {u : GL m K}
    (hu : u ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)))
    (hutri : (u : Matrix m m K).IsUpperTriangular) :
    diagGL t * u * (diagGL t)⁻¹ ∈
      (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) := by
  obtain ⟨h1, -, hdiag⟩ := (mem_map_iwahoriOne_iff A).mp hu
  rw [mem_map_iwahoriOne_iff]
  refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · rw [diagGL_mul_mul_inv_apply]
    rcases lt_or_ge j i with hji | hij
    · simp [hutri hji]
    · rw [Units.val_inv_eq_inv_val]
      exact (A.valuation.map_mul_mul_inv_le (ht hij)).trans (h1 i j)
  · rw [diagGL_mul_mul_inv_apply, hutri hji]
    simp
  · rw [diagGL_mul_mul_inv_apply]
    simpa [mul_comm, mul_assoc] using hdiag i

/-- Conjugating a lower-triangular element of `I₁` by the inverse of a dominant diagonal matrix
keeps it in `I₁`. -/
theorem diagGL_inv_mul_mul_mem_map_iwahoriOne_of_isLowerTriangular {t : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K)) {l : GL m K}
    (hl : l ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)))
    (hltri : (l : Matrix m m K).IsLowerTriangular) :
    (diagGL t)⁻¹ * l * diagGL t ∈
      (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) := by
  obtain ⟨h1, hlow, hdiag⟩ := (mem_map_iwahoriOne_iff A).mp hl
  have hinv : (diagGL t)⁻¹ = diagGL t⁻¹ := (map_inv diagGL t).symm
  rw [hinv, show diagGL t = (diagGL t⁻¹)⁻¹ by simp, mem_map_iwahoriOne_iff]
  have hstep (i j : m) (hji : j ≤ i) :
      A.valuation (((t⁻¹ i : Kˣ) : K) * l i j * ((t⁻¹ j)⁻¹ : Kˣ)) ≤ A.valuation (l i j) := by
    have heq : ((t⁻¹ i : Kˣ) : K) * l i j * ((t⁻¹ j)⁻¹ : Kˣ) = (t j : K) * l i j * (t i : K)⁻¹ := by
      simp [Pi.inv_apply, Units.val_inv_eq_inv_val]
      ring
    rw [heq]
    exact A.valuation.map_mul_mul_inv_le (ht hji)
  refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · rw [diagGL_mul_mul_inv_apply]
    rcases lt_or_ge i j with hij | hji
    · simp [hltri hij]
    · exact (hstep i j hji).trans (h1 i j)
  · rw [diagGL_mul_mul_inv_apply]
    exact (hstep i j hji.le).trans_lt (hlow hji)
  · rw [diagGL_mul_mul_inv_apply]
    simpa [Pi.inv_apply, Units.val_inv_eq_inv_val, mul_comm, mul_assoc] using hdiag i

/-- Every diagonal entry of an element of the pro-`p` Iwahori subgroup `I₁ ⊆ GL_m(K)` has
valuation `1`. -/
theorem _root_.ValuationSubring.valuation_diag_eq_one_of_mem_map_iwahoriOne {g : GL m K}
    (hg : g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K))) (i : m) :
    A.valuation (g i i) = 1 := by
  have hlt : A.valuation (g i i - 1) < A.valuation (1 : K) := by
    simpa only [map_one] using ((mem_map_iwahoriOne_iff A).mp hg).2.2 i
  simpa only [sub_add_cancel, map_one] using Valuation.map_add_eq_of_lt_right A.valuation hlt

/-- A diagonal matrix whose entries all have the same valuation normalises the pro-`p` Iwahori
subgroup `I₁ ⊆ GL_m(K)`. -/
theorem _root_.ValuationSubring.diagGL_mem_normalizer_map_iwahoriOne {t : m → Kˣ}
    (ht : ∀ i j : m, A.valuation (t i : K) = A.valuation (t j : K)) :
    diagGL t ∈ Subgroup.normalizer
      ((iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) : Set (GL m K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hval (i j : m) :
      A.valuation (((diagGL t * g * (diagGL t)⁻¹ : GL m K) : Matrix m m K) i j) =
        A.valuation (g i j) := by
    rw [diagGL_mul_mul_inv_apply]
    have hne : A.valuation (t j : K) ≠ 0 := A.valuation.ne_zero_iff.mpr (t j).ne_zero
    simp [Units.val_inv_eq_inv_val, ht i j, mul_right_comm, hne]
  have hdiag (i : m) :
      ((diagGL t * g * (diagGL t)⁻¹ : GL m K) : Matrix m m K) i i = g i i := by
    rw [diagGL_mul_mul_inv_apply, mul_right_comm, Units.mul_inv, one_mul]
  simp only [mem_map_iwahoriOne_iff, hval, hdiag]

/-- A transvection `1 + c E_{ij}` (`i ≠ j`) lies in the pro-`p` Iwahori subgroup `I₁ ⊆ GL_m(K)`
iff `A.valuation c ≤ 1` when `i < j` and `A.valuation c < 1` when `j < i`. -/
@[simp]
theorem _root_.ValuationSubring.transvectionUnit_mem_map_iwahoriOne_iff {i j : m} (hij : i ≠ j)
    (c : K) :
    transvectionUnit hij c ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ↔
      (i < j ∧ A.valuation c ≤ 1) ∨ (j < i ∧ A.valuation c < 1) := by
  constructor
  · intro hg
    obtain ⟨h1, hlow, -⟩ := (mem_map_iwahoriOne_iff A).mp hg
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Or.inl ⟨hlt, by simpa [coe_transvectionUnit_eq_one_add_single, hij] using h1 i j⟩
    · exact Or.inr ⟨hgt, by simpa [coe_transvectionUnit_eq_one_add_single, hij] using hlow hgt⟩
  · rintro (⟨hlt, hc⟩ | ⟨-, hc⟩)
    · let a : A := ⟨c, (A.valuation_le_one_iff c).mp hc⟩
      refine ⟨transvectionUnit hij a, ?_, map_transvectionUnit (algebraMap A K) hij a⟩
      rw [SetLike.mem_coe, ← comap_generalLinearGroupMap_residue_upperUnitriangularGroup,
        Subgroup.mem_comap, map_transvectionUnit]
      exact transvectionUnit_mem_upperUnitriangularGroup hlt _
    · let a : A := ⟨c, (A.valuation_le_one_iff c).mp hc.le⟩
      refine ⟨transvectionUnit hij a, ?_, map_transvectionUnit (algebraMap A K) hij a⟩
      rw [SetLike.mem_coe, ← comap_generalLinearGroupMap_residue_upperUnitriangularGroup,
        Subgroup.mem_comap, map_transvectionUnit]
      have ha : IsLocalRing.residue A a = 0 :=
        (IsLocalRing.residue_eq_zero_iff a).mpr ((A.valuation_lt_one_iff a).mpr hc)
      rw [ha, transvectionUnit_zero]
      exact one_mem _

end TauCeti
