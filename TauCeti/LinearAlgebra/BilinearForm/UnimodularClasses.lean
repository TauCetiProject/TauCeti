/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.RingTheory.Henselian.SquareClasses

/-!
# The two unimodular forms of each positive rank

Over a Henselian local ring with finite residue field and two invertible, choose a nonsquare
unit `u`. Every symmetric unimodular form of positive rank is isometric to exactly one of the
diagonal forms `⟨1, …, 1⟩` and `⟨1, …, 1, u⟩`. The first occurs exactly when the Gram
determinant is a square. Both forms are symmetric and unimodular and they are not isometric.
In rank zero there is instead a single form, since the space of bilinear forms is trivial.
In particular this gives exactly two integral isometry classes over `ℤ_p` in every positive
rank at an odd prime, and one in rank zero.

`TauCeti.existsUnique_equivalent_diagonal_snoc` exposes the classification
for any chosen nonsquare unit; `exists_unit_forall_existsUnique_equivalent_diagonal_snoc`
also supplies the unit, independently of the rank and the module. The Boolean selecting the
representative distinguishes the two classes.

The proof uses the rank-and-determinant classification
`LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det` and the residue square test.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Module
open LinearMap (BilinForm)

namespace TauCeti

variable {R M : Type*} [CommRing R] [HenselianLocalRing R]
  [Finite (IsLocalRing.ResidueField R)] [AddCommGroup M] [Module R M]

/-- A unit diagonal representative is isometric to a symmetric unimodular form exactly when
the product of its last entry and the Gram determinant is a square. -/
theorem equivalent_diagonal_snoc_iff (h2 : IsUnit (2 : R))
    {B : BilinForm R M} (hB : B.IsSymm) {n : ℕ} (b : Basis (Fin (n + 1)) R M)
    (hdet : IsUnit (B.toMatrix b).det) (u : Rˣ) :
    B.Equivalent (Matrix.diagonal (Fin.snoc (fun _ : Fin n ↦ (1 : R)) (u : R))).toBilin' ↔
      IsSquare ((B.toMatrix b).det * (u : R)) := by
  classical
  have hsymm : (Matrix.diagonal (Fin.snoc (fun _ : Fin n ↦ (1 : R)) (u : R))).toBilin'.IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr (Matrix.isSymm_diagonal _)
  have hd : ((Matrix.diagonal (Fin.snoc (fun _ : Fin n ↦ (1 : R))
      (u : R))).toBilin'.toMatrix (Pi.basisFun R _)).det = u := by
    simp [LinearMap.BilinForm.toMatrix_basisFun, Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simpa only [hd] using hB.equivalent_iff_isSquare_det_mul_det hsymm h2 b
    (Pi.basisFun R _) hdet (hd.symm ▸ u.isUnit)

/-- A positive-rank symmetric unimodular form is isometric to exactly one of the two unit
diagonal representatives. `false` selects determinant one and `true` a fixed nonsquare unit.
The Boolean is `false` exactly when the Gram determinant is a square. -/
theorem existsUnique_equivalent_diagonal_snoc (h2 : IsUnit (2 : R))
    {B : BilinForm R M} (hB : B.IsSymm) {n : ℕ} (b : Basis (Fin (n + 1)) R M)
    (hdet : IsUnit (B.toMatrix b).det) (u : Rˣ) (hu : ¬IsSquare (u : R)) :
    ∃! c : Bool, B.Equivalent (Matrix.diagonal
      (Fin.snoc (fun _ : Fin n ↦ (1 : R)) (if c then (u : R) else 1))).toBilin' := by
  classical
  have hfalse : B.Equivalent (Matrix.diagonal
      (Fin.snoc (fun _ : Fin n ↦ (1 : R)) (1 : R))).toBilin' ↔
      IsSquare (B.toMatrix b).det := by
    simpa using equivalent_diagonal_snoc_iff h2 hB b hdet (1 : Rˣ)
  have htrue : B.Equivalent (Matrix.diagonal
      (Fin.snoc (fun _ : Fin n ↦ (1 : R)) (u : R))).toBilin' ↔
      ¬IsSquare (B.toMatrix b).det :=
    (equivalent_diagonal_snoc_iff h2 hB b hdet u).trans
      (TauCeti.HenselianLocalRing.isSquare_mul_iff_of_not_isSquare h2 hdet u.isUnit hu)
  by_cases h : IsSquare (B.toMatrix b).det
  · refine ⟨false, hfalse.mpr h, ?_⟩
    intro c hc
    cases c
    · rfl
    · exact (htrue.mp hc h).elim
  · refine ⟨true, htrue.mpr h, ?_⟩
    intro c hc
    cases c
    · exact (h (hfalse.mp hc)).elim
    · rfl

open IsLocalRing in
/-- **Exactly two unimodular classes in every positive rank.** A single nonsquare unit gives
representatives in all positive ranks, and every symmetric form with unit Gram determinant
is isometric to exactly one of them. This applies in particular to the integers of an odd
residue characteristic local field. -/
theorem exists_unit_forall_existsUnique_equivalent_diagonal_snoc (h2 : IsUnit (2 : R)) :
    ∃ u : Rˣ, ¬IsSquare (u : R) ∧
      ∀ {n : ℕ} {M : Type*} [AddCommGroup M] [Module R M]
        (B : BilinForm R M) (_ : B.IsSymm) (b : Basis (Fin (n + 1)) R M),
        IsUnit (B.toMatrix b).det →
          ∃! c : Bool, B.Equivalent (Matrix.diagonal
            (Fin.snoc (fun _ : Fin n ↦ (1 : R)) (if c then (u : R) else 1))).toBilin' := by
  have hchar : ringChar (ResidueField R) ≠ 2 := by
    intro h
    have hne := (h2.map (residue R)).ne_zero
    rw [map_ofNat] at hne
    exact hne (by exact_mod_cast h ▸ ringChar.Nat.cast_ringChar)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  obtain ⟨r, hr⟩ := residue_surjective (R := R) a
  have hrunit : IsUnit r := (residue_ne_zero_iff_isUnit r).mp fun h0 ↦
    ha (by simp [← hr, h0])
  obtain ⟨u, rfl⟩ := hrunit
  have hu : ¬IsSquare (u : R) := fun hs ↦ ha (hr ▸ hs.map (residue R))
  exact ⟨u, hu, fun B hB b hdet ↦ existsUnique_equivalent_diagonal_snoc h2 hB b hdet u hu⟩

end TauCeti
