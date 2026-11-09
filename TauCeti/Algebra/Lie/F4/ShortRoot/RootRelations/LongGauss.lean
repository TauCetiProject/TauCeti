/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.Matrix.Step

/-!
# Opposite long-root Gauss relations in the short-root F₄ carrier

At either long simple node, multiplication of opposite root points admits the rank-one
Gauss factorization wherever `1 + a * b` is a unit. The torus factor is the simple coroot,
in fundamental-weight coordinates. Both multiplication orders are given over every
commutative ring, including nonreduced rings and rings of characteristic two.

The proof uses the integral raising and lowering tables of
`TauCeti.F4ShortRoot.raisingMatrix` and `TauCeti.F4ShortRoot.loweringMatrix`.
Their long-root strings have length at most one. A finite certificate records the six
possible matrix-entry patterns, leaving only the scalar unit identities to check.
No identification of the carrier with an independently pinned reductive group is asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open DynkinType

universe v

-- The five entries are those of `1`, `E`, `F`, `EF`, and `FE`. Products are
-- evaluated by the existing step-matrix rule, rather than by a 26-term sum.
private def longGaussEntryData (i : Fin 2) (r c : Fin 26) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  (if r = c then 1 else 0,
    if r = raisingTarget (i.castAdd 2) c then raisingCoeff (i.castAdd 2) c else 0,
    if r = loweringTarget (i.castAdd 2) c then loweringCoeff (i.castAdd 2) c else 0,
    if r = raisingTarget (i.castAdd 2) (loweringTarget (i.castAdd 2) c) then
      raisingCoeff (i.castAdd 2) (loweringTarget (i.castAdd 2) c) *
        loweringCoeff (i.castAdd 2) c else 0,
    if r = loweringTarget (i.castAdd 2) (raisingTarget (i.castAdd 2) c) then
      loweringCoeff (i.castAdd 2) (raisingTarget (i.castAdd 2) c) *
        raisingCoeff (i.castAdd 2) c else 0)

private theorem longGaussEntryData_cases (i : Fin 2) (r c : Fin 26) :
    longGaussEntryData i r c = (0, 0, 0, 0, 0) ∨
    (longGaussEntryData i r c = (1, 0, 0, 0, 0) ∧ f4ShortRootWeight c (i.castAdd 2) = 0) ∨
    (longGaussEntryData i r c = (1, 0, 0, 1, 0) ∧ f4ShortRootWeight c (i.castAdd 2) = 1) ∨
    (longGaussEntryData i r c = (1, 0, 0, 0, 1) ∧ f4ShortRootWeight c (i.castAdd 2) = -1 ∧
      f4ShortRootWeight (raisingTarget (i.castAdd 2) c) (i.castAdd 2) = 1) ∨
    (longGaussEntryData i r c = (0, 1, 0, 0, 0) ∧ f4ShortRootWeight r (i.castAdd 2) = 1) ∨
    (longGaussEntryData i r c = (0, 0, 1, 0, 0) ∧ f4ShortRootWeight c (i.castAdd 2) = 1) := by
  let : DecidableEq (ℤ × ℤ × ℤ × ℤ × ℤ) := inferInstance
  fin_cases i <;> fin_cases r <;> revert c <;> decide

private theorem longGaussEntry (i : Fin 2) (r c : Fin 26)
    {A : Type v} [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    let d := longGaussEntryData i r c
    (d.1 : A) + a * (d.2.1 : A) +
        (b * (d.2.2.1 : A) + (b * a) * (d.2.2.2.1 : A)) =
      ((u ^ f4ShortRootWeight c (i.castAdd 2) : Aˣ) : A) * (d.1 : A) +
        (b * ↑u⁻¹) * ((d.2.2.1 : A) *
          ((u ^ f4ShortRootWeight c (i.castAdd 2) : Aˣ) : A)) +
        ((a * ↑u⁻¹) * (((u ^ f4ShortRootWeight r (i.castAdd 2) : Aˣ) : A) *
          (d.2.1 : A)) +
        ((a * ↑u⁻¹) * (b * ↑u⁻¹)) *
          (((u ^ f4ShortRootWeight (raisingTarget (i.castAdd 2) c) (i.castAdd 2) : Aˣ) : A) *
            (d.2.2.2.2 : A))) := by
  have hscale (x : A) : (x * ↑u⁻¹) * (u : A) = x := by
    rw [mul_assoc, u.inv_mul, mul_one]
  have hdiag : (↑u⁻¹ : A) + ((a * ↑u⁻¹) * (b * ↑u⁻¹)) * (u : A) = 1 := by
    calc
      _ = (↑u⁻¹ : A) + (a * b * ↑u⁻¹) * ((↑u⁻¹ : A) * ↑u) := by ring
      _ = (1 + a * b) * (↑u⁻¹ : A) := by rw [u.inv_mul]; ring
      _ = 1 := by rw [← hu, u.mul_inv]
  dsimp only
  rcases longGaussEntryData_cases i r c with h | ⟨h, hc⟩ | ⟨h, hc⟩ |
    ⟨h, hc, he⟩ | ⟨h, hr⟩ | ⟨h, hc⟩
  · simp only [h, Int.cast_zero, mul_zero, zero_mul, add_zero]
  · simp only [h, hc, zpow_zero, Units.val_one, Int.cast_zero, Int.cast_one,
      mul_zero, mul_one, add_zero]
  · simpa only [h, hc, zpow_one, Int.cast_zero, Int.cast_one,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, mul_comm b a] using hu.symm
  · simpa only [h, hc, he, zpow_neg_one, zpow_one, Int.cast_zero, Int.cast_one,
      mul_zero, zero_mul, mul_one, add_zero, zero_add] using hdiag.symm
  · simpa only [h, hr, zpow_one, Int.cast_zero, Int.cast_one,
      mul_zero, zero_mul, mul_one, add_zero, zero_add] using (hscale a).symm
  · simpa only [h, hc, zpow_one, Int.cast_zero, Int.cast_one,
      mul_zero, mul_one, one_mul, add_zero, zero_add] using (hscale b).symm

private theorem longGaussMatrix (i : Fin 2) {A : Type v} [CommRing A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    let E := (raisingMatrix (i.castAdd 2)).map (Int.castRingHom A)
    let F := (loweringMatrix (i.castAdd 2)).map (Int.castRingHom A)
    let D := Matrix.diagonal fun c => ((u ^ f4ShortRootWeight c (i.castAdd 2) : Aˣ) : A)
    (1 + a • E) * (1 + b • F) =
      (1 + (b * ↑u⁻¹) • F) * D * (1 + (a * ↑u⁻¹) • E) := by
  let E : Matrix (Fin 26) (Fin 26) A :=
    (raisingMatrix (i.castAdd 2)).map (Int.castRingHom A)
  let F : Matrix (Fin 26) (Fin 26) A :=
    (loweringMatrix (i.castAdd 2)).map (Int.castRingHom A)
  let d (c : Fin 26) : A := ↑(u ^ f4ShortRootWeight c (i.castAdd 2))
  -- Name exactly the three matrices in the displayed factorization, for the entry calculations.
  change (1 + a • E) * (1 + b • F) =
    (1 + (b * ↑u⁻¹) • F) * Matrix.diagonal d * (1 + (a * ↑u⁻¹) • E)
  have hE : E.IsStep (raisingTarget (i.castAdd 2))
      (fun c => (raisingCoeff (i.castAdd 2) c : A)) :=
    (Matrix.isStep_of_apply (raisingMatrix_apply (i.castAdd 2))).map
      (Int.castRingHom A) (map_zero _)
  have hF : F.IsStep (loweringTarget (i.castAdd 2))
      (fun c => (loweringCoeff (i.castAdd 2) c : A)) :=
    (Matrix.isStep_of_apply (loweringMatrix_apply (i.castAdd 2))).map
      (Int.castRingHom A) (map_zero _)
  have hD (r c : Fin 26) : Matrix.diagonal d r c =
      d c * (longGaussEntryData i r c).1 := by
    -- The first coordinate records the identity entry, so only the diagonal indicator remains.
    change Matrix.diagonal d r c = d c * ((if r = c then 1 else 0 : ℤ) : A)
    rw [Matrix.diagonal_apply]
    by_cases h : r = c
    · subst r
      simp only [ite_true, Int.cast_one, mul_one]
    · simp only [h, ite_false, Int.cast_zero, mul_zero]
  have hEF (r c : Fin 26) : (E * F) r c = (longGaussEntryData i r c).2.2.2.1 := by
    rw [(hE.mul hF).apply]
    simp only [longGaussEntryData, Function.comp_apply, Int.cast_ite, Int.cast_mul, Int.cast_zero]
  have hFDE (r c : Fin 26) : (F * Matrix.diagonal d * E) r c =
      d (raisingTarget (i.castAdd 2) c) * (longGaussEntryData i r c).2.2.2.2 := by
    rw [((hF.mul (Matrix.isStep_diagonal d)).mul hE).apply]
    simp only [longGaussEntryData, Function.comp_apply, id_eq, Int.cast_ite,
      Int.cast_mul, Int.cast_zero]
    split_ifs
    · rw [mul_comm (↑(loweringCoeff (i.castAdd 2) (raisingTarget (i.castAdd 2) c)) : A)
        (d (raisingTarget (i.castAdd 2) c)), mul_assoc]
    · exact (mul_zero _).symm
  have hI (r c : Fin 26) : (1 : Matrix (Fin 26) (Fin 26) A) r c =
      (longGaussEntryData i r c).1 := by
    simp only [Matrix.one_apply, longGaussEntryData, Int.cast_ite, Int.cast_one, Int.cast_zero]
  have hEin (r c : Fin 26) : E r c = (longGaussEntryData i r c).2.1 := by
    simp only [E, Matrix.map_apply, Int.coe_castRingHom, raisingMatrix_apply,
      longGaussEntryData, Int.cast_ite, Int.cast_zero]
  have hFin (r c : Fin 26) : F r c = (longGaussEntryData i r c).2.2.1 := by
    simp only [F, Matrix.map_apply, Int.coe_castRingHom, loweringMatrix_apply,
      longGaussEntryData, Int.cast_ite, Int.cast_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext r c
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul,
    Matrix.mul_diagonal, hEF, hFDE, hD, hI, hEin, hFin]
  exact longGaussEntry i r c a b u hu

/-- At a long simple node, the positive-negative product has the lower-torus-upper
Gauss factorization. Only `1 + a * b`, not either root parameter, must be a unit. -/
theorem rootSubgroupPoints_inl_mul_inr_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2)
    {A : Type v} [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl_of_lt_two i hi,
    coe_rootSubgroupPoints_inr_of_lt_two i hi, toAdd_ofAdd,
    coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe, torusCharacter_mulSingle]
  -- The certificate uses `Fin 2`; its embedding into `Fin 4` is exactly the long-node inclusion.
  exact longGaussMatrix ⟨i.val, hi⟩ a b u hu

/-- At a long simple node, the negative-positive product has the upper-torus-lower
Gauss factorization, with the inverse simple-coroot torus factor. -/
theorem rootSubgroupPoints_inr_mul_inl_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2)
    {A : Type v} [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  have h := rootSubgroupPoints_inl_mul_inr_of_lt_two i hi (-a) (-b) u
    (by simpa only [neg_mul_neg] using hu)
  simpa only [mul_inv_rev, ← map_inv, ← ofAdd_neg, neg_mul, neg_neg,
    ← Pi.mulSingle_inv, mul_assoc] using congrArg Inv.inv h

end TauCeti.F4ShortRoot
