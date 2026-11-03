/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The triple-bond commutator on the short-root G₂ module

Compute the commutator of the two positive numbered simple-root subgroups on the integral
seven-dimensional module. The formula retains the mixed terms of degrees two through five,
including the quadratic divided-power contribution of the short root. It supplies an explicit
matrix identity for collecting these root elements without inverting two or three.

All identities hold over arbitrary commutative rings, including nonreduced rings. The integral
toral closure is not identified here with the pinned simply connected group scheme of type G₂;
transfer to that group requires such an identification.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The normalization uses the matrices in `TauCeti.Algebra.Lie.G2.ShortRoot.Basic` and the
root-subgroup formulas in `TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

open scoped Matrix commutatorElement
open Multiplicative

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

private def shortMatrix {A : Type v} [CommRing A] (t : A) : Matrix (Fin 7) (Fin 7) A :=
  !![1, t, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 2 * t, t ^ 2, 0, 0;
     0, 0, 0, 1, t, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, t;
     0, 0, 0, 0, 0, 0, 1]

private def longMatrix {A : Type v} [CommRing A] (t : A) : Matrix (Fin 7) (Fin 7) A :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, t, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, t, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

private def collectedMatrix {A : Type v} [CommRing A] (a b : A) : Matrix (Fin 7) (Fin 7) A :=
  !![1, 0, a * b, -2 * a ^ 2 * b, a ^ 3 * b, -a ^ 3 * b ^ 2, 0;
     0, 1, 0, -2 * a * b, a ^ 2 * b, -a ^ 2 * b ^ 2, 0;
     0, 0, 1, 0, 0, a ^ 2 * b, -a ^ 3 * b;
     0, 0, 0, 1, 0, a * b, -a ^ 2 * b;
     0, 0, 0, 0, 1, 0, -a * b;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

-- Row-sized certificates keep the finite matrix calculation within the elaboration budget.
local macro "collection_row" : tactic =>
  `(tactic| (ext c; fin_cases c <;>
    simp [collectedMatrix, shortMatrix, longMatrix, Matrix.mul_apply, Fin.sum_univ_succ]))

private theorem collectionRow0 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 0 =
      (shortMatrix a * longMatrix b) 0 := by
  have h3 : a * b * (2 * a) + -(2 * a ^ 2 * b) = 0 := by ring
  have h4 : a * b * a ^ 2 + (-(2 * a ^ 2 * b * a) + a ^ 3 * b) = 0 := by ring
  have h5 : a ^ 3 * b * b + -(a ^ 3 * b ^ 2) = 0 := by ring
  collection_row
  · exact h3
  · exact h4
  · exact h5
  · rw [h5, zero_mul]

private theorem collectionRow1 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 1 =
      (shortMatrix a * longMatrix b) 1 := by
  have h3 : b * (2 * a) + -(2 * a * b) = 0 := by ring
  have h4 : b * a ^ 2 + (-(2 * a * b * a) + a ^ 2 * b) = 0 := by ring
  have h5 : a ^ 2 * b * b + -(a ^ 2 * b ^ 2) = 0 := by ring
  collection_row
  · exact h3
  · exact h4
  · exact h5
  · rw [h5, zero_mul]

private theorem collectionRow2 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 2 =
      (shortMatrix a * longMatrix b) 2 := by
  have h6 : a ^ 2 * b * a + -(a ^ 3 * b) = 0 := by ring
  collection_row
  exact h6

private theorem collectionRow3 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 3 =
      (shortMatrix a * longMatrix b) 3 := by
  have h6 : a * b * a + -(a ^ 2 * b) = 0 := by ring
  collection_row
  exact h6

private theorem collectionRow4 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 4 =
      (shortMatrix a * longMatrix b) 4 := by
  have h6 : b * a + -(a * b) = 0 := by ring
  collection_row
  exact h6

private theorem collectionRow5 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 5 =
      (shortMatrix a * longMatrix b) 5 := by collection_row

private theorem collectionRow6 {A : Type v} [CommRing A] (a b : A) :
    (collectedMatrix a b * longMatrix b * shortMatrix a) 6 =
      (shortMatrix a * longMatrix b) 6 := by collection_row

private theorem collectionCertificate {A : Type v} [CommRing A] (a b : A) :
    collectedMatrix a b * longMatrix b * shortMatrix a = shortMatrix a * longMatrix b := by
  funext r
  fin_cases r
  · exact collectionRow0 a b
  · exact collectionRow1 a b
  · exact collectionRow2 a b
  · exact collectionRow3 a b
  · exact collectionRow4 a b
  · exact collectionRow5 a b
  · exact collectionRow6 a b

/-- The exact matrix of `[x_{α₁}(a), x_{α₂}(b)]`, with `α₁` short and `α₂` long in
Bourbaki numbering. No characteristic assumption or division is required. -/
theorem coe_commutatorElement_rootSubgroupPoints_inl_zero_inl_one
    (A : Type v) [CommRing A] (a b : A) :
    (((⁅rootSubgroupPoints (.inl 0) A (ofAdd a),
        rootSubgroupPoints (.inl 1) A (ofAdd b)⁆ : points A) :
        Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      !![1, 0, a * b, -2 * a ^ 2 * b, a ^ 3 * b, -a ^ 3 * b ^ 2, 0;
         0, 1, 0, -2 * a * b, a ^ 2 * b, -a ^ 2 * b ^ 2, 0;
         0, 0, 1, 0, 0, a ^ 2 * b, -a ^ 3 * b;
         0, 0, 0, 1, 0, a * b, -a ^ 2 * b;
         0, 0, 0, 0, 1, 0, -a * b;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 1] := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_mul]
  rw [Units.mul_inv_eq_iff_eq_mul, Units.mul_inv_eq_iff_eq_mul]
  rw [coe_rootSubgroupPoints_inl_zero A a, coe_rootSubgroupPoints_inl_one A b]
  simpa only [collectedMatrix, shortMatrix, longMatrix] using (collectionCertificate a b).symm

end TauCeti.G2ShortRoot.IntegralToralClosure
