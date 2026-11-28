/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel

/-!
# Trace matrix for the simple-root sum on the split unitary group

For a split form J = TauCeti.splitGram ϱ T on TauCeti.BesselIndex ϱ κ with frame
TauCeti.besselFrame = (e₀, …, e_{ϱ-1}, z), this file constructs a fixed matrix
TauCeti.besselCharMatrix ϱ T such that for every isometry u ∈ Matrix.unitaryGroupOf J,

	r(besselCharMatrix ϱ T * u) = σ(u) + star (σ(u⁻¹)),

where σ(u) = ∑ a : Fin ϱ, u (e_a) (besselFrame a.succ) is the sum of the entries just above the
diagonal on the Bessel frame (TauCeti.trace_besselCharMatrix_mul).

## Main definitions

* TauCeti.besselCharMatrix: the fixed matrix C on BesselIndex ϱ κ pairing with u via trace.

## Main results

* TauCeti.trace_besselCharMatrix_mul_eq_sum: for any matrix u, the trace 	r(C u) splits into
  the superdiagonal frame entries of u and the paired entries of J u.
* TauCeti.trace_besselCharMatrix_mul: for u in Matrix.unitaryGroupOf (splitGram ϱ T),
  	r(C u) = σ(u) + star (σ(u⁻¹)).
* TauCeti.trace_besselCharMatrix: 	r(C) = 0.

## References

* Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
  72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0),
  src/Lib/DiscreteSeries/Bessel/SchurBound.lean (New.Filling.besselCharMatrix,
  New.Filling.trace_besselCharMatrix_mul).
-/

public section

open Matrix Finset

namespace TauCeti

/-- The fixed matrix C on BesselIndex ϱ κ such that 	r(C u) picks out the superdiagonal
frame entries of u together with the entries of splitGram ϱ T * u at (besselFrame a.succ,
e*_a). -/
def besselCharMatrix {R : Type*} [Semiring R] (ϱ : ℕ) {κ : Type*} [DecidableEq κ]
    (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) :
    Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
  Matrix.of fun y x ↦
    ∑ a : Fin ϱ,
      ((if (.inl a : BesselIndex ϱ κ) = x then
          (if besselFrame a.succ = y then 1 else 0) else 0) +
        if (.inr (.inr a) : BesselIndex ϱ κ) = y then
          splitGram ϱ T (besselFrame a.succ) x else 0)

/-- For any matrix u on BesselIndex ϱ κ, 	r(besselCharMatrix ϱ T * u) is the sum over
 : Fin ϱ of u (e_a) (besselFrame a.succ) plus (splitGram ϱ T * u) (besselFrame a.succ)
(e*_a). -/
theorem trace_besselCharMatrix_mul_eq_sum {R : Type*} [Semiring R] (ϱ : ℕ) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)
    (u : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) :
    (besselCharMatrix ϱ T * u).trace =
      ∑ a : Fin ϱ,
        (u (.inl a) (besselFrame a.succ) +
          (splitGram ϱ T * u) (besselFrame a.succ) (.inr (.inr a))) := by
  simp [besselCharMatrix, trace, Matrix.mul_apply, sum_mul, add_mul, sum_add_distrib,
    @sum_comm (Fin _), -Fintype.sum_sum_type]

/-- For an isometry u of splitGram ϱ T, 	r(besselCharMatrix ϱ T * u) equals
σ(u) + star (σ(u⁻¹)), where σ(u) = ∑ a : Fin ϱ, u (e_a) (besselFrame a.succ). -/
theorem trace_besselCharMatrix_mul {R : Type*} [CommRing R] [StarRing R] (ϱ : ℕ) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)
    (u : unitaryGroupOf (splitGram ϱ T)) :
    (besselCharMatrix ϱ T * ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)).trace =
      (∑ a : Fin ϱ, ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) (besselFrame a.succ)) +
      star (∑ a : Fin ϱ, (((u⁻¹ : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) (besselFrame a.succ)) := by
  have h_unitary :
      splitGram ϱ T * ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) =
      (((u⁻¹ : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)ᴴ * splitGram ϱ T := by
    have hinv := Matrix.mem_unitaryGroupOf_iff.mp u⁻¹.property
    have hmul := congrArg (· * ((u : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)) hinv
    simpa [Matrix.mul_assoc, Matrix.star_eq_conjTranspose] using hmul.symm
  rw [trace_besselCharMatrix_mul_eq_sum, sum_add_distrib, star_sum]
  congr 1
  refine sum_congr rfl fun a _ ↦ ?_
  rw [h_unitary, Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply, Matrix.one_apply]

/-- The trace of esselCharMatrix ϱ T vanishes. -/
theorem trace_besselCharMatrix {R : Type*} [Semiring R] (ϱ : ℕ) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) :
    (besselCharMatrix ϱ T).trace = 0 := by
  have h := trace_besselCharMatrix_mul_eq_sum ϱ T (1 : Matrix (BesselIndex ϱ κ) _ R)
  rw [Matrix.mul_one, Matrix.mul_one] at h
  rw [h]
  refine sum_eq_zero fun a _ ↦ ?_
  cases ha : a.succ using Fin.lastCases with
  | last => simp [besselFrame_last]
  | cast b =>
    have hne : a ≠ b := by
      intro h_eq
      have hval := congrArg Fin.val ha
      simp only [Fin.val_succ, Fin.val_castSucc, h_eq] at hval
      omega
    simp [besselFrame_castSucc, hne, hne.symm]

end TauCeti
