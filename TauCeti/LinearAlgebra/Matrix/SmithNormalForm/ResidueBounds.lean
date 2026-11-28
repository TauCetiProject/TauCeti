/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.ValuationPair

/-!
# Determinant divisibility from residue-space bounds

Let a rectangular matrix over a local ring with total divisibility factor as `Q * D`, with `D`
square, and have a left inverse up to a scalar `w ^ N`. For each `j < N`, bound the dimension of
the reductions of vectors whose images under `Q * D` lie in `w ^ j` times the maximal ideal,
coordinatewise. The determinant of `D` divides `w` raised to the sum of these
dimension bounds.

Using the maximal ideal rather than `w ^ (j + 1)` also counts diagonal factors whose valuations
lie strictly between successive powers of `w`. This is the determinant-budget argument in
`New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd` in `grh-lean`,
`grh/src/New/UpperBound/ElementaryDivisors/Edges.lean` (revision `72fead1`).
-/

public section

open Finset IsLocalRing Module
open scoped Pointwise

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- Summing the numbers of diagonal factors not dividing `w ^ j`, for `0 ≤ j < N`, gives an
exponent whose power of `w` is divisible by the determinant of the diagonal matrix. -/
private theorem det_diagonal_dvd_pow_sum_card {w : R} {N : ℕ} (d : ι → R)
    (hd : ∀ i, d i ∣ w ^ N) :
    (diagonal d).det ∣ w ^ (∑ j ∈ range N, #{i | ¬ d i ∣ w ^ j}) := by
  classical
  have hex (i : ι) : ∃ k : ℕ, d i ∣ w ^ k := ⟨N, hd i⟩
  let e (i : ι) : ℕ := Nat.find (hex i)
  have he (i : ι) : d i ∣ w ^ e i := Nat.find_spec (hex i)
  have heN (i : ι) : e i ≤ N := Nat.find_min' (hex i) (hd i)
  have hiff (i : ι) (j : ℕ) : (¬ d i ∣ w ^ j) ↔ j < e i := by
    refine ⟨fun h ↦ lt_of_not_ge fun hle ↦ h ((he i).trans (pow_dvd_pow w hle)), ?_⟩
    exact Nat.find_min (hex i)
  have hsum : (∑ j ∈ range N, #{i | ¬ d i ∣ w ^ j}) = ∑ i, e i := by
    simp only [card_eq_sum_ones, sum_filter, hiff]
    rw [sum_comm]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_filter]
    have hrange : (range N).filter (· < e i) = range (e i) := by
      ext j
      simp only [mem_filter, mem_range]
      exact and_iff_right_of_imp (fun h ↦ h.trans_le (heN i))
    simp [hrange]
  rw [det_diagonal, hsum, ← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun i _ ↦ he i

variable [IsLocalRing R]

open scoped Classical in
/-- The reductions of the columns of `V⁻¹` indexed by factors not dividing `w ^ j` give that
many independent vectors in a residue subspace containing the divisibility locus. -/
private theorem card_not_dvd_le_finrank [PreValuationRing R] {κ : Type*}
    (Q : Matrix κ ι R) (V : GL ι R) (d : ι → R) {w : R} {j : ℕ}
    {P : Submodule (ResidueField R) (ι → ResidueField R)}
    (hP : ∀ x : ι → R,
      (∀ k, ((Q * diagonal d * V.val) *ᵥ x) k ∈ w ^ j • maximalIdeal R) →
      (fun k ↦ residue R (x k)) ∈ P) : #{i | ¬ d i ∣ w ^ j} ≤ finrank (ResidueField R) P := by
  classical
  let s : Finset ι := univ.filter fun i ↦ ¬ d i ∣ w ^ j
  let E := (GeneralLinearGroup.toLin (GeneralLinearGroup.map (residue R) V⁻¹)).toLinearEquiv
  let b := (Pi.basisFun (ResidueField R) ι).map E
  have hmem (i : s) : b i ∈ P := by
    have hi : ¬ d i ∣ w ^ j := (mem_filter.mp i.property).2
    obtain ⟨c, hc⟩ := (ValuationRing.dvd_total (d i) (w ^ j)).resolve_left hi
    have hcm : c ∈ maximalIdeal R := (mem_maximalIdeal _).2 fun hu ↦
      hi (hc ▸ (hu.mul_right_dvd).mpr (dvd_refl (w ^ j)))
    let x : ι → R := V⁻¹.val *ᵥ Pi.single (i : ι) 1
    have hx : (Q * diagonal d * V.val) *ᵥ x = d i • Q.col i := by
      simp only [x, mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rw [← mulVec_mulVec, diagonal_mulVec_single, mulVec_single, mul_one, op_smul_eq_smul]
    have h : (fun k ↦ residue R (x k)) ∈ P := by
      apply hP
      intro k
      rw [hx, Pi.smul_apply, smul_eq_mul, hc, mul_assoc]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Ideal.mul_mem_right _ _ hcm)
    simpa only [b, E, Basis.map_apply, Pi.basisFun_apply,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv, GeneralLinearGroup.toLin_apply,
      mulVecLin_apply, GeneralLinearGroup.val_map_apply, mulVec_single_one, col_map,
      Function.comp_def, x] using h
  let v : s → P := fun i ↦ ⟨b i, hmem i⟩
  have hli : LinearIndependent (ResidueField R) v :=
    (b.linearIndependent.comp (fun i : s ↦ (i : ι)) Subtype.val_injective).of_comp P.subtype
  simpa only [Fintype.card_coe, s] using hli.fintype_card_le_finrank

/-- **Determinant budget from reductions of divisibility loci.** Suppose `B * (Q * D) = w ^ N • 1`.
If, for each `j < N`, the reductions of vectors sent by `Q * D` into `w ^ j • 𝔪` coordinatewise
lie in `P j`, then `det D` divides `w` to the sum of the dimensions of the `P j`. Here `𝔪` is the
maximal ideal. No discreteness assumption is needed. -/
theorem det_dvd_pow_sum_finrank_of_residue_bounds [PreValuationRing R] {κ : Type*} [Fintype κ]
    (D : Matrix ι ι R) (Q : Matrix κ ι R) (B : Matrix ι κ R)
    {w : R} {N : ℕ} (hB : B * (Q * D) = w ^ N • 1)
    (P : ℕ → Submodule (ResidueField R) (ι → ResidueField R))
    (hP : ∀ j < N, ∀ x : ι → R, (∀ k, ((Q * D) *ᵥ x) k ∈ w ^ j • maximalIdeal R) →
      (fun k ↦ residue R (x k)) ∈ P j) :
    D.det ∣ w ^ (∑ j ∈ range N, finrank (ResidueField R) (P j)) := by
  classical
  obtain ⟨U, V, d, rfl⟩ := D.exists_eq_mul_diagonal_mul_of_preValuationRing
  have hD : (V.val * B * Q * U.val) * diagonal d = w ^ N • 1 := by
    calc
      _ = V.val * (B * (Q * (U.val * diagonal d * V.val))) * V⁻¹.val := by
        simp [Matrix.mul_assoc]
      _ = _ := by rw [hB]; simp
  have hd (i : ι) : d i ∣ w ^ N := by
    refine ⟨(V.val * B * Q * U.val) i i, ?_⟩
    simpa [mul_comm] using (congr_fun₂ hD i i).symm
  have hsum : (∑ j ∈ range N, #{i | ¬ d i ∣ w ^ j}) ≤
      ∑ j ∈ range N, finrank (ResidueField R) (P j) := by
    refine sum_le_sum fun j hj ↦ card_not_dvd_le_finrank (Q * U.val) V d ?_
    simpa only [Matrix.mul_assoc] using hP j (mem_range.mp hj)
  rw [det_mul, det_mul, ← GeneralLinearGroup.val_det_apply, ← GeneralLinearGroup.val_det_apply]
  exact Units.mul_right_dvd.mpr (Units.mul_left_dvd.mpr
    ((det_diagonal_dvd_pow_sum_card d hd).trans (pow_dvd_pow w hsum)))

end Matrix
