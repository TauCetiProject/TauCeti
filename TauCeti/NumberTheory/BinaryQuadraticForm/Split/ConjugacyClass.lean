/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.ConjugacyClass
public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Classes

/-!
# Conjugacy classes of integer matrices with distinct integer eigenvalues

Let `a ≠ d` be integers. The integer matrices of trace `a + d` and determinant `a d` are those
with eigenvalues `a` and `d`; their discriminant `(a + d)² - 4 a d = (d - a)²` is a nonzero
square. When `a d > 0` they are the *split hyperbolic* matrices of the Eichler–Selberg trace
formula. This file classifies them up to `SL(2, ℤ)`-conjugacy.

The form `Q_M = c x² + (d' - a') x y - b y²` of `M = !![a', b; c, d']`
(`TauCeti.BinaryQuadraticForm.ofMatrix`) has discriminant `(d - a)²`, and conjugation of matrices
of a fixed trace is the action on their forms
(`TauCeti.BinaryQuadraticForm.smul_eq_iff_ofConjAct_smul_ofMatrix_eq`). The form of the
upper-triangular matrix `!![a, b; 0, d]` is the triangular form `(d - a) x y - b y²`, so the
classification of forms of square discriminant by triangular representatives
(`TauCeti.BinaryQuadraticForm.exists_smul_eq_splitTriangularForm_of_discrim_eq_sq` and
`TauCeti.BinaryQuadraticForm.exists_smul_splitTriangularForm_eq_iff`) gives:

* every such matrix is conjugate to `!![a, b; 0, d]` for some `0 ≤ b < |d - a|`, and
  `!![a, b; 0, d]` and `!![a, b'; 0, d]` are conjugate exactly when `d - a ∣ b - b'`, so there are
  exactly `|d - a|` conjugacy classes;
* the centraliser of each such matrix in `SL(2, ℤ)` is `{±1}`, of order `2`, because the
  automorphisms of a triangular form are `±1`
  (`TauCeti.BinaryQuadraticForm.smul_splitTriangularForm_eq_self_iff`), so every form of
  nonzero square discriminant has stabiliser of order `2`
  (`TauCeti.BinaryQuadraticForm.card_stabilizer_of_discrim_eq_sq`).

So each class has Popa and Zagier's automorphism weight `2 / |Z_SL(M)| = 1`. This is the split
counterpart of `TauCeti.BinaryQuadraticForm.orbitRelQuotientTraceDetFiberEquiv`, which treats the
elliptic classes.

## Main definitions

* `TauCeti.BinaryQuadraticForm.finEquivOrbitRelQuotientTraceDetFiber`: for `a ≠ d`, the
  bijection `b ↦ [!![a, b; 0, d]]` from `Fin |d - a|` onto the conjugacy classes of matrices of
  trace `a + d` and determinant `a d`.

## Main results

* `TauCeti.BinaryQuadraticForm.exists_smul_eq_upperTriangular`: every matrix of trace `a + d` and
  determinant `a d` is conjugate to some `!![a, b; 0, d]` with `0 ≤ b < |d - a|`.
* `TauCeti.BinaryQuadraticForm.exists_smul_upperTriangular_eq_iff`: `!![a, b; 0, d]` and
  `!![a, b'; 0, d]` are conjugate exactly when `d - a ∣ b - b'`.
* `TauCeti.BinaryQuadraticForm.card_orbitRel_quotient_traceDetFiber_add_mul`: there are
  `|d - a|` conjugacy classes.
* `TauCeti.BinaryQuadraticForm.cardStabilizerOnOrbit_traceDetFiber_add_mul`: each of them has
  centraliser of order `2`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7 (proper-equivalence conventions).
-/

public section

open Matrix MulAction ConjAct
open scoped MatrixGroups

namespace TauCeti

namespace BinaryQuadraticForm

variable {a d : ℤ}

/-- The upper-triangular matrix `!![a, b; 0, d]` has trace `a + d` and determinant `a d`. -/
theorem upperTriangular_mem_traceDetFiber (a b d : ℤ) :
    !![a, b; 0, d] ∈ traceDetFiber (Fin 2) (a + d) (a * d) := by
  simp [mem_traceDetFiber, trace_fin_two, det_fin_two]

/-- The form of `!![a, b; 0, d]` is the triangular form `(d - a) x y - b y²`. -/
@[simp]
theorem ofMatrix_upperTriangular (a b d : ℤ) :
    ofMatrix !![a, b; 0, d] = splitTriangularForm (d - a) (-b) := by
  ext <;> simp [ofMatrix_a, ofMatrix_b, ofMatrix_c, splitTriangularForm_def]

/-- A matrix of trace `a + d` and determinant `a d` has a form of discriminant `(d - a)²`. -/
theorem discrim_ofMatrix_of_mem_traceDetFiber {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ traceDetFiber (Fin 2) (a + d) (a * d)) : (ofMatrix M).discrim = (d - a) ^ 2 := by
  rw [discrim_ofMatrix, (mem_traceDetFiber.1 hM).1, (mem_traceDetFiber.1 hM).2]
  ring

/-- **Upper-triangular representatives**: if `a ≠ d`, every integer matrix of trace `a + d` and
determinant `a d` is `SL(2, ℤ)`-conjugate to `!![a, b; 0, d]` for some `0 ≤ b < |d - a|`. -/
theorem exists_smul_eq_upperTriangular (h : a ≠ d) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ traceDetFiber (Fin 2) (a + d) (a * d)) :
    ∃ g : ConjAct SL(2, ℤ), ∃ b : ℤ, 0 ≤ b ∧ b < |d - a| ∧ g • M = !![a, b; 0, d] := by
  have hs : d - a ≠ 0 := sub_ne_zero.2 h.symm
  obtain ⟨γ, c, -, -, hγ⟩ := exists_smul_eq_splitTriangularForm_of_discrim_eq_sq _ hs
    (discrim_ofMatrix_of_mem_traceDetFiber hM)
  -- `-b` must be congruent to `c` modulo `d - a`; take `b` the least residue of `-c`
  obtain ⟨τ, hτ⟩ := (exists_smul_splitTriangularForm_eq_iff (d - a) c (-(-c % (d - a))) hs).2 <| by
    simpa [sub_eq_add_neg, add_comm] using (Int.dvd_self_sub_emod (x := -c) (m := d - a)).neg_right
  refine ⟨toConjAct (τ * γ), -c % (d - a), Int.emod_nonneg _ hs, Int.emod_lt_abs _ hs, ?_⟩
  rw [smul_eq_iff_ofConjAct_smul_ofMatrix_eq (by simp [(mem_traceDetFiber.1 hM).1, trace_fin_two]),
    ofConjAct_toConjAct, mul_smul, hγ, hτ, ofMatrix_upperTriangular]

/-- **Conjugacy of upper-triangular matrices**: if `a ≠ d`, the matrices `!![a, b; 0, d]` and
`!![a, b'; 0, d]` are `SL(2, ℤ)`-conjugate exactly when `d - a ∣ b - b'`. -/
theorem exists_smul_upperTriangular_eq_iff (h : a ≠ d) (b b' : ℤ) :
    (∃ g : ConjAct SL(2, ℤ), g • !![a, b; 0, d] = !![a, b'; 0, d]) ↔ d - a ∣ b - b' := by
  have hs : d - a ≠ 0 := sub_ne_zero.2 h.symm
  have htr : (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).trace = (!![a, b'; 0, d]).trace := by
    simp [trace_fin_two]
  simp_rw [smul_eq_iff_ofConjAct_smul_ofMatrix_eq htr, ofMatrix_upperTriangular]
  rw [toConjAct.surjective.exists]
  simp_rw [ofConjAct_toConjAct]
  rw [exists_smul_splitTriangularForm_eq_iff _ _ _ hs, neg_sub_neg, dvd_sub_comm]

/-- The map `b ↦ [!![a, b; 0, d]]` from `Fin |d - a|` to the conjugacy classes of matrices of
trace `a + d` and determinant `a d`. -/
private def upperTriangularClass (a d : ℤ) (b : Fin (d - a).natAbs) :
    orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d)) :=
  Quotient.mk'' ⟨!![a, (b : ℤ); 0, d], upperTriangular_mem_traceDetFiber a b d⟩

private theorem upperTriangularClass_bijective (h : a ≠ d) :
    Function.Bijective (upperTriangularClass a d) := by
  have hs : (d - a).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (sub_ne_zero.2 h.symm)
  refine ⟨fun i j hij ↦ ?_, fun X ↦ ?_⟩
  · obtain ⟨g, hg⟩ := Quotient.exact' hij
    -- `d - a` divides `j - i`, and `|j - i| < |d - a|`
    have hdvd := (exists_smul_upperTriangular_eq_iff h j i).1 ⟨g, congrArg Subtype.val hg⟩
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
    exact Fin.ext (by omega)
  · induction X using Quotient.inductionOn' with
    | h M =>
      obtain ⟨g, b, hb₀, hb, hg⟩ := exists_smul_eq_upperTriangular h M.2
      refine ⟨⟨b.toNat, by have := Int.natCast_natAbs (d - a); omega⟩,
        Quotient.sound' ⟨g, Subtype.ext ?_⟩⟩
      simp [hg, Int.toNat_of_nonneg hb₀]

/-- **The conjugacy classes of matrices with eigenvalues `a ≠ d`**: `b ↦ [!![a, b; 0, d]]` is a
bijection from `Fin |d - a|` onto the `SL(2, ℤ)`-conjugacy classes of integer matrices of trace
`a + d` and determinant `a d`. -/
noncomputable def finEquivOrbitRelQuotientTraceDetFiber (h : a ≠ d) :
    Fin (d - a).natAbs ≃
      orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d)) :=
  .ofBijective _ (upperTriangularClass_bijective h)

/-- `finEquivOrbitRelQuotientTraceDetFiber h` sends `b` to the class of `!![a, b; 0, d]`. -/
@[simp]
theorem finEquivOrbitRelQuotientTraceDetFiber_apply (h : a ≠ d) (b : Fin (d - a).natAbs) :
    finEquivOrbitRelQuotientTraceDetFiber h b =
      Quotient.mk'' ⟨!![a, (b : ℤ); 0, d], upperTriangular_mem_traceDetFiber a b d⟩ :=
  (rfl)

/-- If `a ≠ d`, there are finitely many conjugacy classes of matrices of trace `a + d` and
determinant `a d`. -/
theorem finite_orbitRel_quotient_traceDetFiber_add_mul (h : a ≠ d) :
    Finite (orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d))) :=
  .of_equiv _ (finEquivOrbitRelQuotientTraceDetFiber h)

/-- **The number of split conjugacy classes**: if `a ≠ d`, there are exactly `|d - a|`
`SL(2, ℤ)`-conjugacy classes of integer matrices of trace `a + d` and determinant `a d`. -/
theorem card_orbitRel_quotient_traceDetFiber_add_mul (h : a ≠ d) :
    Nat.card (orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d))) =
      (d - a).natAbs := by
  rw [← Nat.card_congr (finEquivOrbitRelQuotientTraceDetFiber h), Nat.card_fin]

/-- **The centralisers are `±1`**: if `a ≠ d`, the centraliser in `SL(2, ℤ)` of an integer matrix
of trace `a + d` and determinant `a d` has order `2`. So every such conjugacy class has
automorphism weight `2 / |Z_SL(M)| = 1`. -/
theorem cardStabilizerOnOrbit_traceDetFiber_add_mul (h : a ≠ d)
    (X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d))) :
    cardStabilizerOnOrbit X = 2 := by
  induction X using Quotient.inductionOn' with
  | h M =>
    rw [cardStabilizerOnOrbit_mk, SubMulAction.stabilizer_of_subMul, ← card_stabilizer_ofMatrix]
    exact card_stabilizer_of_discrim_eq_sq (sub_ne_zero.2 h.symm)
      (discrim_ofMatrix_of_mem_traceDetFiber M.2)

end BinaryQuadraticForm

end TauCeti
