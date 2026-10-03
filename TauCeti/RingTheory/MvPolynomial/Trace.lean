/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.Polynomial.Dickson
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Traces of linear substitution on binary forms

On homogeneous binary forms of degree `w`, substitution by an invertible two-by-two matrix
has trace `dickson 2 (det M) w` evaluated at `trace M`, over any field.
The formula includes matrices with a repeated eigenvalue and does not require diagonalizability.
Traces of substitution also commute with changes of coefficient ring, allowing this calculation
to descend to fields over which the eigenvalues do not lie.

These are the weight polynomials in the elliptic and hyperbolic terms of the
Eichler--Selberg trace formula.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, Section 4.
-/

public section

open Matrix MvPolynomial MulOpposite

namespace TauCeti

universe u

/-- The trace of substitution is the sum of the coefficients of each degree-`w` monomial in
its own image. -/
theorem trace_linearSubstRep_eq_sum {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    (w : ℕ) (M : Matrix σ σ R) :
    LinearMap.trace R (homogeneousSubmodule σ R w) (linearSubstRep σ R w (op M)) =
      ∑ s ∈ (Finset.univ : Finset σ).finsuppAntidiag w,
        (linearSubst M (monomial s 1)).coeff s := by
  classical
  have : Fintype {s : σ →₀ ℕ // s.degree = w} :=
    Fintype.ofFinset (p := {s : σ →₀ ℕ | s.degree = w})
      ((Finset.univ : Finset σ).finsuppAntidiag w) (fun s ↦ by
        simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  rw [LinearMap.trace_eq_matrix_trace R (homogeneousMonomialBasis (R := R) w), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, homogeneousMonomialBasis_repr_apply,
    coe_linearSubstRep_apply, unop_op, coe_homogeneousMonomialBasis]
  exact (Finset.sum_subtype ((Finset.univ : Finset σ).finsuppAntidiag w)
    (by simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
    (fun s ↦ (linearSubst M (monomial s 1)).coeff s)).symm

/-- Changing the coefficient ring commutes with the trace of homogeneous substitution. -/
theorem map_trace_linearSubstRep {σ R S : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] [CommRing S] (w : ℕ) (f : R →+* S) (M : Matrix σ σ R) :
    f (LinearMap.trace R (homogeneousSubmodule σ R w) (linearSubstRep σ R w (op M))) =
      LinearMap.trace S (homogeneousSubmodule σ S w)
        (linearSubstRep σ S w (op (M.map f))) := by
  simp only [trace_linearSubstRep_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← MvPolynomial.coeff_map]
  simp only [linearSubst_eq_aeval, aeval_def, algebraMap_eq, map_eval₂, map_monomial, map_one]
  congr 3
  funext i
  simp

/-- Substitution on binary forms by an upper-triangular matrix has Dickson trace,
independently of its upper-right entry. -/
@[simp]
theorem trace_linearSubstRep_upperTriangular {R : Type*} [CommRing R]
    (w : ℕ) (a b d : R) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (linearSubstRep (Fin 2) R w (op !![a, b; 0, d])) =
      (Polynomial.dickson 2 (a * d) w).eval (a + d) := by
  rw [trace_linearSubstRep_eq_sum]
  simp_rw [coeff_linearSubst_upperTriangular_monomial]
  let e : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ :=
    Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)
  have hs : (∑ s ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag w, a ^ s 0 * d ^ s 1) =
      ∑ p ∈ Finset.antidiagonal w, a ^ p.1 * d ^ p.2 := by
    apply Finset.sum_equiv e
    · intro s
      simp [e, Finset.mem_finsuppAntidiag, Finset.mem_antidiagonal]
    · intro s _
      rfl
  rw [hs, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ a ^ i * d ^ j) w]
  exact (Polynomial.dickson_two_eval_add rfl w).symm

/-- The trace of homogeneous substitution is unchanged by conjugating the matrix. -/
theorem trace_linearSubstRep_eq_of_isConj {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (w : ℕ) {M N : GL σ R} (h : IsConj M N) :
    LinearMap.trace R (homogeneousSubmodule σ R w)
        (linearSubstRep σ R w (op (M : Matrix σ σ R))) =
      LinearMap.trace R (homogeneousSubmodule σ R w)
        (linearSubstRep σ R w (op (N : Matrix σ σ R))) := by
  obtain ⟨P, hP⟩ := isConj_iff.mp h
  have hmat := congrArg Units.val hP
  simp only [Units.val_mul] at hmat
  rw [← hmat]
  simp only [op_mul, map_mul]
  rw [LinearMap.trace_mul_comm, mul_assoc]
  have hcancel : linearSubstRep σ R w (op (P : Matrix σ σ R)) *
      linearSubstRep σ R w (op (↑(P⁻¹) : Matrix σ σ R)) = 1 := by
    rw [← map_mul, ← op_mul, ← Units.val_mul, inv_mul_cancel]
    exact map_one _
  rw [hcancel, mul_one]

/-- Over any field, substitution by an invertible two-by-two matrix on binary forms has
Dickson trace. Neither splitting of the characteristic polynomial nor semisimplicity is needed. -/
@[simp]
theorem trace_linearSubstRep_eq_dickson_eval {K : Type u} [Field K]
    (w : ℕ) (M : GL (Fin 2) K) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (linearSubstRep (Fin 2) K w (op (M : Matrix (Fin 2) (Fin 2) K))) =
      (Polynomial.dickson 2 (M : Matrix (Fin 2) (Fin 2) K).det w).eval
        (M : Matrix (Fin 2) (Fin 2) K).trace := by
  -- Calculate after extending scalars, then descend the trace through the injective field map.
  suffices h : ∀ (L : Type u) [Field L] [IsAlgClosed L] (A : GL (Fin 2) L),
      LinearMap.trace L (homogeneousSubmodule (Fin 2) L w)
          (linearSubstRep (Fin 2) L w (op (A : Matrix (Fin 2) (Fin 2) L))) =
        (Polynomial.dickson 2 (A : Matrix (Fin 2) (Fin 2) L).det w).eval
          (A : Matrix (Fin 2) (Fin 2) L).trace by
    let f := algebraMap K (AlgebraicClosure K)
    apply f.injective
    rw [map_trace_linearSubstRep, ← Polynomial.eval_map_apply f, Polynomial.map_dickson]
    simpa [Matrix.GeneralLinearGroup.map, RingHom.map_det, AddMonoidHom.map_trace] using
      h (AlgebraicClosure K) (Matrix.GeneralLinearGroup.map f M)
  intro L _ _ A
  -- A scalar is already triangular. A nonscalar is conjugate to a triangular matrix with
  -- the same trace and determinant, even when its two eigenvalues coincide.
  by_cases hA : (A : Matrix (Fin 2) (Fin 2) L) ∈ Set.range (Matrix.scalar (Fin 2))
  · obtain ⟨a, ha⟩ := hA
    have hmat : (A : Matrix (Fin 2) (Fin 2) L) = !![a, 0; 0, a] := by
      rw [← ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]
    rw [hmat, trace_linearSubstRep_upperTriangular]
    simp [Matrix.det_fin_two_of, Matrix.trace_fin_two_of]
  · let t := (A : Matrix (Fin 2) (Fin 2) L).trace
    let d := (A : Matrix (Fin 2) (Fin 2) L).det
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root
      (A : Matrix (Fin 2) (Fin 2) L).charpoly (by simp)
    have hroot : a ^ 2 - t * a + d = 0 := by
      simpa [Matrix.charpoly_fin_two, Polynomial.IsRoot, t, d,
        Matrix.trace_fin_two, Matrix.det_fin_two] using ha
    have had : a * (t - a) = d := by linear_combination -hroot
    let B : GL (Fin 2) L := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, 1; 0, t - a] (by
        simpa [Matrix.det_fin_two_of, had] using Matrix.GeneralLinearGroup.det_ne_zero A)
    have hB : (B : Matrix (Fin 2) (Fin 2) L) ∉ Set.range (Matrix.scalar (Fin 2)) := by
      rw [mem_range_scalar_fin_two_iff]
      simp [B]
    have ht : (A : Matrix (Fin 2) (Fin 2) L).trace =
        (B : Matrix (Fin 2) (Fin 2) L).trace := by simp [B, Matrix.trace_fin_two_of, t]
    have hd : (A : Matrix (Fin 2) (Fin 2) L).det =
        (B : Matrix (Fin 2) (Fin 2) L).det := by simp [B, Matrix.det_fin_two_of, had, d]
    rw [trace_linearSubstRep_eq_of_isConj w
      ((isConj_iff_of_notMem_range_scalar hA hB).mpr ⟨ht, hd⟩)]
    simpa only [B, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, add_sub_cancel, had, t, d] using
      trace_linearSubstRep_upperTriangular w a 1 (t - a)

end TauCeti
