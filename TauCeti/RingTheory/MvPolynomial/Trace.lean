/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.Polynomial.Dickson
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Traces of linear substitution on binary forms

On homogeneous binary forms of degree `w`, substitution by any two-by-two matrix
has trace `dickson 2 (det M) w` evaluated at `trace M`, over any commutative ring.
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
    [CommRing R] (w : ℕ) {M N : Matrix σ σ R} (h : IsConj M N) :
    LinearMap.trace R (homogeneousSubmodule σ R w) (linearSubstRep σ R w (op M)) =
      LinearMap.trace R (homogeneousSubmodule σ R w) (linearSubstRep σ R w (op N)) := by
  obtain ⟨P, hP⟩ := h
  let Q := Units.map (linearSubstRep σ R w) (Units.opEquiv.symm (op P))
  have hmap : linearSubstRep σ R w (op M) * (Q : _) =
      (Q : _) * linearSubstRep σ R w (op N) := by
    simpa only [Q, Units.coe_map, Units.coe_opEquiv_symm, unop_op, op_mul, map_mul] using
      congrArg (fun A ↦ linearSubstRep σ R w (op A)) hP.eq
  rw [Q.eq_mul_inv_iff_mul_eq.mpr hmap, LinearMap.trace_conj]

private theorem trace_linearSubstRep_eq_dickson_eval_field {K : Type u} [Field K]
    (w : ℕ) (M : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (linearSubstRep (Fin 2) K w (op M)) =
      (Polynomial.dickson 2 M.det w).eval M.trace := by
  -- Calculate after extending scalars, then descend the trace through the injective field map.
  suffices h : ∀ (L : Type u) [Field L] [IsAlgClosed L] (A : Matrix (Fin 2) (Fin 2) L),
      LinearMap.trace L (homogeneousSubmodule (Fin 2) L w)
          (linearSubstRep (Fin 2) L w (op A)) =
        (Polynomial.dickson 2 A.det w).eval A.trace by
    let f := algebraMap K (AlgebraicClosure K)
    apply f.injective
    rw [map_trace_linearSubstRep, ← Polynomial.eval_map_apply f, Polynomial.map_dickson]
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, AddMonoidHom.map_trace] using
      h (AlgebraicClosure K) (M.map f)
  intro L _ _ A
  -- A scalar is already triangular. A nonscalar is conjugate to a triangular matrix with
  -- the same trace and determinant, even when its two eigenvalues coincide.
  by_cases hA : A ∈ Set.range (Matrix.scalar (Fin 2))
  · obtain ⟨a, ha⟩ := hA
    have hmat : A = !![a, 0; 0, a] := by
      rw [← ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]
    rw [hmat, trace_linearSubstRep_upperTriangular]
    simp [Matrix.det_fin_two_of, Matrix.trace_fin_two_of]
  · let t := A.trace
    let d := A.det
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root A.charpoly (by simp)
    have hroot : a ^ 2 - t * a + d = 0 := by
      simpa [Matrix.charpoly_fin_two, Polynomial.IsRoot, t, d,
        Matrix.trace_fin_two, Matrix.det_fin_two] using ha
    have had : a * (t - a) = d := by linear_combination -hroot
    let B : Matrix (Fin 2) (Fin 2) L := !![a, 1; 0, t - a]
    have hB : B ∉ Set.range (Matrix.scalar (Fin 2)) := by
      rw [mem_range_scalar_fin_two_iff]
      simp [B]
    have ht : A.trace = B.trace := by simp [B, Matrix.trace_fin_two_of, t]
    have hd : A.det = B.det := by simp [B, Matrix.det_fin_two_of, had, d]
    obtain ⟨P, hP, hAP⟩ := exists_det_ne_zero_mul_eq_mul_companionFinTwo hA
    obtain ⟨Q, hQ, hBQ⟩ := exists_det_ne_zero_mul_eq_mul_companionFinTwo hB
    have hAC : IsConj (companionFinTwo A.trace A.det) A :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hP, hAP.symm⟩
    have hBC : IsConj (companionFinTwo A.trace A.det) B := by
      rw [ht, hd]
      exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Q hQ, hBQ.symm⟩
    rw [trace_linearSubstRep_eq_of_isConj w (hAC.symm.trans hBC)]
    simpa only [B, add_sub_cancel, had, t, d] using
      trace_linearSubstRep_upperTriangular w a 1 (t - a)

/-- Over any commutative ring, substitution by a two-by-two matrix on binary forms has
Dickson trace. No invertibility or splitting assumption is needed. -/
@[simp]
theorem trace_linearSubstRep_eq_dickson_eval {R : Type*} [CommRing R]
    (w : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (linearSubstRep (Fin 2) R w (op M)) =
      (Polynomial.dickson 2 M.det w).eval M.trace := by
  -- Prove the polynomial identity for the universal matrix over ℤ, then specialize its entries.
  let S := MvPolynomial (Fin 2 × Fin 2) ℤ
  let A : Matrix (Fin 2) (Fin 2) S := fun i j ↦ X (i, j)
  let f := algebraMap S (FractionRing S)
  have hA : LinearMap.trace S (homogeneousSubmodule (Fin 2) S w)
      (linearSubstRep (Fin 2) S w (op A)) =
        (Polynomial.dickson 2 A.det w).eval A.trace := by
    apply IsFractionRing.injective S (FractionRing S)
    rw [map_trace_linearSubstRep, ← Polynomial.eval_map_apply f, Polynomial.map_dickson]
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, AddMonoidHom.map_trace] using
      trace_linearSubstRep_eq_dickson_eval_field w (A.map f)
  let g : S →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ij ↦ M ij.1 ij.2)
  have hM : A.map g = M := by
    ext i j
    exact MvPolynomial.eval₂Hom_X' (Int.castRingHom R) (fun ij ↦ M ij.1 ij.2) (i, j)
  have h := congrArg g hA
  rw [map_trace_linearSubstRep, ← Polynomial.eval_map_apply g, Polynomial.map_dickson,
    RingHom.map_det, RingHom.mapMatrix_apply, AddMonoidHom.map_trace, hM] at h
  exact h

end TauCeti
