/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
public import TauCeti.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Derivation.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Derivations of determinants and norms

A derivation `D` differentiates a finite product termwise (`Derivation.leibniz_prod`), and hence
a determinant by **Jacobi's formula** `D (det M) = tr (adj M * D M)`, where `D M` applies `D` to
every entry of the square matrix `M` (`Derivation.leibniz_det`). When `M` satisfies a linear
Sylvester differential equation `M.map D = M * P - Q * M`, substituting into Jacobi's formula
yields the **Abel–Jacobi–Liouville formula** `D (det M) = det M * (tr P - tr Q)`
(`Derivation.leibniz_det_of_map_eq_mul_sub_mul`). Applied to the characteristic matrix, it shows
that a derivation acting on `M` as a commutator kills every coefficient of the characteristic
polynomial of `M` (`Derivation.map_charpoly_coeff_eq_zero_of_map_eq_mul_sub_mul`).

Let `S` be an algebra over a commutative ring `A`, and let `D'` be a derivation of `S` extending a
derivation `D` of `A`, in the sense that `D' (algebraMap A S a) = algebraMap A S (D a)`. Then `D`
commutes with the algebraic trace (`Derivation.map_trace`), and the norm of a unit `u` of `S` has
logarithmic derivative the trace of the logarithmic derivative of `u` (`Derivation.leibniz_norm`,
vanishing on both sides when `S` has no finite `A`-basis):

`D (Algebra.norm A u) = Algebra.norm A u * Algebra.trace A S (u⁻¹ * D' u)`.

In a basis of `S` over `A`, the derivation `D'` acts on coordinates as `D` plus a connection
matrix `Γ`, so `D` applied to the matrix of multiplication by `u` is the matrix of
multiplication by `D' u` plus the commutator of that matrix with `Γ`
(`Derivation.map_leftMulMatrix`). The commutator does not contribute to Jacobi's formula. This
is the infinitesimal form of the identity
`log (Algebra.norm A (1 + x)) = Algebra.trace A S (log (1 + x))` in complete filtered algebras
where both logarithms converge, such as Novikov rings.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §8 and §9 (determinants, norms and traces).
-/

public section

open Matrix Finset

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  (D : Derivation R A A)

/-- **Jacobi's formula**: a derivation `D` differentiates the determinant of `M` as the trace of
the adjugate of `M` times the entrywise derivative of `M`. -/
theorem leibniz_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n A) :
    D M.det = (M.adjugate * M.map D).trace := by
  have hcol (σ : Equiv.Perm n) (j : n) :
      ∏ i, M.updateCol j (fun k => D (M k j)) (σ i) i =
        (∏ i ∈ univ.erase j, M (σ i) i) * D (M (σ j) j) := by
    rw [← prod_erase_mul _ _ (mem_univ j), updateCol_self]
    congr 1
    exact prod_congr rfl fun i hi => updateCol_ne (ne_of_mem_erase hi)
  have htrace : (M.adjugate * M.map D).trace =
      ∑ j, (M.updateCol j fun k => D (M k j)).det := by
    refine sum_congr rfl fun j _ => ?_
    rw [diag_apply, Matrix.mul_apply, ← cramer_apply, cramer_eq_adjugate_mulVec]
    simp only [mulVec, dotProduct, map_apply]
  simp only [htrace, det_apply, map_sum, map_zsmul_unit, leibniz_prod, smul_eq_mul, hcol,
    smul_sum]
  exact sum_comm

/-- **The Abel–Jacobi–Liouville formula**: if a derivation `D` acts on a square matrix `M` through
the Sylvester equation `M.map D = M * P - Q * M`, then `D (det M) = det M * (tr P - tr Q)`. -/
theorem leibniz_det_of_map_eq_mul_sub_mul {n : Type*} [Fintype n] [DecidableEq n]
    {M P Q : Matrix n n A} (h : M.map D = M * P - Q * M) :
    D M.det = M.det * (P.trace - Q.trace) := by
  have hP : trace (adjugate M * (M * P)) = M.det * P.trace := by
    rw [← Matrix.mul_assoc, adjugate_mul, smul_one_mul, trace_smul, smul_eq_mul]
  have hQ : trace (adjugate M * (Q * M)) = M.det * Q.trace := by
    rw [trace_mul_comm, Matrix.mul_assoc, mul_adjugate, mul_smul_one, trace_smul, smul_eq_mul]
  rw [leibniz_det, h, Matrix.mul_sub, trace_sub, hP, hQ, mul_sub]

open Polynomial in
/-- If a derivation `D` acts on a square matrix `M` as the commutator with a matrix `B`, then it
kills every coefficient of the characteristic polynomial of `M`. This is the infinitesimal form of
the invariance of the characteristic polynomial under conjugation. -/
theorem map_charpoly_coeff_eq_zero_of_map_eq_mul_sub_mul {n : Type*} [Fintype n] [DecidableEq n]
    {M B : Matrix n n A} (h : M.map D = B * M - M * B) (i : ℕ) : D (M.charpoly.coeff i) = 0 := by
  -- Applying `D` to every coefficient is the derivation `Differential.mapCoeffs` of `A[X]`.
  let : Differential A := ⟨D.restrictScalars ℤ⟩
  have hderiv (a : A) : Differential.deriv a = D a := rfl
  -- It acts on the characteristic matrix as the commutator with `B`, up to sign.
  have hN : (charmatrix M).map Differential.mapCoeffs =
      charmatrix M * -B.map C - -B.map C * charmatrix M := by
    have hmap : (charmatrix M).map Differential.mapCoeffs = -(M.map D).map C := by
      ext p q
      by_cases hpq : p = q <;> simp [hpq, hderiv]
    have hcomm := Matrix.scalar_commute (n := n) (X : A[X]) (fun _ ↦ Commute.all _ _) (B.map C)
    rw [hmap, h, Matrix.map_sub _ (map_sub C), Matrix.map_mul, Matrix.map_mul, charmatrix,
      RingHom.mapMatrix_apply]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, hcomm.eq]
    abel
  rw [← hderiv, ← Differential.coeff_mapCoeffs, charpoly,
    leibniz_det_of_map_eq_mul_sub_mul _ hN, sub_self, mul_zero, coeff_zero]

variable {R' S : Type*} [CommSemiring R'] [CommRing S] [Algebra A S] [Algebra R' S]
  (D' : Derivation R' S S) (hD : ∀ a, D' (algebraMap A S a) = algebraMap A S (D a))

include hD

/-- **Derivations commute with the algebraic trace**: if `D'` is a derivation of an `A`-algebra `S`
extending the derivation `D` of `A`, then `D (Tr s) = Tr (D' s)`. -/
theorem map_trace (s : S) :
    D (Algebra.trace A S s) = Algebra.trace A S (D' s) := by
  classical
  by_cases H : ∃ t : Finset S, Nonempty (Module.Basis t A S)
  · let b := H.choose_spec.some
    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b, AddMonoidHom.map_trace,
      map_leftMulMatrix D D' hD b s, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_mul_comm,
      sub_self, add_zero]
  · simp [Algebra.trace_eq_zero_of_not_exists_basis A H]

/-- **Logarithmic derivative of the norm**: if `D'` is a derivation of an `A`-algebra `S` extending
the derivation `D` of `A`, then for every unit `u` of `S`,
`D (N u) = N u * Tr (u⁻¹ * D' u)`. -/
theorem leibniz_norm (u : Sˣ) :
    D (Algebra.norm A (u : S)) =
      Algebra.norm A (u : S) * Algebra.trace A S (↑u⁻¹ * D' u) := by
  classical
  by_cases H : ∃ t : Finset S, Nonempty (Module.Basis t A S)
  · let b := H.choose_spec.some
    set L := Algebra.leftMulMatrix b
    set Γ : Matrix _ _ A := of fun p q => b.repr (D' (b q)) p
    have hadj : (L u).adjugate = (L u).det • L ↑u⁻¹ :=
      adjugate_eq_det_smul_of_mul_eq_one (by rw [← map_mul, Units.mul_inv, map_one])
    have hcomm : ((L u).adjugate * (L u * Γ - Γ * L u)).trace = 0 := by
      rw [mul_sub, trace_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, adjugate_mul,
        trace_mul_cycle (L u).adjugate Γ (L u), mul_adjugate, sub_self]
    rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b, leibniz_det,
      map_leftMulMatrix D D' hD, Matrix.mul_add, trace_add, hcomm, add_zero, hadj,
      Matrix.smul_mul, trace_smul, smul_eq_mul, ← map_mul]
  · simp [Algebra.norm_eq_one_of_not_exists_basis A H,
      Algebra.trace_eq_zero_of_not_exists_basis A H]

end Derivation
