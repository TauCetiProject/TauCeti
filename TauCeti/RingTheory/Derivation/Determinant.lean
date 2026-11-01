/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Derivation.Matrix

/-!
# Derivations of determinants and norms

A derivation `D` differentiates a finite product termwise (`Derivation.leibniz_prod`), and hence
a determinant by **Jacobi's formula** `D (det M) = tr (adj M * D M)`, where `D M` applies `D` to
every entry of the square matrix `M` (`Derivation.leibniz_det`).

Let `S` be a finite free algebra over a commutative ring `A`, and let `D'` be a derivation of `S`
extending a derivation `D` of `A`, in the sense that `D' (algebraMap A S a) = algebraMap A S (D a)`.
Then the norm of a unit `u` of `S` has logarithmic derivative the trace of the logarithmic
derivative of `u` (`Derivation.leibniz_norm`):

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

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (D : Derivation R A A)

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
    rw [diag_apply, mul_apply, ← cramer_apply, cramer_eq_adjugate_mulVec]
    simp only [mulVec, dotProduct, map_apply]
  simp only [htrace, det_apply, map_sum, map_zsmul_unit, leibniz_prod, smul_eq_mul, hcol,
    smul_sum]
  exact sum_comm

variable {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] (D' : Derivation R S S)
  (hD : ∀ a, D' (algebraMap A S a) = algebraMap A S (D a))

include hD

/-- **Logarithmic derivative of the norm**: if `D'` is a derivation of a finite free `A`-algebra
`S` extending the derivation `D` of `A`, then for every unit `u` of `S`,
`D (N u) = N u * Tr (u⁻¹ * D' u)`. -/
theorem leibniz_norm [Module.Free A S] [Module.Finite A S] (u : Sˣ) :
    D (Algebra.norm A (u : S)) =
      Algebra.norm A (u : S) * Algebra.trace A S (↑u⁻¹ * D' u) := by
  classical
  let b := Module.Free.chooseBasis A S
  set L := Algebra.leftMulMatrix b
  set Γ : Matrix _ _ A := of fun p q => b.repr (D' (b q)) p
  have hadj : (L u).adjugate = (L u).det • L ↑u⁻¹ := by
    calc (L u).adjugate = (L u).adjugate * (L u * L ↑u⁻¹) := by
          rw [← map_mul, Units.mul_inv, map_one, Matrix.mul_one]
      _ = (L u).det • L ↑u⁻¹ := by rw [← Matrix.mul_assoc, adjugate_mul, smul_mul, Matrix.one_mul]
  have hcomm : ((L u).adjugate * (L u * Γ - Γ * L u)).trace = 0 := by
    rw [mul_sub, trace_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, adjugate_mul,
      trace_mul_cycle (L u).adjugate Γ (L u), mul_adjugate, sub_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b, leibniz_det,
    map_leftMulMatrix D D' hD, Matrix.mul_add, trace_add, hcomm, add_zero, hadj,
    Matrix.smul_mul, trace_smul, smul_eq_mul, ← map_mul]

end Derivation
