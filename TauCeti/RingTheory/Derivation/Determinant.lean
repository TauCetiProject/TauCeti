/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

/-!
# Derivations of products, determinants and norms

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
multiplication by `D' u` plus the commutator of that matrix with `Γ`; the commutator does not
contribute to Jacobi's formula. This is the infinitesimal form of the identity
`log (Algebra.norm A (1 + x)) = Algebra.trace A S (log (1 + x))` in complete filtered algebras
where both logarithms converge, such as Novikov rings.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §8 and §9 (determinants, norms and traces).
-/

public section

open Matrix Finset

namespace Derivation

section Prod

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] (D : Derivation R A M)

/-- **Leibniz rule for finite products**: `D (∏ i ∈ s, f i)` is the sum over `j ∈ s` of
`D (f j)` times the product of the other factors. -/
theorem leibniz_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ j ∈ s, (∏ i ∈ s.erase j, f i) • D (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, leibniz, ih, sum_insert ha, erase_insert ha, smul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [erase_insert_of_ne (ne_of_mem_of_not_mem hj ha).symm,
      prod_insert fun h => ha (mem_of_mem_erase h), smul_smul]

end Prod

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

/-- In a basis `b`, the coordinates of `D' x` are the derivatives of the coordinates of `x` plus
the connection term `∑ r, b.repr x r * b.repr (D' (b r)) p`. -/
private theorem repr_apply_eq {ι : Type*} [Fintype ι] (b : Module.Basis ι A S) (x : S) (p : ι) :
    b.repr (D' x) p = D (b.repr x p) + ∑ r, b.repr x r * b.repr (D' (b r)) p := by
  classical
  have hsmul (c : A) (y : S) : D' (c • y) = c • D' y + D c • y := by
    rw [Algebra.smul_def, leibniz, hD, smul_eq_mul, smul_eq_mul, mul_comm y, ← Algebra.smul_def,
      ← Algebra.smul_def]
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, map_sum, Finset.sum_apply']
  simp only [hsmul, map_add, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  rw [add_comm]

/-- In a basis `b`, the entrywise derivative of the matrix of multiplication by `s` is the matrix
of multiplication by `D' s` plus the commutator of that matrix with the connection matrix of
`D'` in `b`. -/
private theorem map_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A S) (s : S) :
    (Algebra.leftMulMatrix b s).map D = Algebra.leftMulMatrix b (D' s) +
      (Algebra.leftMulMatrix b s * (of fun p q => b.repr (D' (b q)) p) -
        (of fun p q => b.repr (D' (b q)) p) * Algebra.leftMulMatrix b s) := by
  ext p q
  have h := repr_apply_eq D D' hD b (s * b q) p
  rw [leibniz, smul_eq_mul, smul_eq_mul, mul_comm (b q), map_add, Finsupp.add_apply,
    ← Algebra.leftMulMatrix_mulVec_repr] at h
  simp only [← Algebra.leftMulMatrix_eq_repr_mul, mulVec, dotProduct] at h
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, of_apply]
  simp only [mul_comm (Algebra.leftMulMatrix b s _ q)] at h
  linear_combination -h

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
