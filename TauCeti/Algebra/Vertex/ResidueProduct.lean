/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Nonnegative residue products of fields

For fields `A(z)` and `B(w)`, their nonnegative residue product is
`Res_z (z - w)ⁿ [A(z), B(w)]`, for `n : ℕ`. Its coefficients are finite sums of
commutators. They define a native `VertexOperator` without any locality assumption:
on each vector, truncation follows from truncation of `B` on that vector and on the
finitely many vectors obtained by applying `A[[i]]`, for `0 ≤ i ≤ n`.

The construction is bilinear. If the fields are local of order `N`, all products
with index at least `N` vanish. These are the singular products used in the
operator product expansion; negative residue products involve normal ordering
and are not constructed here.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
-/

public section

noncomputable section

open Finset Filter

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem bddBelow_support_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V)
    (v : V) :
    BddBelow (Function.support fun k : ℤ ↦
      (∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[-k - 1 + ij.2]] -
          B[[-k - 1 + ij.2]] * A[[(ij.1 : ℤ)]])) v) := by
  have hB (w : V) : ∀ᶠ (m : ℤ) in atTop, (B[[m]]) w = 0 := by
    refine (eventually_ge_atTop (-((HahnModule.of R).symm (B w)).order)).mono ?_
    intro m hm
    exact ncoeff_eq_zero_of_lt_order B m w (by omega)
  have h : ∀ᶠ (m : ℤ) in atTop, ∀ ij ∈ antidiagonal n,
      (B[[m + ij.2]]) v = 0 ∧ (B[[m + ij.2]]) ((A[[(ij.1 : ℤ)]]) v) = 0 := by
    rw [eventually_all_finset]
    intro ij _
    exact (tendsto_atTop_add_const_right atTop (ij.2 : ℤ) tendsto_id).eventually
      ((hB v).and (hB ((A[[(ij.1 : ℤ)]]) v)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨-N, fun k hk ↦ ?_⟩
  by_contra! hlt
  apply hk
  simp only [LinearMap.sum_apply]
  apply sum_eq_zero
  intro ij hij
  obtain ⟨h₁, h₂⟩ := hN (-k - 1) (by omega) ij hij
  simp [h₁, h₂]

/-- The bilinear nonnegative residue product
`(A, B) ↦ Res_z (z - w)ⁿ [A(z), B(w)]`. -/
def nonnegResidueProduct (n : ℕ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A :=
    { toFun := fun B ↦ of_coeff (fun k ↦
        ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[-k - 1 + ij.2]] -
            B[[-k - 1 + ij.2]] * A[[(ij.1 : ℤ)]]))
        (bddBelow_support_nonnegResidueProduct n A B)
      map_add' := by
        intro B C
        apply ext_ncoeff
        intro m
        simp only [ncoeff_of_coeff, map_add, Pi.add_apply]
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro ij _
        simp only [mul_add, add_mul, ← sub_add_sub_comm, smul_add]
      map_smul' := by
        intro r B
        apply ext_ncoeff
        intro m
        simp [← smul_sub, smul_comm, smul_sum] }
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro C
    apply ext_ncoeff
    intro m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ncoeff_of_coeff, map_add,
      LinearMap.add_apply, Pi.add_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro ij _
    simp only [mul_add, add_mul, ← sub_add_sub_comm, smul_add]
  map_smul' := by
    intro r A
    apply LinearMap.ext
    intro B
    apply ext_ncoeff
    intro m
    simp [← smul_sub, smul_comm, smul_sum]

/-- The coefficients of a nonnegative residue product are the finite binomial
commutator sums. -/
@[simp]
theorem ncoeff_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V) (m : ℤ) :
    (nonnegResidueProduct n A B)[[m]] =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]]) := by
  simp [nonnegResidueProduct]

/-- Locality kills every nonnegative residue product at or above its order bound. -/
theorem IsLocalOfOrder.nonnegResidueProduct_eq_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {n : ℕ} (hn : N ≤ n) :
    nonnegResidueProduct n A B = 0 := by
  apply ext_ncoeff
  intro m
  simpa using isLocalOfOrder_iff.mp (h.mono hn) 0 m

end VertexOperator
