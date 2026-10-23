/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Stability
public import TauCeti.NumberTheory.ModularForms.Newforms.NumberField
public import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Hecke characteristic polynomials on the new part of `S_k(N, χ)`

For a character `χ` modulo `N` and a positive integer `n`, the Hecke operator `Tₙ` of the
`Γ₀(N)` Hecke ring preserves the new part `S_k(N, χ)ⁿᵉʷ` of `S_k(N, χ)`, the indices sharing a
factor with the level included. This file computes its characteristic polynomial
`charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ)`.

The newforms of nebentypus `χ` form a basis of `S_k(N, χ)ⁿᵉʷ` (Miyake, Theorem 4.6.13(2)), and
each of them is an eigenvector of `Tₙ` with eigenvalue its `n`th Fourier coefficient
(Diamond–Shurman, Theorem 5.8.2). So `Tₙ` is diagonal in this basis, and

`charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ) = ∏_f (X - aₙ(f))`,

the product running over the newforms `f` of level `N`, weight `k` and nebentypus `χ`. In
particular the trace of `Tₙʲ` is the power sum `∑_f aₙ(f)ʲ`, which determines the coefficients
of the characteristic polynomial through Newton's identities. The characteristic polynomial has
degree `dim S_k(N, χ)ⁿᵉʷ`, which is the number of these newforms
(`HeckeRing.GL2.Newform.finrank_cuspFormsNew_comap_cuspFormCharSpace`). In weight at least two
each `aₙ(f)` is an algebraic integer, so the characteristic polynomial has algebraic-integer
coefficients.

The factorization here is the one into linear factors over `ℂ`. Grouping the newforms into
Galois orbits refines it to the factorization into norms over the character field `ℚ(χ)`; that
refinement needs the Galois stability of the set of newforms of nebentypus `χ`.

## Main definitions

* `TauCeti.heckeTCuspNewCharEnd k χ n`: the operator `Tₙ` on `S_k(N, χ)ⁿᵉʷ`.

## Main results

* `TauCeti.heckeTCuspNewCharEnd_basisCharSpace`: `Tₙ f = aₙ(f) • f` on the basis.
* `TauCeti.charpoly_heckeTCuspNewCharEnd`: `charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ) = ∏_f (X - aₙ(f))`.
* `TauCeti.trace_heckeTCuspNewCharEnd_pow`: `tr(Tₙʲ | S_k(N, χ)ⁿᵉʷ) = ∑_f aₙ(f)ʲ`, with
  `TauCeti.trace_heckeTCuspNewCharEnd` the case `j = 1`.
* `TauCeti.isIntegral_coeff_charpoly_heckeTCuspNewCharEnd`: in weight at least two, the
  coefficients of `charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ)` are algebraic integers.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3, for the integrality of the Hecke eigenvalues.
-/

public section

open Polynomial UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

variable (k) in
/-- The Hecke operator `Tₙ` on the new part `S_k(N, χ)ⁿᵉʷ` of `S_k(N, χ)`: the operator of the
Hecke ring element `heckeTCompositeGamma0 N n`, restricted to the new forms of nebentypus `χ`. -/
noncomputable def heckeTCuspNewCharEnd (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ+) :
    Module.End ℂ ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) :=
  (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n)).restrict fun _ hF ↦
    coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_cuspFormsNew n hF

@[simp]
theorem coe_heckeTCuspNewCharEnd_apply (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ+)
    (F : (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) :
    (heckeTCuspNewCharEnd k χ n F : cuspFormCharSpace k χ) =
      heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F := (rfl)

open HeckeRing.GL2.Newform

variable {χ : (ZMod N)ˣ →* ℂˣ}

/-- **`Tₙ` acts on a newform of nebentypus `χ` by its `n`th Fourier coefficient**, in
`S_k(N, χ)ⁿᵉʷ`: `Tₙ f = aₙ(f) • f` at every positive index `n`, the indices sharing a factor
with the level included. -/
@[simp]
theorem heckeTCuspNewCharEnd_basisCharSpace (n : ℕ+) (f : {f : Newform N k // f.χ = χ}) :
    heckeTCuspNewCharEnd k χ n (basisCharSpace N k χ f) =
      (qExpansion 1 f.1.toCuspForm).coeff n • basisCharSpace N k χ f := by
  obtain ⟨f, rfl⟩ := f
  have hb : (basisCharSpace N k f.χ ⟨f, rfl⟩ : cuspFormCharSpace k f.χ) =
      ⟨f.toCuspForm, f.mem_charSpace⟩ := Subtype.ext (by simp)
  refine Subtype.ext ?_
  rw [coe_heckeTCuspNewCharEnd_apply, Submodule.coe_smul, hb,
    heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_qExpansion_coeff_smul]

/-- `Tₙʲ` acts on a newform of nebentypus `χ` by the `j`th power of its `n`th Fourier
coefficient. -/
theorem heckeTCuspNewCharEnd_pow_basisCharSpace (n : ℕ+) (j : ℕ)
    (f : {f : Newform N k // f.χ = χ}) :
    (heckeTCuspNewCharEnd k χ n ^ j) (basisCharSpace N k χ f) =
      (qExpansion 1 f.1.toCuspForm).coeff n ^ j • basisCharSpace N k χ f := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, one_smul]
  | succ j ih =>
    rw [pow_succ (heckeTCuspNewCharEnd k χ n), Module.End.mul_apply,
      heckeTCuspNewCharEnd_basisCharSpace, map_smul, ih, smul_smul, pow_succ']

/-- **The Hecke characteristic polynomial of a newspace.** The characteristic polynomial of `Tₙ`
on `S_k(N, χ)ⁿᵉʷ` is `∏_f (X - aₙ(f))`, over the newforms `f` of level `N`, weight `k` and
nebentypus `χ`, for every positive index `n`. -/
theorem charpoly_heckeTCuspNewCharEnd [Fintype {f : Newform N k // f.χ = χ}] (n : ℕ+) :
    (heckeTCuspNewCharEnd k χ n).charpoly =
      ∏ f : {f : Newform N k // f.χ = χ}, (X - C ((qExpansion 1 f.1.toCuspForm).coeff n)) := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (basisCharSpace N k χ),
    (Module.Basis.toMatrix_eq_diagonal_iff _ _ _ _).2
      (heckeTCuspNewCharEnd_basisCharSpace (χ := χ) n),
    Matrix.charpoly_diagonal]

/-- **The traces of the powers of `Tₙ` on `S_k(N, χ)ⁿᵉʷ` are the power sums of the Fourier
coefficients of the newforms**: `tr(Tₙʲ) = ∑_f aₙ(f)ʲ`, over the newforms `f` of level `N`,
weight `k` and nebentypus `χ`. These traces determine the coefficients of
`charpoly_heckeTCuspNewCharEnd` through Newton's identities. -/
theorem trace_heckeTCuspNewCharEnd_pow [Fintype {f : Newform N k // f.χ = χ}] (n : ℕ+)
    (j : ℕ) :
    LinearMap.trace ℂ _ (heckeTCuspNewCharEnd k χ n ^ j) =
      ∑ f : {f : Newform N k // f.χ = χ}, (qExpansion 1 f.1.toCuspForm).coeff n ^ j := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (basisCharSpace N k χ),
    (Module.Basis.toMatrix_eq_diagonal_iff _ _ _ _).2
      (heckeTCuspNewCharEnd_pow_basisCharSpace (χ := χ) n j),
    Matrix.trace_diagonal]

/-- **The trace of `Tₙ` on `S_k(N, χ)ⁿᵉʷ` is the sum of the `n`th Fourier coefficients of the
newforms** of level `N`, weight `k` and nebentypus `χ`. -/
theorem trace_heckeTCuspNewCharEnd [Fintype {f : Newform N k // f.χ = χ}] (n : ℕ+) :
    LinearMap.trace ℂ _ (heckeTCuspNewCharEnd k χ n) =
      ∑ f : {f : Newform N k // f.χ = χ}, (qExpansion 1 f.1.toCuspForm).coeff n := by
  simpa using trace_heckeTCuspNewCharEnd_pow (χ := χ) n 1

/-- **In weight at least two the Hecke characteristic polynomials of a newspace have
algebraic-integer coefficients**: every coefficient of `charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ)` is
integral over `ℤ`, since its roots are Fourier coefficients of newforms. -/
theorem isIntegral_coeff_charpoly_heckeTCuspNewCharEnd (hk : 2 ≤ k) (n : ℕ+) (i : ℕ) :
    IsIntegral ℤ ((heckeTCuspNewCharEnd k χ n).charpoly.coeff i) := by
  have : Fintype {f : Newform N k // f.χ = χ} := Fintype.ofFinite _
  let O := integralClosure ℤ ℂ
  have hprod : (heckeTCuspNewCharEnd k χ n).charpoly =
      (∏ f : {f : Newform N k // f.χ = χ},
        (X - C (⟨_, f.1.isIntegral_qExpansion_coeff hk n⟩ : O))).map O.val := by
    simp [charpoly_heckeTCuspNewCharEnd, Polynomial.map_prod]
  rw [hprod, coeff_map]
  exact (Subtype.prop _ : _ ∈ O)

end TauCeti
