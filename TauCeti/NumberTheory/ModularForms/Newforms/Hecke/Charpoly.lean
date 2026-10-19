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
factor with the level included. Its characteristic polynomial
`charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ)` is the Hecke polynomial recorded for each newspace in the LMFDB.

The newforms of nebentypus `χ` form a basis of `S_k(N, χ)ⁿᵉʷ` (Miyake, Theorem 4.6.13(2)), and
each of them is an eigenvector of `Tₙ` with eigenvalue its `n`th Fourier coefficient
(Diamond–Shurman, Theorem 5.8.2). So `Tₙ` is diagonal in this basis, and

`charpoly(Tₙ | S_k(N, χ)ⁿᵉʷ) = ∏_f (X - aₙ(f))`,

the product running over the newforms `f` of level `N`, weight `k` and nebentypus `χ`. In
particular the trace of `Tₙʲ` is the power sum `∑_f aₙ(f)ʲ`, which determines the coefficients
of the characteristic polynomial through Newton's identities, and its degree is the number of
these newforms, the dimension of `S_k(N, χ)ⁿᵉʷ`. In weight at least two each `aₙ(f)` is an
algebraic integer, so the characteristic polynomial has algebraic-integer coefficients.

The factorization here is the one into linear factors over `ℂ`. Grouping the newforms into
Galois orbits refines it to the factorization into norms over the character field `ℚ(χ)`; that
refinement needs the Galois stability of the set of newforms of nebentypus `χ`.

## Main definitions

* `TauCeti.heckeTCuspNewCharEnd k χ n`: the operator `Tₙ` on `S_k(N, χ)ⁿᵉʷ`.
* `HeckeRing.GL2.Newform.basisCharSpace N k χ`: the newforms of nebentypus `χ`, as a basis of
  `S_k(N, χ)ⁿᵉʷ`.

## Main results

* `TauCeti.heckeTCuspNewCharEnd_basisCharSpace`: `Tₙ f = aₙ(f) • f` on the basis.
* `HeckeRing.GL2.Newform.finrank_cuspFormsNew_comap_cuspFormCharSpace`: the dimension of
  `S_k(N, χ)ⁿᵉʷ` is the number of newforms of nebentypus `χ`.
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

end TauCeti

namespace HeckeRing.GL2.Newform

open TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- A newform of nebentypus `χ`, as an element of `S_k(N, χ)ⁿᵉʷ`. -/
private noncomputable def toCuspFormsNewCharSpace {χ : (ZMod N)ˣ →* ℂˣ}
    (f : {f : Newform N k // f.χ = χ}) :
    (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype :=
  ⟨⟨f.1.toCuspForm, by obtain ⟨f, rfl⟩ := f; exact f.mem_charSpace⟩, f.1.isNew⟩

/-- The inclusion of `S_k(N, χ)ⁿᵉʷ` into `S_k(Γ₁(N))`. -/
private noncomputable abbrev cuspFormsNewCharSpaceSubtype (χ : (ZMod N)ˣ →* ℂˣ) :
    (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (cuspFormCharSpace k χ).subtype ∘ₗ
    ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype).subtype

private theorem cuspFormsNewCharSpaceSubtype_injective (χ : (ZMod N)ˣ →* ℂˣ) :
    Function.Injective (cuspFormsNewCharSpaceSubtype (k := k) χ) :=
  Subtype.val_injective.comp Subtype.val_injective

private theorem linearIndependent_toCuspFormsNewCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ (toCuspFormsNewCharSpace (k := k) (χ := χ)) :=
  LinearIndependent.of_comp (cuspFormsNewCharSpaceSubtype χ)
    (linearIndependent_toCuspForm.comp Subtype.val Subtype.val_injective)

private theorem top_le_span_range_toCuspFormsNewCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (toCuspFormsNewCharSpace (k := k) (χ := χ))) := by
  rintro F -
  rw [← Submodule.comap_map_eq_of_injective (cuspFormsNewCharSpaceSubtype_injective χ)
    (Submodule.span ℂ _), Submodule.map_span, ← Set.range_comp, Submodule.mem_comap]
  have hrange : Set.range (cuspFormsNewCharSpaceSubtype χ ∘ toCuspFormsNewCharSpace) =
      (fun f : Newform N k ↦ f.toCuspForm) '' {f | f.χ = χ} := by
    ext g
    simp [toCuspFormsNewCharSpace]
  rw [hrange, span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace]
  exact ⟨F.2, F.1.2⟩

variable (N k) in
/-- **The newforms of nebentypus `χ`, as a basis of `S_k(N, χ)ⁿᵉʷ`** (Miyake, Theorem 4.6.13(2)).
The basis vector at a newform is that newform: `Newform.coe_coe_basisCharSpace_apply`. -/
noncomputable def basisCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.Basis {f : Newform N k // f.χ = χ} ℂ
      ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) :=
  Module.Basis.mk (linearIndependent_toCuspFormsNewCharSpace χ)
    (top_le_span_range_toCuspFormsNewCharSpace χ)

/-- The basis vector of `Newform.basisCharSpace` at a newform is that newform. -/
@[simp]
theorem coe_coe_basisCharSpace_apply (χ : (ZMod N)ˣ →* ℂˣ) (f : {f : Newform N k // f.χ = χ}) :
    ((basisCharSpace N k χ f : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      f.1.toCuspForm := by
  simp [basisCharSpace, toCuspFormsNewCharSpace]

/-- **The dimension of `S_k(N, χ)ⁿᵉʷ` is the number of newforms of nebentypus `χ`.** -/
theorem finrank_cuspFormsNew_comap_cuspFormCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) =
      Nat.card {f : Newform N k // f.χ = χ} :=
  Module.finrank_eq_nat_card_basis (basisCharSpace N k χ)

end HeckeRing.GL2.Newform

namespace TauCeti

open HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **`Tₙ` acts on a newform of nebentypus `χ` by its `n`th Fourier coefficient**, in
`S_k(N, χ)ⁿᵉʷ`: `Tₙ f = aₙ(f) • f` at every positive index `n`, the indices sharing a factor
with the level included. -/
@[simp]
theorem heckeTCuspNewCharEnd_basisCharSpace (n : ℕ+) (f : {f : Newform N k // f.χ = χ}) :
    heckeTCuspNewCharEnd k χ n (basisCharSpace N k χ f) =
      (qExpansion 1 f.1.toCuspForm).coeff n • basisCharSpace N k χ f := by
  obtain ⟨f, rfl⟩ := f
  -- the eigenvector equation of the full eigenform `f.toEigenform`, read on `f` itself
  have key : ∀ g : Eigenform N k, g.toCuspForm = f.toCuspForm → g.χ = f.χ →
      heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N n) ⟨f.toCuspForm, f.mem_charSpace⟩ =
        g.eigenvalue n • ⟨f.toCuspForm, f.mem_charSpace⟩ := by
    rintro ⟨g, χ', -, a, ha, -⟩ rfl rfl
    exact ha n
  have hb : (basisCharSpace N k f.χ ⟨f, rfl⟩ : cuspFormCharSpace k f.χ) =
      ⟨f.toCuspForm, f.mem_charSpace⟩ := Subtype.ext (by simp)
  refine Subtype.ext ?_
  rw [coe_heckeTCuspNewCharEnd_apply, Submodule.coe_smul, hb,
    key f.toEigenform f.toEigenform_toCuspForm f.toEigenform_χ,
    toEigenform_eigenvalue_eq_qExpansion_coeff]

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
