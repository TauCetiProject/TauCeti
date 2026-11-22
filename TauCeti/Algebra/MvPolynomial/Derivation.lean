/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.Derivation.BaseChange
import TauCeti.RingTheory.Derivation.Basic

/-!
# Relative derivations and support preservation for multivariate polynomials

For an `R`-algebra `B`, an `R`-derivation of `MvPolynomial σ B` is uniquely determined by its
values on base constants `C b` and polynomial variables `X i` (`MvPolynomial.derivation_ext'`).
Any `R`-derivation `d : Derivation R B B` lifts coefficientwise to an `R`-derivation
`MvPolynomial.coeffDeriv d` of `MvPolynomial σ B` acting by `d` on `C b` and annihilating `X i`.

If `s ⊆ t` and an `R`-derivation `D` of `MvPolynomial σ B` sends constants and `X i` (`i ∈ s`)
into `MvPolynomial.supported B t`, then `D` maps `MvPolynomial.supported B s` into
`MvPolynomial.supported B t` (`MvPolynomial.derivation_mem_supported`).

## Main definitions

* `MvPolynomial.coeffDeriv`: coefficientwise lift of `d : Derivation R B B` to
  `Derivation R (MvPolynomial σ B) (MvPolynomial σ B)`.

## Main results

* `MvPolynomial.adjoin_range_C_union_range_X`: `MvPolynomial σ B` is generated as an `R`-algebra
  by base constants and variables.
* `MvPolynomial.derivation_ext'`: an `R`-derivation out of `MvPolynomial σ B` is determined by its
  values on `C b` and `X i`.
* `MvPolynomial.derivation_mem_supported`: support preservation/transfer for `R`-derivations of
  `MvPolynomial σ B`.
* `MvPolynomial.coeffDeriv_C`, `MvPolynomial.coeffDeriv_X`: action of `coeffDeriv` on constants
  and variables.
-/

public section

namespace MvPolynomial

open TensorProduct

noncomputable section

section Ext

variable {R B σ : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- `MvPolynomial σ B` is generated as an `R`-algebra by base constants `C b` and polynomial
variables `X i`. -/
theorem adjoin_range_C_union_range_X (R B σ : Type*) [CommSemiring R] [CommSemiring B]
    [Algebra R B] :
    Algebra.adjoin R (Set.range (C : B → MvPolynomial σ B) ∪ Set.range X) = ⊤ := by
  rw [eq_top_iff, ← Subalgebra.restrictScalars_top R (S := B) (A := MvPolynomial σ B),
    ← MvPolynomial.adjoin_range_X (R := B) (σ := σ), Algebra.Subalgebra.restrictScalars_adjoin,
    sup_le_iff]
  refine ⟨?_, Algebra.adjoin_mono Set.subset_union_right⟩
  rintro _ ⟨b, rfl⟩
  exact Algebra.subset_adjoin (Or.inl ⟨b, rfl⟩)

/-- An `R`-derivation out of `MvPolynomial σ B` is uniquely determined by its values on base
constants `C b` and variables `X i`. -/
theorem derivation_ext' {M : Type*} [AddCommMonoid M] [Module R M] [Module (MvPolynomial σ B) M]
    {D₁ D₂ : Derivation R (MvPolynomial σ B) M}
    (hC : ∀ b : B, D₁ (C b) = D₂ (C b)) (hX : ∀ i : σ, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ := by
  refine Derivation.ext_of_adjoin_eq_top _ (adjoin_range_C_union_range_X R B σ) ?_
  rintro _ (⟨b, rfl⟩ | ⟨i, rfl⟩)
  · exact hC b
  · exact hX i

/-- If `s ⊆ t` and an `R`-derivation `D` of `MvPolynomial σ B` sends base constants `C b` and
variables `X i` for `i ∈ s` into `MvPolynomial.supported B t`, then `D` maps
`MvPolynomial.supported B s` into `MvPolynomial.supported B t`. -/
theorem derivation_mem_supported (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    {s t : Set σ} (hst : s ⊆ t) (hC : ∀ b : B, D (C b) ∈ supported B t)
    (hX : ∀ i ∈ s, D (X i) ∈ supported B t) {p : MvPolynomial σ B} (hp : p ∈ supported B s) :
    D p ∈ supported B t := by
  induction hp using Algebra.adjoin_induction with
  | mem _ hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact hX i hi
  | algebraMap b =>
    rw [MvPolynomial.algebraMap_eq]
    exact hC b
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (supported_mono hst hx) ihy) (mul_mem (supported_mono hst hy) ihx)

end Ext

section CoeffDeriv

variable {R B σ : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- Coefficientwise lift of a base derivation `d : Derivation R B B` to an `R`-derivation of
`MvPolynomial σ B`, built from `Derivation.baseChange` and `MvPolynomial.algebraTensorAlgEquiv`. -/
def coeffDeriv (d : Derivation R B B) : Derivation R (MvPolynomial σ B) (MvPolynomial σ B) :=
  ((d.baseChange (MvPolynomial σ R)).restrictScalars R).conjAlgEquiv
    ((Algebra.TensorProduct.comm R (MvPolynomial σ R) B).trans
      ((MvPolynomial.algebraTensorAlgEquiv R B).restrictScalars R))

/-- `coeffDeriv d` acts on base constants `C b` by `d`. -/
@[simp]
theorem coeffDeriv_C (d : Derivation R B B) (b : B) :
    coeffDeriv (σ := σ) d (C b) = C (d b) := by
  have h1 : (algebraTensorAlgEquiv (σ := σ) R B).symm (C b) = b ⊗ₜ[R] (1 : MvPolynomial σ R) := by
    simpa [monomial_zero'] using algebraTensorAlgEquiv_symm_monomial (σ := σ) R B 0 b
  have h2 : algebraTensorAlgEquiv (σ := σ) R B (d b ⊗ₜ[R] (1 : MvPolynomial σ R)) = C (d b) := by
    simp [algebraTensorAlgEquiv_tmul, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  simp [coeffDeriv, h1, h2]

/-- `coeffDeriv d` annihilates polynomial variables `X i`. -/
@[simp]
theorem coeffDeriv_X (d : Derivation R B B) (i : σ) :
    coeffDeriv (σ := σ) d (X i) = 0 := by
  simp [coeffDeriv]

end CoeffDeriv

end

end MvPolynomial
