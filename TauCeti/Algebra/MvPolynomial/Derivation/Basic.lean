/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
import TauCeti.Algebra.MvPolynomial.Supported

/-!
# Relative derivations and support preservation for multivariate polynomials

For an `R`-algebra `B`, an `R`-derivation of `MvPolynomial σ B` is uniquely determined by its
values on base constants `C b` and polynomial variables `X i`
(`TauCeti.MvPolynomial.derivation_ext'`).

If `s ⊆ t` and an `R`-derivation `D` of `MvPolynomial σ B` sends constants and `X i` (`i ∈ s`)
into `MvPolynomial.supported B t`, then `D` maps `MvPolynomial.supported B s` into
`MvPolynomial.supported B t` (`Derivation.map_mem_supported`).

## Main results

* `TauCeti.MvPolynomial.derivation_ext'`: an `R`-derivation out of `MvPolynomial σ B` is
  determined by its values on `C b` and `X i`.
* `Derivation.map_mem_supported`: support preservation/transfer for `R`-derivations of
  `MvPolynomial σ B`.
-/

public section

section Ext

open _root_.MvPolynomial

variable {R B σ : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- An `R`-derivation out of `MvPolynomial σ B` is uniquely determined by its values on base
constants `C b` and variables `X i`. -/
theorem TauCeti.MvPolynomial.derivation_ext' {M : Type*} [AddCommMonoid M] [Module R M]
    [Module (MvPolynomial σ B) M]
    {D₁ D₂ : Derivation R (MvPolynomial σ B) M}
    (hC : ∀ b : B, D₁ (C b) = D₂ (C b)) (hX : ∀ i : σ, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ := by
  refine Derivation.ext_of_adjoin_eq_top _ (TauCeti.MvPolynomial.adjoin_range_C_union_range_X R B σ)
    ?_
  rintro _ (⟨b, rfl⟩ | ⟨i, rfl⟩)
  · exact hC b
  · exact hX i

/-- If `s ⊆ t` and an `R`-derivation `D` of `MvPolynomial σ B` sends base constants `C b` and
variables `X i` for `i ∈ s` into `MvPolynomial.supported B t`, then `D` maps
`MvPolynomial.supported B s` into `MvPolynomial.supported B t`. -/
theorem _root_.Derivation.map_mem_supported
    (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
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
