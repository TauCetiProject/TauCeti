/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Naturality of the fundamental theorem of symmetric polynomials

By the fundamental theorem of symmetric polynomials (`MvPolynomial.esymmAlgEquiv`), every symmetric
polynomial in a finite alphabet `σ` of cardinality `n` over a commutative ring `R` is uniquely a
polynomial in the elementary symmetric polynomials `e₁, …, eₙ`. Because `MvPolynomial.map f` sends
each elementary symmetric polynomial over `R` to the corresponding elementary symmetric polynomial
over `S`, this coordinate expression commutes with changing coefficients along any ring homomorphism
`f : R →+* S`, so specializations defined through elementary-symmetric coordinates are natural in
the base ring.

## Main results

* `MvPolynomial.map_esymmAlgEquiv_symm`: `(esymmAlgEquiv σ R hn).symm` commutes with
  `MvPolynomial.map`.
-/

public section

namespace MvPolynomial

/-- Expressing a symmetric polynomial in the elementary symmetric polynomials commutes with
changing coefficients along a ring homomorphism `f : R →+* S`. -/
theorem map_esymmAlgEquiv_symm {σ R S : Type*} [Fintype σ] [CommRing R] [CommRing S] {n : ℕ}
    (hn : Fintype.card σ = n) (f : R →+* S) (p : symmetricSubalgebra σ R) :
    map f ((esymmAlgEquiv σ R hn).symm p) =
      (esymmAlgEquiv σ S hn).symm ⟨map f p, p.2.map f⟩ := by
  apply (esymmAlgEquiv σ S hn).injective
  apply Subtype.ext
  rw [(esymmAlgEquiv σ S hn).apply_symm_apply]
  have hR : aeval (fun i : Fin n ↦ esymm σ R ((i : ℕ) + 1))
      ((esymmAlgEquiv σ R hn).symm p) = p := by
    rw [← esymmAlgHom_apply, ← esymmAlgEquiv_apply σ R hn, AlgEquiv.apply_symm_apply]
  calc
    (esymmAlgEquiv σ S hn (map f ((esymmAlgEquiv σ R hn).symm p)) : MvPolynomial σ S)
      = eval₂ C (fun i : Fin n ↦ map f (esymm σ R ((i : ℕ) + 1)))
          (map f ((esymmAlgEquiv σ R hn).symm p)) := by
        simp [esymmAlgEquiv_apply, esymmAlgHom_apply, aeval_def, map_esymm]
    _ = map f (aeval (fun i : Fin n ↦ esymm σ R ((i : ℕ) + 1))
          ((esymmAlgEquiv σ R hn).symm p)) := by
        rw [eval₂_map, aeval_def, hom_eval₂]
        exact congrFun (congrArg₂ eval₂ (RingHom.ext fun _ ↦ by simp) rfl) _
    _ = map f p := congrArg (map f) hR

end MvPolynomial
