/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.FiberProduct
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.FieldTheory.SeparableClosure

/-!
# The Galois group of a product of polynomials

Mathlib embeds the Galois group of a product into the product of the Galois groups,
`Polynomial.Gal.restrictProd : (p * q).Gal →* p.Gal × q.Gal`
(`Polynomial.Gal.restrictProd_injective`), and both components are surjective
(`Polynomial.Gal.restrictDvd_surjective`). This file describes the image when `p` and `q` are
separable. Inside the splitting field `L` of `p * q`, the splitting fields `L_p` and `L_q` of the
two factors embed, and a pair `(σ, τ)` lies in the image exactly when `σ` and `τ` agree on the
common part `L_p ∩ L_q`. So `(p * q).Gal` is the fibre product of `p.Gal` and `q.Gal` over the
Galois group of that intersection, and `restrictProd` is an isomorphism exactly when
`L_p ∩ L_q = F`.

Separability is what makes `L/F` Galois, which the description of the image uses.

## Main results

* `Polynomial.Separable.isGalois_splittingField_mul`: the splitting field of a product of two
  separable polynomials is Galois.
* `Polynomial.Gal.mem_range_restrictProd_iff`: the image of `restrictProd` consists of the pairs
  agreeing on `L_p ∩ L_q`.
* `Polynomial.Gal.restrictProd_surjective_iff`: `restrictProd` is surjective iff `L_p ∩ L_q = F`.
-/

public section

namespace TauCeti

open Polynomial IntermediateField

variable {F : Type*} [Field F] {p q : F[X]}

/-- The splitting field of a product of two separable polynomials is Galois, even though the
product itself need not be separable. -/
theorem _root_.Polynomial.Separable.isGalois_splittingField_mul (hp : p.Separable)
    (hq : q.Separable) : IsGalois F (p * q).SplittingField := by
  have hsep : Algebra.IsSeparable F (p * q).SplittingField := by
    rw [← isSeparable_top,
      ← ((isSplittingField_iff_intermediateField (p := p * q)).mp inferInstance).2,
      isSeparable_adjoin_iff_isSeparable]
    intro x hx
    rcases mul_eq_zero.1 ((map_mul (aeval x) p q).symm.trans (aeval_eq_zero_of_mem_rootSet hx))
      with h | h
    · exact hp.of_dvd (minpoly.dvd F x h)
    · exact hq.of_dvd (minpoly.dvd F x h)
  exact ⟨⟩

variable (p q) in
/-- For nonzero `p * q`, `Polynomial.Gal.restrictProd` is the joint restriction from the splitting
field of `p * q` to the splitting fields of `p` and `q`. -/
theorem _root_.Polynomial.Gal.restrictProd_eq_prod_restrict (hpq : p * q ≠ 0)
    [Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits)]
    [Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits)] :
    Gal.restrictProd p q = (Gal.restrict p (p * q).SplittingField).prod
      (Gal.restrict q (p * q).SplittingField) := by
  classical
  simp only [Gal.restrictProd, Gal.restrictDvd_def, hpq, ↓reduceDIte]
  -- The remaining difference is between two proofs of the same `Fact`.
  rfl

/-- **The Galois group of a product is a fibre product.** For separable `p` and `q`, a pair
`(σ, τ) : p.Gal × q.Gal` lies in the image of `Polynomial.Gal.restrictProd` if and only if `σ` and
`τ` agree on the elements that the splitting fields of `p` and `q` have in common inside the
splitting field of `p * q`. -/
theorem _root_.Polynomial.Gal.mem_range_restrictProd_iff (hp : p.Separable) (hq : q.Separable)
    [Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits)]
    [Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits)] (σ : p.Gal) (τ : q.Gal) :
    (σ, τ) ∈ (Gal.restrictProd p q).range ↔
      ∀ (x : p.SplittingField) (y : q.SplittingField),
        algebraMap p.SplittingField (p * q).SplittingField x =
            algebraMap q.SplittingField (p * q).SplittingField y →
          algebraMap p.SplittingField (p * q).SplittingField (σ x) =
            algebraMap q.SplittingField (p * q).SplittingField (τ y) := by
  have := hp.isGalois_splittingField_mul hq
  rw [Gal.restrictProd_eq_prod_restrict p q (mul_ne_zero hp.ne_zero hq.ne_zero)]
  exact AlgEquiv.mem_range_prod_restrictNormalHom_iff σ τ

/-- For separable `p` and `q`, `Polynomial.Gal.restrictProd` is surjective if and only if the
splitting fields of `p` and `q` meet only in `F` inside the splitting field of `p * q`. -/
theorem _root_.Polynomial.Gal.restrictProd_surjective_iff (hp : p.Separable) (hq : q.Separable)
    [Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits)]
    [Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits)] :
    Function.Surjective (Gal.restrictProd p q) ↔
      (IsScalarTower.toAlgHom F p.SplittingField (p * q).SplittingField).fieldRange ⊓
          (IsScalarTower.toAlgHom F q.SplittingField (p * q).SplittingField).fieldRange = ⊥ := by
  have := hp.isGalois_splittingField_mul hq
  rw [Gal.restrictProd_eq_prod_restrict p q (mul_ne_zero hp.ne_zero hq.ne_zero)]
  exact AlgEquiv.prod_restrictNormalHom_surjective_iff

end TauCeti
