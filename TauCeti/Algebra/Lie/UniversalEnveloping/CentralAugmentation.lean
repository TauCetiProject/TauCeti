/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PCenter

/-!
# The central augmentation ideal of a universal enveloping algebra

For a Lie algebra `L` over a commutative ring `R`, let `U(L)` be its universal enveloping
algebra.  The general Hopf-algebra construction of the intersection

`C(H) = Z(H) ∩ H⁺`

of the centre with the augmentation ideal, and of the ideal `H C(H)` it generates, lives in
`TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation`.  This file specialises that construction to
`H = U(L)` by exhibiting explicit elements of it in exponential characteristic `p`: central
`p`-polynomials and, for adjoint-nilpotent `x`, Frobenius powers of `ι x`.

As soon as `Module.End R L` is Noetherian, the central `p`-polynomial attached to each element of
`L` belongs to `C(U(L))`; over a field, finite-dimensionality of `L` supplies this hypothesis.  In
exponential characteristic `p ≠ 1`, if `x` is nilpotent in the adjoint representation, a Frobenius
power of `ι x` itself belongs to `C(U(L))`.  Taking powers then puts explicit powers of `ι x` in
every power of the generated ideal.  This is the input that later makes `x` act nilpotently on a
quotient by such a power.

## Main results

* `pPolynomial_ι_mem_centralAugmentation`: a central `p`-polynomial with zero constant term
  belongs to the intersection.
* `exists_pCentralPolynomial_mem_centralAugmentation_of_isNoetherian`:
  under the Noetherian hypothesis, every element of `L` has such a `p`-polynomial.
* `exists_pow_ι_mem_centralAugmentation_of_isNilpotent_ad`: in exponential characteristic
  `p ≠ 1`, a Frobenius power of `ι x` lies in the intersection when `ad x` is nilpotent.
* `exists_pow_mul_ι_mem_centralAugmentationIdeal_pow_of_isNilpotent_ad`:
  one Frobenius exponent works in every power of the generated ideal when `ad x` is nilpotent.

## See also

`TauCeti.HopfIdeal.centralAugmentation` and `TauCeti.HopfIdeal.centralAugmentationIdeal`, together
with their two-sidedness and their finite central generating set over a left-Noetherian Hopf
algebra, are in `TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation`.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proceedings of the American Mathematical
  Society **17** (1966), 531--533.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

open HopfIdeal

section ExpChar

variable {R L}

/-- A central `p`-polynomial with zero constant term belongs to the central augmentation
submodule. -/
theorem pPolynomial_ι_mem_centralAugmentation {p : ℕ} (hp : p ≠ 0) (e : ℕ)
    (a : Fin e → R) (x : L)
    (hcentral : _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
      Subalgebra.center R U) :
    _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
      centralAugmentation R U := by
  rw [mem_centralAugmentation]
  exact ⟨hcentral, pPolynomial_ι_mem_augmentation_toIdeal R L hp e a x⟩

variable (R L) in
/-- Every element has a central `p`-polynomial in the central augmentation submodule as soon as
`Module.End R L` is Noetherian. -/
theorem exists_pCentralPolynomial_mem_centralAugmentation_of_isNoetherian
    (p : ℕ) [ExpChar R p] [IsNoetherian R (Module.End R L)] (x : L) :
    ∃ (e : ℕ) (a : Fin e → R),
      _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
          ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
        centralAugmentation R U := by
  obtain ⟨e, a, hcentral⟩ := exists_pCentralPolynomial_of_isNoetherian R L p x
  exact ⟨e, a, pPolynomial_ι_mem_centralAugmentation (expChar_ne_zero R p) e a x hcentral⟩

/-- If `ad x` is nilpotent in exponential characteristic `p ≠ 1`, then a Frobenius power of
`ι x` belongs to the central augmentation submodule. -/
theorem exists_pow_ι_mem_centralAugmentation_of_isNilpotent_ad (p : ℕ) [ExpChar R p]
    (hp : p ≠ 1) {x : L} (h : IsNilpotent (LieAlgebra.ad R L x)) :
    ∃ e : ℕ, _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e ∈ centralAugmentation R U := by
  obtain ⟨e, hcentral⟩ := exists_pow_ι_mem_center_of_isNilpotent_ad p hp h
  refine ⟨e, (mem_centralAugmentation R U).mpr ⟨hcentral, ?_⟩⟩
  exact pow_ι_mem_augmentation_toIdeal R L x (pow_ne_zero e (expChar_ne_zero R p))

/-- If `ad x` is nilpotent, every power of the central augmentation ideal contains the
corresponding power of a Frobenius power of `ι x`. -/
theorem exists_pow_mul_ι_mem_centralAugmentationIdeal_pow_of_isNilpotent_ad
    (p : ℕ) [ExpChar R p] (hp : p ≠ 1) {x : L}
    (h : IsNilpotent (LieAlgebra.ad R L x)) :
    ∃ e : ℕ, ∀ n : ℕ, _root_.UniversalEnvelopingAlgebra.ι R x ^ (p ^ e * n) ∈
      centralAugmentationIdeal R U ^ n := by
  obtain ⟨e, he⟩ := exists_pow_ι_mem_centralAugmentation_of_isNilpotent_ad p hp h
  refine ⟨e, fun n ↦ ?_⟩
  rw [pow_mul]
  exact Ideal.pow_mem_pow (mem_centralAugmentationIdeal_of_mem_centralAugmentation R U he) n

end ExpChar

end TauCeti.UniversalEnvelopingAlgebra
