/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Convolution
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The Cauchy product of vector-valued Novikov series

Let `H` be an additive monoid with a period homomorphism `N : H →+ ℝ`, and let `V` and `W` be
modules over a commutative semiring `R`. Novikov series with coefficients in `V` and in `W`
multiply to a Novikov series with coefficients in `V ⊗[R] W`, by the Cauchy product

`(v ⋆ w)_h = ∑_(u + u' = h) v_u ⊗ w_(u')`.

Each coefficient is a finite sum, because only finitely many pairs of support exponents add up
to a given exponent (`TauCeti.NovikovSeries.finite_setOf_add_eq`). For `V = H^*(X; ℚ)` this is
the product underlying the quantum product on the completed state module `V ⊗̂ Λ_ω` of
Gromov–Witten theory. Like the product of scalar Novikov series, it is a convolution: the
bilinear convolution `TauCeti.NovikovSeries.convolutionₗ` along the tensor product map
`TensorProduct.mk R V W` (`TauCeti.NovikovSeries.cauchyProduct_eq_convolutionₗ`).

## Main definitions

* `TauCeti.NovikovSeries.cauchyProduct`: the `R`-bilinear Cauchy product
  `NovikovSeries V H N → NovikovSeries W H N → NovikovSeries (V ⊗[R] W) H N`.

## Main statements

* `TauCeti.NovikovSeries.coeff_cauchyProduct_eq_sum`: a coefficient of the Cauchy product at `h`
  is a sum over any finite set of pairs adding up to `h` that contains every such pair of
  support exponents; `TauCeti.NovikovSeries.coeff_cauchyProduct_eq_sum_of_injOn` reindexes such
  a sum along an injective map.
* `TauCeti.NovikovSeries.cauchyProduct_single_single`: the Cauchy product of two monomials.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 11.1 (the Novikov ring and quantum cohomology
  with Novikov coefficients).
-/

public section

noncomputable section

open Function Set

open scoped TensorProduct

namespace TauCeti

namespace NovikovSeries

variable {R V W H : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W]
  [Module R W] [AddZeroClass H] {N : H →+ ℝ}

variable (R) in
/-- **The Cauchy product** of Novikov series with coefficients in `V` and `W`: the series with
coefficients in `V ⊗[R] W` whose coefficient at `h` is the finite sum
`∑_(u + u' = h) v_u ⊗ w_(u')`, the bilinear convolution `TauCeti.NovikovSeries.convolutionₗ`
along `⊗ₜ`. -/
def cauchyProduct :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries (V ⊗[R] W) H N :=
  convolutionₗ (TensorProduct.mk R V W)

/-- The Cauchy product is the bilinear convolution along the tensor product map. -/
theorem cauchyProduct_eq_convolutionₗ :
    cauchyProduct R = convolutionₗ (TensorProduct.mk R V W) (H := H) (N := N) :=
  (rfl)

/-- The coefficient of the Cauchy product at `h`, as a sum over the finite set of pairs of support
exponents adding up to `h`. -/
theorem coeff_cauchyProduct (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (cauchyProduct R v w).coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 :=
  coeff_convolutionₗ _ v w h

/-- A coefficient of the Cauchy product is the sum of `v_u ⊗ w_(u')` over any finite set of pairs
`(u, u')` with `u + u' = h` containing every such pair of support exponents. -/
theorem coeff_cauchyProduct_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (cauchyProduct R v w).coeff h = ∑ p ∈ s, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 :=
  coeff_convolutionₗ_eq_sum _ hs hvw

/-- A coefficient of the Cauchy product as a sum over a finite set `F`, mapped injectively by `f`
to pairs adding up to `h`, whose image contains every such pair of support exponents. -/
theorem coeff_cauchyProduct_eq_sum_of_injOn {ι : Type*} {v : NovikovSeries V H N}
    {w : NovikovSeries W H N} {h : H} {F : Finset ι} {f : ι → H × H}
    (hf : ∀ t ∈ F, (f t).1 + (f t).2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → ∃ t ∈ F, f t = (u, u'))
    (hinj : Set.InjOn f F) :
    (cauchyProduct R v w).coeff h = ∑ t ∈ F, v.coeff (f t).1 ⊗ₜ[R] w.coeff (f t).2 :=
  coeff_convolutionₗ_eq_sum_of_injOn _ hf hvw hinj

/-- The Cauchy product of two monomials is the monomial of the sum of their exponents. -/
@[simp]
theorem cauchyProduct_single_single (A A' : H) (x : V) (y : W) :
    cauchyProduct R (single (N := N) A x) (single A' y) =
      (single (A + A') (x ⊗ₜ[R] y) : NovikovSeries (V ⊗[R] W) H N) :=
  convolutionₗ_single_single _ A A' x y

end NovikovSeries

end TauCeti
