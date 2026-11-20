/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear convolution of Novikov series

Let `H` be an additive monoid with a period homomorphism `N : H →+ ℝ`, and let
`β : V →ₗ[R] W →ₗ[R] U` be a bilinear map of modules over a commutative semiring `R`. The
convolution `TauCeti.NovikovSeries.convolve` of Novikov series with coefficients in `V` and `W`
along the underlying biadditive map of `β` is `R`-bilinear. This file bundles it as the bilinear
map `TauCeti.NovikovSeries.convolution β`, with coefficients
`(convolution β v w).coeff h = ∑_(u + u' = h) β (v.coeff u) (w.coeff u')`.

Along the multiplication of `R` it is the product of Novikov series
(`TauCeti.NovikovSeries.convolution_mul`). Along the tensor product `V → W → V ⊗ W` it is the
Cauchy product of Novikov series with coefficients in `V` and `W`, the shape of the quantum and
Gromov–Witten products on `V ⊗̂ Λ`.

## Main definitions

* `TauCeti.NovikovSeries.convolution`: the convolution of Novikov series along a bilinear map, as
  a bilinear map.

## Main results

* `TauCeti.NovikovSeries.coeff_convolution`: the coefficients of a convolution.
* `TauCeti.NovikovSeries.convolution_single_single`: convolving monomials adds their exponents.
* `TauCeti.NovikovSeries.convolution_mul`: convolution along the multiplication of `R` is the
  product of Novikov series.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*} [AddZeroClass H] {N : H →+ ℝ} [CommSemiring R] {V W U : Type*}
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]
  (β : V →ₗ[R] W →ₗ[R] U)

/-- Convolution along a bilinear map commutes with scalars in the first series. -/
private theorem convolve_smul_left (c : R) (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolve (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) (c • v) w =
      c • convolve (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v w := by
  classical
  ext h
  rw [coeff_smul, coeff_convolve_eq_sum_union _ v w v w fun u u' hu hu' =>
    Or.inl ⟨fun h0 => hu (by rw [coeff_smul, h0, smul_zero]), hu'⟩, union_self, coeff_convolve,
    smul_sum]
  simp

/-- Convolution along a bilinear map commutes with scalars in the second series. -/
private theorem convolve_smul_right (c : R) (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolve (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v (c • w) =
      c • convolve (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v w := by
  classical
  ext h
  rw [coeff_smul, coeff_convolve_eq_sum_union _ v w v w fun u u' hu hu' =>
    Or.inl ⟨hu, fun h0 => hu' (by rw [coeff_smul, h0, smul_zero])⟩, union_self, coeff_convolve,
    smul_sum]
  simp

/-- **The convolution of Novikov series along a bilinear map.** For an `R`-bilinear map
`β : V → W → U`, the coefficient of `convolution β v w` at `h` is `∑_(u + u' = h) β (v_u) (w_u')`,
a finite sum: it is the convolution `TauCeti.NovikovSeries.convolve` along the underlying
biadditive map of `β`. For `β` the multiplication of `R` this is the product of Novikov series,
and for the tensor product `V → W → V ⊗ W` it is the Cauchy product of Novikov series with
coefficients in `V` and `W`. -/
def convolution :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries U H N :=
  LinearMap.mk₂ R (convolve (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom))
    (convolve_add_left _) (convolve_smul_left β) (convolve_add_right _) (convolve_smul_right β)

/-- The bilinear convolution is the convolution along the underlying biadditive map. -/
theorem convolution_apply (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolution β v w = convolve (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v w :=
  (rfl)

/-- A coefficient of the convolution is the sum of `β (v_u) (w_u')` over the finite set of pairs
of support exponents with `u + u' = h`. -/
theorem coeff_convolution (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (convolution β v w).coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, β (v.coeff p.1) (w.coeff p.2) := by
  simp [convolution_apply, coeff_convolve]

/-- Convolving monomials adds their exponents. -/
@[simp]
theorem convolution_single_single (g g' : H) (x : V) (y : W) :
    convolution β (single g x : NovikovSeries V H N) (single g' y) = single (g + g') (β x y) :=
  convolve_single_single _ g g' x y

/-- Convolution along the multiplication of `R` is the product of Novikov series. -/
theorem convolution_mul (a b : NovikovSeries R H N) :
    convolution (LinearMap.mul R R) a b = a * b := by
  have hβ : LinearMap.toAddMonoidHom'.comp (LinearMap.mul R R).toAddMonoidHom =
      AddMonoidHom.mul := by
    ext x y
    simp
  rw [convolution_apply, mul_eq_convolve, hβ]

end NovikovSeries

end TauCeti
