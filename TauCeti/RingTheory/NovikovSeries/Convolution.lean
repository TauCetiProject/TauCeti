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
convolution `TauCeti.NovikovSeries.convolution` of Novikov series with coefficients in `V` and `W`
along the underlying biadditive map of `β` is `R`-bilinear. This file bundles it as the bilinear
map `TauCeti.NovikovSeries.convolutionₗ β`, with coefficients
`(convolutionₗ β v w).coeff h = ∑_(u + u' = h) β (v.coeff u) (w.coeff u')`.

Along the multiplication of `R` it is the product of Novikov series
(`TauCeti.NovikovSeries.convolutionₗ_mul`). Along the tensor product `V → W → V ⊗ W` it is the
Cauchy product `TauCeti.NovikovSeries.cauchyProduct` of Novikov series with coefficients in `V`
and `W`, the shape of the quantum and Gromov–Witten products on `V ⊗̂ Λ`.

## Main definitions

* `TauCeti.NovikovSeries.convolutionₗ`: the convolution of Novikov series along a bilinear map,
  as a bilinear map.

## Main results

* `TauCeti.NovikovSeries.coeff_convolutionₗ`, `TauCeti.NovikovSeries.coeff_convolutionₗ_eq_sum`:
  the coefficients of a convolution, as sums over finite sets of pairs of exponents.
* `TauCeti.NovikovSeries.convolutionₗ_single_single`: convolving monomials adds their exponents.
* `TauCeti.NovikovSeries.convolutionₗ_mul`: convolution along the multiplication of `R` is the
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

/-- A coefficient of the convolution of `v'` and `w'` along `β`, as a sum over the pairs of
support exponents of `v, w` adding up to `h`, provided these contain the pairs of support
exponents of `v', w'`. -/
private theorem coeff_convolution_eq_sum_of_support_subset {v' : NovikovSeries V H N}
    {w' : NovikovSeries W H N} (v : NovikovSeries V H N) (w : NovikovSeries W H N) {h : H}
    (hvw : ∀ u u', v'.coeff u ≠ 0 → w'.coeff u' ≠ 0 → v.coeff u ≠ 0 ∧ w.coeff u' ≠ 0) :
    (convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v' w').coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, β (v'.coeff p.1) (w'.coeff p.2) :=
  coeff_convolution_eq_sum (fun _ hp => ((Set.Finite.mem_toFinset _).1 hp).1)
    fun u u' huu' hu hu' => (Set.Finite.mem_toFinset _).2 ⟨huu', hvw u u' hu hu'⟩

/-- Convolution along a bilinear map commutes with scalars in the first series. -/
private theorem convolution_smul_left (c : R) (v : NovikovSeries V H N)
    (w : NovikovSeries W H N) :
    convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) (c • v) w =
      c • convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v w := by
  ext h
  rw [coeff_smul, coeff_convolution_eq_sum_of_support_subset β v w fun u u' hu hu' => ?_,
    coeff_convolution_eq_sum_of_support_subset β v w fun u u' hu hu' => ⟨hu, hu'⟩, smul_sum]
  · simp only [coeff_smul, map_smul, LinearMap.smul_apply]
  · exact ⟨fun hv => hu (by rw [coeff_smul, hv, smul_zero]), hu'⟩

/-- Convolution along a bilinear map commutes with scalars in the second series. -/
private theorem convolution_smul_right (c : R) (v : NovikovSeries V H N)
    (w : NovikovSeries W H N) :
    convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v (c • w) =
      c • convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v w := by
  ext h
  rw [coeff_smul, coeff_convolution_eq_sum_of_support_subset β v w fun u u' hu hu' => ?_,
    coeff_convolution_eq_sum_of_support_subset β v w fun u u' hu hu' => ⟨hu, hu'⟩, smul_sum]
  · simp only [coeff_smul, map_smul]
  · exact ⟨hu, fun hw => hu' (by rw [coeff_smul, hw, smul_zero])⟩

/-- **The convolution of Novikov series along a bilinear map.** For an `R`-bilinear map
`β : V → W → U`, the coefficient of `convolutionₗ β v w` at `h` is
`∑_(u + u' = h) β (v_u) (w_u')`, a finite sum: it is the convolution
`TauCeti.NovikovSeries.convolution` along the underlying biadditive map of `β`. For `β` the
multiplication of `R` this is the product of Novikov series, and for the tensor product
`V → W → V ⊗ W` it is the Cauchy product of Novikov series with coefficients in `V` and `W`. -/
def convolutionₗ :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries U H N :=
  LinearMap.mk₂ R (convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom))
    (convolution_add_left _) (convolution_smul_left β) (convolution_add_right _)
    (convolution_smul_right β)

/-- The bilinear convolution is the convolution along the underlying biadditive map. -/
theorem convolutionₗ_apply (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolutionₗ β v w = convolution (LinearMap.toAddMonoidHom'.comp β.toAddMonoidHom) v w :=
  (rfl)

/-- A coefficient of the convolution is the sum of `β (v_u) (w_u')` over the finite set of pairs
of support exponents with `u + u' = h`. -/
theorem coeff_convolutionₗ (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (convolutionₗ β v w).coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, β (v.coeff p.1) (w.coeff p.2) :=
  coeff_convolution _ v w h

/-- A coefficient of the convolution is the sum of `β (v_u) (w_u')` over any finite set of pairs
`(u, u')` with `u + u' = h` containing every such pair of support exponents. -/
theorem coeff_convolutionₗ_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (convolutionₗ β v w).coeff h = ∑ p ∈ s, β (v.coeff p.1) (w.coeff p.2) :=
  coeff_convolution_eq_sum hs hvw

/-- A coefficient of the convolution as a sum over a finite set `F`, mapped injectively by `f` to
pairs adding up to `h`, whose image contains every such pair of support exponents. -/
theorem coeff_convolutionₗ_eq_sum_of_injOn {ι : Type*} {v : NovikovSeries V H N}
    {w : NovikovSeries W H N} {h : H} {F : Finset ι} {f : ι → H × H}
    (hf : ∀ t ∈ F, (f t).1 + (f t).2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → ∃ t ∈ F, f t = (u, u'))
    (hinj : Set.InjOn f F) :
    (convolutionₗ β v w).coeff h = ∑ t ∈ F, β (v.coeff (f t).1) (w.coeff (f t).2) :=
  coeff_convolution_eq_sum_of_injOn hf hvw hinj

/-- Convolving monomials adds their exponents. -/
@[simp]
theorem convolutionₗ_single_single (g g' : H) (x : V) (y : W) :
    convolutionₗ β (single g x : NovikovSeries V H N) (single g' y) = single (g + g') (β x y) :=
  convolution_single_single _ g g' x y

/-- Convolution along the multiplication of `R` is the product of Novikov series. -/
theorem convolutionₗ_mul (a b : NovikovSeries R H N) :
    convolutionₗ (LinearMap.mul R R) a b = a * b := by
  have hβ : LinearMap.toAddMonoidHom'.comp (LinearMap.mul R R).toAddMonoidHom =
      AddMonoidHom.mul := by
    ext x y
    simp
  rw [convolutionₗ_apply, mul_eq_convolution, hβ]

end NovikovSeries

end TauCeti
