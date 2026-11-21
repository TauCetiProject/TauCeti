/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
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
Gromov–Witten theory. Like the product of scalar Novikov series, it is a
`TauCeti.NovikovSeries.convolution`, here along the tensor product map `V →+ W →+ V ⊗[R] W`.

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

variable (R V W) in
/-- The tensor product map `v ↦ w ↦ v ⊗ w`, as an additive bilinear map. -/
private def tmulAddMonoidHom : V →+ W →+ V ⊗[R] W :=
  LinearMap.toAddMonoidHom'.comp (TensorProduct.mk R V W).toAddMonoidHom

/-- A coefficient of the Cauchy product of `v'` and `w'`, before bundling, as a sum over the pairs
of support exponents of `v, w` adding up to `h`, provided these contain the pairs of support
exponents of `v', w'`. -/
private theorem coeff_convolution_tmul_eq_sum_of_support_subset {v' : NovikovSeries V H N}
    {w' : NovikovSeries W H N} (v : NovikovSeries V H N) (w : NovikovSeries W H N) {h : H}
    (hvw : ∀ u u', v'.coeff u ≠ 0 → w'.coeff u' ≠ 0 → v.coeff u ≠ 0 ∧ w.coeff u' ≠ 0) :
    (convolution (tmulAddMonoidHom R V W) v' w').coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, v'.coeff p.1 ⊗ₜ[R] w'.coeff p.2 :=
  coeff_convolution_eq_sum (fun _ hp => ((Set.Finite.mem_toFinset _).1 hp).1)
    fun u u' huu' hu hu' => (Set.Finite.mem_toFinset _).2 ⟨huu', hvw u u' hu hu'⟩

/-- The pairs of support exponents of `r • v` and `w` are among those of `v` and `w`. -/
private theorem convolution_tmul_smul_left (r : R) (v : NovikovSeries V H N)
    (w : NovikovSeries W H N) : convolution (tmulAddMonoidHom R V W) (r • v) w =
      r • convolution (tmulAddMonoidHom R V W) v w := by
  ext h
  rw [coeff_smul, coeff_convolution_tmul_eq_sum_of_support_subset v w fun u u' hu hu' => ?_,
    coeff_convolution_tmul_eq_sum_of_support_subset v w fun u u' hu hu' => ⟨hu, hu'⟩,
    Finset.smul_sum]
  · simp only [coeff_smul, TensorProduct.smul_tmul']
  · exact ⟨fun hv => hu (by rw [coeff_smul, hv, smul_zero]), hu'⟩

/-- The pairs of support exponents of `v` and `r • w` are among those of `v` and `w`. -/
private theorem convolution_tmul_smul_right (r : R) (v : NovikovSeries V H N)
    (w : NovikovSeries W H N) : convolution (tmulAddMonoidHom R V W) v (r • w) =
      r • convolution (tmulAddMonoidHom R V W) v w := by
  ext h
  rw [coeff_smul, coeff_convolution_tmul_eq_sum_of_support_subset v w fun u u' hu hu' => ?_,
    coeff_convolution_tmul_eq_sum_of_support_subset v w fun u u' hu hu' => ⟨hu, hu'⟩,
    Finset.smul_sum]
  · simp only [coeff_smul, TensorProduct.tmul_smul]
  · exact ⟨hu, fun hw => hu' (by rw [coeff_smul, hw, smul_zero])⟩

variable (R) in
/-- **The Cauchy product** of Novikov series with coefficients in `V` and `W`: the series with
coefficients in `V ⊗[R] W` whose coefficient at `h` is the finite sum
`∑_(u + u' = h) v_u ⊗ w_(u')`, the convolution along `⊗ₜ`. It is `R`-bilinear. -/
def cauchyProduct :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries (V ⊗[R] W) H N :=
  LinearMap.mk₂ R (convolution (tmulAddMonoidHom R V W)) (convolution_add_left _)
    convolution_tmul_smul_left (convolution_add_right _) convolution_tmul_smul_right

/-- The coefficient of the Cauchy product at `h`, as a sum over the finite set of pairs of support
exponents adding up to `h`. -/
theorem coeff_cauchyProduct (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (cauchyProduct R v w).coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 :=
  coeff_convolution _ v w h

/-- A coefficient of the Cauchy product is the sum of `v_u ⊗ w_(u')` over any finite set of pairs
`(u, u')` with `u + u' = h` containing every such pair of support exponents. -/
theorem coeff_cauchyProduct_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (cauchyProduct R v w).coeff h = ∑ p ∈ s, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 :=
  coeff_convolution_eq_sum hs hvw

/-- A coefficient of the Cauchy product as a sum over a finite set `F`, mapped injectively by `f`
to pairs adding up to `h`, whose image contains every such pair of support exponents. -/
theorem coeff_cauchyProduct_eq_sum_of_injOn {ι : Type*} {v : NovikovSeries V H N}
    {w : NovikovSeries W H N} {h : H} {F : Finset ι} {f : ι → H × H}
    (hf : ∀ t ∈ F, (f t).1 + (f t).2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → ∃ t ∈ F, f t = (u, u'))
    (hinj : Set.InjOn f F) :
    (cauchyProduct R v w).coeff h = ∑ t ∈ F, v.coeff (f t).1 ⊗ₜ[R] w.coeff (f t).2 :=
  coeff_convolution_eq_sum_of_injOn hf hvw hinj

/-- The Cauchy product of two monomials is the monomial of the sum of their exponents. -/
@[simp]
theorem cauchyProduct_single_single (A A' : H) (x : V) (y : W) :
    cauchyProduct R (single (N := N) A x) (single A' y) =
      (single (A + A') (x ⊗ₜ[R] y) : NovikovSeries (V ⊗[R] W) H N) :=
  convolution_single_single _ A A' x y

end NovikovSeries

end TauCeti
