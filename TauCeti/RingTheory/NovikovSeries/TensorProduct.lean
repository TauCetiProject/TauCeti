/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The Cauchy product of vector-valued Novikov series

Let `H` be a commutative group with a period homomorphism `N : H →+ ℝ`, and let `V` and `W` be
modules over a commutative semiring `R`. Novikov series with coefficients in `V` and in `W`
multiply to a Novikov series with coefficients in `V ⊗[R] W`, by the Cauchy product

`(v ⋆ w)_h = ∑_(u + u' = h) v_u ⊗ w_(u')`.

Each coefficient is a finite sum, because only finitely many pairs of support exponents add up
to a given exponent (`TauCeti.NovikovSeries.finite_setOf_add_eq`). For `V = H^*(X; ℚ)` this is
the product underlying the quantum product on the completed state module `V ⊗̂ Λ_ω` of
Gromov–Witten theory. It is the vector-valued analogue of the convolution of scalar Novikov
series in `TauCeti.RingTheory.NovikovSeries.Multiplication`.

## Main definitions

* `TauCeti.NovikovSeries.cauchyProduct`: the `R`-bilinear Cauchy product
  `NovikovSeries V H N → NovikovSeries W H N → NovikovSeries (V ⊗[R] W) H N`.

## Main statements

* `TauCeti.NovikovSeries.coeff_cauchyProduct_eq_sum`: a coefficient of the Cauchy product is a
  sum over any finite set of exponents containing the relevant support exponents.
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
  [Module R W] [AddCommGroup H] {N : H →+ ℝ}

/-- Only finitely many exponents `u` have `v_u ≠ 0` and `w_(h - u) ≠ 0`. -/
theorem finite_setOf_coeff_ne_zero_coeff_sub_ne_zero {S T : Type*} [Zero S] [Zero T]
    (v : NovikovSeries S H N) (w : NovikovSeries T H N) (h : H) :
    {u | v.coeff u ≠ 0 ∧ w.coeff (h - u) ≠ 0}.Finite :=
  ((finite_setOf_add_eq v w h).image Prod.fst).subset fun u hu =>
    ⟨(u, h - u), ⟨add_sub_cancel u h, hu.1, hu.2⟩, rfl⟩

/-- Each coefficient of the Cauchy product is a sum with finitely many nonzero terms. -/
private theorem finite_support_tmul_coeff_sub (v : NovikovSeries V H N) (w : NovikovSeries W H N)
    (h : H) : (Function.support fun u => v.coeff u ⊗ₜ[R] w.coeff (h - u)).Finite :=
  (finite_setOf_coeff_ne_zero_coeff_sub_ne_zero v w h).subset fun u hu =>
    ⟨fun hv => hu (by simp [hv]), fun hw => hu (by simp [hw])⟩

/-- The Cauchy product of two vector-valued Novikov series is a Novikov series. -/
private theorem tmul_coeff_sub_finite_lt (v : NovikovSeries V H N) (w : NovikovSeries W H N)
    (C : ℝ) :
    {h | ∑ᶠ u, v.coeff u ⊗ₜ[R] w.coeff (h - u) ≠ 0 ∧ N h < C}.Finite := by
  refine ((finite_setOf_period_add_lt v w C).image fun p => p.1 + p.2).subset ?_
  rintro h ⟨hh, hC⟩
  obtain ⟨u, hu⟩ : ∃ u, v.coeff u ⊗ₜ[R] w.coeff (h - u) ≠ 0 := by
    by_contra! hu
    exact hh (finsum_eq_zero_of_forall_eq_zero hu)
  refine ⟨(u, h - u), ⟨?_, fun hv => hu (by simp [hv]), fun hw => hu (by simp [hw])⟩,
    add_sub_cancel u h⟩
  rwa [add_sub_cancel]

/-- The Cauchy product of two vector-valued Novikov series, before bundling. -/
private def cauchyProductAux (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    NovikovSeries (V ⊗[R] W) H N where
  coeff h := ∑ᶠ u, v.coeff u ⊗ₜ[R] w.coeff (h - u)
  finite_lt := tmul_coeff_sub_finite_lt v w

variable (R) in
/-- **The Cauchy product** of Novikov series with coefficients in `V` and `W`: the series with
coefficients in `V ⊗[R] W` whose coefficient at `h` is the finite sum
`∑_(u + u' = h) v_u ⊗ w_(u')`. It is `R`-bilinear. -/
def cauchyProduct :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries (V ⊗[R] W) H N :=
  LinearMap.mk₂ R cauchyProductAux
    (fun v v' w => by
      ext h
      simp only [cauchyProductAux, coeff_add, TensorProduct.add_tmul]
      exact finsum_add_distrib (finite_support_tmul_coeff_sub v w h)
        (finite_support_tmul_coeff_sub v' w h))
    (fun r v w => by
      ext h
      simp only [cauchyProductAux, coeff_smul, ← TensorProduct.smul_tmul' (R := R)]
      exact (smul_finsum' r (finite_support_tmul_coeff_sub v w h)).symm)
    (fun v w w' => by
      ext h
      simp only [cauchyProductAux, coeff_add, TensorProduct.tmul_add]
      exact finsum_add_distrib (finite_support_tmul_coeff_sub v w h)
        (finite_support_tmul_coeff_sub v w' h))
    (fun r v w => by
      ext h
      simp only [cauchyProductAux, coeff_smul, TensorProduct.tmul_smul]
      exact (smul_finsum' r (finite_support_tmul_coeff_sub v w h)).symm)

/-- The coefficient of the Cauchy product at `h` is `∑_u v_u ⊗ w_(h - u)`. -/
theorem coeff_cauchyProduct (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (cauchyProduct R v w).coeff h = ∑ᶠ u, v.coeff u ⊗ₜ[R] w.coeff (h - u) :=
  (rfl)

/-- A coefficient of the Cauchy product is a sum over any finite set of exponents `u` containing
every `u` with `v_u ≠ 0` and `w_(h - u) ≠ 0`. -/
theorem coeff_cauchyProduct_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset H} (hs : ∀ u, v.coeff u ≠ 0 → w.coeff (h - u) ≠ 0 → u ∈ s) :
    (cauchyProduct R v w).coeff h = ∑ u ∈ s, v.coeff u ⊗ₜ[R] w.coeff (h - u) := by
  rw [coeff_cauchyProduct]
  refine finsum_eq_sum_of_support_subset _ fun u hu => hs u (fun hv => hu ?_) (fun hw => hu ?_)
  · simp [hv]
  · simp [hw]

/-- The Cauchy product of two monomials is the monomial of the sum of their exponents. -/
@[simp]
theorem cauchyProduct_single_single (A A' : H) (x : V) (y : W) :
    cauchyProduct R (single (N := N) A x) (single A' y) =
      (single (A + A') (x ⊗ₜ[R] y) : NovikovSeries (V ⊗[R] W) H N) := by
  classical
  ext h
  rw [coeff_cauchyProduct_eq_sum (s := {A}) fun u hu _ => by
    by_contra hA
    exact hu (coeff_single_of_ne (Finset.notMem_singleton.1 hA) x)]
  by_cases hh : h = A + A'
  · subst hh
    simp
  · rw [Finset.sum_singleton, coeff_single_same, coeff_single_of_ne hh,
      coeff_single_of_ne (fun h' => hh (by rw [← h']; abel)), TensorProduct.tmul_zero]

end NovikovSeries

end TauCeti
