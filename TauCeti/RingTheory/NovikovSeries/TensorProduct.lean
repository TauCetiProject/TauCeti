/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Basic
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
Gromov–Witten theory. It is the vector-valued analogue of the convolution of scalar Novikov
series in `TauCeti.RingTheory.NovikovSeries.Multiplication`.

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

/-- The Cauchy product of two vector-valued Novikov series, before bundling. -/
private def cauchyProductAux (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    NovikovSeries (V ⊗[R] W) H N where
  coeff h := ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, v.coeff p.1 ⊗ₜ[R] w.coeff p.2
  finite_lt C := ((finite_setOf_period_add_lt v w C).image fun p => p.1 + p.2).subset <| by
    rintro h ⟨hh, hC⟩
    obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
    rw [Set.Finite.mem_toFinset] at hp
    exact ⟨p, ⟨by rw [hp.1]; exact hC, hp.2⟩, hp.1⟩

/-- A coefficient of the Cauchy product, before bundling, is a sum over any finite set of pairs
adding up to the exponent and containing every such pair of support exponents. -/
private theorem coeff_cauchyProductAux_eq_sum {v : NovikovSeries V H N}
    {w : NovikovSeries W H N} {h : H} {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (cauchyProductAux (R := R) v w).coeff h = ∑ p ∈ s, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 := by
  refine Finset.sum_subset (fun p hp => ?_) fun p hps hp => ?_
  · rw [Set.Finite.mem_toFinset] at hp
    exact hvw p.1 p.2 hp.1 hp.2.1 hp.2.2
  · rw [Set.Finite.mem_toFinset] at hp
    by_cases hv : v.coeff p.1 = 0
    · rw [hv, TensorProduct.zero_tmul]
    by_cases hw : w.coeff p.2 = 0
    · rw [hw, TensorProduct.tmul_zero]
    exact absurd ⟨hs p hps, hv, hw⟩ hp

/-- A coefficient of the Cauchy product of `v'` and `w'`, before bundling, as a sum over the pairs
of support exponents of `v, w` adding up to `h`, provided these contain the pairs of support
exponents of `v', w'`. -/
private theorem coeff_cauchyProductAux_eq_sum_of_support_subset {v' : NovikovSeries V H N}
    {w' : NovikovSeries W H N} (v : NovikovSeries V H N) (w : NovikovSeries W H N) {h : H}
    (hvw : ∀ u u', v'.coeff u ≠ 0 → w'.coeff u' ≠ 0 → v.coeff u ≠ 0 ∧ w.coeff u' ≠ 0) :
    (cauchyProductAux (R := R) v' w').coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, v'.coeff p.1 ⊗ₜ[R] w'.coeff p.2 :=
  coeff_cauchyProductAux_eq_sum (fun _ hp => ((Set.Finite.mem_toFinset _).1 hp).1)
    fun u u' huu' hu hu' => (Set.Finite.mem_toFinset _).2 ⟨huu', hvw u u' hu hu'⟩

/-- A coefficient of the Cauchy product, before bundling, as a sum over the union of the pairs of
support exponents of `v₁, w₁` and of `v₂, w₂` adding up to `h`, provided these cover the pairs of
support exponents of `v, w`. -/
private theorem coeff_cauchyProductAux_eq_sum_union [DecidableEq H] {v : NovikovSeries V H N}
    {w : NovikovSeries W H N} (v₁ v₂ : NovikovSeries V H N) (w₁ w₂ : NovikovSeries W H N) {h : H}
    (hvw : ∀ u u', v.coeff u ≠ 0 → w.coeff u' ≠ 0 →
      v₁.coeff u ≠ 0 ∧ w₁.coeff u' ≠ 0 ∨ v₂.coeff u ≠ 0 ∧ w₂.coeff u' ≠ 0) :
    (cauchyProductAux (R := R) v w).coeff h = ∑ p ∈ (finite_setOf_add_eq v₁ w₁ h).toFinset ∪
      (finite_setOf_add_eq v₂ w₂ h).toFinset, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 := by
  refine coeff_cauchyProductAux_eq_sum (fun p hp => ?_) fun u u' huu' hu hu' => ?_
  · rcases Finset.mem_union.1 hp with hp | hp <;> exact ((Set.Finite.mem_toFinset _).1 hp).1
  · rcases hvw u u' hu hu' with h₁ | h₂
    · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 ⟨huu', h₁⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨huu', h₂⟩)

/-- The pairs of support exponents of `v + v'` and `w` are among those of `v` and `w` or of `v'`
and `w`. -/
private theorem cauchyProductAux_add_left (v v' : NovikovSeries V H N) (w : NovikovSeries W H N) :
    cauchyProductAux (R := R) (v + v') w = cauchyProductAux v w + cauchyProductAux v' w := by
  classical
  ext h
  rw [coeff_add, coeff_cauchyProductAux_eq_sum_union v v' w w fun u u' hu hu' => ?_,
    coeff_cauchyProductAux_eq_sum_union v v' w w fun u u' hu hu' => Or.inl ⟨hu, hu'⟩,
    coeff_cauchyProductAux_eq_sum_union v v' w w fun u u' hu hu' => Or.inr ⟨hu, hu'⟩,
    ← Finset.sum_add_distrib]
  · simp only [coeff_add, TensorProduct.add_tmul]
  · rw [coeff_add] at hu
    by_cases hv : v.coeff u = 0
    · exact Or.inr ⟨by rwa [hv, zero_add] at hu, hu'⟩
    · exact Or.inl ⟨hv, hu'⟩

/-- The pairs of support exponents of `v` and `w + w'` are among those of `v` and `w` or of `v`
and `w'`. -/
private theorem cauchyProductAux_add_right (v : NovikovSeries V H N) (w w' : NovikovSeries W H N) :
    cauchyProductAux (R := R) v (w + w') = cauchyProductAux v w + cauchyProductAux v w' := by
  classical
  ext h
  rw [coeff_add, coeff_cauchyProductAux_eq_sum_union v v w w' fun u u' hu hu' => ?_,
    coeff_cauchyProductAux_eq_sum_union v v w w' fun u u' hu hu' => Or.inl ⟨hu, hu'⟩,
    coeff_cauchyProductAux_eq_sum_union v v w w' fun u u' hu hu' => Or.inr ⟨hu, hu'⟩,
    ← Finset.sum_add_distrib]
  · simp only [coeff_add, TensorProduct.tmul_add]
  · rw [coeff_add] at hu'
    by_cases hw : w.coeff u' = 0
    · exact Or.inr ⟨hu, by rwa [hw, zero_add] at hu'⟩
    · exact Or.inl ⟨hu, hw⟩

/-- The pairs of support exponents of `r • v` and `w` are among those of `v` and `w`. -/
private theorem cauchyProductAux_smul_left (r : R) (v : NovikovSeries V H N)
    (w : NovikovSeries W H N) : cauchyProductAux (r • v) w = r • cauchyProductAux (R := R) v w := by
  ext h
  rw [coeff_smul, coeff_cauchyProductAux_eq_sum_of_support_subset v w fun u u' hu hu' => ?_,
    coeff_cauchyProductAux_eq_sum_of_support_subset v w fun u u' hu hu' => ⟨hu, hu'⟩,
    Finset.smul_sum]
  · simp only [coeff_smul, TensorProduct.smul_tmul']
  · exact ⟨fun hv => hu (by rw [coeff_smul, hv, smul_zero]), hu'⟩

/-- The pairs of support exponents of `v` and `r • w` are among those of `v` and `w`. -/
private theorem cauchyProductAux_smul_right (r : R) (v : NovikovSeries V H N)
    (w : NovikovSeries W H N) : cauchyProductAux v (r • w) = r • cauchyProductAux (R := R) v w := by
  ext h
  rw [coeff_smul, coeff_cauchyProductAux_eq_sum_of_support_subset v w fun u u' hu hu' => ?_,
    coeff_cauchyProductAux_eq_sum_of_support_subset v w fun u u' hu hu' => ⟨hu, hu'⟩,
    Finset.smul_sum]
  · simp only [coeff_smul, TensorProduct.tmul_smul]
  · exact ⟨hu, fun hw => hu' (by rw [coeff_smul, hw, smul_zero])⟩

variable (R) in
/-- **The Cauchy product** of Novikov series with coefficients in `V` and `W`: the series with
coefficients in `V ⊗[R] W` whose coefficient at `h` is the finite sum
`∑_(u + u' = h) v_u ⊗ w_(u')`. It is `R`-bilinear. -/
def cauchyProduct :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries (V ⊗[R] W) H N :=
  LinearMap.mk₂ R cauchyProductAux cauchyProductAux_add_left cauchyProductAux_smul_left
    cauchyProductAux_add_right cauchyProductAux_smul_right

/-- The coefficient of the Cauchy product at `h`, as a sum over the finite set of pairs of support
exponents adding up to `h`. -/
theorem coeff_cauchyProduct (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (cauchyProduct R v w).coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 :=
  (rfl)

/-- A coefficient of the Cauchy product is the sum of `v_u ⊗ w_(u')` over any finite set of pairs
`(u, u')` with `u + u' = h` containing every such pair of support exponents. -/
theorem coeff_cauchyProduct_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (cauchyProduct R v w).coeff h = ∑ p ∈ s, v.coeff p.1 ⊗ₜ[R] w.coeff p.2 :=
  coeff_cauchyProductAux_eq_sum hs hvw

/-- A coefficient of the Cauchy product as a sum over a finite set `F`, mapped injectively by `f`
to pairs adding up to `h`, whose image contains every such pair of support exponents. -/
theorem coeff_cauchyProduct_eq_sum_of_injOn {ι : Type*} {v : NovikovSeries V H N}
    {w : NovikovSeries W H N} {h : H} {F : Finset ι} {f : ι → H × H}
    (hf : ∀ t ∈ F, (f t).1 + (f t).2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → ∃ t ∈ F, f t = (u, u'))
    (hinj : Set.InjOn f F) :
    (cauchyProduct R v w).coeff h = ∑ t ∈ F, v.coeff (f t).1 ⊗ₜ[R] w.coeff (f t).2 := by
  classical
  rw [coeff_cauchyProduct_eq_sum (s := F.image f) (fun p hp => ?_) fun u u' huu' hu hu' =>
    Finset.mem_image.2 (hvw u u' huu' hu hu'), Finset.sum_image hinj]
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
  exact hf t ht

/-- The Cauchy product of two monomials is the monomial of the sum of their exponents. -/
@[simp]
theorem cauchyProduct_single_single (A A' : H) (x : V) (y : W) :
    cauchyProduct R (single (N := N) A x) (single A' y) =
      (single (A + A') (x ⊗ₜ[R] y) : NovikovSeries (V ⊗[R] W) H N) := by
  classical
  ext h
  rw [coeff_cauchyProduct_eq_sum (s := ({(A, A')} : Finset (H × H)).filter fun p => p.1 + p.2 = h)
    (fun p hp => (Finset.mem_filter.1 hp).2) fun u u' huu' hu hu' => ?_]
  · simp [Finset.sum_filter, coeff_single, Pi.single_apply, eq_comm]
  · refine Finset.mem_filter.2 ⟨Finset.mem_singleton.2 ?_, huu'⟩
    rw [Prod.mk.injEq]
    exact ⟨not_imp_comm.1 (coeff_single_of_ne · x) hu, not_imp_comm.1 (coeff_single_of_ne · y) hu'⟩

end NovikovSeries

end TauCeti
