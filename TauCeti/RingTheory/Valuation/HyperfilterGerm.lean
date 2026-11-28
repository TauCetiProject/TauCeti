/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ultrapowers of pre-valuation rings and surjectivity of the telescope map

An ultrapower `(U : Filter ι).Germ R` of a commutative ring `R` in which divisibility is total
(`PreValuationRing R`) along any ultrafilter `U : Ultrafilter ι` is again a `PreValuationRing`:
for any two sequences `a, b : ι → R`, at every index either `a i ∣ b i` or `b i ∣ a i`, so one
of the two holds almost everywhere along `U` (`TauCeti.preValuationRing_ultrafilter_germ`). In
particular this holds for the hyperfilter `Filter.hyperfilter ι`
(`TauCeti.preValuationRing_hyperfilter_germ`).

Moreover, in a countable ultrapower `(Filter.hyperfilter ℕ).Germ R` of any commutative ring `R`,
the telescope map `TauCeti.telescope ((Filter.hyperfilter ℕ).Germ R) a` sending `(x_j)` to
`(x_j - a * x_{j+1})` is surjective for every element `a` of the ultrapower
(`TauCeti.surjective_telescope_hyperfilter_germ`): at coordinate `k > j`, the finite sum
`∑_{i ∈ [j, k)} a^{i - j} c_i(k)` solves the `j`-th equation.

## Main results

* `TauCeti.preValuationRing_ultrafilter_germ`: an ultrapower of a `PreValuationRing` along any
  ultrafilter is a `PreValuationRing`.
* `TauCeti.preValuationRing_hyperfilter_germ`: the hyperfilter ultrapower of a `PreValuationRing`
  is a `PreValuationRing`.
* `TauCeti.surjective_telescope_hyperfilter_germ`: in `(Filter.hyperfilter ℕ).Germ R`, the
  telescope map `TauCeti.telescope` is surjective for every `a`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicComparison/Descent/TestCovers.lean`, declarations
`New.Variety.preValuationRing_hyperfilter_germ` and
`New.Variety.surjective_shiftDiff_hyperfilter_germ`, generalized from `Filter.hyperfilter ℕ` to
arbitrary ultrafilters `Ultrafilter ι` and from `a : ℕ` to arbitrary `a : (hyperfilter ℕ).Germ R`
using `TauCeti.telescope`.
-/

public section

namespace TauCeti

/-- An ultrapower of a `PreValuationRing` along any ultrafilter is again a `PreValuationRing`. -/
theorem preValuationRing_ultrafilter_germ {ι R : Type*} [CommRing R] [PreValuationRing R]
    (U : Ultrafilter ι) : PreValuationRing ((U : Filter ι).Germ R) := by
  let γ : (ι → R) →+* (U : Filter ι).Germ R := Filter.Germ.coeRingHom _
  have hγ : Function.Surjective γ := Quotient.exists_rep
  refine ⟨hγ.forall₂.mpr fun a b ↦ ?_⟩
  choose c hc using fun i ↦ PreValuationRing.cond (a i) (b i)
  have h_ae : (∀ᶠ i in (U : Filter ι), a i * c i = b i) ∨
      ∀ᶠ i in (U : Filter ι), b i * c i = a i :=
    Ultrafilter.eventually_or.mp (Filter.Eventually.of_forall hc)
  exact ⟨γ c, h_ae.imp Filter.Germ.coe_eq.mpr Filter.Germ.coe_eq.mpr⟩

/-- The hyperfilter ultrapower of a `PreValuationRing` is again a `PreValuationRing`. -/
theorem preValuationRing_hyperfilter_germ {ι R : Type*} [Infinite ι] [CommRing R]
    [PreValuationRing R] :
    PreValuationRing (((Filter.hyperfilter ι : Ultrafilter ι) : Filter ι).Germ R) :=
  preValuationRing_ultrafilter_germ (Filter.hyperfilter ι)

/-- In a countable ultrapower `(Filter.hyperfilter ℕ).Germ R` of a commutative ring `R`, the
telescope map `(x_j) ↦ (x_j - a * x_{j+1})` is surjective for every element `a`. -/
theorem surjective_telescope_hyperfilter_germ {R : Type*} [CommRing R]
    (a : ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Germ R) :
    Function.Surjective
      (telescope (((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Germ R) a) := by
  let γ : (ℕ → R) →+* ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Germ R :=
    Filter.Germ.coeRingHom _
  have hγ : Function.Surjective γ := Quotient.exists_rep
  obtain ⟨a₀, rfl⟩ := hγ a
  refine hγ.comp_left.forall.mpr fun c ↦ ?_
  let x : ℕ → ℕ → R := fun j k ↦ ∑ i ∈ Finset.range (k - j), a₀ k ^ i * c (j + i) k
  refine ⟨fun j ↦ γ (x j), funext fun j ↦ ?_⟩
  rw [telescope_apply]
  refine Filter.Germ.coe_eq.mpr ((Nat.cofinite_eq_atTop ▸ Filter.hyperfilter_le_cofinite)
    ((Filter.eventually_gt_atTop j).mono fun k hk ↦ ?_))
  have hsub : k - j = (k - (j + 1)) + 1 := by omega
  simp only [x, hsub, Finset.sum_range_succ', pow_zero, one_mul, add_zero, pow_succ',
    mul_assoc, ← Finset.mul_sum, add_assoc, add_comm 1]
  exact add_sub_cancel_left (a₀ k * _) (c j k)

end TauCeti
