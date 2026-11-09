/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.PowerSeries.Swap

/-!
# The difference of the Euler derivations of an iterated power series

An element of `R⟦X⟧⟦X⟧` is a power series in two variables, the inner variable `u` and the outer
variable `v`: the coefficient of `uᵃ vᵇ` in `f` is `coeff a (coeff b f)`. This file defines the
derivation `u ∂/∂u - v ∂/∂v`, the difference of the Euler derivations in the two variables. It
multiplies the coefficient of `uᵃ vᵇ` by `a - b`, so it kills every series in the product `u v`.

## Main definitions

* `PowerSeries.eulerDiffDerivation`: the derivation `u ∂/∂u - v ∂/∂v` of `R⟦u⟧⟦v⟧`.

## Main results

* `PowerSeries.coeff_coeff_eulerDiffDerivation`: it multiplies the coefficient of `uᵃ vᵇ` by
  `a - b`.
* `PowerSeries.map_map_eulerDiffDerivation`: it is compatible with change of coefficients.
* `PowerSeries.swap_eulerDiffDerivation`: it anticommutes with the exchange `u ↔ v`.
-/

public section

namespace PowerSeries

variable (R : Type*) [CommRing R]

/-- The derivation `u ∂/∂u - v ∂/∂v` of `R⟦u⟧⟦v⟧`, the inner variable being `u` and the outer one
`v`: it multiplies the coefficient of `uᵃ vᵇ` by `a - b`. -/
noncomputable def eulerDiffDerivation : Derivation R R⟦X⟧⟦X⟧ R⟦X⟧⟦X⟧ :=
  Derivation.mk'
    { toFun f := mk fun b ↦ mk fun a ↦ ((a : R) - b) * coeff a (coeff b f)
      map_add' f g := by
        ext b a
        simp [mul_add]
      map_smul' r f := by
        ext b a
        simp
        ring }
    fun f g ↦ by
      ext b a
      simp only [LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, smul_eq_mul, mul_comm g, map_add,
        coeff_mul, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun q hq ↦ ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
      subst hp hq
      push_cast
      ring

variable {R}

/-- The coefficient of `uᵃ vᵇ` in `(u ∂/∂u - v ∂/∂v) f` is `(a - b)` times that of `f`. -/
@[simp]
theorem coeff_coeff_eulerDiffDerivation (f : R⟦X⟧⟦X⟧) (a b : ℕ) :
    coeff a (coeff b (eulerDiffDerivation R f)) = ((a : R) - b) * coeff a (coeff b f) := by
  simp [eulerDiffDerivation]

/-- The derivation `u ∂/∂u - v ∂/∂v` is compatible with change of coefficients. -/
@[simp]
theorem map_map_eulerDiffDerivation {S : Type*} [CommRing S] (f : R →+* S) (F : R⟦X⟧⟦X⟧) :
    map (map f) (eulerDiffDerivation R F) = eulerDiffDerivation S (map (map f) F) := by
  ext b a
  simp

/-- Exchanging `u` and `v` changes the sign of `u ∂/∂u - v ∂/∂v`. -/
@[simp]
theorem swap_eulerDiffDerivation (F : R⟦X⟧⟦X⟧) :
    swap (eulerDiffDerivation R F) = -eulerDiffDerivation R (swap F) := by
  ext b a
  simp only [coeff_coeff_swap, coeff_coeff_eulerDiffDerivation, map_neg]
  ring

end PowerSeries
