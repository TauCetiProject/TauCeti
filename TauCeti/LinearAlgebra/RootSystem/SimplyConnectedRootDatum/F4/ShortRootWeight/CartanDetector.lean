/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.Basic

/-!
# Detecting Cartan coordinates with the short-root weights of type F4

The type-`F₄` short-root weights span the integral character lattice. Consequently, their
pairings detect any four-tuple in an additive commutative group. This packages that consequence
without extending scalars or choosing a basis after reduction.

## Main declaration

* `TauCeti.DynkinType.eq_zero_of_f4ShortRootWeight_smul_eq_zero`: a four-tuple is zero if every
  short-root weight gives the zero integral linear combination of its entries.
-/

public section

namespace TauCeti.DynkinType

open scoped BigOperators

/-- **The type-`F₄` short-root weights detect four Cartan coordinates.**

This works in any additive commutative group, using its canonical `ℤ`-module structure. In
particular, it applies after reduction to characteristic two without a separate base-change
spanning argument. -/
theorem eq_zero_of_f4ShortRootWeight_smul_eq_zero {A : Type*} [AddCommGroup A]
    (h : Fin 4 → A)
    (hweights : ∀ a : Fin 26, ∑ j, f4ShortRootWeight a j • h j = 0) : h = 0 := by
  let φ₀ : (Fin 4 → ℤ) →+ A :=
    { toFun := fun x ↦ ∑ j, x j • h j
      map_zero' := by simp
      map_add' := by simp [add_smul, Finset.sum_add_distrib] }
  let φ : (Fin 4 → ℤ) →ₗ[ℤ] A := φ₀.toIntLinearMap
  have hφ_weight (a : Fin 26) : φ (f4ShortRootWeight a) = 0 := by
    simpa [φ, φ₀] using hweights a
  have hφ : φ = 0 :=
    LinearMap.ext_on_range span_range_f4ShortRootWeight_eq_top hφ_weight
  funext i
  have hi := LinearMap.congr_fun hφ (Pi.basisFun ℤ (Fin 4) i)
  simpa [φ, φ₀] using hi

/-- The short pinned F₄ roots detect every Cartan coordinate in an additive commutative group. -/
theorem eq_zero_of_f4Root_smul_eq_zero_on_short {A : Type*} [AddCommGroup A]
    (c : Fin 4 → A)
    (hc : ∀ β : Fin 48, f4Length β = 1 → ∑ i, f4Root β i • c i = 0) :
    c = 0 := by
  apply eq_zero_of_f4ShortRootWeight_smul_eq_zero
  intro a
  by_cases ha : f4ShortRootWeight a = 0
  · simp only [ha, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · obtain ⟨β, hβ, hroot⟩ :=
      (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha
    simpa only [← hroot] using hc β hβ

end TauCeti.DynkinType
