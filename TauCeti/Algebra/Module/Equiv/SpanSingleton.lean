/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Span

/-!
# Generators of a module isomorphic to the base ring

A generator of a module `N`, that is an element `x` with `span K {x} = ⊤`, is carried by a linear
isomorphism `N ≃ₗ[K] K` to a generator of the ideal `⊤`, that is to a unit of `K`
(`Submodule.span_image_linearEquiv`, `Ideal.span_singleton_eq_top`). So when `1` is the only unit
of the commutative semiring `K`, as for `ZMod 2`, a module isomorphic to `K` has exactly one
generator. This is what makes Thom classes with such coefficients unique on every fibre, without
any orientation.

Conversely, a linear functional `Ψ` on a module `N ≃ₗ[K] K` taking the value `1` on `x` makes `x`
a generator: `Ψ` factors through the isomorphism as multiplication by `Ψ (e⁻¹ 1)`, so `e x` is a
unit of `K` and `a ↦ a • x` is bijective.

In the same way, a linear map between two modules isomorphic to `K` is, read in the two copies of
`K`, multiplication by its value at `1`. When `K` has no zero divisors it therefore vanishes as
soon as it vanishes at a single nonzero element.

## Main results

* `LinearEquiv.span_singleton_apply_eq_top_iff`: a linear equivalence carries generators to
  generators.
* `LinearEquiv.span_singleton_eq_top_iff_isUnit`: an element of a module isomorphic to the base
  ring generates it exactly when its image is a unit.
* `LinearEquiv.eq_of_span_singleton_eq_top`: a module isomorphic to a commutative semiring whose
  only unit is `1` has a single generator.
* `LinearEquiv.isUnit_apply_of_apply_eq_one`, `LinearEquiv.bijective_smul_of_apply_eq_one`: an
  element on which a linear functional takes the value `1` is carried to a unit, and generates
  freely.
* `LinearEquiv.linearMap_eq_zero_of_apply_eq_zero`: over a semiring without zero divisors, a
  linear map between modules isomorphic to the base ring vanishing at a nonzero element is zero.
-/

public section

namespace LinearEquiv

/-- A linear equivalence carries generators to generators: `e x` spans the codomain if and only if
`x` spans the domain. -/
theorem span_singleton_apply_eq_top_iff {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) {x : M} :
    Submodule.span R {e x} = ⊤ ↔ Submodule.span R {x} = ⊤ := by
  rw [← Set.image_singleton, Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

/-- **Generators of a module isomorphic to the base ring are units**: for `e : M ≃ₗ[R] R`, an
element `x` spans `M` if and only if `e x` is a unit of `R`. Over a noncommutative ring this needs
every left inverse to be a two-sided inverse. -/
theorem span_singleton_eq_top_iff_isUnit {R M : Type*} [Semiring R] [IsDedekindFiniteMonoid R]
    [AddCommMonoid M] [Module R M] (e : M ≃ₗ[R] R) {x : M} :
    Submodule.span R {x} = ⊤ ↔ IsUnit (e x) := by
  rw [← e.span_singleton_apply_eq_top_iff, Ideal.eq_top_iff_one, Submodule.mem_span_singleton,
    isUnit_iff_exists_inv']
  simp only [smul_eq_mul]

/-- **A module isomorphic to `K` has a single generator when `1` is the only unit of `K`**: two
elements `x` and `y` of a module `N ≃ₗ[K] K` with `span K {x} = ⊤` and `span K {y} = ⊤` are
equal. -/
theorem eq_of_span_singleton_eq_top {K N : Type*} [CommSemiring K] [Subsingleton Kˣ]
    [AddCommMonoid N] [Module K N] (φ : N ≃ₗ[K] K) {x y : N}
    (hx : Submodule.span K {x} = ⊤) (hy : Submodule.span K {y} = ⊤) : x = y := by
  have hunit {z : N} (hz : Submodule.span K {z} = ⊤) : IsUnit (φ z) :=
    φ.span_singleton_eq_top_iff_isUnit.1 hz
  exact φ.injective (by
    rw [← (hunit hx).unit_spec, ← (hunit hy).unit_spec, Subsingleton.elim (hunit hx).unit])

/-- If a linear functional `Ψ` on a module `N ≃ₗ[K] K` takes the value `1` on `x`, then `e x` is a
unit of `K`, with inverse `Ψ (e⁻¹ 1)`. -/
theorem isUnit_apply_of_apply_eq_one {K N : Type*} [CommSemiring K] [AddCommMonoid N]
    [Module K N] (e : N ≃ₗ[K] K) (Ψ : N →ₗ[K] K) {x : N} (hx : Ψ x = 1) : IsUnit (e x) := by
  -- `x = e x • e⁻¹ 1`, so `Ψ x = e x * Ψ (e⁻¹ 1)`.
  have hxe : x = e x • e.symm 1 := by simp [← map_smul]
  exact IsUnit.of_mul_eq_one (Ψ (e.symm 1)) <| by simpa [hx] using (congrArg Ψ hxe).symm

/-- If a linear functional `Ψ` on a module `N ≃ₗ[K] K` takes the value `1` on `x`, then
`a ↦ a • x` is bijective. -/
theorem bijective_smul_of_apply_eq_one {K N : Type*} [CommSemiring K] [AddCommMonoid N]
    [Module K N] (e : N ≃ₗ[K] K) (Ψ : N →ₗ[K] K) {x : N} (hx : Ψ x = 1) :
    Function.Bijective fun a : K ↦ a • x := by
  -- `a ↦ a • x` is `a ↦ e⁻¹ (a * e x)`, a composite of bijections.
  convert e.symm.bijective.comp
    (Units.mulRight (e.isUnit_apply_of_apply_eq_one Ψ hx).unit).bijective using 1
  funext a
  simp [← smul_eq_mul]

/-- **A linear map between modules isomorphic to the base ring is determined by one nonzero
value.** Let `K` be a semiring without zero divisors and `e : M ≃ₗ[K] K`, `e' : N ≃ₗ[K] K`. If a
linear map `g : M →ₗ[K] N` vanishes at some nonzero `u`, then `g = 0`: read in the two copies of
`K`, `g` is left multiplication by its value at `1`, and `e u ≠ 0`. -/
theorem linearMap_eq_zero_of_apply_eq_zero {K M N : Type*} [Semiring K] [NoZeroDivisors K]
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N] (e : M ≃ₗ[K] K)
    (e' : N ≃ₗ[K] K) (g : M →ₗ[K] N) {u : M} (hu : u ≠ 0) (hg : g u = 0) : g = 0 := by
  set L : K →ₗ[K] K := e'.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap
  have hL (k : K) : L k = k * L 1 := by simpa using L.map_smul k 1
  have h1 : L 1 = 0 := by
    have h := hL (e u)
    simp only [L, LinearMap.comp_apply, coe_coe, symm_apply_apply, hg, map_zero] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (e.map_ne_zero_iff.2 hu)
  ext y
  have h := hL (e y)
  simp only [L, LinearMap.comp_apply, coe_coe, symm_apply_apply, h1, mul_zero,
    map_eq_zero_iff] at h
  exact h

end LinearEquiv
