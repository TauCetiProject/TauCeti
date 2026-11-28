/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.FieldTheory.Finite.InvolutionNorm
import TauCeti.RingTheory.Henselian.Basic

/-!
# Fixed units of an involution of a Henselian local ring are norms

Let `R` be a Henselian local ring with finite residue field in which `2` is a unit, and `σ` an
involutive ring endomorphism of `R` that acts nontrivially on the residue field, that is
`σ t - t` is a unit for some `t ∈ R`. This is the situation of the ring of integers of an
unramified quadratic extension of nonarchimedean local fields of odd residue characteristic,
with `σ` its nontrivial automorphism. Then every unit `u` with `σ u = u` is a norm: `u = σ y * y`
for some `y ∈ R`, necessarily a unit.

The residue of `u` is fixed by the involution `τ` that `σ` induces on the residue field, so it is
a norm `τ x * x` there (`TauCeti.FiniteField.exists_apply_mul_self_eq`). A lift `y₀` of `x`
leaves the `σ`-fixed quotient `c = u / (σ y₀ * y₀) ≡ 1`, which has a square root `z ≡ 1` by
Hensel's lemma (`TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem`). Since
`σ z ^ 2 = z ^ 2` and `σ z + z ≡ 2` is a unit, `σ z = z`, and `y = y₀ * z` has `σ y * y = u`.

## Main results

* `TauCeti.HenselianLocalRing.exists_apply_mul_self_eq`: every unit fixed by `σ` is `σ y * y`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2, Proposition 3 (the norm of an unramified extension
  maps the units onto the units).
-/

public section

open IsLocalRing

namespace TauCeti.HenselianLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- **Fixed units of an involution of a Henselian local ring are norms.** Let `R` be a Henselian
local ring with finite residue field in which `2` is a unit, and `σ` an involutive ring
endomorphism of `R` with `σ t - t` a unit for some `t`. Then every unit `u` with `σ u = u` is
`σ y * y` for some `y ∈ R`. -/
theorem exists_apply_mul_self_eq (h2 : IsUnit (2 : R)) {σ : R →+* R} (hσ : ∀ z, σ (σ z) = z)
    {t : R} (ht : IsUnit (σ t - t)) {u : R} (hu : IsUnit u) (hσu : σ u = u) :
    ∃ y, σ y * y = u := by
  -- `σ` is a local homomorphism: a unit `σ z` gives the unit `z = σ (σ z)`
  have : IsLocalHom σ := ⟨fun z hz ↦ hσ z ▸ hz.map σ⟩
  have hmem {z : R} (hz : z ∈ maximalIdeal R) : σ z ∈ maximalIdeal R :=
    map_nonunit σ z hz
  -- the involution `τ` that `σ` induces on the residue field moves the residue of `t` and fixes
  -- that of `u`
  set τ := ResidueField.map σ
  have hτ (z : R) : τ (residue R z) = residue R (σ z) := ResidueField.map_residue σ z
  have hττ (x : ResidueField R) : τ (τ x) = x := by
    obtain ⟨z, rfl⟩ := residue_surjective x
    rw [hτ, hτ, hσ]
  have hτt : τ (residue R t) ≠ residue R t := by
    rw [hτ, Ne, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact fun h ↦ h ht
  obtain ⟨x, hx⟩ := FiniteField.exists_apply_mul_self_eq hττ hτt (a := residue R u)
    (by rw [hτ, hσu])
  -- a lift `y₀` of `x` has `σ y₀ * y₀ ≡ u`, a unit
  obtain ⟨y₀, rfl⟩ := residue_surjective x
  rw [hτ, ← map_mul] at hx
  have hv : IsUnit (σ y₀ * y₀) := by
    rw [← residue_ne_zero_iff_isUnit, hx, residue_ne_zero_iff_isUnit]
    exact hu
  -- the quotient `c = u / (σ y₀ * y₀)` is `≡ 1` and fixed by `σ`
  set c := u * ↑hv.unit⁻¹ with hc
  have hvc : σ y₀ * y₀ * c = u := by rw [hc, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have hσc : σ c = c := by
    have hσv : σ (σ y₀ * y₀) = σ y₀ * y₀ := by rw [map_mul, hσ, mul_comm]
    apply hv.mul_left_cancel
    rw [hvc, ← hσv, ← map_mul, hvc, hσu]
  have hc1 : c - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    apply mul_left_cancel₀ ((residue_ne_zero_iff_isUnit _).2 hv)
    rw [← map_mul, hvc, mul_one, hx]
  -- Hensel's lemma: `c = z ^ 2` with `z ≡ 1`
  obtain ⟨z, hz, hz1⟩ := HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem le_rfl
    (n := 2) (by rw [Nat.cast_ofNat]; exact h2) hc1
  -- `σ z = z`: `(σ z - z) (σ z + z) = σ c - c = 0` and `σ z + z ≡ 2` is a unit
  have hσz : σ z = z := by
    have hsum : IsUnit (σ z + z) := by
      have hm : σ z + z - 2 ∈ maximalIdeal R := by
        have := add_mem (hmem hz1) hz1
        rwa [map_sub, map_one, sub_add_sub_comm, one_add_one_eq_two] at this
      rw [← residue_ne_zero_iff_isUnit]
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
      rw [hm, residue_ne_zero_iff_isUnit]
      exact h2
    refine sub_eq_zero.1 (hsum.mul_left_eq_zero.1 ?_)
    have hσz2 : σ z ^ 2 = c := by rw [← map_pow, hz, hσc]
    linear_combination hσz2 - hz
  exact ⟨y₀ * z, by rw [map_mul, hσz, mul_mul_mul_comm, ← sq, hz, hvc]⟩

end TauCeti.HenselianLocalRing
