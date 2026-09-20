/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Finite
public import TauCeti.NumberTheory.LocalField.PowerSubgroup

/-!
# The Hilbert symbol of two units of a local field of odd residue characteristic

Let `K` be a nonarchimedean local field in which `2` is a unit of the ring of integers, that is,
of odd residue characteristic. This file proves that the norm-equation Hilbert symbol
`TauCeti.hilbertSymbol` of two units of `𝒪[K]` is `1`.

The norm equation `b = x ^ 2 - a * y ^ 2` is first solved in the residue field, where the binary
form on the right is universal because the field is finite. One of the two coordinates of that
residue solution is nonzero, and clearing the other one exhibits a unit of `𝒪[K]` whose residue
is a square. Away from residue characteristic two such a unit is a square in `K`, by Hensel's
lemma, and its square root is the missing coordinate.

A pair of units is the generic case at a finite place of a number field: outside the finitely
many places dividing `2` or a coefficient of a fixed diagonalization, all the pairwise symbols of
that diagonalization are `1`, so the Hasse invariant of a global quadratic form is trivial at
almost every place.

## Main results

* `TauCeti.hilbertSymbol_unramified`: the symbol of two units of `𝒪[K]` is `1` when `2` is a unit
  of `𝒪[K]`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 63:11 and 63:12.
-/

public section

open IsLocalRing ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The Hilbert symbol is trivial at a good place.** If `2` is a unit of `𝒪[K]`, then the
norm-equation Hilbert symbol of two units of `𝒪[K]` is `1`. -/
theorem hilbertSymbol_unramified (h2 : IsUnit (2 : 𝒪[K])) {a b : Kˣ}
    (ha : a ∈ unitFiltration K 0) (hb : b ∈ unitFiltration K 0) :
    hilbertSymbol a b = 1 := by
  set A : 𝒪[K]ˣ := unitFiltrationToIntegerUnits 0 ⟨a, ha⟩
  set B : 𝒪[K]ˣ := unitFiltrationToIntegerUnits 0 ⟨b, hb⟩
  have hAK : ((A : 𝒪[K]) : K) = (a : K) := coe_unitFiltrationToIntegerUnits 0 ⟨a, ha⟩
  have hBK : ((B : 𝒪[K]) : K) = (b : K) := coe_unitFiltrationToIntegerUnits 0 ⟨b, hb⟩
  have hAres : residue 𝒪[K] (A : 𝒪[K]) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr A.isUnit
  have hBres : residue 𝒪[K] (B : 𝒪[K]) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr B.isUnit
  obtain ⟨x, y, hxy⟩ := exists_eq_sq_sub_mul_sq_of_finite hAres (residue 𝒪[K] (B : 𝒪[K]))
  obtain ⟨t, ht⟩ := residue_surjective (R := 𝒪[K]) y
  -- A unit of `𝒪[K]` whose residue is a square has a square root in `K`.
  have hsq : ∀ C : 𝒪[K]ˣ, IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) C) →
      ∃ z : K, ((C : 𝒪[K]) : K) = z ^ 2 := by
    intro C hC
    obtain ⟨r, hr⟩ := (isSquare_unitsMap_subtype_iff h2 C).mpr hC
    exact ⟨(r : K), by simpa [pow_two] using congrArg Units.val hr⟩
  rw [hilbertSymbol_eq_one_iff]
  by_cases hx : x = 0
  · -- The residue solution has first coordinate zero, so `-b * a` has square residue.
    have hy : y ≠ 0 := by
      rintro rfl
      refine hBres ?_
      rw [hxy, hx]
      ring
    have hC : IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) (-B * A)) := by
      refine ⟨Units.mk0 (residue 𝒪[K] (A : 𝒪[K]) * y) (mul_ne_zero hAres hy), Units.ext ?_⟩
      simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.val_neg, map_neg,
        map_mul, Units.val_mk0, hxy, hx]
      ring
    obtain ⟨z, hz⟩ := hsq _ hC
    have hzK : -(b : K) * (a : K) = z ^ 2 := by
      rw [← hz, ← hAK, ← hBK]
      push_cast
      ring
    refine ⟨0, z / (a : K), ?_⟩
    have ha0 : (a : K) ≠ 0 := a.ne_zero
    field_simp
    linear_combination -hzK
  · -- Otherwise `b + a * t ^ 2` has square residue, for `t` a lift of the second coordinate.
    have hres : residue 𝒪[K] ((B : 𝒪[K]) + (A : 𝒪[K]) * t ^ 2) = x ^ 2 := by
      simp only [map_add, map_mul, map_pow, ht, hxy]
      ring
    have hCunit : IsUnit ((B : 𝒪[K]) + (A : 𝒪[K]) * t ^ 2) :=
      (residue_ne_zero_iff_isUnit _).mp (by rw [hres]; exact pow_ne_zero 2 hx)
    have hC : IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) hCunit.unit) := by
      refine ⟨Units.mk0 x hx, Units.ext ?_⟩
      simp only [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, Units.val_mul,
        Units.val_mk0, hres]
      ring
    obtain ⟨z, hz⟩ := hsq _ hC
    rw [IsUnit.unit_spec] at hz
    push_cast at hz
    rw [hAK, hBK] at hz
    exact ⟨z, ((t : 𝒪[K]) : K), by linear_combination hz⟩

end TauCeti
