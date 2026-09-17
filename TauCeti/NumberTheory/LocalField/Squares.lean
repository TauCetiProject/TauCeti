/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.Henselian

/-!
# Deep units are squares

In a nonarchimedean local field of characteristic different from two, every unit in
`U(K, 2 v_K(2) + 1)` is a square. In particular the subgroup of squares is open, including
in residue characteristic two. This supplies the neighborhoods in which a nonzero value
stays in one square class, used in approximation arguments for quadratic forms.

The exponent is `natCastValuation K 2 h2`, so no choice of a dyadic base field is needed.
The proof identifies `𝓂[K]^(2 v_K(2) + 1)` with `4 𝓂[K]` and applies Hensel's lemma to
`X² + X - c` at zero: if `c ∈ 𝓂[K]`, then `c = t² + t` and `1 + 4c = (1 + 2t)²`.

This file proves the containment and its topological consequence, but does not assert that
the depth is sharp.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, local square theorem.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every unit of depth `2 v_K(2) + 1` is a square. This includes dyadic local fields;
only characteristic two itself is excluded. -/
theorem unitFiltration_le_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    unitFiltration K (2 * natCastValuation K 2 h2 + 1) ≤
      (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  intro x hx
  obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp hx
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have he : natCastValuation K 4 h4 = 2 * natCastValuation K 2 h2 := by
    simpa using natCastValuation_pow K 2 h2
  rw [← he, pow_succ, ← span_natCast_eq_maximalIdeal_pow K 4 h4] at hu
  obtain ⟨c, hc, hcu⟩ := Ideal.mem_span_singleton_mul.mp hu
  have hsq : IsSquare (u : 𝒪[K]) := by
    have hu' : (u : 𝒪[K]) = 1 + 4 * c := by linear_combination -hcu
    rw [hu']
    exact HenselianRing.isSquare_one_add_four_mul_of_mem hc
  obtain ⟨a, ha⟩ := hsq
  have haU : IsUnit a := isUnit_mul_self_iff.mp (ha ▸ u.isUnit)
  refine ⟨Units.map (Subring.subtype 𝒪[K]).toMonoidHom haU.unit, ?_⟩
  apply Units.ext
  simpa [pow_two, haU.unit_spec, ← hux] using congrArg (fun z : 𝒪[K] ↦ (z : K)) ha.symm

/-- The square subgroup of a nonarchimedean local field of characteristic different from two
is open in its unit group, also at dyadic places. -/
theorem isOpen_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    IsOpen ((powMonoidHom 2 : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isOpen_mono (unitFiltration_le_range_powMonoidHom_two h2)
    (isOpen_unitFiltration _)

/-- The square subgroup is closed in the unit group of a nonarchimedean local field of
characteristic different from two. -/
theorem isClosed_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    IsClosed ((powMonoidHom 2 : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_range_powMonoidHom_two h2)

end TauCeti
