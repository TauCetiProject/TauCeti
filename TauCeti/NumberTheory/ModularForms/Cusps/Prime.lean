/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Residue
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.Data.ZMod.Divisibility
import Mathlib.Algebra.Field.ZMod

/-!
# Constant terms at prime level

The cusp constant terms of a modular form on `Γ₀(p)`, for prime `p`, are
determined by those at infinity and zero. In weight two they satisfy `a₀(∞) + p a₀(0) = 0`.
Consequently a weight-two form on `Γ₀(p)` is cuspidal precisely when its constant
term at infinity vanishes. This identifies the boundary data needed to split off
the corrected weight-two Eisenstein series.

The argument uses the width-weighted residue relation and the index `p + 1`,
without choosing a set of representatives for all cusp translation orbits.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§2.4, 3.1 and 4.2.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup ModularForm UpperHalfPlane
open scoped MatrixGroups

namespace ModularForm

variable {p : ℕ} [Fact p.Prime] {k : ℤ}

/-- At prime level, a cusp constant term is the one at infinity if `p` divides the
denominator of its representative, and the one at zero otherwise. -/
theorem constantTermAt_Gamma0_prime
    (f : ModularForm ((Gamma0 p).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    constantTermAt γ f =
      if (p : ℤ) ∣ γ 1 0 then constantTermAt 1 f else constantTermAt S f := by
  classical
  split_ifs with h
  · simpa using constantTermAt_mul_left
      (Subgroup.mem_map_of_mem _ (mem_Gamma0_iff_dvd.mpr h)) 1 f
  · have hc : (γ 1 0 : ZMod p) ≠ 0 := by
      exact fun hc ↦ h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc)
    obtain ⟨j, hj⟩ := ZMod.exists_dvd_sub_val_mul p (γ 1 1) (γ 1 0)
      (isUnit_iff_ne_zero.mpr hc)
    let δ := γ * T ^ (-(j.val : ℤ)) * S⁻¹
    have hδ : δ ∈ Gamma0 p := by
      rw [mem_Gamma0_iff_dvd]
      have he : δ 1 0 = (j.val : ℤ) * γ 1 0 - γ 1 1 := by
        simp [δ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          coe_T_zpow, coe_S]
        ring
      rw [he]
      exact (dvd_sub_comm).mp hj
    have hγ : γ = δ * S * T ^ (j.val : ℤ) := by simp [δ, mul_assoc]
    rw [hγ, constantTermAt_mul_T_zpow,
      constantTermAt_mul_left (Subgroup.mem_map_of_mem _ hδ)]

end ModularForm

namespace ModularForm

open TauCeti.ModularForm

variable {p : ℕ} [Fact p.Prime]

private abbrev infinityOrbit (p : ℕ) :
    CuspTranslationOrbit ((Gamma0 p).map (mapGL ℝ)) :=
  ⟦(QuotientGroup.mk 1 : 𝒮ℒ ⧸ ((Gamma0 p).map (mapGL ℝ)).subgroupOf 𝒮ℒ)⟧

private theorem constantTerm_other_orbit {k : ℤ}
    (f : ModularForm ((Gamma0 p).map (mapGL ℝ)) k)
    (c : CuspTranslationOrbit ((Gamma0 p).map (mapGL ℝ))) (hc : c ≠ infinityOrbit p) :
    constantTermAtCuspTranslationOrbit f c = constantTermAt S f := by
  induction c using Quotient.inductionOn with
  | h q =>
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨γ, hγ⟩ := x.property
      have hx : x = (mapGL ℝ).rangeRestrict γ := Subtype.ext hγ.symm
      rw [hx, constantTermAtCuspTranslationOrbit_mk_mapGL,
        ModularForm.constantTermAt_Gamma0_prime]
      refine ite_eq_right ?_
      intro h
      have hγmem : γ ∈ Gamma0 p := by
        apply (Gamma0 p).inv_mem_iff.mp
        exact mem_Gamma0_iff_dvd.mpr h
      apply hc
      congr 1
      rw [hx, QuotientGroup.eq]
      simpa only [mul_one, Subgroup.mem_subgroupOf, InvMemClass.coe_inv,
        MonoidHom.coe_rangeRestrict, ← map_inv] using
          Subgroup.mem_map_of_mem (mapGL ℝ) ((Gamma0 p).inv_mem hγmem)

/-- The two cusp constant terms of a weight-two form at prime level satisfy the
residue relation `a₀(∞) + p a₀(0) = 0`. -/
theorem weight_two_constantTermAt_one_add_prime_mul_constantTermAt_S_eq_zero
    (f : ModularForm ((Gamma0 p).map (mapGL ℝ)) 2) :
    constantTermAt 1 f + (p : ℂ) * constantTermAt S f = 0 := by
  classical
  have hwidth : cuspTranslationOrbitWidth (infinityOrbit p) = 1 := by
    rw [cuspTranslationOrbitWidth_mk_one]
    apply Nat.dvd_one.mp
    apply TauCeti.Subgroup.natCast_mem_strictPeriods_iff.mp
    simp [CongruenceSubgroup.strictPeriods_Gamma0]
  have htotal :
      ∑ c : CuspTranslationOrbit ((Gamma0 p).map (mapGL ℝ)), cuspTranslationOrbitWidth c =
        p + 1 := by
    calc
      _ = ((Gamma0 p).map (mapGL ℝ)).relIndex 𝒮ℒ := by
        rw [sum_cuspTranslationOrbitWidth, Subgroup.relIndex, Subgroup.index_eq_card]
      _ = (Gamma0 p).relIndex ⊤ := by
        rw [MonoidHom.range_eq_map (mapGL ℝ)]
        exact Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective
      _ = p + 1 := by
        rw [Subgroup.relIndex_top_right]
        exact Gamma0_prime_index p Fact.out
  have hsum :=
    weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero f
  have hterms : ∀ c : CuspTranslationOrbit ((Gamma0 p).map (mapGL ℝ)),
      (cuspTranslationOrbitWidth c : ℂ) * constantTermAtCuspTranslationOrbit f c =
        (cuspTranslationOrbitWidth c : ℂ) * constantTermAt S f +
          if c = infinityOrbit p then constantTermAt 1 f - constantTermAt S f else 0 := by
    intro c
    by_cases hc : c = infinityOrbit p
    · subst c
      have hconst : constantTermAtCuspTranslationOrbit f (infinityOrbit p) =
          constantTermAt 1 f := by
        simpa only [map_one, inv_one] using
          (constantTermAtCuspTranslationOrbit_mk_mapGL (f := f) (γ := 1))
      rw [hwidth, hconst]
      simp only [Nat.cast_one, one_mul, ite_true]
      ring
    · rw [constantTerm_other_orbit f c hc, ite_eq_right hc, add_zero]
  simp_rw [hterms] at hsum
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum, htotal] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.cast_add, Nat.cast_one] at hsum
  linear_combination hsum

end ModularForm

namespace ModularForm

variable {p : ℕ} [Fact p.Prime]

/-- A weight-two form on `Γ₀(p)` is cuspidal exactly when its constant term at infinity
vanishes. The residue relation then forces the constant term at zero to vanish too. -/
@[simp↓]
theorem weight_two_mem_cuspFormSubmodule_Gamma0_prime_iff
    (f : ModularForm ((Gamma0 p).map (mapGL ℝ)) 2) :
    f ∈ cuspFormSubmodule ((Gamma0 p).map (mapGL ℝ)) 2 ↔ constantTermAt 1 f = 0 := by
  rw [mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
  refine ⟨fun h ↦ h 1, fun h γ ↦ ?_⟩
  have hS : constantTermAt S f = 0 := by
    have hrel :=
      weight_two_constantTermAt_one_add_prime_mul_constantTermAt_S_eq_zero f
    rw [h, zero_add] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left
      (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
  rw [constantTermAt_Gamma0_prime, h, hS]
  split_ifs <;> rfl

end ModularForm
