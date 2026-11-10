/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Character
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.BoundedAtCusp
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.LevelOne
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd.Slash
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The Hecke–Schoeneberg theorem

For an even full lattice `L` of rank `2k` and level `N`, its theta series is a modular form
of weight `k` on `Γ₁(N)` with quadratic nebentypus `ZLattice.IsEven.thetaCharacter`. This file
extends the evaluated Gauss-sum transformation law to every matrix of `Γ₀(N)` and bundles the
result as `ZLattice.thetaFormOfLevel`. Membership in `TauCeti.modFormCharSpace` records the
nebentypus in the diamond-eigenspace convention, without introducing a new type of modular form.

The reduction to matrices with positive lower-left and positive odd upper-left entries uses
translation invariance and the character parity `χ(-1) = (-1)^k`. Holomorphy and boundedness
at all rational cusps are supplied by the analytic theory of theta series. The coefficients
are the representation numbers of `L`; when `L` is unimodular this construction agrees with
the level-one theta form, viewed on the smaller subgroup.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Module Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

/-- **The Hecke–Schoeneberg transformation law.** The theta series of an even full lattice of
rank `2k` transforms under every matrix of `Γ₀(level L)` by its quadratic character evaluated
at the lower-right entry. -/
theorem IsEven.thetaSeries_slash_of_mem_Gamma0 (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (level L)) :
    thetaSeries L ∣[(k : ℤ)] A =
      hL.thetaCharacter ⟨k, by omega⟩ (A 1 1 : ℤ) • thetaSeries L := by
  borelize E
  apply TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd
    (by simpa using hL.thetaCharacter_neg_one ⟨k, by omega⟩ hk)
    (hL.thetaSeries_slash_T _) ?_ hA
  intro B hB hc ha hao
  obtain ⟨a, haeq⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨c, hceq⟩ := Int.eq_ofNat_of_zero_le hc.le
  have haodd : Odd a := by rw [haeq] at hao; exact_mod_cast hao
  have hN : level L ∣ c := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB
    rw [hceq] at h
    exact_mod_cast h
  exact hL.thetaSeries_slash_eq_thetaCharacter_smul_of_odd
    ⟨k, by omega⟩ hk B haeq hceq haodd hN

/-- The theta series of an even full lattice of rank `2k`, as a modular form on
`Γ₁(level L)` of weight `k`. Its character-space membership is
`ZLattice.thetaFormOfLevel_mem_modFormCharSpace`. -/
noncomputable def thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    ModularForm ((CongruenceSubgroup.Gamma1 (level L)).map (mapGL ℝ)) k where
  toFun := thetaSeries L
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
      hL.thetaSeries_slash_of_mem_Gamma0 hk (CongruenceSubgroup.Gamma1_in_Gamma0 _ hA)]
    have hd := (CongruenceSubgroup.mem_Gamma1_iff.mp hA).2
    rw [hd, map_one, one_smul]
  holo' := mdifferentiable_thetaSeries L
  bdd_at_cusps' hc := hL.isBoundedAt_thetaSeries hk (hc.mono (Subgroup.map_le_range _ _))

/-- The underlying function of the general-level theta form is the lattice theta series. -/
@[simp]
theorem coe_thetaFormOfLevel (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    ⇑(thetaFormOfLevel hL hk) = thetaSeries L := (rfl)

/-- The general-level theta form lies in the character space of the quadratic theta character.
Equivalently, it satisfies the classical nebentypus law on `Γ₀(level L)`. -/
theorem thetaFormOfLevel_mem_modFormCharSpace (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk ∈
      TauCeti.modFormCharSpace k (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩)) := by
  apply (TauCeti.mem_modFormCharSpace_iff_nebentypus _ _ _).mpr
  intro A
  simpa only [coe_thetaFormOfLevel, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] using
    hL.thetaSeries_slash_of_mem_Gamma0 hk A.property

/-- The coefficients of the theta form in `q = exp (2 π i τ)` are representation numbers. -/
theorem qExpansion_thetaFormOfLevel_coeff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (m : ℕ) :
    (qExpansion 1 (thetaFormOfLevel hL hk)).coeff m = representationNumber L (2 * m) := by
  rw [coe_thetaFormOfLevel, hL.qExpansion_thetaSeries_coeff]

/-- The general-level theta form is nonzero. -/
@[simp]
theorem thetaFormOfLevel_ne_zero (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk ≠ 0 := fun h ↦
  thetaSeries_ne_zero_of_re_eq_zero L UpperHalfPlane.I_re (by
    rw [← coe_thetaFormOfLevel hL hk, h, FunLike.coe_zero]
    rfl)

/-- For an even unimodular lattice, the general-level construction is the restriction of the
level-one theta form. In this case `level L = 1` by `ZLattice.IsEven.level_eq_one_iff`. -/
theorem thetaFormOfLevel_eq_restrict_thetaForm (hL : IsEven L) (hU : IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) :
    thetaFormOfLevel hL hk =
      (thetaForm hL hU hk).restrict (Subgroup.map_le_range _ _) := by
  apply ModularForm.ext
  exact congrFun (by rw [ModularForm.coe_restrict, coe_thetaForm, coe_thetaFormOfLevel])

end ZLattice
