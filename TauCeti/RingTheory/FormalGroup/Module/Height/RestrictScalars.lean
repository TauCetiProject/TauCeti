/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Module.Height.Basic
public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.RamificationInertia.Tower
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Restriction of scalars and formal-module height

Restricting a formal module along a finite extension of discrete valuation rings multiplies
its height by the rank of the extension. The ramification index enters through the order of
the smaller uniformizer's action and the residue degree through the change in residue
cardinality. For a formal module with scalars finite over the p-adic integers, this computes
the ordinary formal-group height on the special fibre.
-/

public section

open IsLocalRing

namespace TauCeti.FormalModule

variable {A O R : Type*} [CommRing O] [IsDomain O] [_root_.IsDiscreteValuationRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] {F : FormalGroup R}

section Restrict

variable (A) [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Algebra A O] [Module.Finite A O] [Algebra A R] [IsScalarTower A O R]

/-- Restricting scalars along a finite extension of DVRs multiplies height by the extension rank,
including at infinite height. -/
@[simp]
theorem height_restrictScalars (ρ : FormalModule O F) :
    (ρ.restrictScalars A).height = Module.finrank A O * ρ.height := by
  have : FaithfulSMul A O := IsDiscreteValuationRing.faithfulSMul_of_isIntegral
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible O
  let e := (maximalIdeal O).ramificationIdx A
  let f := (maximalIdeal O).inertiaDeg A
  have hef : e * f = Module.finrank A O :=
    RamificationInertia.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing A
  have hcard : Nat.card (ResidueField A) ^ f = Nat.card (ResidueField O) :=
    Ideal.cardQuot_pow_inertiaDeg (maximalIdeal A) (maximalIdeal O)
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_unit_mul_pow_ramificationIdx hπ
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A O)).mpr hπ.ne_zero) hϖ
  have hassoc : Associated (ϖ ^ e) (algebraMap A O π) := ⟨u, (mul_comm _ _).trans hu.symm⟩
  -- On the same special fibre, the two uniformizer actions have orders N^e and N.
  let τ := ρ.map (IsScalarTower.toAlgHom O R (ResidueField R))
  have hord : (PowerSeries.map (residue R) ((ρ.restrictScalars A).act π).toPowerSeries).order =
      (PowerSeries.map (residue R) (ρ.act ϖ).toPowerSeries).order ^ e := by
    simpa only [τ, restrictScalars_act, map_residue_act_toPowerSeries] using
      (τ.order_act_eq_of_associated hassoc.symm).trans (τ.order_act_pow ϖ e)
  cases hρ : ρ.height with
  | top =>
    have hd : Module.finrank A O ≠ 0 := Module.finrank_pos.ne'
    have he : e ≠ 0 := left_ne_zero_of_mul (hef ▸ hd)
    rw [ENat.mul_top (Nat.cast_ne_zero.mpr hd), (ρ.restrictScalars A).height_eq_top_iff hπ,
      ← PowerSeries.order_eq_top, hord, (ρ.height_eq_top_iff hϖ).mp hρ,
      PowerSeries.order_zero, ENat.top_pow he]
  | coe h =>
    rw [← ENat.natCast_mul, (ρ.restrictScalars A).height_eq_natCast_iff hπ, hord,
      (ρ.height_eq_natCast_iff hϖ).mp hρ, ← Nat.cast_pow, ← hcard, ← hef]
    simp only [← pow_mul, mul_comm, mul_assoc]

end Restrict

variable {p : ℕ} [Fact p.Prime]

/-- For p-adic integer scalars, formal-module height agrees with the ordinary p-height of
the formal group on the special fibre. -/
theorem height_eq_formalGroup_height [Algebra ℤ_[p] R] (ρ : FormalModule ℤ_[p] F) :
    ρ.height = (F.map (residue R)).height p := by
  rw [ρ.height_eq_of_irreducible PadicInt.irreducible_p, PadicInt.card_residueField,
    ρ.act_natCast, F.map_nsmulSeries, FormalGroup.height_eq_log_order_nsmulSeries]

/-- The p-height of a formal module with scalars finite over the p-adic integers is its
formal-module height times the rank of the scalar ring over the p-adic integers. -/
theorem formalGroup_height_eq_finrank_mul_height [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (ρ : FormalModule O F) :
    (F.map (residue R)).height p = Module.finrank ℤ_[p] O * ρ.height := by
  let : Algebra ℤ_[p] R := ((algebraMap O R).comp (algebraMap ℤ_[p] O)).toAlgebra
  have : IsScalarTower ℤ_[p] O R := IsScalarTower.of_algebraMap_eq' rfl
  exact (ρ.restrictScalars ℤ_[p]).height_eq_formalGroup_height.symm.trans
    (ρ.height_restrictScalars ℤ_[p])

end TauCeti.FormalModule
