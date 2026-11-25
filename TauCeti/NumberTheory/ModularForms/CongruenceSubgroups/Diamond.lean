/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Units

/-!
# Diamond actions on congruence-subgroup orbit spaces

For any `SL(2, ℤ)`-space `X`, the normalizer action of `Γ₀(N)` on `Γ₁(N) \ X` descends
along the lower-right-entry map to an action of `(ℤ/Nℤ)ˣ`. The permutation homomorphism
`TauCeti.gamma1QuotientDiamond` and its scalar action agree on every orbit class, and
`TauCeti.gamma1QuotientDiamond_comp_toHomUnits` states the factorization that characterizes it.
`TauCeti.gamma1Quotient_map_of_le_units_smul` expresses compatibility with passing to a divisor
of the level.
This applies both to the upper half-plane and to boundary orbits, at every level.
-/

public section

open CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ) {X : Type*} [MulAction SL(2, ℤ) X]

/-- The normalizer action of `Γ₀(N)` on `Γ₁(N) \ X` descends along the lower-right-entry
map to an action of `(ℤ/Nℤ)ˣ`, represented as a homomorphism to permutations. -/
noncomputable def gamma1QuotientDiamond :
    (ZMod N)ˣ →* Equiv.Perm (MulAction.orbitRel.Quotient (Gamma1 N) X) :=
  (Gamma0Map N).toHomUnits.liftOfSurjective Gamma0Map_toHomUnits_surjective
    ⟨(MulAction.normalizerOrbitRelQuotientPermHom (X := X) (Gamma1 N)).comp
      (Subgroup.inclusion (Gamma0_le_normalizer_Gamma1 N)), fun γ hγ ↦
        MulAction.normalizerOrbitRelQuotientPermHom_eq_one_of_mem (Gamma1 N) _
          ((mem_Gamma1_iff_toHomUnits_eq_one γ).mpr hγ)⟩

/-- **The diamond permutations factor the normalizer action**: precomposed with the
lower-right-entry map, `TauCeti.gamma1QuotientDiamond N` is the normalizer permutation
representation restricted to `Γ₀(N)`. Since the lower-right-entry map is surjective, this
characterizes `TauCeti.gamma1QuotientDiamond N`. -/
theorem gamma1QuotientDiamond_comp_toHomUnits :
    (gamma1QuotientDiamond N (X := X)).comp (Gamma0Map N).toHomUnits =
      (MulAction.normalizerOrbitRelQuotientPermHom (X := X) (Gamma1 N)).comp
        (Subgroup.inclusion (Gamma0_le_normalizer_Gamma1 N)) :=
  MonoidHom.liftOfRightInverse_comp _ _ _ _

/-- The diamond permutation associated to the lower-right entry of `γ ∈ Γ₀(N)` translates a
representative by `γ`. -/
theorem gamma1QuotientDiamond_apply_mk (γ : Gamma0 N) (z : X) :
    gamma1QuotientDiamond N ((Gamma0Map N).toHomUnits γ) ⟦z⟧ =
      ⟦(γ : SL(2, ℤ)) • z⟧ := by
  have h := congrArg (fun f ↦ f γ ⟦z⟧)
    (gamma1QuotientDiamond_comp_toHomUnits N (X := X))
  simpa only [MonoidHom.comp_apply,
    MulAction.normalizerOrbitRelQuotientPermHom_apply, Subgroup.coe_inclusion] using h

/-- Units modulo `N` act on `Γ₁(N) \ X` by the descended normalizer action. -/
noncomputable instance instMulActionUnitsZModGamma1Quotient :
    MulAction (ZMod N)ˣ (MulAction.orbitRel.Quotient (Gamma1 N) X) :=
  MulAction.compHom _ (gamma1QuotientDiamond N (X := X))

/-- The diamond permutation agrees with the unit action on every orbit class. -/
@[simp]
theorem gamma1QuotientDiamond_apply (d : (ZMod N)ˣ)
    (q : MulAction.orbitRel.Quotient (Gamma1 N) X) :
    gamma1QuotientDiamond N d q = d • q := by
  rw [MulAction.compHom_smul_def, Equiv.Perm.smul_def]

/-- The diamond action translates representatives by any lift of its unit to `Γ₀(N)`. -/
@[simp]
theorem units_smul_gamma1Quotient_mk (γ : Gamma0 N) (z : X) :
    (Gamma0Map N).toHomUnits γ •
        (⟦z⟧ : MulAction.orbitRel.Quotient (Gamma1 N) X) =
      ⟦(γ : SL(2, ℤ)) • z⟧ := by
  rw [← gamma1QuotientDiamond_apply]
  exact gamma1QuotientDiamond_apply_mk N γ z

/-- Passing from level `L` to a divisor `N` of `L` commutes with diamonds, reducing the unit
modulo `N`. -/
@[simp↓]
theorem gamma1Quotient_map_of_le_units_smul {L : ℕ} (h : N ∣ L) (d : (ZMod L)ˣ)
    (q : MulAction.orbitRel.Quotient (Gamma1 L) X) :
    Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (Gamma1_le_Gamma1_of_dvd h)) (d • q) =
      ZMod.unitsMap h d •
        Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (Gamma1_le_Gamma1_of_dvd h)) q := by
  obtain ⟨γ, rfl⟩ := Gamma0Map_toHomUnits_surjective d
  have hd := (Gamma0Map_toHomUnits_of_dvd h γ (Gamma0_le_Gamma0_of_dvd h γ.property)).symm
  induction q using Quotient.inductionOn with
  | h z =>
    rw [units_smul_gamma1Quotient_mk, Setoid.map_of_le_mk, Setoid.map_of_le_mk, hd,
      units_smul_gamma1Quotient_mk]

end TauCeti
