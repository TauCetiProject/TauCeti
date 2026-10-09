/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Coefficients
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The idele formation and the idele-class formation of a number field

For a number field `K` with separable closure `Kˢ` and absolute Galois group `G_K`, this file
assembles the two global formations on `G_K`:

* `ideleFormation K`, whose coefficient module is the ideles `I_{Kˢ}` of `Kˢ`
  (`TauCeti.ClassFieldTheory.IdeleCoeff K`);
* `globalFormation K`, whose coefficient module is the idele classes `C_{Kˢ} = I_{Kˢ} / (Kˢ)ˣ`
  (`TauCeti.ClassFieldTheory.IdeleClassCoeff K`).

Together with the formation `TauCeti.ClassFieldTheory.unitsFormation K` of the multiplicative
group `(Kˢ)ˣ`, they are the three terms of the exact sequence `0 → (Kˢ)ˣ → I_{Kˢ} → C_{Kˢ} → 0`
of discrete `G_K`-modules given by `principalIdele` and `ideleClassMk`. The global class
formation lives on `globalFormation K`, while the local invariants are summed on the second
cohomology of the layers of `ideleFormation K`.

By Galois descent for ideles (`mem_range_ideleCoeffOf_iff`), the level of `ideleFormation K` at
the open subgroup fixing a finite Galois subextension `E` is the idele group `I_E`
(`ideleLevelEquiv`), compatibly with the action of `Gal(E/K)` (`ideleLevelEquiv_smul`). So for a
finite Galois extension `L/K` inside `Kˢ`, the coefficient module of the layer of `L` is the
`Gal(L/K)`-module `I_L`, and the second cohomology of that layer is `H²(Gal(L/K), I_L)`.

Both coefficient modules are discrete with open stabilizers, so the continuous cohomology of `G_K`
with coefficients in either of them is the colimit of the cohomology of the finite quotients
`G_K ⧸ U` with coefficients in the `U`-invariants, by the general
`TauCeti.ContCohomology.continuousFiniteQuotientColimit`.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleFormation K`: the formation of the ideles of `Kˢ`.
* `TauCeti.ClassFieldTheory.globalFormation K`: the formation of the idele classes of `Kˢ`.
* `TauCeti.ClassFieldTheory.ideleCoeffEquivIdeleFormation K`,
  `TauCeti.ClassFieldTheory.ideleClassCoeffEquivGlobalFormation K`: their coefficient modules as
  `IdeleCoeff K` and `IdeleClassCoeff K`.
* `TauCeti.ClassFieldTheory.ideleLevelEquiv E hU`: the level of the idele formation at an open
  subgroup with fixed field a finite Galois subextension `E` is the idele group `I_E`.

## Main results

* `TauCeti.ClassFieldTheory.mem_level_ideleFormation_iff`: the level of the idele formation at an
  open subgroup with fixed field `E` consists of the ideles of `E`.
* `TauCeti.ClassFieldTheory.ideleLevelEquiv_smul`: `ideleLevelEquiv` is Galois equivariant.

## Implementation notes

As for `unitsFormation`, the bodies of the formations are not exposed, and their coefficient
modules are read through the equivariant dictionaries `ideleCoeffEquivIdeleFormation` and
`ideleClassCoeffEquivGlobalFormation`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

/-! ### The idele formation -/

/-- **The idele formation of a number field `K`**: the discrete module `I_{Kˢ}` of ideles of the
separable closure, written additively as `IdeleCoeff K`, over the absolute Galois group `G_K`. -/
def ideleFormation : Formation (AbsoluteGaloisGroup K) :=
  ⟨ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (IdeleCoeff K),
    ofDiscreteModule_isSmoothDiscrete ℤ (AbsoluteGaloisGroup K) (IdeleCoeff K)⟩

/-- **The coefficient dictionary** between `IdeleCoeff K` and the coefficient module of
`ideleFormation K`. It is equivariant by `ideleCoeffEquivIdeleFormation_smul`. -/
def ideleCoeffEquivIdeleFormation : IdeleCoeff K ≃+ (ideleFormation K).toRep.V :=
  AddEquiv.refl _

/-- **The coefficient dictionary of the idele formation is equivariant**: `G_K` acts on the
coefficient module of `ideleFormation K` as it acts on the ideles of `Kˢ`. -/
@[simp]
theorem ideleCoeffEquivIdeleFormation_smul (g : AbsoluteGaloisGroup K) (x : IdeleCoeff K) :
    ideleCoeffEquivIdeleFormation K (g • x) =
      (ideleFormation K).toRep.ρ g (ideleCoeffEquivIdeleFormation K x) :=
  (rfl)

/-! ### The idele-class formation -/

/-- **The idele-class formation of a number field `K`**: the discrete module `C_{Kˢ}` of idele
classes of the separable closure, written additively as `IdeleClassCoeff K`, over the absolute
Galois group `G_K`. -/
def globalFormation : Formation (AbsoluteGaloisGroup K) :=
  ⟨ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (IdeleClassCoeff K),
    ofDiscreteModule_isSmoothDiscrete ℤ (AbsoluteGaloisGroup K) (IdeleClassCoeff K)⟩

/-- **The coefficient dictionary** between `IdeleClassCoeff K` and the coefficient module of
`globalFormation K`. It is equivariant by `ideleClassCoeffEquivGlobalFormation_smul`. -/
def ideleClassCoeffEquivGlobalFormation : IdeleClassCoeff K ≃+ (globalFormation K).toRep.V :=
  AddEquiv.refl _

/-- **The coefficient dictionary of the idele-class formation is equivariant**: `G_K` acts on the
coefficient module of `globalFormation K` as it acts on the idele classes of `Kˢ`. -/
@[simp]
theorem ideleClassCoeffEquivGlobalFormation_smul (g : AbsoluteGaloisGroup K)
    (x : IdeleClassCoeff K) :
    ideleClassCoeffEquivGlobalFormation K (g • x) =
      (globalFormation K).toRep.ρ g (ideleClassCoeffEquivGlobalFormation K x) :=
  (rfl)

/-! ### The levels of the idele formation -/

section Level

open IntermediateField NumberField

variable {K}

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-- **The level of the idele formation at an open subgroup with fixed field `E`** consists of the
ideles of `E`. -/
theorem mem_level_ideleFormation_iff (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) {x : IdeleCoeff K} :
    (dsimp% only (ideleCoeffEquivIdeleFormation K x ∈ (ideleFormation K).level U)) ↔
      x ∈ (ideleCoeffOf K E).range := by
  have hU' : U.toSubgroup = (E : IntermediateField K (SeparableClosure K)).fixingSubgroup := by
    rw [← hU]
    exact (InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩).symm
  rw [Formation.mem_level, mem_range_ideleCoeffOf_iff, ← hU']
  refine forall₂_congr fun u _ ↦ ?_
  rw [← ideleCoeffEquivIdeleFormation_smul, (ideleCoeffEquivIdeleFormation K).injective.eq_iff]

/-- The additive map `I_E → (I_{Kˢ})^U` underlying `ideleLevelEquiv`. -/
private def ideleLevelHom (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) :
    Additive (IdeleGroup (𝓞 E) E) →+ (ideleFormation K).level U :=
  AddMonoidHom.codRestrict ((ideleCoeffEquivIdeleFormation K).toAddMonoidHom.comp
      (ideleCoeffOf K E)) _
    fun a ↦ (mem_level_ideleFormation_iff E hU).2 ⟨a, rfl⟩

private theorem bijective_ideleLevelHom (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) : Function.Bijective (ideleLevelHom E hU) := by
  refine ⟨fun a b hab ↦ ideleCoeffOf_injective E
    ((ideleCoeffEquivIdeleFormation K).injective (congrArg Subtype.val hab)), fun z ↦ ?_⟩
  obtain ⟨z, hz⟩ := z
  obtain ⟨x, rfl⟩ := (ideleCoeffEquivIdeleFormation K).surjective z
  obtain ⟨a, rfl⟩ := (mem_level_ideleFormation_iff E hU).1 hz
  exact ⟨a, rfl⟩

/-- **The level of the idele formation is the idele group of the fixed field**: if the fixed
field of the open subgroup `U` is the finite Galois subextension `E`, then `ideleCoeffOf K E`
identifies the ideles `I_E` of `E` with the level `(I_{Kˢ})^U` of `ideleFormation K`. Applied to
the open normal subgroup fixing a finite Galois extension `L/K`, it identifies the top level of
the layer of `L` with `I_L`. -/
def ideleLevelEquiv (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) :
    Additive (IdeleGroup (𝓞 E) E) ≃+ (ideleFormation K).level U :=
  AddEquiv.ofBijective (ideleLevelHom E hU) (bijective_ideleLevelHom E hU)

/-- `ideleLevelEquiv E hU` sends an idele of `E` to the same idele of `Kˢ`. -/
@[simp]
theorem ideleLevelEquiv_apply_coe (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) (a : Additive (IdeleGroup (𝓞 E) E)) :
    (dsimp% only
      ((ideleLevelEquiv E hU a : (ideleFormation K).level U) : (ideleFormation K).toRep.V)) =
      ideleCoeffEquivIdeleFormation K (ideleCoeffOf K E a) :=
  (rfl)

/-- **`ideleLevelEquiv` is Galois equivariant**: `g ∈ G_K` acts on the level as its restriction to
`Gal(E/K)` acts on the ideles of `E`. -/
theorem ideleLevelEquiv_smul (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) (g : AbsoluteGaloisGroup K)
    (a : IdeleGroup (𝓞 E) E) :
    (dsimp% only ((ideleLevelEquiv E hU
        (.ofMul (Units.map (GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E)) a)) :
          (ideleFormation K).level U) : (ideleFormation K).toRep.V)) =
      (ideleFormation K).toRep.ρ g (ideleLevelEquiv E hU (.ofMul a)) := by
  rw [ideleLevelEquiv_apply_coe, ideleLevelEquiv_apply_coe, ← smul_ideleCoeffOf,
    ideleCoeffEquivIdeleFormation_smul]

end Level

end TauCeti.ClassFieldTheory
