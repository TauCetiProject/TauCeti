/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Coefficients

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

end TauCeti.ClassFieldTheory
