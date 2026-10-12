/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.DegreeThree
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation
import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive

/-!
# The third cohomology of the units of a local field

For a nonarchimedean local field `K` with absolute Galois group `G_K`, this file proves

```text
H³(G_K, (Kˢ)ˣ) = 0
```

on Mathlib's continuous cohomology of the coefficient object `TauCeti.ClassFieldTheory.unitsRep K`
(`TauCeti.ClassFieldTheory.subsingleton_h3_unitsRep`). The units formation of `K` is a class
formation (`TauCeti.ClassFieldTheory.localClassFormation`), so the continuous third cohomology of
its module vanishes by Tate's theorem on every finite layer and the finite-quotient colimit
(`TauCeti.ClassFieldTheory.ClassFormation.subsingleton_continuousCohomology_three`). The module of
the units formation is `(Kˢ)ˣ` over `Gal(Kˢ/K)`, while `unitsRep K` is the same group over `G_K`,
on which it acts through the restriction isomorphism
`TauCeti.absoluteGaloisGroupRestrictEquiv : G_K ≃ₜ* Gal(Kˢ/K)`; the two continuous cohomologies are
compared along that isomorphism.

This vanishing is one input of the cohomological dimension `cd_ℓ G_K = 2` of a finite extension of
`ℚ_p`. For a finite extension `L/K`, the Kummer sequence `1 → μ_ℓ → (Lˢ)ˣ → (Lˢ)ˣ → 1` and the
vanishing of `H³(G_L, (Lˢ)ˣ)` identify `H³(G_L, μ_ℓ)` with the cokernel of the `ℓ`-th power map on
`H²(G_L, (Lˢ)ˣ)`; that cokernel vanishes by the second input, the invariant isomorphism
`Br(L) ≅ ℚ/ℤ`, which makes `H²(G_L, (Lˢ)ˣ)` divisible.

## Main results

* `TauCeti.ClassFieldTheory.subsingleton_h3_unitsRep`: `H³(G_K, (Kˢ)ˣ) = 0`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.1.8).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

variable (K : Type) [Field K]

attribute [local instance] TopRep.distribMulAction

/-- The coefficient dictionary from the module of the units formation, over `Gal(Kˢ/K)`, to
`unitsRep K`, over `G_K`: both are `TauCeti.UnitsCoeff K`. -/
private def unitsFormationToUnitsRep : (unitsFormation K).module.V ≃ₗ[ℤ] (unitsRep K).V :=
  ((unitsCoeffEquivUnitsFormation K).symm.trans (unitsCoeffEquivUnitsRep K)).toIntLinearEquiv

/-- The dictionary sends the image of `y : UnitsCoeff K` in the units formation to its image in
`unitsRep K`. -/
private theorem unitsFormationToUnitsRep_unitsCoeffEquivUnitsFormation (y : UnitsCoeff K) :
    unitsFormationToUnitsRep K (unitsCoeffEquivUnitsFormation K y) =
      unitsCoeffEquivUnitsRep K y := by
  simp [unitsFormationToUnitsRep]

/-- The dictionary is equivariant along the restriction isomorphism `G_K ≃ Gal(Kˢ/K)`. -/
private theorem unitsFormationToUnitsRep_smul (g : Field.absoluteGaloisGroup K)
    (x : (unitsFormation K).module.V) :
    unitsFormationToUnitsRep K (absoluteGaloisGroupRestrictEquiv K g • x) =
      g • unitsFormationToUnitsRep K x := by
  obtain ⟨y, rfl⟩ := (unitsCoeffEquivUnitsFormation K).surjective x
  rw [TopRep.distribMulAction_smul, TopRep.distribMulAction_smul, ← Formation.toRep_ρ_apply,
    ← unitsCoeffEquivUnitsFormation_smul, unitsFormationToUnitsRep_unitsCoeffEquivUnitsFormation,
    unitsFormationToUnitsRep_unitsCoeffEquivUnitsFormation, unitsCoeffEquivUnitsRep_smul]

/-- **Vanishing transfers from the units formation to `unitsRep K`**, along the restriction
isomorphism `G_K ≃ₜ* Gal(Kˢ/K)` and the coefficient dictionary. -/
private theorem subsingleton_continuousCohomology_unitsRep (n : ℕ)
    [Subsingleton (continuousCohomology n (unitsFormation K).module)] :
    Subsingleton (continuousCohomology n (unitsRep K)) := by
  have := (unitsFormation K).smooth.discreteTopology
  have := (unitsFormation K).smooth.continuousSMul
  have : Subsingleton (continuousCohomology n
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (unitsFormation K).module.V)) :=
    (ofDiscreteModuleRestrictScalarsIntEquiv (unitsFormation K).module n).injective.subsingleton
  have :=
    ContinuousCohomology.subsingleton_continuousCohomology_ofDiscreteModule_of_continuousMulEquiv
      (absoluteGaloisGroupRestrictEquiv K) (unitsFormationToUnitsRep K)
      (unitsFormationToUnitsRep_smul K) n
  exact (ofDiscreteModuleRestrictScalarsIntEquiv (unitsRep K) n).symm.injective.subsingleton

/-- **`H³(G_K, (Kˢ)ˣ) = 0`** for a nonarchimedean local field `K`: the units formation of `K` is a
class formation, whose continuous third cohomology vanishes by Tate's theorem on every finite layer,
`H-hat^3(Gal(L/K), Lˣ) ≅ H-hat^1(Gal(L/K), ℤ) = 0`, and the finite-quotient colimit. -/
theorem subsingleton_h3_unitsRep [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Subsingleton (continuousCohomology 3 (unitsRep K)) :=
  have := (localClassFormation K).subsingleton_continuousCohomology_three
  subsingleton_continuousCohomology_unitsRep K 3

end TauCeti.ClassFieldTheory
