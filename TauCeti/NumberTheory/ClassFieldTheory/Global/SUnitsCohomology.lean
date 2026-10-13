/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.RepresentationTheory.Homological.TateCohomology.FiniteGeneration
import TauCeti.NumberTheory.NumberField.Units.SUnit

/-!
# Finiteness of low-degree Tate cohomology of `S`-units

For a finite set `S` of finite places of a number field `K`, the `S`-units of a number-field
extension `L/K` are finitely generated. Consequently their degree-zero and degree-minus-one
Tate cohomology groups are finite. These are the finiteness inputs in the short exact sequence
`U_{L,S} → I_{L,S} → C_L` used to compute the Herbrand quotient of idele classes.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- The integral representation on the `S`-units of `L` is finitely generated when `S` is
finite. -/
theorem moduleFinite_sUnitsRep : Module.Finite ℤ (sUnitsRep L S) := by
  let : Finite ↥(HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) S) :=
    (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 L) (Set.toFinite S)).to_subtype
  have hfg : AddGroup.FG
      (Additive ((HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) S).unit L)) :=
    AddGroup.fg_iff_mul_fg.mpr inferInstance
  exact Module.Finite.iff_addGroup_fg.mpr hfg

/-- The degree-zero Tate cohomology of the `S`-units is finite. -/
theorem finite_tateCohomology_zero_sUnitsRep :
    Finite (tateCohomology (sUnitsRep L S) 0) := by
  have := moduleFinite_sUnitsRep (L := L) S
  exact TateCohomology.finite_tateCohomology_zero_of_moduleFinite (sUnitsRep L S)

/-- The degree-minus-one Tate cohomology of the `S`-units is finite. -/
theorem finite_tateCohomology_negOne_sUnitsRep :
    Finite (tateCohomology (sUnitsRep L S) (-1)) := by
  have := moduleFinite_sUnitsRep (L := L) S
  exact TateCohomology.finite_tateCohomology_negOne_of_moduleFinite (sUnitsRep L S)

end TauCeti.ClassFieldTheory
