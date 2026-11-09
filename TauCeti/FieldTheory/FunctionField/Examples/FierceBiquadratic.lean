/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.FieldTheory.RatFunc.PIndependent
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.FierceBiquadratic.Basic

/-!
# A fierce biquadratic extension over explicit constants

Take `k = 𝔽₂(s)(u)` and `A = k[t]_(t)`, realized as the valuation ring of the `t`-adic
place of `k(t)`. The two variables `s, u` are `2`-independent. Thus the ring
`B = A[y, z]`, with `y² + t y = s` and `z² + t z = u`, is a discrete valuation ring
whose residue extension is purely inseparable of degree four, even though `t` remains
a uniformizer. This instantiates the fierce biquadratic construction without any
nonsquare or independence assumptions on unspecified constants.

## References

* I. B. Fesenko, S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., for
  fierce extensions with inseparable residue fields.
-/

public section

noncomputable section

namespace TauCeti.FierceBiquadraticExample

open _root_.IsLocalRing

/-- The explicit constant field `𝔽₂(s)(u)`. -/
abbrev Constants := RatFunc (RatFunc (ZMod 2))

/-- The `t`-adic place of `𝔽₂(s)(u)(t)`. -/
abbrev basePlace : Place Constants (RatFunc Constants) :=
  Place.adicOfIrreducible (Polynomial.irreducible_X (R := Constants))

/-- The DVR `𝔽₂(s)(u)[t]_(t)`, realized inside its fraction field. -/
abbrev BaseRing := basePlace.integers

instance : CharP BaseRing 2 :=
  charP_of_injective_algebraMap (algebraMap Constants BaseRing).injective 2

private theorem uniformizer_X :
    basePlace.valuation.IsUniformizer (RatFunc.X : RatFunc Constants) := by
  simpa only [RatFunc.algebraMap_X] using
    Place.isUniformizer_adicOfIrreducible (Polynomial.irreducible_X (R := Constants))

/-- The parameter `t` in the local base ring. -/
def t : BaseRing :=
  ⟨RatFunc.X, basePlace.mem_integers_iff.mpr uniformizer_X.val_lt_one.le⟩

/-- The first independent constant, `s`. -/
def s : BaseRing := algebraMap Constants BaseRing (RatFunc.C (RatFunc.X : RatFunc (ZMod 2)))

/-- The second independent constant, `u`. -/
def u : BaseRing := algebraMap Constants BaseRing RatFunc.X

@[simp]
theorem coe_t : (t : RatFunc Constants) = RatFunc.X := (rfl)

@[simp]
theorem coe_s : (s : RatFunc Constants) =
    RatFunc.C (RatFunc.C (RatFunc.X : RatFunc (ZMod 2))) := by
  simp [s, RatFunc.algebraMap_eq_C]

@[simp]
theorem coe_u : (u : RatFunc Constants) = RatFunc.C (RatFunc.X : Constants) := by
  simp [u, RatFunc.algebraMap_eq_C]

/-- The parameter `t` is a uniformizer of the base ring. -/
theorem irreducible_t : Irreducible t :=
  basePlace.irreducible_of_isUniformizer (by simpa only [coe_t] using uniformizer_X)

private theorem t_mem_maximalIdeal : t ∈ maximalIdeal BaseRing :=
  (mem_maximalIdeal t).mpr irreducible_t.not_isUnit

private def residueEquiv : basePlace.ResidueField ≃ₐ[Constants] Constants :=
  (basePlace.residueFieldEquivOfDegreeEqOne (by
    simp [Place.degree_adicOfIrreducible])).symm

/-- Reduction identifies the first constant with a nonsquare in `𝔽₂(s)(u)`. -/
theorem sq_ne_residue_s (a : ResidueField BaseRing) :
    a ^ 2 ≠ residue BaseRing s := by
  intro h
  apply RatFunc.pow_ne_C_X (by decide : 1 < 2) (residueEquiv a)
  simpa only [s, map_pow, ← basePlace.algebraMap_residueField, AlgEquiv.commutes,
    Algebra.algebraMap_self, RingHom.id_apply] using congrArg residueEquiv h

/-- In the residue field, the reduction of `u` is not of the form `a² + s b²`. -/
theorem sq_add_residue_s_mul_sq_ne_residue_u (a b : ResidueField BaseRing) :
    a ^ 2 + residue BaseRing s * b ^ 2 ≠ residue BaseRing u := by
  intro h
  apply RatFunc.pow_add_C_mul_pow_ne_X 2 (residueEquiv a) (residueEquiv b)
    (RatFunc.X : RatFunc (ZMod 2))
  simpa only [s, u, map_add, map_mul, map_pow, ← basePlace.algebraMap_residueField,
    AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply] using congrArg residueEquiv h

/-- The biquadratic ring with equations `y² + t y = s` and `z² + t z = u`. -/
abbrev ExtensionRing := FierceBiquadratic.RingYZ t s u

instance : IsDomain ExtensionRing :=
  FierceBiquadratic.isDomain_ringYZ t_mem_maximalIdeal
    sq_ne_residue_s sq_add_residue_s_mul_sq_ne_residue_u

/-- The explicit biquadratic extension is a discrete valuation ring. -/
instance : IsDiscreteValuationRing ExtensionRing :=
  FierceBiquadratic.isDiscreteValuationRing_ringYZ t_mem_maximalIdeal
    sq_ne_residue_s sq_add_residue_s_mul_sq_ne_residue_u

instance : IsLocalHom (algebraMap BaseRing ExtensionRing) :=
  FierceBiquadratic.isLocalHom_algebraMap_ringYZ t_mem_maximalIdeal
    sq_ne_residue_s sq_add_residue_s_mul_sq_ne_residue_u

/-- The parameter remains a uniformizer in the extension: its ramification index is one. -/
theorem irreducible_algebraMap_t : Irreducible (algebraMap BaseRing ExtensionRing t) :=
  FierceBiquadratic.irreducible_algebraMap_ringYZ irreducible_t
    sq_ne_residue_s sq_add_residue_s_mul_sq_ne_residue_u

/-- The explicit residue extension has degree four. -/
theorem finrank_residueField :
    Module.finrank (ResidueField BaseRing) (ResidueField ExtensionRing) = 4 :=
  FierceBiquadratic.finrank_residueField_ringYZ t_mem_maximalIdeal
    sq_ne_residue_s sq_add_residue_s_mul_sq_ne_residue_u

/-- The explicit degree-four residue extension is purely inseparable. -/
instance : IsPurelyInseparable (ResidueField BaseRing) (ResidueField ExtensionRing) :=
  FierceBiquadratic.isPurelyInseparable_residueField_ringYZ t_mem_maximalIdeal

end TauCeti.FierceBiquadraticExample
