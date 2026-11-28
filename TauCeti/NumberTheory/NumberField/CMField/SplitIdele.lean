/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Norm-one finite ideles at split places of CM fields

At a place distinct from its conjugate, any residue unit lifts to an integral norm-one finite
idele that is `1` away from the pair. The lift uses `FiniteAdeleRing.unitsOfAdicCompletion`
and `FiniteAdeleRing.unitsProj_star_eq_one_iff`. Choosing a generator of the residue unit group
then gives a scaling whose residue has order `Nm(w) - 1`. By `orderOf_dvd_iff_pow_eq_one`,
its `i`-th power reduces to `1` exactly when `Nm(w) - 1` divides `i`.

The generator construction follows `New.Data.exists_isScalingAt_valuation_pow_iff` in
`grh/src/New/UpperBound/Size/ShortColumns.lean` of lsernau/grh-lean, revision `72fead1`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

/-- Every residue unit at a split place of a CM number field lifts to an integral finite idele
of norm one that is `1` away from the place and its conjugate. -/
theorem exists_unitary_integral_idele_reduction_eq {E : Type*} [Field E] [NumberField E]
    [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (hw : w.conjPlace ≠ w)
    (r : (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ) :
    ∃ z : integralUnits (𝓞 E) E, (z : (𝔸ᶠ[E])ˣ) ∈ unitary ((𝔸ᶠ[E])ˣ) ∧
      (∀ v, v ≠ w → v ≠ w.conjPlace → unitsProj E v z = 1) ∧
      w.integralUnitsReduction z = r := by
  obtain ⟨u, rfl⟩ := (w.adicCompletionIntegers E).surjective_unitGroupToResidueFieldUnits r
  let a := unitsOfAdicCompletion E w (u : (w.adicCompletion E)ˣ)
  have ha : a ∈ integralUnits (𝓞 E) E := unitsOfAdicCompletion_mem_integralUnits_iff.mpr
    ((Valuation.mem_unitGroup_iff _ Valued.v _).mp u.property)
  have hstar : star a ∈ integralUnits (𝓞 E) E := by
    simpa only [mem_integralUnits_iff_val_mem_and_inv_mem, Units.coe_star,
      Units.coe_star_inv, star_mem_integralAdeles_iff] using ha
  let z : integralUnits (𝓞 E) E := ⟨a * (star a)⁻¹, (integralUnits (𝓞 E) E).mul_mem ha
    ((integralUnits (𝓞 E) E).inv_mem hstar)⟩
  have hproj (v : HeightOneSpectrum (𝓞 E)) (hv : v ≠ w.conjPlace) :
      unitsProj E v z = unitsProj E v a := by
    have hcv : v.conjPlace ≠ w := fun h ↦ hv ((conjPlace_conjPlace v).symm.trans (congrArg _ h))
    have hstarOne := (unitsProj_star_eq_one_iff (v := v) (a := a)).2
      (unitsProj_unitsOfAdicCompletion_of_ne hcv (u : (w.adicCompletion E)ˣ))
    have hz : (z : (𝔸ᶠ[E])ˣ) = a * (star a)⁻¹ := rfl
    simp only [hz, map_mul, map_inv, hstarOne, inv_one, mul_one]
  refine ⟨z, (Unitary.mul_inv_mem_iff a (star a)).mpr ?_,
    fun v hv hvc ↦ (hproj v hvc).trans (unitsProj_unitsOfAdicCompletion_of_ne hv _),
    integralUnitsReduction_eq_of_unitsProj_eq w z u
      ((hproj w hw.symm).trans (unitsProj_unitsOfAdicCompletion w _))⟩
  rw [star_star, mul_comm]

/-- At a split place of a CM number field there is an integral norm-one finite idele,
trivial away from the conjugate pair, whose residue has order equal to the absolute norm
of the prime minus one. -/
theorem exists_unitary_integral_idele_residue_generator {E : Type*} [Field E] [NumberField E]
    [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (hw : w.conjPlace ≠ w) :
    ∃ z : integralUnits (𝓞 E) E, (z : (𝔸ᶠ[E])ˣ) ∈ unitary ((𝔸ᶠ[E])ˣ) ∧
      (∀ v, v ≠ w → v ≠ w.conjPlace → unitsProj E v z = 1) ∧
      orderOf (w.integralUnitsReduction z) = Ideal.absNorm w.asIdeal - 1 := by
  obtain ⟨r, hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic (IsLocalRing.ResidueField (w.adicCompletionIntegers E))ˣ)
  obtain ⟨z, hz, hs, hrz⟩ := w.exists_unitary_integral_idele_reduction_eq hw r
  refine ⟨z, hz, hs, ?_⟩
  rw [hrz, hr, Nat.card_units, w.natCard_residueField_adicCompletionIntegers_eq_absNorm]

end IsDedekindDomain.HeightOneSpectrum
