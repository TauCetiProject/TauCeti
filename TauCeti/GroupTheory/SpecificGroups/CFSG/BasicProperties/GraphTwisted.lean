/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.Finiteness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TrialityD4

/-!
# Finiteness for the graph-twisted D and E families

The graph automorphism commutes with Frobenius and has order two, or three for triality.
The corresponding power of the Steinberg map is therefore a power of Frobenius on the whole
matrix carrier, so its fixed group is finite.
-/

public section

namespace TauCeti

/-- Squaring the twisted type-D Steinberg map removes its graph factor. -/
theorem TypeTwistedDLieIndex.steinberg_sq (d : TypeTwistedDLieIndex) :
    (show Monoid.End d.toTypeDDiagramLieIndex.AmbientGroup from d.steinberg) ^ 2 =
      (show Monoid.End d.toTypeDDiagramLieIndex.AmbientGroup from
        d.toTypeDDiagramLieIndex.frobenius) ^ 2 := by
  have hc : Commute (show Monoid.End _ from d.graphAut.toMonoidHom)
      d.toTypeDDiagramLieIndex.frobenius := d.graphAut_comp_frobenius
  rw [d.steinberg_def]
  change ((show Monoid.End _ from d.graphAut.toMonoidHom) *
    (show Monoid.End _ from d.toTypeDDiagramLieIndex.frobenius)) ^ 2 = _
  rw [hc.mul_pow]
  have hg : (show Monoid.End _ from d.graphAut.toMonoidHom) ^ 2 = 1 := by
    apply MonoidHom.ext
    intro g
    exact congrArg (fun e : MulAut _ => e g) d.graphAut_sq
  rw [hg, one_mul]

/-- The twisted type-D Steinberg fixed group is finite. -/
theorem TypeTwistedDLieIndex.finite_fixedPoints (d : TypeTwistedDLieIndex) :
    Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg (d.1.fieldExponent * 2) 2 (Nat.mul_ne_zero d.1.fieldExponent_pos.ne' (by decide))
  intro g i j
  rw [d.steinberg_sq]
  change ((d.toTypeDDiagramLieIndex.frobenius (d.toTypeDDiagramLieIndex.frobenius g) :
    Matrix.GeneralLinearGroup
      (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) i j) = _
  rw [d.toTypeDDiagramLieIndex.coe_frobenius_apply,
    d.toTypeDDiagramLieIndex.coe_frobenius_apply, d.1.fieldOrder_eq_characteristic_pow,
    ← pow_mul, ← pow_two, ← pow_mul]

/-- Squaring the twisted E₆ Steinberg map removes its graph factor. -/
theorem TypeTwistedE6LieIndex.steinberg_sq (d : TypeTwistedE6LieIndex) :
    (show Monoid.End d.AmbientGroup from d.steinberg) ^ 2 =
      (show Monoid.End d.AmbientGroup from d.frobenius) ^ 2 := by
  have hc : Commute (show Monoid.End _ from d.graphAut.toMonoidHom) d.frobenius :=
    d.graphAut_comp_frobenius
  rw [d.steinberg_def]
  change ((show Monoid.End _ from d.graphAut.toMonoidHom) *
    (show Monoid.End _ from d.frobenius)) ^ 2 = _
  rw [hc.mul_pow]
  have hg : (show Monoid.End _ from d.graphAut.toMonoidHom) ^ 2 = 1 := by
    apply MonoidHom.ext
    intro g
    exact congrArg (fun e : MulAut _ => e g) d.graphAut_sq
  rw [hg, one_mul]

/-- The doubled-minuscule Steinberg fixed group of twisted E₆ is finite. -/
theorem TypeTwistedE6LieIndex.finite_fixedPoints (d : TypeTwistedE6LieIndex) :
    Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg (d.1.fieldExponent * 2) 2 (Nat.mul_ne_zero d.1.fieldExponent_pos.ne' (by decide))
  intro g i j
  rw [d.steinberg_sq]
  change ((d.frobenius (d.frobenius g) : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) i j) = _
  rw [d.coe_frobenius_apply, d.coe_frobenius_apply, d.1.fieldOrder_eq_characteristic_pow,
    ← pow_mul, ← pow_two, ← pow_mul]

/-- Cubing the triality Steinberg map removes its graph factor. -/
theorem TypeTrialityD4LieIndex.steinberg_pow_three (d : TypeTrialityD4LieIndex) :
    (show Monoid.End d.AmbientGroup from d.steinberg) ^ 3 =
      (show Monoid.End d.AmbientGroup from d.frobenius) ^ 3 := by
  have hc : Commute (show Monoid.End _ from d.graphAut.toMonoidHom) d.frobenius :=
    d.graphAut_comp_frobenius
  rw [d.steinberg_def]
  change ((show Monoid.End _ from d.graphAut.toMonoidHom) *
    (show Monoid.End _ from d.frobenius)) ^ 3 = _
  rw [hc.mul_pow]
  have hg : (show Monoid.End _ from d.graphAut.toMonoidHom) ^ 3 = 1 := by
    apply MonoidHom.ext
    intro g
    exact congrArg (fun e : MulAut _ => e g) d.graphAut_pow_three
  rw [hg, one_mul]

/-- The tripled-carrier Steinberg fixed group of triality D₄ is finite. -/
theorem TypeTrialityD4LieIndex.finite_fixedPoints (d : TypeTrialityD4LieIndex) :
    Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg (d.1.fieldExponent * 3) 3 (Nat.mul_ne_zero d.1.fieldExponent_pos.ne' (by decide))
  intro g i j
  rw [d.steinberg_pow_three]
  change ((d.frobenius (d.frobenius (d.frobenius g)) :
    Matrix.GeneralLinearGroup (Fin 24) d.1.Closure) i j) = _
  rw [d.coe_frobenius_apply, d.coe_frobenius_apply, d.coe_frobenius_apply,
    d.1.fieldOrder_eq_characteristic_pow, ← pow_mul, ← pow_mul,
    ← pow_two, ← pow_succ', ← pow_mul]

end TauCeti
