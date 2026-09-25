/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.CongruenceLattice
public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Volume
public import TauCeti.NumberTheory.NumberField.Global.RayClass.MainTerm
import TauCeti.NumberTheory.NumberField.Global.RayClass.ClassNumber
import TauCeti.RingTheory.DedekindDomain.Totient

/-!
# The geometric coefficient of the ray ideal count

Counting the points of a coset of `congruenceLattice 𝔪 (mk0 𝔞)` in the norm-`≤ t` section of
`rayFundamentalDomain 𝔪` gives a main term `V / covol · t`, where `V` is the volume of the
norm-one section of the domain and `covol` the covolume of the lattice. This file evaluates the
coefficient `V / covol · N 𝔞` that this produces for the ideals of a ray class, where
`t = x · N 𝔞`, in terms of `rayClassIdealMainTerm 𝔪`.

Writing `w_𝔪` for the number of roots of unity congruent to one modulo `𝔪`, the coefficient is
`V / covol · N 𝔞 = w_𝔪 · rayClassIdealMainTerm 𝔪`.

## Main results

* `TauCeti.GlobalNumberFields.measureReal_div_covolume_congruenceLattice_mul_absNorm`: the
  coefficient is `w_𝔪` times `rayClassIdealMainTerm 𝔪`.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units
open scoped nonZeroDivisors Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem card_unitsCongruenceTorsion_mul_rayClassIdealMainTerm (𝔪 : Modulus K) :
    Nat.card (unitsCongruenceTorsion 𝔪) * rayClassIdealMainTerm 𝔪 =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
          (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
        (2 ^ 𝔪.infinitePart.card * Ideal.absNorm 𝔪.finitePart * √|(discr K : ℝ)|) := by
  have h𝔪 : (Ideal.absNorm 𝔪.finitePart : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_zero)
  have := Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  -- the correction product is the proportion of residues modulo `𝔪₀` that are units
  rw [rayClassIdealMainTerm_eq, ← mul_div_cancel_left₀ (∏ v ∈ 𝔪.support, _) h𝔪,
    ← Ideal.card_units_quotient_eq_absNorm_mul_prod 𝔪.finitePart 𝔪.mem_support_iff,
    dedekindZeta_residue_def, classNumber, ← Nat.card_eq_fintype_card]
  field_simp [discr_ne_zero, torsionOrder_ne_zero, Nat.card_pos.ne']
  -- `h_𝔪 · [E : E_𝔪] = h · #(𝓞 K ⧸ 𝔪₀)ˣ · 2 ^ s` and `[E : E_𝔪] · w_𝔪 = [E : E_𝔪 μ_K] · w_K`
  grind [congrArg (Nat.cast : ℕ → ℝ) (card_rayClassGroup_mul_index 𝔪),
    congrArg (Nat.cast : ℕ → ℝ) (index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion 𝔪)]

open scoped Classical in
/-- **The geometric coefficient of the ray ideal count.**  The volume of the norm-one section of
`rayFundamentalDomain 𝔪`, over the covolume of the congruence lattice of a nonzero integral ideal
`𝔞`, times the norm of `𝔞`, is `w_𝔪 · rayClassIdealMainTerm 𝔪`, where `w_𝔪` is the number of
roots of unity congruent to one modulo `𝔪`. In particular the left-hand side does not depend
on `𝔞`. -/
theorem measureReal_div_covolume_congruenceLattice_mul_absNorm (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) /
          ZLattice.covolume (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)) volume *
        Ideal.absNorm (𝔞 : Ideal (𝓞 K)) =
      Nat.card (unitsCongruenceTorsion 𝔪) * rayClassIdealMainTerm 𝔪 := by
  have h := covolume_congruenceLattice_div_absNorm 𝔪 (FractionalIdeal.mk0 K 𝔞)
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h
  rw [div_mul_eq_mul_div, ← div_div_eq_mul_div, h,
    measureReal_rayFundamentalDomain_inter_normLeOne,
    card_unitsCongruenceTorsion_mul_rayClassIdealMainTerm]
  field_simp
  ring

end TauCeti.GlobalNumberFields
