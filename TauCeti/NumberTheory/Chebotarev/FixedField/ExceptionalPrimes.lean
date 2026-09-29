/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimesAboveRamifiedPrimes
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia

/-!
# Ramification below a fixed field

The exceptional set used in the fixed-field contraction is defined by ramification over the
original base. A prime of the fixed field may belong to it even when the extension above the
fixed field is unramified. This occurs when its inertia group in the full Galois extension is
nontrivial but meets the subgroup defining the fixed field trivially.

For example, in the splitting field `ℚ(∛2, ζ₃)` of `X³ - 2`, inertia above `2` has order three
and is disjoint from a transposition subgroup whose fixed field is `ℚ(∛2)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, for inertia in a tower of number fields.
-/

public section

open scoped NumberField
open IntermediateField
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- If inertia at `Q` over `K` is nontrivial, the prime below `Q` in `L ^ H` lies above
a prime ramifying in `L / K`. -/
theorem under_mem_primesAboveRamifiedPrimes_of_inertia_ne_bot
    (H : Subgroup (L ≃ₐ[K] L)) (Q : HeightOneSpectrum (𝓞 L))
    (hI : Q.asIdeal.inertia (L ≃ₐ[K] L) ≠ ⊥) :
    Q.under (𝓞 ↥(fixedField H)) ∈
      primesAboveRamifiedPrimes K L ↥(fixedField H) := by
  let E := fixedField H
  let _ : IsScalarTower K E L := E.isScalarTower_mid'
  have hurK : ¬ Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := by
    intro hur
    exact hI ((Ideal.isUnramifiedAt_iff_inertia_eq_bot Q.asIdeal).mp hur)
  exact under_mem_primesAboveRamifiedPrimes_of_not_isUnramifiedAt Q hurK

omit [IsGalois K L] in
/-- The prime below `Q` in `L ^ H` is unramified in `L` exactly when the inertia group
at `Q` over `K` is disjoint from `H`. Together with
`under_mem_primesAboveRamifiedPrimes_of_inertia_ne_bot`, this shows that the set of primes
above those ramifying over `K` can strictly contain the primes ramifying in `L / L ^ H`. -/
theorem under_notMem_ramifiedPrimes_iff_disjoint_inertia
    (H : Subgroup (L ≃ₐ[K] L)) (Q : HeightOneSpectrum (𝓞 L)) :
    Q.under (𝓞 ↥(fixedField H)) ∉ ramifiedPrimes ↥(fixedField H) L ↔
      Disjoint (Q.asIdeal.inertia (L ≃ₐ[K] L)) H := by
  let E := fixedField H
  let _ : IsScalarTower K E L := E.isScalarTower_mid'
  let _ : IsGalois E L := IsGalois.of_fixed_field L H
  constructor
  · intro h
    rw [mem_ramifiedPrimes_iff, not_not] at h
    exact disjoint_iff.mpr
      ((Ideal.isUnramifiedAt_fixedField_iff_inertia_inf_eq_bot Q.asIdeal H).mp
        (h Q.asIdeal))
  · intro h
    rw [mem_ramifiedPrimes_iff, not_not]
    intro R _ hRP
    have hidx : R.ramificationIdx (𝓞 E) = Q.asIdeal.ramificationIdx (𝓞 E) :=
      Ideal.ramificationIdx_eq_of_isGaloisGroup
        (Q.under (𝓞 E)).asIdeal R Q.asIdeal (L ≃ₐ[E] L)
    rw [← Ideal.ramificationIdx_eq_one_iff]
    exact hidx.trans ((Ideal.ramificationIdx_eq_one_iff).mpr
      ((Ideal.isUnramifiedAt_fixedField_iff_inertia_inf_eq_bot Q.asIdeal H).mpr
        (disjoint_iff.mp h)))

end NumberField.Chebotarev
