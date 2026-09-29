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

/-- If the inertia group at `Q` is nontrivial but disjoint from `H`, its contraction to the fixed
field `L ^ H` lies over a prime ramifying in `L / K`, while that prime is unramified in `L / L ^ H`.
Thus the exceptional set for a fixed-field contraction must be defined below in `K`, rather than
using ramification in `L / L ^ H`. -/
theorem fixedField_mem_primesAboveRamifiedPrimes_of_disjoint_inertia
    (H : Subgroup (L ≃ₐ[K] L)) (Q : HeightOneSpectrum (𝓞 L))
    (hI : Q.asIdeal.inertia (L ≃ₐ[K] L) ≠ ⊥)
    (hdisj : Q.asIdeal.inertia (L ≃ₐ[K] L) ⊓ H = ⊥) :
    Q.under (𝓞 ↥(fixedField H)) ∈
        primesAboveRamifiedPrimes K L ↥(fixedField H) ∧
      Q.under (𝓞 ↥(fixedField H)) ∉ ramifiedPrimes ↥(fixedField H) L := by
  let E := fixedField H
  let _ : IsScalarTower K E L := E.isScalarTower_mid'
  let _ : IsGalois E L := IsGalois.of_fixed_field L H
  have hurK : ¬ Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := by
    intro hur
    exact hI ((Ideal.isUnramifiedAt_iff_inertia_eq_bot Q.asIdeal).mp hur)
  have hurE : Algebra.IsUnramifiedAt (𝓞 E) Q.asIdeal := by
    rw [← Ideal.ramificationIdx_eq_one_iff (R := 𝓞 E) (q := Q.asIdeal),
      ← Ideal.card_inertia_eq_ramificationIdx (𝓞 E) (L ≃ₐ[E] L) Q.asIdeal,
      Ideal.card_inertia_fixedField_eq_card_inf Q.asIdeal H, hdisj]
    simp
  constructor
  · rw [mem_primesAboveRamifiedPrimes_iff, mem_ramifiedPrimes_iff]
    intro hur
    have hunder : Q.asIdeal.under (𝓞 K) =
        ((Q.under (𝓞 E)).under (𝓞 K)).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
      exact (Ideal.under_under (B := 𝓞 E) Q.asIdeal).symm
    let : Q.asIdeal.LiesOver ((Q.under (𝓞 E)).under (𝓞 K)).asIdeal :=
      ⟨hunder.symm⟩
    exact hurK (hur Q.asIdeal)
  · rw [mem_ramifiedPrimes_iff, not_not]
    intro R _ hRP
    have hQP : Q.asIdeal.LiesOver (Q.under (𝓞 E)).asIdeal :=
      ⟨HeightOneSpectrum.under_asIdeal (𝓞 E) Q⟩
    have hidx : R.ramificationIdx (𝓞 E) = Q.asIdeal.ramificationIdx (𝓞 E) :=
      Ideal.ramificationIdx_eq_of_isGaloisGroup
        (Q.under (𝓞 E)).asIdeal R Q.asIdeal (L ≃ₐ[E] L)
    rw [← Ideal.ramificationIdx_eq_one_iff]
    exact hidx.trans ((Ideal.ramificationIdx_eq_one_iff).mpr hurE)

end NumberField.Chebotarev
