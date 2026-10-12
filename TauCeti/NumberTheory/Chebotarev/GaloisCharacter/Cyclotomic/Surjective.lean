/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic
import TauCeti.NumberTheory.Chebotarev.Density.SplitsCompletely

/-!
# Surjectivity of the cyclotomic Artin map

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`. This file proves that
the Artin map `cyclotomicArtin K F m` from the ray class group of `cyclotomicModulus K m` to
`Gal(F/K)` is surjective.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_surjective`: the cyclotomic Artin map is surjective.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open IsDedekindDomain IntermediateField
open scoped symmDiff

namespace NumberField.Chebotarev

variable (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- Every prime `𝔭 ∤ m` has its Frobenius in the image of the Artin map, so it splits completely in
-- the fixed field of that image.
variable {K m} in
private theorem mem_frobeniusPrimeSet_fixedField_range_cyclotomicArtin
    [IsMulCommutative (F ≃ₐ[K] F)] {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    𝔭 ∈ frobeniusPrimeSet K (fixedField (cyclotomicArtin K F m).range) 1 := by
  have hmem := asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mpr h𝔭
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 F)))
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
  have hσH : AlgEquiv.restrictNormalHom (fixedField (cyclotomicArtin K F m).range) σ = 1 := by
    rw [← MonoidHom.mem_ker, restrictNormalHom_ker, fixingSubgroup_fixedField]
    exact ⟨_, cyclotomicArtin_idealClass_of_isArithFrobAt F m 𝔭 hmem Q hσ⟩
  simpa only [ConjClasses.map_mk, hσH, ← ConjClasses.one_eq_mk_one] using
    frobeniusPrimeSet_subset_map_restrictNormalHom (M := fixedField (cyclotomicArtin K F m).range) _
      (mem_frobeniusPrimeSet_mk_of_isArithFrobAt (fun Q _ _ ↦
        isUnramifiedAt_of_notMem_cyclotomicModulus_support F m
          (mem_cyclotomicModulus_support_iff.not.mpr h𝔭) Q) Q hσ)

/-- **The cyclotomic Artin map is surjective.** For `F = K(μ_m)`, every automorphism of `F / K` is
the Artin automorphism of a ray class of `cyclotomicModulus K m`. -/
theorem cyclotomicArtin_surjective : Function.Surjective (cyclotomicArtin K F m) := by
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  rw [← MonoidHom.range_eq_top]
  set H := (cyclotomicArtin K F m).range
  -- Every prime not dividing `m` splits completely in the fixed field of `H`, so the completely
  -- split primes of that field have density one; they also have density one over its degree, so
  -- the fixed field is `K` and `H` is the whole Galois group.
  have hfin : (frobeniusPrimeSet K (fixedField H) 1 ∆ Set.univ).Finite := by
    refine (cyclotomicModulus K m).support.finite_toSet.subset fun 𝔭 h𝔭 ↦ by_contra fun h ↦ ?_
    rw [← Set.top_eq_univ, symmDiff_top] at h𝔭
    exact h𝔭 (mem_frobeniusPrimeSet_fixedField_range_cyclotomicArtin F
      (mem_cyclotomicModulus_support_iff.not.mp h))
  have hdeg := (hasDirichletDensity_frobeniusPrimeSet_one K (fixedField H)).unique
    (Set.hasDirichletDensity_univ.of_finite_symmDiff hfin)
  rw [one_div, inv_eq_one, Nat.cast_eq_one, IntermediateField.finrank_eq_one_iff] at hdeg
  rw [← fixingSubgroup_fixedField H, hdeg, fixingSubgroup_bot]

end NumberField.Chebotarev
