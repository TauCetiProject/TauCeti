/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.OddPrime

/-!
# The genus and the discriminant form

By
`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule`,
at every odd prime `p` the localization `L_p` is determined by `rank L`, the square class of `det L`
in `ℤ_p`, and `(A_L)_p`. When `L` and `M` have equal signature and isometric discriminant bilinear
modules `b_L ≅ b_M`, their ranks and signed determinants agree, so `SameGenus` reduces to real
signature, `L_2 ≃ M_2`, and `b_L ≅ b_M` (or `q_L ≅ q_M` when even).

When `Odd L.discriminant`, `L_2` is unimodular (`det L ∈ ℤ_2ˣ`):
* For even lattices, `L_2` is classified by rank and `2`-adic determinant square class, and at odd
  order `q_L` and `b_L` are equivalent, yielding Nikulin's Corollary 1.9.4.
* In general, `vanDerBlij` for odd discriminant expresses the mod-`8` norm of a characteristic
  vector via signature and the odd-prime Gauss sums of `L.evenSublattice`, which match `(A_L)_p`
  since `[L : L.evenSublattice] ≤ 2`. Hence signature, evenness, and `b_L` determine `L_2`, giving
  Nikulin's Corollary 1.16.3.

## Main results

* `IntegralLattice.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinearModule`
* `IntegralLattice.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadraticModule`
* `TauCeti.IntegralLattice.sameGenus_iff_of_odd_discriminant` (Nikulin Corollary 1.16.3)
* `TauCeti.IntegralLattice.sameGenus_iff_of_isEven_of_odd_discriminant` (Nikulin Corollary 1.9.4)

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Thm. 1.3.3,
  Cors. 1.9.4 and 1.16.3.
* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291--293.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Ch. 15, §7.
-/

public section

open Module AddCommGroup

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Reduction of the genus to `p = 2` and the discriminant form -/

/-- **Genus characterization up to dyadic equivalence.** Two nondegenerate integral lattices lie in
one genus if and only if they have the same real signature, isometric dyadic localizations `L_2` and
`M_2`, and isometric discriminant bilinear modules. -/
theorem sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinearModule
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate] :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h ↦ ⟨h.signature_eq, h.localIntegralForm_equivalent 2,
    h.nonempty_isometry_discriminantBilinearModule⟩, ?_⟩
  rintro ⟨hsig, h2, ⟨f⟩⟩
  have hdisc := discriminant_eq_of_isometry f
  have hdet := L.determinant_eq_of_signature_eq_of_discriminant_eq hsig hdisc
  refine (sameGenus_iff L M).mpr ⟨hsig, fun p ↦ ?_⟩
  by_cases hp2 : p = 2
  · subst hp2
    exact h2
  · refine (L.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule M hp2).mpr
      ⟨L.finrank_eq_of_signature_eq hsig, ?_, ⟨f.restrictPrimaryComponent p⟩⟩
    rw [hdet]
    exact IsSquare.mul_self _

/-- **Genus characterization for even lattices up to dyadic equivalence.** Two even nondegenerate
integral lattices lie in one genus if and only if they have the same real signature, isometric
dyadic localizations `L_2` and `M_2`, and isometric discriminant quadratic modules. -/
theorem sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadraticModule
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h ↦ ⟨h.signature_eq, h.localIntegralForm_equivalent 2,
    h.nonempty_isometry_discriminantQuadraticModule hL⟩, ?_⟩
  rintro ⟨hsig, h2, ⟨f⟩⟩
  rw [L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinearModule M,
    ← L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    ← M.discriminantQuadraticModule_toFiniteBilinearModule hM]
  exact ⟨hsig, h2, ⟨f.toFiniteBilinearModule⟩⟩

/-! ### Odd-discriminant genus classification (Nikulin Corollaries 1.9.4 and 1.16.3) -/

/-- **Genus classification at odd discriminant (Nikulin, Corollary 1.16.3).** Let `L` and `M` be
nondegenerate integral lattices such that `L` has odd discriminant. Then `L` and `M` lie in one
genus if and only if their signatures agree, `L` is even if and only if `M` is even, and their
discriminant bilinear modules are isometric. -/
theorem sameGenus_iff_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        (L.IsEven ↔ M.IsEven) ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.isEven_iff,
    h.nonempty_isometry_discriminantBilinearModule⟩, ?_⟩
  rintro ⟨hsig, heven, ⟨f⟩⟩
  have hdisc := discriminant_eq_of_isometry f
  have hdet := L.determinant_eq_of_signature_eq_of_discriminant_eq hsig hdisc
  have hL2 : IsUnit (L.determinant : ℤ_[2]) :=
    L.odd_discriminant_iff_isUnit_determinant_padicInt_two.mp hodd
  have hM2 : IsUnit (M.determinant : ℤ_[2]) := hdet ▸ hL2
  obtain ⟨w, hw⟩ := L.exists_isCharacteristicVector
  obtain ⟨w', hw'⟩ := M.exists_isCharacteristicVector
  refine (L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinearModule M).mpr
    ⟨hsig, ?_, ⟨f⟩⟩
  refine (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M hL2 hM2 hw hw').mpr
    ⟨L.finrank_eq_of_signature_eq hsig, heven, hdet ▸ IsSquare.mul_self _, ?_⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  rw [L.integralNorm_cast_zmod_eight_eq_of_odd_discriminant hodd hw,
    M.integralNorm_cast_zmod_eight_eq_of_odd_discriminant (hdisc ▸ hodd) hw']
  have hsig' := hsig
  simp only [signature, Prod.mk.injEq] at hsig'
  rw [hsig'.1, hsig'.2.2, ← hdisc]
  congr 1
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_ne_two : p ≠ 2 := fun h2 ↦
    Nat.not_even_iff_odd.mpr hodd
      (even_iff_two_dvd.mpr (h2 ▸ Nat.dvd_of_mem_primeFactors hp))
  have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_ne_two
  let eL := evenSublatticePrimaryBilinearIsometry L hp_odd
  let eM := evenSublatticePrimaryBilinearIsometry M hp_odd
  have hquad : Nonempty (FiniteQuadraticModule.Isometry
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (primaryComponent
          (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p))
      ((M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice).restrict
        (primaryComponent
          (M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice) p))) :=
    (L.evenSublattice.nonempty_isometry_restrict_discriminantQuadraticModule_primaryComponent_iff
        M.evenSublattice L.isEven_evenSublattice M.isEven_evenSublattice hp_odd).mpr
      ⟨eL.trans ((f.restrictPrimaryComponent p).trans eM.symm)⟩
  exact hquad.some.gaussSign_eq

/-- **Genus classification for even lattices of odd discriminant (Nikulin, Corollary 1.9.4).** Two
even nondegenerate lattices of odd discriminant lie in one genus if and only if their signatures
agree and their discriminant quadratic modules are isometric. -/
theorem sameGenus_iff_of_isEven_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) (hodd : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        Nonempty (FiniteQuadraticModule.Isometry
          (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) := by
  have hodd_card : Odd (Nat.card (L.discriminantQuadraticModule hL)) := by
    rwa [L.natCard_discriminantQuadraticModule, L.natCard_discriminantGroup]
  rw [L.sameGenus_iff_of_odd_discriminant M hodd,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_card,
    L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    M.discriminantQuadraticModule_toFiniteBilinearModule hM]
  simp [hL, hM]

end TauCeti.IntegralLattice
