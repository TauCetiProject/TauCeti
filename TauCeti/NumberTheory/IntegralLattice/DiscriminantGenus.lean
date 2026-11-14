/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.OddPrime
import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice

/-!
# The genus and the discriminant form

By
`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule`,
at every odd prime `p` the integral localization `L_p` of a nondegenerate lattice `L` is determined
up to isometry by `rank L`, the square class of `det L` in `ℤ_p`, and the `p`-primary discriminant
bilinear module `(A_L)_p`. When two nondegenerate lattices `L` and `M` have equal real signature
and isometric discriminant bilinear forms `b_L ≅ b_M`, their ranks and signed determinants already
coincide, so every odd-prime local equivalence holds automatically. The genus relation
`TauCeti.IntegralLattice.SameGenus` therefore reduces to three invariants: real signature, the
dyadic localization `L_2`, and the discriminant form (`b_L` in general, or `q_L` for even lattices).

When `L` has **odd discriminant** (`Odd L.discriminant`, equivalently `det L ∈ ℤ_2ˣ` by
`TauCeti.IntegralLattice.odd_discriminant_iff_isUnit_determinant_padicInt_two`), the dyadic
localization `L_2` is unimodular and is itself determined by the remaining invariants:

* For even lattices of odd discriminant, `L_2` is an even unimodular `ℤ_2`-form, classified by rank
  and `2`-adic determinant square class
  (`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isEven`).
  Moreover, at odd order `q_L` and `b_L` carry the same isometry information, giving Nikulin's
  Corollary 1.9.4 unconditionally for odd discriminant.
* For general (possibly odd) lattices of odd discriminant, `L` admits an integral characteristic
  vector `w` (`TauCeti.IntegralLattice.exists_isCharacteristicVector`), and the odd-discriminant
  generalization of `TauCeti.IntegralLattice.vanDerBlij`
  (`TauCeti.IntegralLattice.integralNorm_cast_zmod_eight_eq_of_odd_discriminant`) expresses
  `B(w, w) mod 8` as `(sigPos L - sigNeg L)` minus the odd-prime Gauss-sum invariants of the
  canonical even sublattice `N = L.evenSublattice`. Since `[L : N] ≤ 2` is prime to every odd prime
  `p`, `(A_N)_p` is isometric to `(A_L)_p`; thus `signature` and `b_L` determine the characteristic
  norm modulo `8`, hence `L_2`, proving Nikulin's Corollary 1.16.3 for all nondegenerate lattices of
  odd discriminant (generalizing `TauCeti.IntegralLattice.sameGenus_iff_of_isUnimodular`).

## Main results

* `IntegralLattice.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinearModule`
  and
  `IntegralLattice.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadraticModule`
  — reduction of `SameGenus` for nondegenerate lattices to real signature, `L_2 ≃ M_2`, and isometry
  of the discriminant form.
* `TauCeti.IntegralLattice.sameGenus_iff_of_isEven_of_odd_discriminant` and
  `TauCeti.IntegralLattice.sameGenus_iff_discriminantBilinearModule_of_isEven_of_odd_discriminant`:
  Nikulin's Corollary 1.9.4 for even lattices of odd discriminant.
* `TauCeti.IntegralLattice.sameGenus_iff_of_odd_discriminant`: Nikulin's Corollary 1.16.3 for
  nondegenerate lattices of odd discriminant (`SameGenus` iff equal signature, matching evenness,
  and isometric discriminant bilinear modules).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Theorem 1.3.3
  and Corollaries 1.9.4 and 1.16.3.
* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291--293.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module AddCommGroup

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Reduction of the genus to `p = 2` and the discriminant form -/

/-- Equal signatures and isometric discriminant bilinear modules force equal signed determinants. -/
private theorem determinant_eq_of_signature_eq_of_isometry_discriminantBilinear
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    (hsig : L.signature = M.signature)
    (f : FiniteBilinearModule.Isometry L.discriminantBilinearModule M.discriminantBilinearModule) :
    L.determinant = M.determinant := by
  have hcard : Nat.card L.DiscriminantGroup = Nat.card M.DiscriminantGroup :=
    Nat.card_congr f.toAddEquiv.toEquiv
  have hdisc : L.discriminant = M.discriminant := by
    simpa only [natCard_discriminantGroup] using hcard
  have hneg : L.sigNeg = M.sigNeg := congrArg (fun s ↦ s.2.2) hsig
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
    M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hneg, hdisc]

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
  have hdet := determinant_eq_of_signature_eq_of_isometry_discriminantBilinear hsig f
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
  exact (L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinearModule M).mpr
    ⟨hsig, h2, ⟨f.toFiniteBilinearModule⟩⟩

/-! ### Odd-discriminant genus classification (Nikulin Corollaries 1.9.4 and 1.16.3) -/

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
  refine ⟨fun h ↦ ⟨h.signature_eq, h.nonempty_isometry_discriminantQuadraticModule hL⟩, ?_⟩
  rintro ⟨hsig, ⟨f⟩⟩
  have hdet := determinant_eq_of_signature_eq_of_isometry_discriminantBilinear hsig
    f.toFiniteBilinearModule
  have hL2 : IsUnit (L.determinant : ℤ_[2]) :=
    L.odd_discriminant_iff_isUnit_determinant_padicInt_two.mp hodd
  have hM2 : IsUnit (M.determinant : ℤ_[2]) := hdet ▸ hL2
  refine
    (L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadraticModule M hL hM).mpr
      ⟨hsig, ?_, ⟨f⟩⟩
  refine (L.localIntegralForm_two_equivalent_iff_of_isEven M hL hM hL2 hM2).mpr
    ⟨L.finrank_eq_of_signature_eq hsig, ?_⟩
  rw [hdet]
  exact IsSquare.mul_self _

/-- For even nondegenerate lattices of odd discriminant, the discriminant bilinear module already
determines the genus together with the signature. -/
theorem sameGenus_iff_discriminantBilinearModule_of_isEven_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) (hodd : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  have hodd_card : Odd (Nat.card (L.discriminantQuadraticModule hL)) := by
    rwa [L.natCard_discriminantQuadraticModule, L.natCard_discriminantGroup]
  rw [L.sameGenus_iff_of_isEven_of_odd_discriminant M hL hM hodd,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_card,
    L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    M.discriminantQuadraticModule_toFiniteBilinearModule hM]

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
  have hdet := determinant_eq_of_signature_eq_of_isometry_discriminantBilinear hsig f
  have hdisc : L.discriminant = M.discriminant := by
    rw [discriminant_def, discriminant_def, hdet]
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
  let eL := primaryDiscriminantBilinearIsometry
    (L.evenSublattice.localInclusionIsometryEquiv L p L.evenSublattice_form
      L.evenSublattice_carrier_le
      (L.not_dvd_relIndex_evenSublattice_of_odd hp_odd hp_prime.ne_one))
  let eM := primaryDiscriminantBilinearIsometry
    (M.evenSublattice.localInclusionIsometryEquiv M p M.evenSublattice_form
      M.evenSublattice_carrier_le
      (M.not_dvd_relIndex_evenSublattice_of_odd hp_odd hp_prime.ne_one))
  exact (FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd
    ((L.evenSublattice.discriminantQuadraticModule
      L.isEven_evenSublattice).odd_natCard_restrict_primaryComponent hp_prime hp_ne_two)
    (eL.trans ((f.restrictPrimaryComponent p).trans eM.symm))).gaussSign_eq

end TauCeti.IntegralLattice
