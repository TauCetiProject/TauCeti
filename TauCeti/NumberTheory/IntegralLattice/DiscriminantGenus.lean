/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.GaussSum
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.LinearAlgebra.IntegralLattice.Index
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Characteristic
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.OddPrime
import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice

/-!
# The genus and discriminant forms

Lattices in the same genus share their real signature, their dyadic localization `L_2`, and their
discriminant bilinear form `b_L`
(`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantBilinearModule`), or their
discriminant quadratic form `q_L` when they are even
(`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantQuadraticModule`). Because
signature and discriminant-group order determine the signed determinant
(`TauCeti.IntegralLattice.determinant_eq_of_signature_eq_of_natCard_discriminantGroup_eq`), and the
`p`-primary discriminant bilinear form classifies `L_p` at every odd prime `p`
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_primaryDiscriminantBilinear`), those
invariants conversely decide the genus of any nondegenerate integral lattice: all odd-prime local
conditions are absorbed into `b_L` (or `q_L`), leaving only the dyadic localization `L_2`.

When `L` has odd discriminant — equivalently, when its signed determinant is a unit in `ℤ_2`
(`TauCeti.IntegralLattice.isUnit_determinant_two_iff_odd_discriminant`) — the dyadic localization
`L_2` is unimodular and is itself determined by the remaining invariants:

* For even lattices of odd discriminant, rank and determinant square class already classify `L_2`
  (`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isEven`), and `q_L` has odd
  order so its isometry class coincides with that of `b_L`
  (`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`). Thus two even
  nondegenerate lattices of odd discriminant lie in one genus if and only if they have the same
  signature and isometric discriminant quadratic forms (the odd-discriminant case of Nikulin's
  Corollary 1.9.4).
* For general nondegenerate lattices of odd discriminant (even or odd), `L` admits an integral
  characteristic vector `w`
  (`TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`), and the oddity
  `w² mod 8` is pinned down by `sigPos L - sigNeg L mod 8` together with the odd primary components
  of `b_L`: passing to the canonical even sublattice `N` leaves all odd-prime localizations
  unchanged (`[L : N] ≤ 2`), while Milgram's theorem on `q_N` equates `sigPos L - sigNeg L` modulo
  `8` with `(w² mod 8)` plus the odd-prime Gauss-sum invariants determined by `b_L`. Consequently
  two nondegenerate lattices of odd discriminant lie in one genus if and only if they have the same
  signature, the same parity, and isometric discriminant bilinear forms (the odd-discriminant case
  of Nikulin's Corollary 1.16.3).

## Main results

* `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_and_discriminantBilinear` and
  `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_and_discriminantQuadratic`: dyadic
  reduction of the genus of nondegenerate lattices via the discriminant form.
* `TauCeti.IntegralLattice.integralNorm_modEq_eight_of_odd_discriminant`: for nondegenerate
  lattices of odd discriminant whose signature differences `sigPos - sigNeg` agree modulo eight and
  whose discriminant bilinear modules are isometric, characteristic vectors have congruent norms
  modulo eight.
* `TauCeti.IntegralLattice.sameGenus_iff_discriminantBilinear_of_odd_discriminant`: nondegenerate
  lattices of odd discriminant lie in one genus if and only if their signatures, parities, and
  discriminant bilinear forms agree.
* `TauCeti.IntegralLattice.sameGenus_iff_discriminantQuadratic_of_isEven_of_odd_discriminant`: even
  nondegenerate lattices of odd discriminant lie in one genus if and only if their signatures and
  discriminant quadratic forms agree.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9
  (Corollary 1.9.4) and §1.16 (Corollary 1.16.3).
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open AddCommGroup Module

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Dyadic reduction of the genus -/

/-- **Dyadic reduction of the genus via the discriminant bilinear form.** Two nondegenerate
integral lattices lie in one genus if and only if their real signatures agree, their dyadic
localizations are integrally isometric, and their discriminant bilinear modules are isometric. -/
theorem sameGenus_iff_localIntegralForm_two_and_discriminantBilinear
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate] :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.localIntegralForm_equivalent 2,
    h.nonempty_isometry_discriminantBilinearModule⟩, ?_⟩
  rintro ⟨hsig, htwo, ⟨e⟩⟩
  have hdet : L.determinant = M.determinant :=
    determinant_eq_of_signature_eq_of_natCard_discriminantGroup_eq hsig
      (Nat.card_congr e.toAddEquiv.toEquiv)
  have hrank : finrank ℤ L = finrank ℤ M := L.finrank_eq_of_signature_eq hsig
  refine (sameGenus_iff L M).mpr ⟨hsig, fun p ↦ ?_⟩
  by_cases hp : p = 2
  · subst hp
    exact htwo
  · exact (localIntegralForm_equivalent_iff_primaryDiscriminantBilinear_of_determinant_eq
      L M hp hdet).mpr ⟨hrank, ⟨e.restrictPrimaryComponent p⟩⟩

/-- **Dyadic reduction of the genus for even lattices via the discriminant quadratic form.** Two
even nondegenerate integral lattices lie in one genus if and only if their real signatures agree,
their dyadic localizations are integrally isometric, and their discriminant quadratic modules are
isometric. -/
theorem sameGenus_iff_localIntegralForm_two_and_discriminantQuadratic
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.localIntegralForm_equivalent 2,
    h.nonempty_isometry_discriminantQuadraticModule hL⟩, ?_⟩
  rintro ⟨hsig, htwo, ⟨e⟩⟩
  exact (sameGenus_iff_localIntegralForm_two_and_discriminantBilinear L M).mpr
    ⟨hsig, htwo, ⟨e.toFiniteBilinearModule⟩⟩

/-! ### Oddity invariance and odd-discriminant genera -/

/-- At any odd prime `p`, an isometry between the `p`-primary discriminant bilinear modules of `L`
and `M` forces the `p`-primary discriminant quadratic modules of `L.evenSublattice` and
`M.evenSublattice` to have the same Gauss-sum invariant. -/
private theorem gaussSign_restrict_primaryComponent_evenSublattice_eq_of_odd
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (e : FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p))) :
    ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
      (primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p)).gaussSign =
    ((M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice).restrict
      (primaryComponent
        (M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice) p)).gaussSign := by
  let eL := primaryDiscriminantBilinearIsometry
    (L.evenSublattice.localInclusionIsometryEquiv L p
      L.evenSublattice_form L.evenSublattice_carrier_le
      (L.not_dvd_relIndex_evenSublattice_of_ne_two Fact.out hp))
  let eM := primaryDiscriminantBilinearIsometry
    (M.evenSublattice.localInclusionIsometryEquiv M p
      M.evenSublattice_form M.evenSublattice_carrier_le
      (M.not_dvd_relIndex_evenSublattice_of_ne_two Fact.out hp))
  have hodd := (L.evenSublattice.discriminantQuadraticModule
    L.isEven_evenSublattice).odd_natCard_restrict_primaryComponent Fact.out hp
  exact FiniteQuadraticModule.gaussSign_eq_of_bilinear_isometry_of_odd hodd
    (eL.trans (e.trans eM.symm))

private theorem primeFactors_evenSublattice_subset (K : IntegralLattice V) [K.IsNondegenerate]
    {d : ℕ} (hd : Odd d) (hK : K.discriminant = d) :
    (Nat.card (K.evenSublattice.discriminantQuadraticModule
      K.isEven_evenSublattice)).primeFactors ⊆ insert 2 d.primeFactors := by
  intro p hp
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ Nat.card (K.evenSublattice.discriminantQuadraticModule K.isEven_evenSublattice) :=
    Nat.dvd_of_mem_primeFactors hp
  rw [K.evenSublattice.natCard_discriminantQuadraticModule K.isEven_evenSublattice,
    K.evenSublattice.natCard_discriminantGroup,
    K.evenSublattice.discriminant_eq_mul_relIndex_sq K K.evenSublattice_form
      K.evenSublattice_carrier_le, hK] at hdvd
  rcases hp_prime.dvd_mul.mp hdvd with hdvdD | hdvdIdx
  · exact Finset.mem_insert_of_mem (hp_prime.mem_primeFactors hdvdD hd.pos.ne')
  · by_cases hp2 : p = 2
    · subst hp2
      exact Finset.mem_insert_self 2 _
    · exact False.elim (K.not_dvd_relIndex_evenSublattice_of_ne_two hp_prime hp2
        (hp_prime.dvd_of_dvd_pow hdvdIdx))

/-- **Oddity invariance for odd discriminant.** If two nondegenerate integral lattices `L` and `M`
with `L.discriminant` odd have signature differences `sigPos - sigNeg` congruent modulo eight and
isometric discriminant bilinear modules, then any characteristic vectors `w` of `L` and `w'` of `M`
have equal integral norms modulo eight. -/
theorem integralNorm_modEq_eight_of_odd_discriminant
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : Odd L.discriminant)
    (hsig : ((L.sigPos : ℤ) - L.sigNeg) ≡ ((M.sigPos : ℤ) - M.sigNeg) [ZMOD 8])
    (e : FiniteBilinearModule.Isometry L.discriminantBilinearModule M.discriminantBilinearModule)
    {w : L} {w' : M} (hw : L.IsCharacteristicVector w) (hw' : M.IsCharacteristicVector w') :
    L.integralNorm w ≡ M.integralNorm w' [ZMOD 8] := by
  classical
  have hdisc_eq : L.discriminant = M.discriminant := by
    have hcard : Nat.card L.DiscriminantGroup = Nat.card M.DiscriminantGroup :=
      Nat.card_congr e.toAddEquiv.toEquiv
    rwa [L.natCard_discriminantGroup, M.natCard_discriminantGroup] at hcard
  have hM : Odd M.discriminant := hdisc_eq ▸ hL
  let P : Finset ℕ := L.discriminant.primeFactors
  have h2P : 2 ∉ P := fun hmem ↦ hL.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
  have hP_prime (p : ℕ) (hp : p ∈ insert 2 P) : p.Prime := by
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors hp'
  let AL := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let AM := M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice
  have hsumL := FiniteQuadraticModule.gaussSign_eq_sum_of_primeFactors_subset
    (L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice)
    hP_prime (primeFactors_evenSublattice_subset L hL rfl)
  have hsumM := FiniteQuadraticModule.gaussSign_eq_sum_of_primeFactors_subset
    (M.evenSublattice.isNondegenerate_discriminantQuadraticModule M.isEven_evenSublattice)
    hP_prime (primeFactors_evenSublattice_subset M hL hdisc_eq.symm)
  rw [Finset.sum_insert h2P,
    L.gaussSign_restrict_primaryComponent_two_evenSublattice hL hw] at hsumL
  rw [Finset.sum_insert h2P,
    M.gaussSign_restrict_primaryComponent_two_evenSublattice hM hw'] at hsumM
  have hmilL := L.evenSublattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg
    L.isEven_evenSublattice
  have hmilM := M.evenSublattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg
    M.isEven_evenSublattice
  have hsigL := L.evenSublattice_signature
  have hsigM := M.evenSublattice_signature
  simp only [signature, Prod.mk.injEq] at hsigL hsigM
  have hsig_eq : ((L.sigPos : ZMod 8) - L.sigNeg) = ((M.sigPos : ZMod 8) - M.sigNeg) := by
    simpa only [Int.cast_sub, Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff _ _ 8).mpr hsig
  have hAL_eq_AM : AL.gaussSign = AM.gaussSign := by
    rw [hmilL, hmilM, hsigL.1, hsigL.2.2, hsigM.1, hsigM.2.2, hsig_eq]
  have hodd_sum : ∑ p ∈ P, (AL.restrict (primaryComponent AL p)).gaussSign =
      ∑ p ∈ P, (AM.restrict (primaryComponent AM p)).gaussSign := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hp_prime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact gaussSign_restrict_primaryComponent_evenSublattice_eq_of_odd L M
      (fun h2 ↦ h2P (h2 ▸ hp)) (e.restrictPrimaryComponent p)
  have h := (hsumL.symm.trans hAL_eq_AM).trans hsumM
  rw [hodd_sum] at h
  exact (ZMod.intCast_eq_intCast_iff _ _ 8).mp (add_right_cancel h)

/-- **The genus of lattices of odd discriminant (Nikulin, Corollary 1.16.3, odd-discriminant
case).** Let `L` and `M` be nondegenerate integral lattices with `L.discriminant` odd. Then `L` and
`M` lie in the same genus if and only if they have the same real signature, `L` is even if and only
if `M` is, and their discriminant bilinear modules are isometric. -/
theorem sameGenus_iff_discriminantBilinear_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧ (L.IsEven ↔ M.IsEven) ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.isEven_iff, h.nonempty_isometry_discriminantBilinearModule⟩,
    ?_⟩
  rintro ⟨hsig, heven, ⟨e⟩⟩
  have hcard : Nat.card L.DiscriminantGroup = Nat.card M.DiscriminantGroup :=
    Nat.card_congr e.toAddEquiv.toEquiv
  have hdisc_eq : L.discriminant = M.discriminant := by
    rwa [L.natCard_discriminantGroup, M.natCard_discriminantGroup] at hcard
  have hM : Odd M.discriminant := hdisc_eq ▸ hL
  have hdet : L.determinant = M.determinant :=
    determinant_eq_of_signature_eq_of_natCard_discriminantGroup_eq hsig hcard
  have hsig8 : ((L.sigPos : ℤ) - L.sigNeg) ≡ ((M.sigPos : ℤ) - M.sigNeg) [ZMOD 8] := by
    have h : ((L.sigPos : ℤ) - L.sigNeg) = ((M.sigPos : ℤ) - M.sigNeg) :=
      congrArg (fun s : ℕ × ℕ × ℕ ↦ (s.1 : ℤ) - s.2.2) hsig
    rw [h]
  obtain ⟨w, hw⟩ := exists_isCharacteristicVector_of_odd_discriminant hL
  obtain ⟨w', hw'⟩ := exists_isCharacteristicVector_of_odd_discriminant hM
  refine (sameGenus_iff_localIntegralForm_two_and_discriminantBilinear L M).mpr ⟨hsig, ?_, ⟨e⟩⟩
  exact (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M
    (L.isUnit_determinant_two_iff_odd_discriminant.mpr hL)
    (M.isUnit_determinant_two_iff_odd_discriminant.mpr hM) hw hw').mpr
    ⟨L.finrank_eq_of_signature_eq hsig, heven, hdet ▸ IsSquare.mul_self _,
      integralNorm_modEq_eight_of_odd_discriminant hL hsig8 e hw hw'⟩

/-- **The genus of even lattices of odd discriminant (Nikulin, Corollary 1.9.4, odd-discriminant
case).** Let `L` and `M` be even nondegenerate integral lattices with `L.discriminant` odd. Then
`L` and `M` lie in the same genus if and only if they have the same real signature and their
discriminant quadratic modules are isometric. -/
theorem sameGenus_iff_discriminantQuadratic_of_isEven_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hLe : L.IsEven) (hMe : M.IsEven) (hL : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        Nonempty (FiniteQuadraticModule.Isometry
          (L.discriminantQuadraticModule hLe) (M.discriminantQuadraticModule hMe)) := by
  have hoddA : Odd (Nat.card (L.discriminantQuadraticModule hLe)) := by
    rwa [L.natCard_discriminantQuadraticModule hLe, L.natCard_discriminantGroup]
  rw [sameGenus_iff_discriminantBilinear_of_odd_discriminant L M hL,
    ← L.discriminantQuadraticModule_toFiniteBilinearModule hLe,
    ← M.discriminantQuadraticModule_toFiniteBilinearModule hMe,
    ← FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hoddA]
  simp [hLe, hMe]

end TauCeti.IntegralLattice
