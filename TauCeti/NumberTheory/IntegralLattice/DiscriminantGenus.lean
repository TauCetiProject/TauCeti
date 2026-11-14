/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.Data.Int.MulPred
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.GaussSum
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Characteristic
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.OddPrime
import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The genus and discriminant forms

Lattices in the same genus share their real signature, their dyadic localization `L_2`, and their
discriminant bilinear form `b_L`
(`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantBilinearModule`), or their
discriminant quadratic form `q_L` when they are even
(`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantQuadraticModule`). Because
signature and discriminant-group order determine the signed determinant, and the `p`-primary
discriminant bilinear form classifies `L_p` at every odd prime `p`
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_primaryDiscriminantBilinear`),
those invariants conversely decide the genus of any nondegenerate integral lattice: all odd-prime
local conditions are absorbed into `b_L` (or `q_L`), leaving only the dyadic localization `L_2`.

When `L` has odd discriminant — equivalently, when its signed determinant is a unit in `ℤ_2` — the
dyadic localization `L_2` is unimodular and is itself determined by the remaining invariants:

* For even lattices of odd discriminant, rank and determinant square class already classify `L_2`
  (`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isEven`), and `q_L` has odd
  order so its isometry class coincides with that of `b_L`
  (`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`). Thus two even
  nondegenerate lattices of odd discriminant lie in one genus if and only if they have the same
  signature and isometric discriminant quadratic forms (the odd-discriminant case of Nikulin's
  Corollary 1.9.4).
* For general nondegenerate lattices of odd discriminant (even or odd), `L` admits an integral
  characteristic vector `w`, and the oddity `w² mod 8` is pinned down by the signature together
  with the odd primary components of `b_L`: passing to the canonical even sublattice `N` leaves all
  odd-prime localizations unchanged (`[L : N] ≤ 2`), while Milgram's theorem on `q_N` equates
  `sigPos L - sigNeg L` modulo `8` with `(w² mod 8)` plus the odd-prime Gauss-sum invariants
  determined by `b_L`. Consequently two nondegenerate lattices of odd discriminant lie in one genus
  if and only if they have the same signature, the same parity, and isometric discriminant bilinear
  forms (the odd-discriminant case of Nikulin's Corollary 1.16.3).

## Main results

* `TauCeti.IntegralLattice.determinant_eq_of_signature_eq_of_natCard_discriminantGroup_eq`: equal
  signatures and equal discriminant-group orders force equal signed determinants.
* `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_and_discriminantBilinear` and
  `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_and_discriminantQuadratic`: dyadic
  reduction of the genus of nondegenerate lattices via the discriminant form.
* `TauCeti.IntegralLattice.isUnit_determinant_two_iff_odd_discriminant`: a lattice has a `2`-adic
  unit determinant if and only if its discriminant is odd.
* `TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`: every lattice of odd
  discriminant admits an integral characteristic vector.
* `TauCeti.IntegralLattice.integralNorm_modEq_eight_of_odd_discriminant`: for nondegenerate
  lattices of odd discriminant, equal signatures and isometric discriminant bilinear modules force
  characteristic vectors to have congruent norms modulo eight.
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

/-! ### Signed determinant and dyadic reduction of the genus -/

/-- Equal signatures and equal discriminant-group orders imply equal signed determinants, without
any nondegeneracy assumption. -/
theorem determinant_eq_of_signature_eq_of_natCard_discriminantGroup_eq
    {L : IntegralLattice V} {M : IntegralLattice W} (hsig : L.signature = M.signature)
    (hcard : Nat.card L.DiscriminantGroup = Nat.card M.DiscriminantGroup) :
    L.determinant = M.determinant := by
  have hneg : L.sigNeg = M.sigNeg := congrArg (fun s ↦ s.2.2) hsig
  have hdisc : L.discriminant = M.discriminant := by
    rwa [L.natCard_discriminantGroup, M.natCard_discriminantGroup] at hcard
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
    M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hneg, hdisc]

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

/-! ### Odd discriminant and characteristic vectors -/

/-- The signed determinant of an integral lattice is a unit in `ℤ_2` if and only if the lattice
discriminant is odd. -/
theorem isUnit_determinant_two_iff_odd_discriminant (L : IntegralLattice V) :
    IsUnit (L.determinant : ℤ_[2]) ↔ Odd L.discriminant := by
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast,
    IsUnit.mul_iff, and_iff_right ((isUnit_one.neg).pow L.sigNeg),
    PadicInt.isUnit_natCast_iff, Nat.odd_iff, Nat.dvd_iff_mod_eq_zero]
  omega

/-- Every integral lattice of odd discriminant admits an integral characteristic vector. -/
theorem exists_isCharacteristicVector_of_odd_discriminant {L : IntegralLattice V}
    (hL : Odd L.discriminant) : ∃ w : L, L.IsCharacteristicVector w := by
  classical
  have hunit : IsUnit (L.determinant : ℤ_[2]) :=
    (L.isUnit_determinant_two_iff_odd_discriminant).mpr hL
  have := L.isPerfPair_localIntegralForm_of_isUnit_determinant 2 hunit
  obtain ⟨w₂, hw₂⟩ :=
    (L.isSymm_localIntegralForm 2).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  let b := Module.finBasis ℤ L
  let b₂ := b.baseChange ℤ_[2]
  let m : Fin (finrank ℤ L) → ℤ := fun i ↦ ((b₂.repr w₂ i).appr 1 : ℤ)
  refine ⟨∑ i, m i • b i, (L.isCharacteristicVector_iff_isCharacteristic _).mpr ?_⟩
  refine (L.isSymm_integralForm.isCharacteristic_iff_forall_basis Int.two_dvd_sq_sub_self b).mpr
    fun j ↦ ?_
  have hdvd_diff : (2 : ℤ_[2]) ∣
      L.localIntegralForm 2 w₂ (b₂ j) - (L.integralForm (∑ i, m i • b i) (b j) : ℤ_[2]) := by
    rw [← b₂.sum_repr w₂]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ ↦ ?_
    have hbij : L.localIntegralForm 2 (b₂ i) (b₂ j) = (L.integralForm (b i) (b j) : ℤ_[2]) := by
      simp [b₂]
    rw [hbij, ← sub_mul]
    exact dvd_mul_of_dvd_left (by simpa [m] using PadicInt.dvd_sub_appr (b₂.repr w₂ i) 1) _
  have hbj : L.localIntegralForm 2 (b₂ j) (b₂ j) = (L.integralForm (b j) (b j) : ℤ_[2]) := by
    simp [b₂]
  have hdvd₂ : (2 : ℤ_[2]) ∣
      ((L.integralForm (∑ i, m i • b i) (b j) - L.integralForm (b j) (b j) : ℤ) : ℤ_[2]) := by
    have hsub := dvd_sub (LinearMap.BilinForm.isCharacteristic_iff.mp hw₂ (b₂ j)) hdvd_diff
    rwa [hbj, sub_sub_sub_cancel_left, ← Int.cast_sub] at hsub
  exact_mod_cast (PadicInt.pow_p_dvd_int_iff (p := 2) 1 _).mp (by simpa using hdvd₂)

/-! ### Oddity invariance and odd-discriminant genera -/

private theorem not_dvd_relIndex_evenSublattice_of_ne_two (K : IntegralLattice V)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ¬ p ∣ K.evenSublattice.carrier.toAddSubgroup.relIndex K.carrier.toAddSubgroup := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  let IK := K.toIntermediateCarrier K.evenSublattice_form.symm K.evenSublattice_carrier_le
  have hILat : IK.1.IsLattice ℚ := by
    rw [K.coe_toIntermediateCarrier]
    infer_instance
  have hpos : 0 < K.evenSublattice.carrier.toAddSubgroup.relIndex K.carrier.toAddSubgroup := by
    simpa only [IntermediateCarrier.index_def, IK, coe_toIntermediateCarrier] using
      IntermediateCarrier.index_pos IK
  have hle := K.relIndex_evenSublattice_le_two
  intro hdvd
  have := Nat.le_of_dvd hpos hdvd
  omega

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
      (not_dvd_relIndex_evenSublattice_of_ne_two L hp))
  let eM := primaryDiscriminantBilinearIsometry
    (M.evenSublattice.localInclusionIsometryEquiv M p
      M.evenSublattice_form M.evenSublattice_carrier_le
      (not_dvd_relIndex_evenSublattice_of_ne_two M hp))
  have hodd : Odd (Nat.card
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (primaryComponent
          (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p))) := by
    -- The carrier of `(N.discriminantQuadraticModule _).restrict P` is definitionally `P`.
    change Odd (Nat.card (primaryComponent L.evenSublattice.DiscriminantGroup p))
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ Fact.out]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  exact FiniteQuadraticModule.gaussSign_eq_of_bilinear_isometry_of_odd hodd
    (eL.trans (e.trans eM.symm))

private theorem primeFactors_evenSublattice_subset (K : IntegralLattice V) [K.IsNondegenerate]
    {d : ℕ} (hd : Odd d) (hK : K.discriminant = d) :
    (Nat.card (K.evenSublattice.discriminantQuadraticModule
      K.isEven_evenSublattice)).primeFactors ⊆ insert 2 d.primeFactors := by
  let IK := K.toIntermediateCarrier K.evenSublattice_form.symm K.evenSublattice_carrier_le
  have hILat : IK.1.IsLattice ℚ := by
    rw [K.coe_toIntermediateCarrier]
    infer_instance
  have hIK := K.isIntegral_toIntermediateCarrier K.evenSublattice_form.symm
    K.evenSublattice_carrier_le
  have hcardK : Nat.card (K.evenSublattice.discriminantQuadraticModule K.isEven_evenSublattice) =
      d * IntermediateCarrier.index IK ^ 2 := by
    -- The carrier of `discriminantQuadraticModule` is definitionally `DiscriminantGroup`.
    change Nat.card K.evenSublattice.DiscriminantGroup = _
    rw [K.evenSublattice.natCard_discriminantGroup, ← hIK.discriminant_mul_index_sq,
      K.toIntegralLattice_toIntermediateCarrier, hK]
  intro p hp
  rw [hcardK] at hp
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  rcases hp_prime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hdvdD | hdvdIdx
  · exact Finset.mem_insert_of_mem (hp_prime.mem_primeFactors hdvdD hd.pos.ne')
  · have hdvdI : p ∣ IntermediateCarrier.index IK := hp_prime.dvd_of_dvd_pow hdvdIdx
    have hpos : 0 < IntermediateCarrier.index IK := IntermediateCarrier.index_pos IK
    have hle : IntermediateCarrier.index IK ≤ 2 := by
      simpa only [IntermediateCarrier.index_def, IK, coe_toIntermediateCarrier] using
        K.relIndex_evenSublattice_le_two
    have hp_le : p ≤ 2 := (Nat.le_of_dvd hpos hdvdI).trans hle
    have hp_ge : 2 ≤ p := hp_prime.two_le
    exact Finset.mem_insert.mpr (Or.inl (by omega))

/-- **Oddity invariance for odd discriminant.** If two nondegenerate integral lattices `L` and `M`
with `L.discriminant` odd have equal real signatures and isometric discriminant bilinear modules,
then any characteristic vectors `w` of `L` and `w'` of `M` have equal integral norms modulo
eight. -/
theorem integralNorm_modEq_eight_of_odd_discriminant
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : Odd L.discriminant) (hsig : L.signature = M.signature)
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
  simp only [signature, Prod.mk.injEq] at hsig hsigL hsigM
  have hAL_eq_AM : AL.gaussSign = AM.gaussSign := by
    rw [hmilL, hmilM, hsigL.1, hsigL.2.2, hsigM.1, hsigM.2.2, hsig.1, hsig.2.2]
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
  obtain ⟨w, hw⟩ := exists_isCharacteristicVector_of_odd_discriminant hL
  obtain ⟨w', hw'⟩ := exists_isCharacteristicVector_of_odd_discriminant hM
  refine (sameGenus_iff_localIntegralForm_two_and_discriminantBilinear L M).mpr ⟨hsig, ?_, ⟨e⟩⟩
  exact (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M
    (L.isUnit_determinant_two_iff_odd_discriminant.mpr hL)
    (M.isUnit_determinant_two_iff_odd_discriminant.mpr hM) hw hw').mpr
    ⟨L.finrank_eq_of_signature_eq hsig, heven, hdet ▸ IsSquare.mul_self _,
      integralNorm_modEq_eight_of_odd_discriminant hL hsig e hw hw'⟩

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
    -- The carrier of `discriminantQuadraticModule` is definitionally `DiscriminantGroup`.
    change Odd (Nat.card L.DiscriminantGroup)
    rwa [L.natCard_discriminantGroup]
  rw [sameGenus_iff_discriminantBilinear_of_odd_discriminant L M hL,
    ← L.discriminantQuadraticModule_toFiniteBilinearModule hLe,
    ← M.discriminantQuadraticModule_toFiniteBilinearModule hMe,
    ← FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hoddA]
  simp [hLe, hMe]

end TauCeti.IntegralLattice
