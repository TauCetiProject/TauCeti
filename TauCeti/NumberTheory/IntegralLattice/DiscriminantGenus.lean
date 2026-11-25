/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import Mathlib.Tactic.IntervalCases
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.OddDiscriminant
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Discriminant
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Classification
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Classification of genera by signature and discriminant form

Let `L` and `M` be nondegenerate integral lattices. When `L` and `M` lie in the same genus, their
signatures agree, they have the same parity, and their discriminant bilinear forms `b_L` and `b_M`
— as well as their discriminant quadratic forms `q_L` and `q_M` when both lattices are even — are
isometric (`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantBilinearModule` and
`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantQuadraticModule`).

Away from `2`, the odd-prime local classification reduces the genus relation to the real signature,
the discriminant bilinear form, and the dyadic localization `L_2`
(`TauCeti.IntegralLattice.sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent`).
For even lattices of equal signature, Milgram's theorem equates the Gauss-sum invariants of `q_L`
and `q_M`, so Nikulin's comparison theorem makes `q_L ≃ q_M` equivalent to `b_L ≃ b_M`
(`nonempty_isometry_discriminantQuadraticModule_iff_discriminantBilinearModule`), giving the
quadratic away-from-`2` reduction
`TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_and_discriminantQuadraticModule`.

When `L` has odd discriminant, its dyadic localization is unimodular over `ℤ_2`. Every such lattice
has a characteristic vector (`exists_isCharacteristicVector_of_odd_discriminant`), and the
odd-discriminant van der Blij–Milgram identity
(`TauCeti.IntegralLattice.integralNorm_characteristicVector_modEq_of_odd_discriminant`) shows that
the signature and `b_L` determine the characteristic norm modulo `8`, hence classify `L_2` once the
parity (`IsEven`) is fixed. This yields the odd-discriminant cases of Nikulin's genus theorems:

* `TauCeti.IntegralLattice.sameGenus_iff_of_odd_discriminant` (Nikulin, Corollary 1.16.3 for odd
  discriminant): `L.SameGenus M` if and only if `L.signature = M.signature`, `L.IsEven ↔ M.IsEven`,
  and `b_L ≃ b_M`.
* `TauCeti.IntegralLattice.sameGenus_iff_of_isEven_of_odd_discriminant` (Nikulin, Corollary 1.9.4
  for odd discriminant): for even lattices of odd discriminant, `L.SameGenus M` if and only if
  `L.signature = M.signature` and `q_L ≃ q_M`.

Finally, the rank-two lattices `⟨1⟩ ⊕ ⟨15⟩` and `⟨3⟩ ⊕ ⟨5⟩` show that the discriminant-form
condition is indispensable even when the signature, signed determinant, parity, discriminant-group
isomorphism type (`ℤ/15ℤ`), and dyadic localization all agree: their `2`-adic localizations are
isometric (`localIntegralForm_two_equivalent_rankOne_one_fifteen_three_five`), yet `b_{⟨1⟩ ⊕ ⟨15⟩}`
has `3`-torsion self-pairings `{0, 2/3}` while `b_{⟨3⟩ ⊕ ⟨5⟩}` realizes `1/3`, so their
discriminant bilinear modules are not isometric and the lattices lie in distinct genera
(`TauCeti.IntegralLattice.not_sameGenus_rankOne_one_fifteen_three_five`).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Proposition
  1.9.2, Corollary 1.9.4, Theorem 1.11.3, and Corollary 1.16.3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V} {M : IntegralLattice W}

/-! ### Polar comparison for discriminant forms of even lattices -/

/-- **For even lattices of equal signature, quadratic and bilinear discriminant isometry coincide.**
Milgram's theorem identifies the Gauss-sum invariants of `q_L` and `q_M` with the common signature
difference modulo `8`, after which Nikulin's comparison theorem corrects any bilinear isometry
`b_L ≃ b_M` to obtain a quadratic isometry `q_L ≃ q_M`, potentially changing its underlying map. -/
theorem nonempty_isometry_discriminantQuadraticModule_iff_discriminantBilinearModule
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) (hM : M.IsEven)
    (hsig : L.signature = M.signature) :
    Nonempty (FiniteQuadraticModule.Isometry
        (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) ↔
      Nonempty (FiniteBilinearModule.Isometry
        L.discriminantBilinearModule M.discriminantBilinearModule) := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq
    (L.isNondegenerate_discriminantQuadraticModule hL),
    L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    M.discriminantQuadraticModule_toFiniteBilinearModule hM]
  simp only [signature, Prod.mk.injEq] at hsig
  have hsign : (L.discriminantQuadraticModule hL).gaussSign =
      (M.discriminantQuadraticModule hM).gaussSign := by
    rw [L.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg hL,
      M.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg hM, hsig.1, hsig.2.2]
  exact and_iff_left hsign

/-! ### Reduction of the even genus to the dyadic localization and discriminant quadratic form -/

/-- **Reduction of the even genus to `2`-adic equivalence and the discriminant quadratic form.**
Two even nondegenerate integral lattices lie in the same genus if and only if they have the same
signature, isometric `2`-adic localizations, and isometric discriminant quadratic modules. -/
theorem sameGenus_iff_localIntegralForm_two_and_discriminantQuadraticModule
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) (hM : M.IsEven) :
    L.SameGenus M ↔ L.signature = M.signature ∧
      (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ∧
      Nonempty (FiniteQuadraticModule.Isometry
        (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) := by
  rw [sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent]
  exact ⟨fun ⟨hsig, hbil, h2⟩ ↦ ⟨hsig, h2,
      (nonempty_isometry_discriminantQuadraticModule_iff_discriminantBilinearModule hL hM hsig).mpr
        hbil⟩,
    fun ⟨hsig, h2, hquad⟩ ↦ ⟨hsig,
      (nonempty_isometry_discriminantQuadraticModule_iff_discriminantBilinearModule hL hM hsig).mp
        hquad, h2⟩⟩

/-! ### Classification of genera of odd discriminant -/

private theorem discriminant_and_determinant_eq_of_isometry_discriminantBilinearModule
    [L.IsNondegenerate] [M.IsNondegenerate] (hsig : L.signature = M.signature)
    (f : FiniteBilinearModule.Isometry L.discriminantBilinearModule M.discriminantBilinearModule) :
    L.discriminant = M.discriminant ∧ L.determinant = M.determinant := by
  have hdisc : L.discriminant = M.discriminant := by
    rw [← L.natCard_discriminantGroup, ← M.natCard_discriminantGroup]
    exact Nat.card_congr f.toAddEquiv.toEquiv
  have hneg : L.sigNeg = M.sigNeg := congrArg (fun s ↦ s.2.2) hsig
  refine ⟨hdisc, ?_⟩
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
    M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hneg, hdisc]

private theorem isUnit_determinant_padicInt_two_of_odd_discriminant
    (hodd : Odd L.discriminant) : IsUnit (L.determinant : ℤ_[2]) := by
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  refine IsUnit.mul ((isUnit_one.neg).pow _) (PadicInt.isUnit_natCast_iff.mpr fun hdvd ↦ ?_)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨m, hm⟩ := hdvd
  omega

/-- **Genus classification for lattices of odd discriminant (Nikulin, Corollary 1.16.3, odd
discriminant case).** If `L` and `M` are nondegenerate integral lattices and `L` has odd
discriminant, then `L` and `M` lie in the same genus if and only if their signatures agree, they
are both even or both odd, and their discriminant bilinear modules are isometric. -/
theorem sameGenus_iff_of_odd_discriminant [L.IsNondegenerate] [M.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    L.SameGenus M ↔ L.signature = M.signature ∧ (L.IsEven ↔ M.IsEven) ∧
      Nonempty (FiniteBilinearModule.Isometry
        L.discriminantBilinearModule M.discriminantBilinearModule) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.isEven_iff, h.nonempty_isometry_discriminantBilinearModule⟩,
    fun ⟨hsig, heven, ⟨f⟩⟩ ↦ ?_⟩
  obtain ⟨hdisc, hdet⟩ :=
    discriminant_and_determinant_eq_of_isometry_discriminantBilinearModule hsig f
  have hoddM : Odd M.discriminant := hdisc ▸ hodd
  obtain ⟨w, hw⟩ := L.exists_isCharacteristicVector_of_odd_discriminant hodd
  obtain ⟨w', hw'⟩ := M.exists_isCharacteristicVector_of_odd_discriminant hoddM
  have hmod := L.integralNorm_characteristicVector_modEq_of_odd_discriminant hodd hsig hw hw' f
  have h2 : (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) :=
    (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M
      (isUnit_determinant_padicInt_two_of_odd_discriminant hodd)
      (isUnit_determinant_padicInt_two_of_odd_discriminant hoddM) hw hw').mpr
      ⟨L.finrank_eq_of_signature_eq hsig, heven, hdet ▸ IsSquare.mul_self _, hmod⟩
  exact sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent.mpr ⟨hsig, ⟨f⟩, h2⟩

/-- **Genus classification for even lattices of odd discriminant (Nikulin, Corollary 1.9.4, odd
discriminant case).** Two even nondegenerate integral lattices with `Odd L.discriminant` lie in the
same genus if and only if their signatures agree and their discriminant quadratic modules are
isometric. -/
theorem sameGenus_iff_of_isEven_of_odd_discriminant [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) (hodd : Odd L.discriminant) :
    L.SameGenus M ↔ L.signature = M.signature ∧
      Nonempty (FiniteQuadraticModule.Isometry
        (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) := by
  rw [sameGenus_iff_of_odd_discriminant hodd]
  exact ⟨fun ⟨hsig, _, hbil⟩ ↦ ⟨hsig,
      (nonempty_isometry_discriminantQuadraticModule_iff_discriminantBilinearModule hL hM hsig).mpr
        hbil⟩,
    fun ⟨hsig, hquad⟩ ↦ ⟨hsig, iff_of_true hL hM,
      (nonempty_isometry_discriminantQuadraticModule_iff_discriminantBilinearModule hL hM hsig).mp
        hquad⟩⟩

/-! ### Sharpness: `⟨1⟩ ⊕ ⟨15⟩` and `⟨3⟩ ⊕ ⟨5⟩` -/

private def rankOneUnit (a : ℤ) : rankOne a :=
  ⟨1, (mem_rankOne_carrier_iff a 1).mpr ⟨1, Int.cast_one⟩⟩

private theorem isCharacteristicVector_rankOneUnit (a : ℤ) :
    (rankOne a).IsCharacteristicVector (rankOneUnit a) := by
  rw [(rankOne a).isCharacteristicVector_iff]
  intro x
  obtain ⟨z, hz⟩ := (mem_rankOne_carrier_iff a (x : ℚ)).mp x.property
  rw [integralForm_rankOne_eq _ x (k := 1) rfl hz.symm, integralNorm_rankOne_eq x hz.symm,
    Int.modEq_iff_dvd]
  obtain ⟨m, hm⟩ := Int.two_dvd_mul_add_one z
  exact ⟨a * (m - z), by linear_combination a * hm⟩

/-- The positive definite odd rank-two lattices `⟨1⟩ ⊕ ⟨15⟩` and `⟨3⟩ ⊕ ⟨5⟩` have isometric
`2`-adic integral localizations: both are odd unimodular over `ℤ_2` of determinant `15`, and their
characteristic vectors `(1, 1)` have norms `16` and `8`, both divisible by `8`. -/
theorem localIntegralForm_two_equivalent_rankOne_one_fifteen_three_five :
    (((rankOne 1).orthogonalSum (rankOne 15)).localIntegralForm 2).Equivalent
      (((rankOne 3).orthogonalSum (rankOne 5)).localIntegralForm 2) := by
  let L₁ := (rankOne 1).orthogonalSum (rankOne 15)
  let L₂ := (rankOne 3).orthogonalSum (rankOne 5)
  let w₁ : L₁ := (orthogonalSumCarrierEquiv (rankOne 1) (rankOne 15)).symm
    (rankOneUnit 1, rankOneUnit 15)
  let w₂ : L₂ := (orthogonalSumCarrierEquiv (rankOne 3) (rankOne 5)).symm
    (rankOneUnit 3, rankOneUnit 5)
  have hw₁ : L₁.IsCharacteristicVector w₁ := by
    rw [isCharacteristicVector_orthogonalSum_iff]
    simp [w₁, orthogonalSumFst_apply, orthogonalSumSnd_apply, isCharacteristicVector_rankOneUnit]
  have hw₂ : L₂.IsCharacteristicVector w₂ := by
    rw [isCharacteristicVector_orthogonalSum_iff]
    simp [w₂, orthogonalSumFst_apply, orthogonalSumSnd_apply, isCharacteristicVector_rankOneUnit]
  have hdet₁ : L₁.determinant = 15 := by simp [L₁]
  have hdet₂ : L₂.determinant = 15 := by simp [L₂]
  have hu₁ : IsUnit (L₁.determinant : ℤ_[2]) := by
    rw [hdet₁]; exact PadicInt.isUnit_intCast_iff.mpr (by decide)
  have hu₂ : IsUnit (L₂.determinant : ℤ_[2]) := by
    rw [hdet₂]; exact PadicInt.isUnit_intCast_iff.mpr (by decide)
  refine (L₁.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector L₂ hu₁ hu₂ hw₁ hw₂).mpr
    ⟨by simp [L₁, L₂], by simp only [L₁, L₂, isEven_orthogonalSum_iff, isEven_rankOne_iff]; decide,
      ?_, ?_⟩
  · rw [hdet₁, hdet₂]
    exact IsSquare.mul_self _
  · have hn₁ : L₁.integralNorm w₁ = 16 := by
      simp only [L₁, w₁, integralNorm_orthogonalSum, orthogonalSumFst_apply,
        orthogonalSumSnd_apply, LinearEquiv.apply_symm_apply,
        integralNorm_rankOne_eq (rankOneUnit 1) (k := 1) rfl,
        integralNorm_rankOne_eq (rankOneUnit 15) (k := 1) rfl]
      norm_num
    have hn₂ : L₂.integralNorm w₂ = 8 := by
      simp only [L₂, w₂, integralNorm_orthogonalSum, orthogonalSumFst_apply,
        orthogonalSumSnd_apply, LinearEquiv.apply_symm_apply,
        integralNorm_rankOne_eq (rankOneUnit 3) (k := 1) rfl,
        integralNorm_rankOne_eq (rankOneUnit 5) (k := 1) rfl]
      norm_num
    rw [hn₁, hn₂]
    decide

private theorem not_exists_three_torsion_selfPairing_one_third
    (y : (rankOne 15).DiscriminantGroup) (hy3 : 3 • y = 0)
    (hpair : (rankOne 15).discriminantPairing y y =
      (rankOne 3).discriminantPairing (rankOneClass 3) (rankOneClass 3)) : False := by
  let m : ZMod 15 := rankOneDiscriminantEquiv 15 y
  have hm3 : 3 • m = 0 :=
    (map_nsmul (rankOneDiscriminantEquiv 15) 3 y).symm.trans (by rw [hy3, map_zero])
  have hy : y = (m.val : ℤ) • rankOneClass 15 :=
    (rankOneDiscriminantEquiv 15).injective (by
      rw [rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast, ZMod.natCast_zmod_val])
  rw [hy, discriminantPairing_zsmul_rankOneClass, discriminantPairing_rankOneClass_self] at hpair
  have hdiff : (((((m.val : ℤ) : ℚ) * ((m.val : ℤ) : ℚ) / ((15 : ℤ) : ℚ) -
      (1 : ℚ) / ((3 : ℤ) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact hpair
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp ((AddCircle.coe_eq_zero_iff_mem_one _).mp hdiff)
  rw [eq_intCast] at hn
  have hm5 : 5 ∣ m.val := by
    have h15 : 15 ∣ 3 * m.val := by
      have hz : ((3 * m.val : ℕ) : ZMod 15) = 0 := by simpa [nsmul_eq_mul] using hm3
      exact (ZMod.natCast_eq_zero_iff _ 15).mp hz
    omega
  obtain ⟨t, ht⟩ := hm5
  have ht3 : t < 3 := by have := m.val_lt; omega
  have hqn : (5 * (t : ℤ) ^ 2 - 1 : ℚ) = 3 * n := by
    rw [ht] at hn
    push_cast at hn ⊢
    linear_combination -3 * hn
  have hin : 5 * (t : ℤ) ^ 2 - 1 = 3 * n := by exact_mod_cast hqn
  interval_cases t <;> omega

/-- **The discriminant bilinear modules of `⟨1⟩ ⊕ ⟨15⟩` and `⟨3⟩ ⊕ ⟨5⟩` are not isometric,**
even though their underlying discriminant groups are both cyclic of order `15`: in `b_{⟨3⟩ ⊕ ⟨5⟩}`
the `3`-torsion generator has self-pairing `1/3 mod ℤ`, whereas every `3`-torsion element of
`b_{⟨1⟩ ⊕ ⟨15⟩}` has self-pairing `5 t² / 3 ≡ 0` or `2/3 mod ℤ`. -/
theorem isEmpty_isometry_discriminantBilinearModule_rankOne_one_fifteen_three_five :
    IsEmpty (FiniteBilinearModule.Isometry
      ((rankOne 1).orthogonalSum (rankOne 15)).discriminantBilinearModule
      ((rankOne 3).orthogonalSum (rankOne 5)).discriminantBilinearModule) := by
  refine ⟨fun f ↦ ?_⟩
  let g := ((rankOne 3).discriminantBilinearIsometryOrthogonalSum (rankOne 5)).symm.trans
    (f.symm.trans ((rankOne 1).discriminantBilinearIsometryOrthogonalSum (rankOne 15)))
  let c : ((rankOne 3).discriminantBilinearModule.prod
      (rankOne 5).discriminantBilinearModule) := (rankOneClass 3, 0)
  have hc3 : 3 • c = 0 := by
    have h3 : 3 • rankOneClass 3 = 0 := (rankOneDiscriminantEquiv 3).injective <| by
      rw [← natCast_zsmul, rankOneDiscriminantEquiv_zsmul_rankOneClass, map_zero]
      decide
    exact Prod.ext h3 (nsmul_zero 3)
  have hgc3 : 3 • g c = 0 :=
    (map_nsmul g.toAddEquiv 3 c).symm.trans (by rw [hc3, map_zero])
  have hsub1 : Subsingleton (rankOne 1).discriminantBilinearModule :=
    ((rankOne 1).isUnimodular_iff_subsingleton_discriminantGroup).mp
      ((isUnimodular_rankOne_iff 1).mpr isUnit_one)
  have hy1 : (g c).1 = 0 := hsub1.elim _ _
  have hpair := g.map_pairing c c
  rw [FiniteBilinearModule.prod_pairing, FiniteBilinearModule.prod_pairing,
    hy1, FiniteBilinearModule.pairing_zero_left, zero_add,
    FiniteBilinearModule.pairing_zero_left, add_zero,
    discriminantBilinearModule_pairing] at hpair
  exact not_exists_three_torsion_selfPairing_one_third (g c).2 (congrArg Prod.snd hgc3)
    (((rankOne 15).discriminantBilinearModule_pairing (g c).2 (g c).2).symm.trans hpair)

/-- **The lattices `⟨1⟩ ⊕ ⟨15⟩` and `⟨3⟩ ⊕ ⟨5⟩` do not lie in the same genus,** despite having the
same signature `(2, 0, 0)`, signed determinant `15`, odd parity, cyclic discriminant group of order
`15`, and `2`-adic localization. -/
theorem not_sameGenus_rankOne_one_fifteen_three_five :
    ¬ ((rankOne 1).orthogonalSum (rankOne 15)).SameGenus
        ((rankOne 3).orthogonalSum (rankOne 5)) := by
  intro h
  obtain ⟨f⟩ := h.nonempty_isometry_discriminantBilinearModule
  exact isEmpty_isometry_discriminantBilinearModule_rankOne_one_fifteen_three_five.false f

end TauCeti.IntegralLattice
