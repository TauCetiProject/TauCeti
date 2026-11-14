/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
public import TauCeti.NumberTheory.IntegralLattice.Genus
import Mathlib.Tactic.FinCases
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum.AffineLagrangian
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.OddPrime
import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The genus and the discriminant form

By `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_discriminantBilinear`, at every odd
prime `p` the integral localization `L_p` of a nondegenerate lattice `L` is determined up to
isometry by `rank L`, the square class of `det L` in `ℤ_p`, and the `p`-primary discriminant
bilinear module `(A_L)_p`. When two nondegenerate lattices `L` and `M` have equal real signature
and isometric discriminant bilinear forms `b_L ≅ b_M`, their ranks and signed determinants already
coincide, so every odd-prime local equivalence holds automatically. The genus relation
`TauCeti.IntegralLattice.SameGenus` therefore reduces to three invariants: real signature, the
dyadic localization `L_2`, and the discriminant form (`b_L` in general, or `q_L` for even lattices).

When `L` has **odd discriminant** (`Odd L.discriminant`, equivalently `det L ∈ ℤ_2ˣ`), the dyadic
localization `L_2` is unimodular and is itself determined by the remaining invariants:

* For even lattices of odd discriminant, `L_2` is an even unimodular `ℤ_2`-form, classified by rank
  and `2`-adic determinant square class
  (`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isEven`).
  Moreover, at odd order `q_L` and `b_L` carry the same isometry information, giving Nikulin's
  Corollary 1.9.4 unconditionally for odd discriminant.
* For general (possibly odd) lattices of odd discriminant, `L` admits an integral characteristic
  vector `w` (`TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`). In the
  canonical even sublattice `N = L.evenSublattice` of index `[L : N] ∈ {1, 2}`, the subgroup
  `L / N` is a bilinear Lagrangian inside the `2`-primary component `(A_N)_2` of order `[L : N]²`,
  and `q_N` is constant with value `B(w, w) / 8` on the coset `(w / 2 + N) + L / N`. Evaluating the
  `2`-primary Gauss sum and combining with Milgram's theorem on `N` identifies `B(w, w) mod 8` with
  `(sigPos L - sigNeg L)` minus the odd-prime Gauss signs of `A_N`. Since `[L : N] ≤ 2` is a unit at
  every odd prime `p`, `(A_N)_p` is isometric to `(A_L)_p`; thus `signature` and `b_L` determine
  the characteristic norm modulo `8`, hence `L_2`, proving Nikulin's Corollary 1.16.3 for all
  nondegenerate lattices of odd discriminant (generalizing
  `TauCeti.IntegralLattice.sameGenus_iff_of_isUnimodular`).

The file concludes with two concrete rank-two test pairs of odd discriminant:

* `⟨1⟩ ⊕ ⟨5⟩` and `!![2, 1; 1, 3]` are positive definite odd binary lattices of determinant `5`
  that are **not** in the same genus: their discriminant pairings on `ℤ/5` represent `1/5` and
  `3/5 mod ℤ`, and `3` is a quadratic nonresidue modulo `5`.
* `⟨1⟩ ⊕ ⟨39⟩` and `⟨3⟩ ⊕ ⟨13⟩` are positive definite odd binary lattices of determinant `39`
  that **lie in the same genus** (`1/3 + 9/13 = 40/39 ≡ 1/39 mod ℤ`), yet are **not isometric**
  because only the first represents `1`.

## Main results

* `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinear`
  and
  `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadratic`
  — reduction of `SameGenus` for nondegenerate lattices to real signature, `L_2 ≃ M_2`, and isometry
  of the discriminant form.
* `TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`: every lattice of odd
  discriminant admits an integral characteristic vector.
* `TauCeti.IntegralLattice.sameGenus_iff_of_isEven_of_odd_discriminant` and
  `TauCeti.IntegralLattice.sameGenus_iff_discriminantBilinear_of_isEven_of_odd_discriminant`:
  Nikulin's Corollary 1.9.4 for even lattices of odd discriminant.
* `TauCeti.IntegralLattice.sameGenus_iff_of_odd_discriminant`: Nikulin's Corollary 1.16.3 for
  nondegenerate lattices of odd discriminant (`SameGenus` iff equal signature, matching evenness,
  and isometric discriminant bilinear forms).
* `TauCeti.IntegralLattice.not_sameGenus_rankOne_one_five_binaryDeterminantFive`: `⟨1⟩ ⊕ ⟨5⟩` and
  `!![2, 1; 1, 3]` lie in distinct genera.
* `TauCeti.IntegralLattice.sameGenus_rankOne_one_thirtyNine_three_thirteen` and
  `TauCeti.IntegralLattice.isEmpty_isometry_rankOne_one_thirtyNine_three_thirteen`: `⟨1⟩ ⊕ ⟨39⟩`
  and `⟨3⟩ ⊕ ⟨13⟩` lie in one genus but are not isometric.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Theorem 1.3.3
  and Corollaries 1.9.4 and 1.16.3.
* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291--293.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module AddCommGroup
open scoped Real TensorProduct

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
theorem sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinear
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
  · refine (L.localIntegralForm_equivalent_iff_discriminantBilinear M hp2).mpr
      ⟨L.finrank_eq_of_signature_eq hsig, ?_, ⟨f.restrictPrimaryComponent p⟩⟩
    rw [hdet]
    exact IsSquare.mul_self _

/-- **Genus characterization for even lattices up to dyadic equivalence.** Two even nondegenerate
integral lattices lie in one genus if and only if they have the same real signature, isometric
dyadic localizations `L_2` and `M_2`, and isometric discriminant quadratic modules. -/
theorem sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadratic
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
  exact (L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinear M).mpr
    ⟨hsig, h2, ⟨f.toFiniteBilinearModule⟩⟩

/-! ### Characteristic vectors and `2`-primary Gauss sums at odd discriminant -/

/-- The discriminant of `L` is odd if and only if its signed determinant is a unit in `ℤ_2`. -/
theorem odd_discriminant_iff_isUnit_determinant_padicInt_two (L : IntegralLattice V) :
    Odd L.discriminant ↔ IsUnit (L.determinant : ℤ_[2]) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [PadicInt.isUnit_intCast_iff, discriminant_def, ← Nat.not_even_iff_odd, even_iff_two_dvd]
  refine not_congr ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨k.natAbs, ?_⟩⟩
  · rcases Int.natAbs_eq L.determinant with h | h
    · exact ⟨k, by rw [h, hk]; push_cast; ring⟩
    · exact ⟨-k, by rw [h, hk]; push_cast; ring⟩
  · rw [hk, Int.natAbs_mul]
    rfl

/-- **Every lattice of odd discriminant has a characteristic vector.** Its dyadic localization is
unimodular, so it admits a `2`-adic characteristic vector whose coordinate approximation modulo `2`
is an integral characteristic vector of `L`. -/
theorem exists_isCharacteristicVector_of_odd_discriminant (L : IntegralLattice V)
    (hodd : Odd L.discriminant) : ∃ w : L, L.IsCharacteristicVector w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet2 : IsUnit (L.determinant : ℤ_[2]) :=
    L.odd_discriminant_iff_isUnit_determinant_padicInt_two.mp hodd
  have := L.isPerfPair_localIntegralForm_of_isUnit_determinant 2 hdet2
  obtain ⟨w₂, hw₂⟩ :=
    (L.isSymm_localIntegralForm 2).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  let b := Module.finBasis ℤ L
  let c := (b.baseChange ℤ_[2]).repr w₂
  have hdvd (i) : (2 : ℤ_[2]) ∣ (((c i).appr 1 : ℤ) : ℤ_[2]) - c i := by
    have hspec : (2 : ℤ_[2]) ^ 1 ∣ c i - ((c i).appr 1 : ℤ) :=
      Ideal.mem_span_singleton.mp (PadicInt.appr_spec 1 (c i))
    rw [pow_one] at hspec
    simpa only [neg_sub] using hspec.neg_right
  choose d hd using hdvd
  let w : L := ∑ i, ((c i).appr 1 : ℤ) • b i
  let v₂ : L.LocalCarrier 2 := ∑ i, d i • b.baseChange ℤ_[2] i
  have hdecomp : ((1 : ℤ_[2]) ⊗ₜ[ℤ] w : L.LocalCarrier 2) = w₂ + (2 : ℤ_[2]) • v₂ := by
    have hw_tmul : ((1 : ℤ_[2]) ⊗ₜ[ℤ] w : L.LocalCarrier 2) =
        ∑ i, (((c i).appr 1 : ℤ) : ℤ_[2]) • b.baseChange ℤ_[2] i := by
      simp only [w, TensorProduct.tmul_sum, Basis.baseChange_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul, zsmul_one]
      symm
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hw_tmul, ← (b.baseChange ℤ_[2]).sum_repr w₂]
    simp only [c, v₂, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [sub_eq_iff_eq_add'.mp (hd i), add_smul, mul_smul]
  have hw_loc : (L.localIntegralForm 2).IsCharacteristic ((1 : ℤ_[2]) ⊗ₜ[ℤ] w) := by
    rw [hdecomp]
    exact hw₂.add_two_smul v₂
  refine ⟨w, (L.isCharacteristicVector_iff_isCharacteristic w).mpr ?_⟩
  rw [LinearMap.BilinForm.isCharacteristic_iff]
  intro x
  have hx2 := LinearMap.BilinForm.isCharacteristic_iff.mp hw_loc ((1 : ℤ_[2]) ⊗ₜ[ℤ] x)
  simp only [localIntegralForm_tmul, one_mul] at hx2
  have h2 : (2 : ℤ_[2]) ∣ ((L.integralForm w x : ℤ) : ℤ_[2]) - (L.integralForm x x : ℤ) ↔
      (2 : ℤ) ∣ L.integralForm w x - L.integralForm x x := by
    simpa only [pow_one, Int.cast_sub, Nat.cast_ofNat] using
      PadicInt.pow_p_dvd_int_iff (p := 2) 1 (L.integralForm w x - L.integralForm x x)
  exact h2.mp hx2

/-- Half of a characteristic vector lies in the dual carrier of `L.evenSublattice`. -/
private theorem half_characteristic_mem_evenSublattice_dual (L : IntegralLattice V) {w : L}
    (hw : L.IsCharacteristicVector w) :
    (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  let yL : L := ⟨y, L.evenSublattice_carrier_le hy⟩
  have he : Even (L.integralNorm yL) := (L.mem_evenSublattice_carrier_iff yL).mp hy
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp
    (((L.isCharacteristicVector_iff w).mp hw yL).trans
      (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp he)))
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← L.integralForm_cast w yL, hk]
  push_cast
  ring

/-- The Gauss-sum invariant of a nondegenerate finite quadratic module is the sum of the Gauss-sum
invariants of its `p`-primary components over any finite set of primes containing all prime factors
of its order. -/
private theorem gaussSign_eq_sum_primaryComponent (A : FiniteQuadraticModule)
    (hA : A.IsNondegenerate) (S : Finset ℕ) (hS_prime : ∀ p ∈ S, p.Prime)
    (hS_factors : (Nat.card A).primeFactors ⊆ S) :
    A.gaussSign = ∑ p ∈ S, (A.restrict (primaryComponent A p)).gaussSign := by
  classical
  let B : (Nat.card A).primeFactors → FiniteQuadraticModule :=
    fun p ↦ A.restrict (primaryComponent A p.1)
  let e : FiniteQuadraticModule.Isometry (FiniteQuadraticModule.pi B) A.primaryComponents :=
    { toLinearEquiv :=
        { toFun := id
          invFun := id
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      map_app' := fun x ↦ by
        let x' : A.primaryComponents.carrier := x
        -- Both quadratic maps evaluate to `∑ p, A.quadratic (x p)`.
        change A.primaryComponents.quadratic x' = (FiniteQuadraticModule.pi B).quadratic x
        rw [A.primaryComponents_quadratic x', FiniteQuadraticModule.pi_quadratic B x]
        rfl }
  have hpi : A.gaussSign = ∑ p : (Nat.card A).primeFactors, (B p).gaussSign := by
    rw [← A.primaryDecomposition.gaussSign_eq, ← e.gaussSign_eq,
      FiniteQuadraticModule.gaussSign_pi B fun p ↦
        A.isNondegenerate_restrict_primaryComponent hA (Nat.prime_of_mem_primeFactors p.2)]
  rw [hpi, Finset.univ_eq_attach,
    Finset.sum_attach (Nat.card A).primeFactors
      (fun p ↦ (A.restrict (primaryComponent A p)).gaussSign)]
  refine Finset.sum_subset hS_factors fun p hpS hnp ↦ ?_
  have hp : p.Prime := hS_prime p hpS
  have hfact : (Nat.card A).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦
      hnp (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
  have hcard : Nat.card (A.restrict (primaryComponent A p)) = 1 := by
    -- The carrier of `A.restrict H` is `H`.
    change Nat.card (primaryComponent A p) = 1
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ hp, hfact, pow_zero]
  have : Subsingleton (A.restrict (primaryComponent A p)) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  exact FiniteQuadraticModule.gaussSign_eq_zero_of_subsingleton _

private theorem index_evenSublattice_toIntermediateCarrier (L : IntegralLattice V) :
    IntermediateCarrier.index
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) =
    L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup := by
  rw [IntermediateCarrier.index_def, coe_toIntermediateCarrier]

/-- The class of `(1 / 2) • w` in `L.evenSublattice.DiscriminantGroup` has order dividing `4`, hence
lies in the `2`-primary component. -/
private theorem half_characteristic_class_mem_primaryComponent_two (L : IntegralLattice V)
    [L.IsNondegenerate] {w : L} (hw : L.IsCharacteristicVector w) :
    (Submodule.Quotient.mk
      (⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_evenSublattice_dual L hw⟩ :
        L.evenSublattice.dualCarrier) :
        L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) ∈
      primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2 := by
  let u_w : L.evenSublattice.dualCarrier :=
    ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_evenSublattice_dual L hw⟩
  refine AddCommGroup.mem_primaryComponent.mpr ⟨2, ?_⟩
  -- Unfold `2 ^ 2` to `4` in the underlying `DiscriminantGroup`.
  change ((4 : ℕ) • Submodule.Quotient.mk u_w : L.evenSublattice.DiscriminantGroup) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    L.evenSublattice.mem_carrierInDual_iff]
  have hval : (((4 : ℕ) • u_w : L.evenSublattice.dualCarrier) : V) = (((2 : ℤ) • w : L) : V) := by
    simp only [SetLike.val_smul, u_w, Submodule.coe_smul_of_tower]
    rw [← Nat.cast_smul_eq_nsmul ℚ 4, smul_smul]
    norm_num
    rw [two_smul ℚ (w : V), two_zsmul]
  rw [hval, L.evenSublattice_carrier]
  exact Submodule.mem_map_of_mem (L.two_smul_mem_evenSubmodule w)

/-- The discriminant quadratic map of `L.evenSublattice` is constant on the `L / L.evenSublattice`
coset of `(1 / 2) • w`. -/
private theorem discriminantQuadraticMap_half_characteristic_add (L : IntegralLattice V)
    {w : L} (hw : L.IsCharacteristicVector w)
    (h : L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk
          ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_evenSublattice_dual L hw⟩ + h.1) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk
          ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_evenSublattice_dual L hw⟩) := by
  obtain ⟨x, hx⟩ := h
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hyL : (y : V) ∈ L.carrier := by
      have := (L.evenSublattice.mk_mem_discriminantSubgroup_iff
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) y).mp hx
      rwa [coe_toIntermediateCarrier] at this
    let y₀ : L := ⟨y, hyL⟩
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ((L.isCharacteristicVector_iff w).mp hw y₀)
    have hstep : L.form ((1 / 2 : ℚ) • (w : V) + y) ((1 / 2 : ℚ) • (w : V) + y) / 2 =
        L.form ((1 / 2 : ℚ) • (w : V)) ((1 / 2 : ℚ) • (w : V)) / 2 +
          ((L.integralForm w y₀ + k : ℤ) : ℚ) := by
      rw [← L.norm_apply, ← L.norm_apply, L.norm_add]
      simp only [L.norm_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
      have hwy : L.form w y = L.integralForm w y₀ := (L.integralForm_cast w y₀).symm
      have hyy : L.norm y = L.integralNorm y₀ := (L.integralNorm_cast y₀).symm
      have hkq : (L.integralNorm y₀ : ℚ) - L.integralForm w y₀ = 2 * k := by exact_mod_cast hk
      rw [hwy, hyy]
      push_cast
      linarith
    rw [← Submodule.Quotient.mk_add, discriminantQuadraticMap_mk, discriminantQuadraticMap_mk,
      L.evenSublattice_form]
    simp only [Submodule.coe_add]
    rw [hstep, AddCircle.coe_add_intCast]

/-- For a nondegenerate lattice `L` of odd discriminant and a characteristic vector `w`, the
`2`-primary component of the discriminant quadratic module of `L.evenSublattice` has Gauss-sum
invariant `(L.integralNorm w : ZMod 8)`. -/
private theorem gaussSign_primaryComponent_two_evenSublattice (L : IntegralLattice V)
    [L.IsNondegenerate] (hodd : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
      (primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).gaussSign =
      (L.integralNorm w : ZMod 8) := by
  let N := L.evenSublattice
  have hNe : N.IsEven := L.isEven_evenSublattice
  let A := N.discriminantQuadraticModule hNe
  let M₀ : N.IntermediateCarrier :=
    L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hI : IntermediateCarrier.IsIntegral M₀ :=
    L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hL_eq : hI.toIntegralLattice = L :=
    L.toIntegralLattice_toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
      hI
  have hpos : 0 < IntermediateCarrier.index M₀ := IntermediateCarrier.index_pos M₀
  have hle2 : IntermediateCarrier.index M₀ ≤ 2 :=
    (index_evenSublattice_toIntermediateCarrier L).trans_le L.relIndex_evenSublattice_le_two
  have hidx_cases : IntermediateCarrier.index M₀ = 1 ∨ IntermediateCarrier.index M₀ = 2 := by omega
  have hfact_L : L.discriminant.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦
      Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)
  have hcard_A2 : Nat.card (primaryComponent A 2) = IntermediateCarrier.index M₀ ^ 2 := by
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ Nat.prime_two]
    have hcardA : Nat.card A = L.discriminant * IntermediateCarrier.index M₀ ^ 2 := by
      -- The underlying carrier of `A` is `N.DiscriminantGroup`.
      change Nat.card N.DiscriminantGroup = L.discriminant * IntermediateCarrier.index M₀ ^ 2
      rw [N.natCard_discriminantGroup, ← hI.discriminant_mul_index_sq, hL_eq]
    rw [hcardA]
    rcases hidx_cases with h1 | h2
    · simp [h1, hfact_L]
    · rw [h2, Nat.factorization_mul hodd.pos.ne' (by decide), Finsupp.add_apply, hfact_L, zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
        smul_eq_mul, mul_one]
  let H : AddSubgroup A := N.discriminantSubgroup M₀
  have hcard_H : Nat.card H = IntermediateCarrier.index M₀ :=
    (IntermediateCarrier.index_eq_natCard_discriminantSubgroup M₀).symm
  have hH_le : H ≤ primaryComponent A 2 := fun x hx ↦ by
    have hkill : IntermediateCarrier.index M₀ • x = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (hcard_H ▸ H.addOrderOf_dvd_natCard hx)
    refine AddCommGroup.mem_primaryComponent.mpr ⟨1, ?_⟩
    rw [pow_one]
    rcases hidx_cases with h1 | h2
    · rw [h1, one_nsmul] at hkill
      simp [hkill]
    · rwa [h2] at hkill
  let A₂ := A.restrict (primaryComponent A 2)
  let H₂ : AddSubgroup A₂ := H.addSubgroupOf (primaryComponent A 2)
  let eH : H₂ ≃+ H :=
    { toFun := fun z ↦ ⟨z.1.1, z.2⟩
      invFun := fun y ↦ ⟨⟨y.1, hH_le y.2⟩, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have hcard_H2 : Nat.card H₂ = IntermediateCarrier.index M₀ :=
    (Nat.card_congr eH.toEquiv).trans hcard_H
  have hH2_iso : H₂ ≤ A₂.toFiniteBilinearModule.orthogonalComplement H₂ := fun x hx ↦ by
    rw [A₂.toFiniteBilinearModule.mem_orthogonalComplement_iff]
    exact fun y hy ↦ (N.discriminantBilinearModule_pairing x.1 y.1).trans
      ((IntermediateCarrier.isIntegral_iff_forall_discriminantPairing_eq_zero M₀).mp hI
        x.1 hx y.1 hy)
  have hH2_lag : A₂.toFiniteBilinearModule.IsLagrangian H₂ := by
    rw [A₂.toFiniteBilinearModule.isLagrangian_def]
    refine AddSubgroup.eq_of_le_of_card_ge hH2_iso ?_
    have hmul := FiniteBilinearModule.IsNondegenerate.card_mul_card_orthogonalComplement
      A₂.toFiniteBilinearModule
      (A.isNondegenerate_restrict_primaryComponent
        (N.isNondegenerate_discriminantQuadraticModule hNe) Nat.prime_two) H₂
    have hcard_A2' : Nat.card A₂.toFiniteBilinearModule = Nat.card H₂ * Nat.card H₂ := by
      -- The underlying carrier of `A₂` is `primaryComponent A 2`.
      change Nat.card (primaryComponent A 2) = Nat.card H₂ * Nat.card H₂
      rw [hcard_A2, hcard_H2, sq]
    rw [hcard_A2'] at hmul
    exact (Nat.mul_left_cancel (hcard_H2 ▸ hpos) hmul).le
  let u_w : N.dualCarrier :=
    ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_evenSublattice_dual L hw⟩
  let a₂ : A₂ :=
    ⟨Submodule.Quotient.mk u_w, half_characteristic_class_mem_primaryComponent_two L hw⟩
  have hqa : A₂.quadratic a₂ = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
    rw [FiniteQuadraticModule.restrict_quadratic, discriminantQuadraticModule_quadratic,
      discriminantQuadraticMap_mk, L.evenSublattice_form, ZMod.toRatAddCircle_intCast,
      L.integralNorm_cast, L.norm_apply]
    simp only [u_w, map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    ring
  have ha_const (h : H₂) : A₂.quadratic (a₂ + h) = A₂.quadratic a₂ :=
    discriminantQuadraticMap_half_characteristic_add L hw ⟨h.1.1, h.2⟩
  have hG := FiniteQuadraticModule.gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian
    a₂ hH2_lag ha_const
  refine FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq A₂ ?_
  have hcard_eq : (Nat.card H₂ : ℂ) = √(Nat.card A₂) := by
    have hsq : Nat.card A₂ = Nat.card H₂ ^ 2 := by
      -- The underlying carrier of `A₂` is `primaryComponent A 2`.
      change Nat.card (primaryComponent A 2) = Nat.card H₂ ^ 2
      rw [hcard_A2, hcard_H2]
    rw [hsq, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [hG, hqa, hcard_eq]

/-- **Generalized van der Blij identity at odd discriminant.** For a nondegenerate lattice `L` of
odd discriminant and a characteristic vector `w`, the norm of `w` modulo `8` equals the signature
difference of `L` minus the odd-prime Gauss-sum invariants of `L.evenSublattice`. -/
private theorem integralNorm_cast_zmod_eight_eq_of_odd_discriminant (L : IntegralLattice V)
    [L.IsNondegenerate] (hodd : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    (L.integralNorm w : ZMod 8) = ((L.sigPos : ZMod 8) - L.sigNeg) -
      ∑ p ∈ L.discriminant.primeFactors,
        ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
          (primaryComponent
            (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p)).gaussSign :=
  by
  classical
  let N := L.evenSublattice
  have hNe : N.IsEven := L.isEven_evenSublattice
  let A := N.discriminantQuadraticModule hNe
  let M₀ : N.IntermediateCarrier :=
    L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hI : IntermediateCarrier.IsIntegral M₀ :=
    L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hL_eq : hI.toIntegralLattice = L :=
    L.toIntegralLattice_toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
      hI
  have hle2 : IntermediateCarrier.index M₀ ≤ 2 :=
    (index_evenSublattice_toIntermediateCarrier L).trans_le L.relIndex_evenSublattice_le_two
  have hpos : 0 < IntermediateCarrier.index M₀ := IntermediateCarrier.index_pos M₀
  have hdisc_N : Nat.card A = L.discriminant * IntermediateCarrier.index M₀ ^ 2 := by
    -- The underlying carrier of `A` is `N.DiscriminantGroup`.
    change Nat.card N.DiscriminantGroup = L.discriminant * IntermediateCarrier.index M₀ ^ 2
    rw [N.natCard_discriminantGroup, ← hI.discriminant_mul_index_sq, hL_eq]
  have h2_notMem : 2 ∉ L.discriminant.primeFactors := fun hm ↦
    Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hm))
  have hsub : (Nat.card A).primeFactors ⊆ insert 2 L.discriminant.primeFactors := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    rw [hdisc_N] at hdvd
    rcases hp_prime.dvd_mul.mp hdvd with hdL | hdI
    · exact Finset.mem_insert_of_mem
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hdL, hodd.pos.ne'⟩)
    · have hdI' : p ∣ IntermediateCarrier.index M₀ := hp_prime.dvd_of_dvd_pow hdI
      have hp_le : p ≤ 2 := (Nat.le_of_dvd hpos hdI').trans hle2
      have hp2 : p = 2 := le_antisymm hp_le hp_prime.two_le
      simp [hp2]
  have hprime_S : ∀ p ∈ insert 2 L.discriminant.primeFactors, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors hp'
  have hsum := gaussSign_eq_sum_primaryComponent A
    (N.isNondegenerate_discriminantQuadraticModule hNe)
    (insert 2 L.discriminant.primeFactors) hprime_S hsub
  rw [Finset.sum_insert h2_notMem,
    gaussSign_primaryComponent_two_evenSublattice L hodd hw] at hsum
  have hmilgram : A.gaussSign = (L.sigPos : ZMod 8) - L.sigNeg := by
    have hm := N.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg hNe
    have hsig := L.evenSublattice_signature
    simp only [signature, Prod.mk.injEq] at hsig
    rwa [hsig.1, hsig.2.2] at hm
  rw [hmilgram] at hsum
  exact eq_sub_of_add_eq hsum.symm

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
  refine (L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantQuadratic M hL hM).mpr
    ⟨hsig, ?_, ⟨f⟩⟩
  refine (L.localIntegralForm_two_equivalent_iff_of_isEven M hL hM hL2 hM2).mpr
    ⟨L.finrank_eq_of_signature_eq hsig, ?_⟩
  rw [hdet]
  exact IsSquare.mul_self _

/-- For even nondegenerate lattices of odd discriminant, the discriminant bilinear module already
determines the genus together with the signature. -/
theorem sameGenus_iff_discriminantBilinear_of_isEven_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) (hodd : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  have hodd_card : Odd (Nat.card (L.discriminantQuadraticModule hL)) := by
    -- The carrier of `L.discriminantQuadraticModule hL` is `L.DiscriminantGroup`.
    change Odd (Nat.card L.DiscriminantGroup)
    rwa [L.natCard_discriminantGroup]
  rw [L.sameGenus_iff_of_isEven_of_odd_discriminant M hL hM hodd,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_card]
  rfl

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
  obtain ⟨w, hw⟩ := L.exists_isCharacteristicVector_of_odd_discriminant hodd
  obtain ⟨w', hw'⟩ := M.exists_isCharacteristicVector_of_odd_discriminant (hdisc ▸ hodd)
  refine (L.sameGenus_iff_localIntegralForm_two_equivalent_and_discriminantBilinear M).mpr
    ⟨hsig, ?_, ⟨f⟩⟩
  refine (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M hL2 hM2 hw hw').mpr
    ⟨L.finrank_eq_of_signature_eq hsig, heven, hdet ▸ IsSquare.mul_self _, ?_⟩
  -- Compare `(L.integralNorm w : ZMod 8)` and `(M.integralNorm w' : ZMod 8)` via `evenSublattice`.
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  rw [integralNorm_cast_zmod_eight_eq_of_odd_discriminant L hodd hw,
    integralNorm_cast_zmod_eight_eq_of_odd_discriminant M (hdisc ▸ hodd) hw']
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
  -- At every odd prime `p`, `[L : N_L] ≤ 2` is prime to `p`, so `(A_{N_L})_p ≅ (A_L)_p`.
  have hndvd_L : ¬p ∣ L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup :=
    fun hdvd ↦ by
      have hpos : 0 < L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup :=
        index_evenSublattice_toIntermediateCarrier L ▸ IntermediateCarrier.index_pos
          (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
      have hle := (Nat.le_of_dvd hpos hdvd).trans L.relIndex_evenSublattice_le_two
      exact hp_ne_two (le_antisymm hle hp_prime.two_le)
  have hndvd_M : ¬p ∣ M.evenSublattice.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup :=
    fun hdvd ↦ by
      have hpos : 0 < M.evenSublattice.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup :=
        index_evenSublattice_toIntermediateCarrier M ▸ IntermediateCarrier.index_pos
          (M.toIntermediateCarrier M.evenSublattice_form.symm M.evenSublattice_carrier_le)
      have hle := (Nat.le_of_dvd hpos hdvd).trans M.relIndex_evenSublattice_le_two
      exact hp_ne_two (le_antisymm hle hp_prime.two_le)
  let eL := primaryDiscriminantBilinearIsometry
    (L.evenSublattice.localInclusionIsometryEquiv L p L.evenSublattice_form
      L.evenSublattice_carrier_le hndvd_L)
  let eM := primaryDiscriminantBilinearIsometry
    (M.evenSublattice.localInclusionIsometryEquiv M p M.evenSublattice_form
      M.evenSublattice_carrier_le hndvd_M)
  have hodd_NL : Odd (Nat.card
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (primaryComponent
          (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p))) := by
    -- The carrier of the restricted module is `primaryComponent _ p`.
    change Odd (Nat.card (primaryComponent L.evenSublattice.DiscriminantGroup p))
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ hp_prime]
    exact hp_odd.pow
  exact (FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd hodd_NL
    (eL.trans ((f.restrictPrimaryComponent p).trans eM.symm))).gaussSign_eq

/-! ### Concrete rank-two genus witnesses of odd discriminant -/

private def binaryFiveMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 3]

private theorem binaryFiveMatrix_isSymm : binaryFiveMatrix.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The positive definite odd binary integral lattice with Gram matrix `!![2, 1; 1, 3]` and
determinant `5`. -/
noncomputable def binaryDeterminantFive : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) binaryFiveMatrix binaryFiveMatrix_isSymm

/-- The signed determinant of `binaryDeterminantFive` is `5`. -/
@[simp]
theorem binaryDeterminantFive_determinant : binaryDeterminantFive.determinant = 5 := by
  rw [binaryDeterminantFive, determinant_ofGramMatrix]
  norm_num [binaryFiveMatrix, Matrix.det_fin_two]

/-- The lattice `binaryDeterminantFive` is nondegenerate. -/
instance : binaryDeterminantFive.IsNondegenerate :=
  ⟨binaryDeterminantFive.determinant_ne_zero_iff.mp (by simp)⟩

/-- The lattice `binaryDeterminantFive` is odd: its second basis vector has norm `3`. -/
theorem binaryDeterminantFive_not_isEven : ¬binaryDeterminantFive.IsEven := by
  intro he
  dsimp only [binaryDeterminantFive] at he
  let b := ofGramMatrix.basis (Pi.basisFun ℚ (Fin 2)) binaryFiveMatrix binaryFiveMatrix_isSymm
  have h1 := ((ofGramMatrix (Pi.basisFun ℚ (Fin 2)) binaryFiveMatrix
    binaryFiveMatrix_isSymm).isEven_iff_basis b).mp he 1
  rw [integralNorm_apply, ← gramMatrix_apply, gramMatrix_ofGramMatrix] at h1
  exact (by decide : ¬Even (binaryFiveMatrix 1 1)) h1

/-- The lattice `binaryDeterminantFive` is positive definite. -/
theorem binaryDeterminantFive_isPosDef : binaryDeterminantFive.IsPosDef := by
  rw [binaryDeterminantFive.isPosDef_iff]
  intro x hx
  dsimp only [binaryDeterminantFive]
  rw [form_ofGramMatrix_basisFun_apply]
  simp only [Fin.sum_univ_two, binaryFiveMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_ofNat, Int.cast_one]
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra! h
    apply hx
    ext i
    fin_cases i <;> simp [h]
  rcases hx' with h | h
  · have := sq_pos_iff.mpr h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
  · have := sq_pos_iff.mpr h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]

/-- **`⟨1⟩ ⊕ ⟨5⟩` and `!![2, 1; 1, 3]` do not lie in the same genus.** Both are positive definite
odd binary lattices of determinant `5`, yet the discriminant pairing of `⟨1⟩ ⊕ ⟨5⟩` takes values
`k² / 5 mod ℤ` while `!![2, 1; 1, 3]` has a dual vector `(3/5, -1/5)` of self-pairing
`3/5 mod ℤ`. -/
theorem not_sameGenus_rankOne_one_five_binaryDeterminantFive :
    ¬((rankOne 1).orthogonalSum (rankOne 5)).SameGenus binaryDeterminantFive := by
  have : NeZero (5 : ℤ) := ⟨by decide⟩
  intro h
  obtain ⟨f⟩ := h.symm.nonempty_isometry_discriminantBilinearModule
  let v_vec : Fin 2 → ℚ := ![3 / 5, -1 / 5]
  have hv_dual : v_vec ∈ binaryDeterminantFive.dualCarrier := by
    rw [binaryDeterminantFive, mem_ofGramMatrix_basisFun_dualCarrier_iff]
    intro i
    fin_cases i
    · exact ⟨1, by simp [v_vec, binaryFiveMatrix, Fin.sum_univ_two]; norm_num⟩
    · exact ⟨0, by simp [v_vec, binaryFiveMatrix, Fin.sum_univ_two]; norm_num⟩
  let c : binaryDeterminantFive.discriminantBilinearModule :=
    Submodule.Quotient.mk ⟨v_vec, hv_dual⟩
  have hpair_c : binaryDeterminantFive.discriminantBilinearModule.pairing c c =
      ((3 / 5 : ℚ) : AddCircle (1 : ℚ)) := by
    rw [discriminantBilinearModule_pairing, discriminantPairing_mk]
    dsimp only [binaryDeterminantFive]
    rw [form_ofGramMatrix_basisFun_apply]
    congr 1
    simp [v_vec, binaryFiveMatrix, Fin.sum_univ_two]
    norm_num
  -- Decompose `f c` in `A_{⟨1⟩ ⊕ ⟨5⟩} ≃ A_{⟨1⟩} × A_{⟨5⟩}`; `A_{⟨1⟩}` is trivial.
  let e := (rankOne 1).discriminantBilinearIsometryOrthogonalSum (rankOne 5)
  have hpair_img := (e.map_pairing (f c) (f c)).trans (f.map_pairing c c)
  rw [hpair_c, FiniteBilinearModule.prod_pairing] at hpair_img
  have : Subsingleton (rankOne 1).discriminantBilinearModule := by
    -- The carrier of `discriminantBilinearModule` is `DiscriminantGroup`.
    change Subsingleton (rankOne 1).DiscriminantGroup
    exact ((rankOne 1).isUnimodular_iff_subsingleton_discriminantGroup).mp
      ((isUnimodular_rankOne_iff 1).mpr isUnit_one)
  have hfst : (rankOne 1).discriminantBilinearModule.pairing (e (f c)).1 (e (f c)).1 = 0 := by
    rw [Subsingleton.elim (e (f c)).1 0, FiniteBilinearModule.pairing_zero_left]
  let c₅ : (rankOne 5).DiscriminantGroup := (e (f c)).2
  have hc5_pair : (rankOne 5).discriminantBilinearModule.pairing (e (f c)).2 (e (f c)).2 =
      (rankOne 5).discriminantPairing c₅ c₅ :=
    (rankOne 5).discriminantBilinearModule_pairing c₅ c₅
  rw [hfst, zero_add, hc5_pair] at hpair_img
  -- Write `c₅` as `k • rankOneClass 5` with `k < 5`.
  obtain ⟨k, hk_lt, hk_eq⟩ : ∃ k : ℕ, k < 5 ∧ c₅ = (k : ℤ) • rankOneClass 5 := by
    refine ⟨(rankOneDiscriminantEquiv 5 c₅).val, ZMod.val_lt _, ?_⟩
    apply (rankOneDiscriminantEquiv 5).injective
    rw [rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast]
    exact (ZMod.natCast_zmod_val _).symm
  rw [hk_eq, discriminantPairing_zsmul_rankOneClass, ← sub_eq_zero, ← AddCircle.coe_sub,
    AddCircle.coe_eq_zero_iff] at hpair_img
  obtain ⟨m, hm⟩ := hpair_img
  rw [zsmul_one] at hm
  have hmod : (k : ℤ) * k - 3 = 5 * m := by
    have hq : ((k : ℤ) * k - 3 : ℚ) = (5 * m : ℤ) := by
      push_cast at hm ⊢
      linarith
    exact_mod_cast hq
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
    rfl | rfl | rfl | rfl | rfl <;> omega

/-- The additive homomorphism `ZMod 39 →+ A_{⟨3⟩} × A_{⟨13⟩}` sending `k` to
`(k • rankOneClass 3, (3 * k) • rankOneClass 13)`. -/
private noncomputable def zmodThirtyNineHomProd :
    ZMod 39 →+ (rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup :=
  haveI : NeZero (3 : ℤ) := ⟨by decide⟩
  haveI : NeZero (13 : ℤ) := ⟨by decide⟩
  ((rankOneDiscriminantEquiv 3).symm.toAddMonoidHom.comp
      (ZMod.castHom (by decide : 3 ∣ 39) (ZMod 3)).toAddMonoidHom).prod
    ((rankOneDiscriminantEquiv 13).symm.toAddMonoidHom.comp
      ((3 : ℕ) • (ZMod.castHom (by decide : 13 ∣ 39) (ZMod 13)).toAddMonoidHom))

private theorem zmodThirtyNineHomProd_intCast (k : ℤ) :
    zmodThirtyNineHomProd (k : ZMod 39) =
      (haveI : NeZero (3 : ℤ) := ⟨by decide⟩
       haveI : NeZero (13 : ℤ) := ⟨by decide⟩
       (k • rankOneClass 3, (3 * k) • rankOneClass 13)) := by
  have : NeZero (3 : ℤ) := ⟨by decide⟩
  have : NeZero (13 : ℤ) := ⟨by decide⟩
  ext
  · apply (rankOneDiscriminantEquiv 3).injective
    -- Unfold `zmodThirtyNineHomProd` on the first factor.
    change rankOneDiscriminantEquiv 3
        ((rankOneDiscriminantEquiv 3).symm
          (ZMod.castHom (by decide : 3 ∣ 39) (ZMod 3) (k : ZMod 39))) = _
    rw [(rankOneDiscriminantEquiv 3).apply_symm_apply, map_intCast,
      rankOneDiscriminantEquiv_zsmul_rankOneClass]
  · apply (rankOneDiscriminantEquiv 13).injective
    -- Unfold `zmodThirtyNineHomProd` on the second factor.
    change rankOneDiscriminantEquiv 13
        ((rankOneDiscriminantEquiv 13).symm
          ((3 : ℕ) • ZMod.castHom (by decide : 13 ∣ 39) (ZMod 13) (k : ZMod 39))) = _
    rw [(rankOneDiscriminantEquiv 13).apply_symm_apply, map_intCast,
      rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_mul, nsmul_eq_mul, Nat.cast_ofNat]
    rfl

/-- The additive isomorphism `ZMod 39 ≃+ A_{⟨3⟩} × A_{⟨13⟩}` sending `1` to
`(rankOneClass 3, 3 • rankOneClass 13)`. -/
private noncomputable def zmodThirtyNineEquivProd :
    ZMod 39 ≃+ (rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup := by
  haveI : NeZero (3 : ℤ) := ⟨by decide⟩
  haveI : NeZero (13 : ℤ) := ⟨by decide⟩
  refine AddEquiv.ofBijective zmodThirtyNineHomProd
    ((Nat.bijective_iff_injective_and_card zmodThirtyNineHomProd).mpr ⟨?_, ?_⟩)
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hval : z = ((z.val : ℤ) : ZMod 39) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hval, zmodThirtyNineHomProd_intCast] at hz
    have h3 : 3 ∣ z.val := by
      have := congrArg (rankOneDiscriminantEquiv 3) (congrArg Prod.fst hz)
      simp only [Prod.fst_zero, rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast,
        map_zero] at this
      exact (ZMod.natCast_eq_zero_iff z.val 3).mp this
    have h13 : 13 ∣ z.val := by
      have := congrArg (rankOneDiscriminantEquiv 13) (congrArg Prod.snd hz)
      simp only [Prod.snd_zero, rankOneDiscriminantEquiv_zsmul_rankOneClass, map_zero] at this
      have hdvd : (13 : ℤ) ∣ 3 * (z.val : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 13).mp this
      exact Int.ofNat_dvd.mp ((by decide : IsCoprime (13 : ℤ) 3).dvd_of_dvd_mul_left hdvd)
    have h39 : 39 ∣ z.val :=
      by simpa using (by decide : Nat.Coprime 3 13).mul_dvd_of_dvd_of_dvd h3 h13
    have hlt := z.val_lt
    exact (ZMod.val_eq_zero z).mp (by omega)
  · rw [Nat.card_zmod, Nat.card_prod, natCard_rankOne_discriminantGroup,
      natCard_rankOne_discriminantGroup]
    norm_num

private theorem zmodThirtyNineEquivProd_intCast (k : ℤ) :
    zmodThirtyNineEquivProd (k : ZMod 39) =
      (haveI : NeZero (3 : ℤ) := ⟨by decide⟩
       haveI : NeZero (13 : ℤ) := ⟨by decide⟩
       (k • rankOneClass 3, (3 * k) • rankOneClass 13)) :=
  zmodThirtyNineHomProd_intCast k

/-- An explicit bilinear isometry between the discriminant forms of `⟨1⟩ ⊕ ⟨39⟩` and
`⟨3⟩ ⊕ ⟨13⟩`, sending the generator of `ℤ/39` to `(1, 3) ∈ ℤ/3 × ℤ/13` via
`1/3 + 9/13 = 40/39 ≡ 1/39 (mod 1)`. -/
private noncomputable def discriminantIsometry_one_thirtyNine_three_thirteen :
    FiniteBilinearModule.Isometry
      ((rankOne 1).orthogonalSum (rankOne 39)).discriminantBilinearModule
      ((rankOne 3).orthogonalSum (rankOne 13)).discriminantBilinearModule := by
  haveI : NeZero (3 : ℤ) := ⟨by decide⟩
  haveI : NeZero (13 : ℤ) := ⟨by decide⟩
  haveI : NeZero (39 : ℤ) := ⟨by decide⟩
  haveI : Subsingleton (rankOne 1).discriminantBilinearModule := by
    -- The carrier of `discriminantBilinearModule` is `DiscriminantGroup`.
    change Subsingleton (rankOne 1).DiscriminantGroup
    exact ((rankOne 1).isUnimodular_iff_subsingleton_discriminantGroup).mp
      ((isUnimodular_rankOne_iff 1).mpr isUnit_one)
  let eL := (rankOne 1).discriminantBilinearIsometryOrthogonalSum (rankOne 39)
  let eM := (rankOne 3).discriminantBilinearIsometryOrthogonalSum (rankOne 13)
  let β : ((rankOne 1).discriminantBilinearModule.prod (rankOne 39).discriminantBilinearModule) ≃+
      ((rankOne 3).discriminantBilinearModule.prod (rankOne 13).discriminantBilinearModule) :=
    { toFun := fun p ↦ zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 p.2)
      invFun := fun q ↦ (0, (rankOneDiscriminantEquiv 39).symm (zmodThirtyNineEquivProd.symm q))
      left_inv := fun p ↦ Prod.ext (Subsingleton.elim _ _) (by
        let p₂ : (rankOne 39).DiscriminantGroup := p.2
        -- Both sides live in `(rankOne 39).DiscriminantGroup`.
        change (rankOneDiscriminantEquiv 39).symm
          (zmodThirtyNineEquivProd.symm (zmodThirtyNineEquivProd
            (rankOneDiscriminantEquiv 39 p₂))) = p₂
        rw [zmodThirtyNineEquivProd.symm_apply_apply,
          (rankOneDiscriminantEquiv 39).symm_apply_apply])
      right_inv := fun q ↦ by
        let q' : (rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup := q
        -- Both sides live in `(rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup`.
        change zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39
          ((rankOneDiscriminantEquiv 39).symm (zmodThirtyNineEquivProd.symm q'))) = q'
        rw [(rankOneDiscriminantEquiv 39).apply_symm_apply,
          zmodThirtyNineEquivProd.apply_symm_apply]
      map_add' := fun p q ↦ by
        let p₂ : (rankOne 39).DiscriminantGroup := p.2
        let q₂ : (rankOne 39).DiscriminantGroup := q.2
        -- Addition on `prod` is componentwise addition on the discriminant groups.
        change zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 (p₂ + q₂)) =
          zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 p₂) +
            zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 q₂)
        rw [map_add, map_add] }
  let mid : FiniteBilinearModule.Isometry
      ((rankOne 1).discriminantBilinearModule.prod (rankOne 39).discriminantBilinearModule)
      ((rankOne 3).discriminantBilinearModule.prod (rankOne 13).discriminantBilinearModule) :=
    { toAddEquiv := β
      map_pairing' := fun x y ↦ by
        let x₂ : (rankOne 39).DiscriminantGroup := x.2
        let y₂ : (rankOne 39).DiscriminantGroup := y.2
        let kx : ℤ := (rankOneDiscriminantEquiv 39 x₂).val
        let ky : ℤ := (rankOneDiscriminantEquiv 39 y₂).val
        have hx2 : x₂ = kx • rankOneClass 39 := by
          apply (rankOneDiscriminantEquiv 39).injective
          rw [rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast]
          exact (ZMod.natCast_zmod_val _).symm
        have hy2 : y₂ = ky • rankOneClass 39 := by
          apply (rankOneDiscriminantEquiv 39).injective
          rw [rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast]
          exact (ZMod.natCast_zmod_val _).symm
        have hβx : (β x : (rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup) =
            (kx • rankOneClass 3, (3 * kx) • rankOneClass 13) := by
          -- Unfold `β x` to `zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 x₂)`.
          change zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 x₂) = _
          rw [hx2, rankOneDiscriminantEquiv_zsmul_rankOneClass, zmodThirtyNineEquivProd_intCast]
        have hβy : (β y : (rankOne 3).DiscriminantGroup × (rankOne 13).DiscriminantGroup) =
            (ky • rankOneClass 3, (3 * ky) • rankOneClass 13) := by
          -- Unfold `β y` to `zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 y₂)`.
          change zmodThirtyNineEquivProd (rankOneDiscriminantEquiv 39 y₂) = _
          rw [hy2, rankOneDiscriminantEquiv_zsmul_rankOneClass, zmodThirtyNineEquivProd_intCast]
        have hgoal :
            ((rankOne 3).discriminantBilinearModule.prod
                (rankOne 13).discriminantBilinearModule).pairing (β x) (β y) =
            ((rankOne 1).discriminantBilinearModule.prod
                (rankOne 39).discriminantBilinearModule).pairing x y := by
          rw [FiniteBilinearModule.prod_pairing, FiniteBilinearModule.prod_pairing,
            Subsingleton.elim x.1 0, FiniteBilinearModule.pairing_zero_left, zero_add,
            (rankOne 3).discriminantBilinearModule_pairing (β x).1 (β y).1,
            (rankOne 13).discriminantBilinearModule_pairing (β x).2 (β y).2,
            (rankOne 39).discriminantBilinearModule_pairing x₂ y₂,
            congrArg Prod.fst hβx, congrArg Prod.fst hβy,
            congrArg Prod.snd hβx, congrArg Prod.snd hβy, hx2, hy2,
            discriminantPairing_zsmul_rankOneClass, discriminantPairing_zsmul_rankOneClass,
            discriminantPairing_zsmul_rankOneClass, ← AddCircle.coe_add, ← sub_eq_zero,
            ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
          refine ⟨kx * ky, ?_⟩
          rw [zsmul_one]
          push_cast
          ring
        exact hgoal }
  exact eL.trans (mid.trans eM.symm)

/-- **`⟨1⟩ ⊕ ⟨39⟩` and `⟨3⟩ ⊕ ⟨13⟩` lie in the same genus.** Both are positive definite odd
binary lattices of odd discriminant `39` with isometric discriminant bilinear modules, so
`sameGenus_iff_of_odd_discriminant` applies directly. -/
theorem sameGenus_rankOne_one_thirtyNine_three_thirteen :
    ((rankOne 1).orthogonalSum (rankOne 39)).SameGenus
      ((rankOne 3).orthogonalSum (rankOne 13)) := by
  have hodd : Odd ((rankOne 1).orthogonalSum (rankOne 39)).discriminant := by
    rw [discriminant_orthogonalSum, rankOne_discriminant, rankOne_discriminant]
    decide
  refine (((rankOne 1).orthogonalSum (rankOne 39)).sameGenus_iff_of_odd_discriminant
    ((rankOne 3).orthogonalSum (rankOne 13)) hodd).mpr ⟨?_, ?_,
      ⟨discriminantIsometry_one_thirtyNine_three_thirteen⟩⟩
  · rw [signature_orthogonalSum, signature_orthogonalSum]
    have h1 := rankOne_signature_of_pos (a := 1) (by norm_num)
    have h39 := rankOne_signature_of_pos (a := 39) (by norm_num)
    have h3 := rankOne_signature_of_pos (a := 3) (by norm_num)
    have h13 := rankOne_signature_of_pos (a := 13) (by norm_num)
    simp only [signature, Prod.mk.injEq] at h1 h39 h3 h13 ⊢
    omega
  · rw [isEven_orthogonalSum_iff, isEven_orthogonalSum_iff, isEven_rankOne_iff,
      isEven_rankOne_iff, isEven_rankOne_iff, isEven_rankOne_iff]
    decide

/-- **`⟨1⟩ ⊕ ⟨39⟩` and `⟨3⟩ ⊕ ⟨13⟩` are not isometric**, even though they lie in the same genus:
`(1, 0)` has norm `1` in `⟨1⟩ ⊕ ⟨39⟩`, whereas every vector in `⟨3⟩ ⊕ ⟨13⟩` has norm
`3x² + 13y²`. -/
theorem isEmpty_isometry_rankOne_one_thirtyNine_three_thirteen :
    IsEmpty (Isometry ((rankOne 1).orthogonalSum (rankOne 39))
      ((rankOne 3).orthogonalSum (rankOne 13))) := by
  refine ⟨fun e ↦ ?_⟩
  let u₁ : rankOne 1 := ⟨1, (mem_rankOne_carrier_iff 1 1).mpr ⟨1, by norm_num⟩⟩
  let v := orthogonalSumInl (rankOne 1) (rankOne 39) u₁
  have hv_norm : ((rankOne 1).orthogonalSum (rankOne 39)).integralNorm v = 1 := by
    rw [integralNorm_orthogonalSum, orthogonalSumFst_inl, orthogonalSumSnd_inl,
      integralNorm_zero, add_zero, integralNorm_rankOne_eq u₁ (k := 1) rfl]
    norm_num
  have himg_norm : ((rankOne 3).orthogonalSum (rankOne 13)).integralNorm (e.carrierEquiv v) = 1 :=
    by rw [integralNorm_apply, e.carrierEquiv_map_integralForm, ← integralNorm_apply, hv_norm]
  rw [integralNorm_orthogonalSum] at himg_norm
  obtain ⟨x, hx⟩ := (mem_rankOne_carrier_iff 3 _).mp
    (orthogonalSumFst (rankOne 3) (rankOne 13) (e.carrierEquiv v)).2
  obtain ⟨y, hy⟩ := (mem_rankOne_carrier_iff 13 _).mp
    (orthogonalSumSnd (rankOne 3) (rankOne 13) (e.carrierEquiv v)).2
  rw [integralNorm_rankOne_eq _ hx.symm, integralNorm_rankOne_eq _ hy.symm] at himg_norm
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne y 0 with rfl | hy0
    · omega
    · have : 0 < y ^ 2 := sq_pos_iff.mpr hy0
      nlinarith
  · have : 0 < x ^ 2 := sq_pos_iff.mpr hx0
    have : 0 ≤ y ^ 2 := sq_nonneg y
    nlinarith

end TauCeti.IntegralLattice
