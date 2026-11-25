/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum.AffineLagrangian
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Subgroup
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Metabolic
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Bilinear

/-!
# Van der Blij's characteristic-norm congruence

In a unimodular integral lattice, every characteristic vector has integral norm congruent to the
signature difference modulo eight. More generally, when the discriminant `d = |det L|` is odd, the
lattice still has a characteristic vector `w`
(`TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`), its discriminant
bilinear module `b_L` of odd order `d` carries a unique quadratic refinement
(`TauCeti.FiniteBilinearModule.quadraticRefinement`), and the signature difference modulo
eight splits as `w²` plus the Gauss-sum invariant of that refinement. Both statements apply to all
signatures and to both even and odd lattices.

For the canonical even sublattice `N` of an odd-discriminant lattice `L`, the discriminant quadratic
module `q_N` has order `d · [L : N]²` with `[L : N] ∈ {1, 2}`, so it splits orthogonally into its
`2`-primary component and its `d`-torsion subgroup. On the `2`-primary component, `H = L/N` is a
bilinear Lagrangian, and `w/2` defines a `2`-primary class on whose `H`-coset `q_N` takes the
constant value `w²/8`, giving Gauss-sum invariant `w² mod 8`. On the `d`-torsion subgroup, the
orthogonal-quotient comparison `b_L ≅ H⊥ / H` restricts to a bilinear isometry onto `b_L`, hence a
quadratic isometry onto the canonical quadratic refinement of `b_L`. Milgram's theorem identifies
the total Gauss-sum invariant of `q_N` with the signature of `N`, which equals the signature of `L`.
When `L` is unimodular, `b_L` is trivial and the odd-order Gauss-sum term vanishes.

## Main results

* `TauCeti.IntegralLattice.sigPos_sub_sigNeg_eq_integralNorm_add_gaussSign`: for
  `Odd L.discriminant` and characteristic `w`, `(L.sigPos : ZMod 8) - L.sigNeg` equals
  `(L.integralNorm w : ZMod 8)` plus the Gauss-sum invariant of the canonical quadratic refinement
  of `b_L`.
* `TauCeti.IntegralLattice.integralNorm_characteristicVector_modEq_of_odd_discriminant`: two
  odd-discriminant lattices with equal signatures and isometric discriminant bilinear modules have
  characteristic norms congruent modulo eight.
* `TauCeti.IntegralLattice.vanDerBlij`: in a unimodular lattice,
  `L.sigPos - L.sigNeg ≡ w² [ZMOD 8]`.

## References

* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291–293.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.16.
-/

public section

open scoped Real

namespace TauCeti.IntegralLattice

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

private theorem half_characteristic_mem_dual {w : L} (hw : L.IsCharacteristicVector w) :
    (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  let yL : L := ⟨y, L.evenSublattice_carrier_le hy⟩
  have he : Even (L.integralNorm yL) := (L.mem_evenSublattice_carrier_iff yL).mp hy
  have hp := (L.isCharacteristicVector_iff w).mp hw yL
  have hb : 2 ∣ L.integralForm w yL := Int.modEq_zero_iff_dvd.mp
    (hp.trans (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp he)))
  obtain ⟨k, hk⟩ := hb
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← L.integralForm_cast w yL, hk]
  push_cast
  ring

private def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_dual L hw⟩

private theorem quadratic_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (halfCharacteristicDual L hw)) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [discriminantQuadraticMap_mk, L.evenSublattice_form, ZMod.toRatAddCircle_intCast,
    L.integralNorm_cast, L.norm_apply]
  simp only [halfCharacteristicDual, Subtype.coe_mk, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  congr 1
  ring

private theorem halfNorm_add_lattice_vector {w : L} (hw : L.IsCharacteristicVector w)
    (y : L) :
    ∃ k : ℤ, L.form ((1 / 2 : ℚ) • (w : V) + y)
        ((1 / 2 : ℚ) • (w : V) + y) / 2 =
      L.form ((1 / 2 : ℚ) • (w : V)) ((1 / 2 : ℚ) • (w : V)) / 2 + k := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ((L.isCharacteristicVector_iff w).mp hw y)
  refine ⟨L.integralForm w y + k, ?_⟩
  rw [← L.norm_apply, ← L.norm_apply, L.norm_add]
  simp only [L.norm_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← L.integralForm_cast w y, ← L.integralNorm_cast y]
  have hkq : (L.integralNorm y : ℚ) - L.integralForm w y = 2 * k := by exact_mod_cast hk
  push_cast
  linarith

private theorem quadratic_halfCharacteristicDual_add {w : L}
    (hw : L.IsCharacteristicVector w)
    (h : L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        ((Submodule.Quotient.mk (halfCharacteristicDual L hw) :
          L.evenSublattice.DiscriminantGroup) + h) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (halfCharacteristicDual L hw)) := by
  obtain ⟨x, hx⟩ := h
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hy : (y : V) ∈ L.carrier := by
      have := (L.evenSublattice.mk_mem_discriminantSubgroup_iff
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) y).mp hx
      rwa [coe_toIntermediateCarrier] at this
    obtain ⟨k, hk⟩ := halfNorm_add_lattice_vector L hw ⟨y, hy⟩
    rw [← Submodule.Quotient.mk_add, discriminantQuadraticMap_mk,
      discriminantQuadraticMap_mk, L.evenSublattice_form]
    simp only [Submodule.coe_add, halfCharacteristicDual, Subtype.coe_mk]
    rw [hk, AddCircle.coe_add_intCast]

/-- Every element of `L / L.evenSublattice` is killed by `2`, so the subgroup sits inside the
`2`-primary component of the discriminant group of `L.evenSublattice`. -/
private theorem two_nsmul_eq_zero_of_mem_evenSublattice_discriminantSubgroup
    {x : L.evenSublattice.DiscriminantGroup}
    (hx : x ∈ L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    2 • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hy : (y : V) ∈ L.carrier := by
      have := (L.evenSublattice.mk_mem_discriminantSubgroup_iff
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) y).mp hx
      rwa [coe_toIntermediateCarrier] at this
    have h2 : (2 • y : L.evenSublattice.dualCarrier) ∈ L.evenSublattice.carrierInDual := by
      rw [mem_carrierInDual_iff, ← natCast_zsmul, SetLike.val_smul, evenSublattice_carrier]
      exact ⟨(2 : ℤ) • (⟨y, hy⟩ : L), L.two_smul_mem_evenSubmodule ⟨y, hy⟩, rfl⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact h2

/-- For a lattice `L` of odd discriminant, the discriminant group `A` of `N = L.evenSublattice`
has order `L.discriminant * #H²` where `H = L / N`, and its `2`-primary component has order `#H²`
for some `2`-power `#H = 2 ^ r`. -/
private theorem natCard_evenSublattice_discriminantGroup_of_odd [L.IsNondegenerate]
    (hL : Odd L.discriminant) :
    let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
    let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
    Nat.card A = L.discriminant * Nat.card H ^ 2 ∧
      Nat.card (AddCommGroup.primaryComponent A 2) = Nat.card H ^ 2 ∧
      ∃ r : ℕ, Nat.card H = 2 ^ r := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  have hI := L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm
    L.evenSublattice_carrier_le
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  have hH_iso : L.evenSublattice.discriminantBilinearModule.IsIsotropic H :=
    (IntermediateCarrier.isIntegral_iff_isIsotropic_discriminantSubgroup _).mp hI
  have hcardQ : Nat.card (L.evenSublattice.discriminantBilinearModule.orthogonalQuotient H) =
      L.discriminant := by
    rw [IntermediateCarrier.natCard_discriminantBilinearOrthogonalQuotient hI,
      L.toIntegralLattice_toIntermediateCarrier]
  have hcardA : Nat.card A = L.discriminant * Nat.card H ^ 2 := by
    have h := FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_mul_card_sq
      L.evenSublattice.discriminantBilinearModule
      L.evenSublattice.isNondegenerate_discriminantBilinearModule hH_iso
    rw [hcardQ] at h
    exact h.symm
  have hHle : H ≤ AddCommGroup.primaryComponent A 2 := fun x hx ↦
    AddCommGroup.mem_primaryComponent.mpr
      ⟨1, two_nsmul_eq_zero_of_mem_evenSublattice_discriminantSubgroup L hx⟩
  have hdvd : Nat.card H ∣ 2 ^ (Nat.card A).factorization 2 := by
    rw [← TauCeti.AddCommGroup.natCard_primaryComponent A Nat.prime_two,
      ← Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHle).toEquiv]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcard2 : Nat.card (AddCommGroup.primaryComponent A 2) = Nat.card H ^ 2 := by
    have hf0 : L.discriminant.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦ by
        obtain ⟨k, hk⟩ := hL; obtain ⟨m, hm⟩ := hdvd; omega
    rw [TauCeti.AddCommGroup.natCard_primaryComponent A Nat.prime_two, hcardA, hr, ← pow_mul,
      Nat.factorization_mul hL.pos.ne' (by positivity), Finsupp.add_apply, hf0, zero_add,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, pow_mul]
  exact ⟨hcardA, hcard2, r, hr⟩

private theorem mk_halfCharacteristicDual_mem_primaryComponent_two [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) :
    (Submodule.Quotient.mk (halfCharacteristicDual L hw) :
      L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) ∈
        AddCommGroup.primaryComponent
          (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2 := by
  refine AddCommGroup.mem_primaryComponent.mpr ⟨2, ?_⟩
  -- View scalar multiplication on the exposed quotient `L.evenSublattice.DiscriminantGroup`.
  change (2 ^ 2 : ℕ) • (Submodule.Quotient.mk (halfCharacteristicDual L hw) :
    L.evenSublattice.DiscriminantGroup) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    mem_carrierInDual_iff, ← natCast_zsmul, SetLike.val_smul, halfCharacteristicDual,
    Subtype.coe_mk, evenSublattice_carrier]
  refine ⟨(2 : ℤ) • w, L.two_smul_mem_evenSubmodule w, ?_⟩
  have h2half : (1 / 2 : ℚ) • (w : V) + (1 / 2 : ℚ) • (w : V) = (w : V) := by
    rw [← add_smul]; norm_num
  have h4 : (2 ^ 2 : ℕ) = 2 + 2 := rfl
  simp only [Submodule.coe_subtype, SetLike.val_smul, natCast_zsmul]
  rw [h4, add_nsmul, two_nsmul, h2half, two_zsmul]

/-- The `2`-primary component of the discriminant quadratic module of `L.evenSublattice` has
Gauss-sum invariant `(L.integralNorm w : ZMod 8)` for any characteristic vector `w` of an
odd-discriminant lattice `L`. -/
private theorem gaussSign_primaryComponent_two_evenSublattice [L.IsNondegenerate]
    (hL : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
      (AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).gaussSign =
      (L.integralNorm w : ZMod 8) := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P₂ := AddCommGroup.primaryComponent A 2
  let A₂ := A.restrict P₂
  have hI := L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm
    L.evenSublattice_carrier_le
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  have hHle : H ≤ P₂ := fun x hx ↦ AddCommGroup.mem_primaryComponent.mpr
    ⟨1, two_nsmul_eq_zero_of_mem_evenSublattice_discriminantSubgroup L hx⟩
  let H₂ : AddSubgroup A₂ := AddSubgroup.primaryPart H 2
  have hH_iso : A.toFiniteBilinearModule.IsIsotropic H := by
    simpa only [A, L.evenSublattice.discriminantQuadraticModule_toFiniteBilinearModule
      L.isEven_evenSublattice] using
      (IntermediateCarrier.isIntegral_iff_isIsotropic_discriminantSubgroup _).mp hI
  have hH₂_iso : A₂.toFiniteBilinearModule.IsIsotropic H₂ :=
    (A.toFiniteBilinearModule.isIsotropic_iff_primaryPart H).mp hH_iso 2 Nat.prime_two
  have hA₂_nondeg : A₂.IsNondegenerate :=
    A.isNondegenerate_restrict_primaryComponent
      (L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice)
      Nat.prime_two
  obtain ⟨-, hcard2, -⟩ := natCard_evenSublattice_discriminantGroup_of_odd L hL
  have hcardH₂ : Nat.card H₂ ^ 2 = Nat.card A₂ := by
    have heq : Nat.card H₂ = Nat.card H := Nat.card_congr
      { toFun := fun x ↦ ⟨x.val.val, (AddSubgroup.mem_primaryPart_iff H 2 x.val).mp x.property⟩
        invFun := fun y ↦
          ⟨⟨y.val, hHle y.property⟩, (AddSubgroup.mem_primaryPart_iff H 2 _).mpr y.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact (congrArg (· ^ 2) heq).trans hcard2.symm
  have hH₂_lagr : A₂.toFiniteBilinearModule.IsLagrangian H₂ :=
    FiniteBilinearModule.IsIsotropic.isLagrangian_of_card_sq_eq A₂.toFiniteBilinearModule hH₂_iso
      hA₂_nondeg hcardH₂
  let a₂ : A₂ :=
    ⟨Submodule.Quotient.mk (halfCharacteristicDual L hw),
      mk_halfCharacteristicDual_mem_primaryComponent_two L hw⟩
  have ha₂ (h : H₂) : A₂.quadratic (a₂ + h) = A₂.quadratic a₂ :=
    quadratic_halfCharacteristicDual_add L hw
      ⟨h.val.val, (AddSubgroup.mem_primaryPart_iff H 2 h.val).mp h.property⟩
  have hqa₂ : A₂.quadratic a₂ = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) :=
    quadratic_halfCharacteristicDual L hw
  refine FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq A₂ ?_
  rw [FiniteQuadraticModule.gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian a₂ hH₂_lagr
    ha₂, hqa₂, ← hcardH₂, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_natCast]

/-- The `d`-torsion subgroup `ker(d • ·)` of the discriminant quadratic module of
`L.evenSublattice`, where `d = L.discriminant`. -/
private noncomputable def evenSublatticeOddSubgroup [L.IsNondegenerate] :
    AddSubgroup (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) :=
  (nsmulAddMonoidHom L.discriminant :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) →+ _).ker

private theorem disjoint_primaryComponent_two_evenSublatticeOddSubgroup [L.IsNondegenerate]
    (hL : Odd L.discriminant)
    {z : L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice}
    (hz2 : z ∈ AddCommGroup.primaryComponent
      (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)
    (hzd : z ∈ evenSublatticeOddSubgroup L) : z = 0 := by
  obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.mp hz2
  exact (nsmul_eq_zero_iff_of_coprime (hL.coprime_two_left.pow_left m)).mp ⟨hm, hzd⟩

private theorem pairing_primaryComponent_two_evenSublatticeOddSubgroup [L.IsNondegenerate]
    (hL : Odd L.discriminant)
    {x y : L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice}
    (hx : x ∈ AddCommGroup.primaryComponent
      (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)
    (hy : y ∈ evenSublatticeOddSubgroup L) :
    (L.evenSublattice.discriminantQuadraticModule
      L.isEven_evenSublattice).toFiniteBilinearModule.pairing x y = 0 := by
  let B := (L.evenSublattice.discriminantQuadraticModule
    L.isEven_evenSublattice).toFiniteBilinearModule
  obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.mp hx
  have hy0 : L.discriminant • y = 0 := hy
  refine (nsmul_eq_zero_iff_of_coprime (hL.coprime_two_left.pow_left m)).mp ⟨?_, ?_⟩
  · rw [← B.pairing_nsmul_left, hm, B.pairing_zero_left]
  · rw [← map_nsmul, hy0, map_zero]

private noncomputable def evenSublatticeProdAddMonoidHom [L.IsNondegenerate] :
    (AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2 ×
      evenSublatticeOddSubgroup L) →+
      (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) where
  toFun p := p.1.val + p.2.val
  map_zero' := by simp
  map_add' p q := by simp [add_add_add_comm]

private theorem evenSublatticeProdAddMonoidHom_apply [L.IsNondegenerate]
    (p : AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2 ×
      evenSublatticeOddSubgroup L) :
    evenSublatticeProdAddMonoidHom L p = p.1.val + p.2.val :=
  rfl

/-- Bézout decomposition of the discriminant group of `L.evenSublattice` as `P₂ × K`, where `P₂` is
the `2`-primary component and `K` is the `L.discriminant`-torsion subgroup. -/
private theorem bijective_evenSublatticeProdAddMonoidHom [L.IsNondegenerate]
    (hL : Odd L.discriminant) :
    Function.Bijective (evenSublatticeProdAddMonoidHom L) := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P₂ := AddCommGroup.primaryComponent A 2
  let K := evenSublatticeOddSubgroup L
  obtain ⟨hcardA, -, r, hr⟩ := natCard_evenSublattice_discriminantGroup_of_odd L hL
  refine ⟨fun p q hpq ↦ ?_, fun z ↦ ?_⟩
  · have hsub : p.1.val - q.1.val = q.2.val - p.2.val :=
      sub_eq_sub_iff_add_eq_add.mpr (hpq.trans (add_comm _ _))
    have h0 : p.1.val - q.1.val = 0 :=
      disjoint_primaryComponent_two_evenSublatticeOddSubgroup L hL
        (sub_mem p.1.property q.1.property) (hsub ▸ sub_mem q.2.property p.2.property)
    exact Prod.ext (Subtype.ext (sub_eq_zero.mp h0))
      (Subtype.ext (sub_eq_zero.mp (hsub.symm.trans h0)).symm)
  · let q := 2 ^ (r * 2)
    have hcardAq : Nat.card A = L.discriminant * q := by rw [hcardA, hr, ← pow_mul]
    have hbez : (1 : ℤ) = L.discriminant * Nat.gcdA L.discriminant q +
        q * Nat.gcdB L.discriminant q := by
      have hg := Nat.gcd_eq_gcd_ab L.discriminant q
      rwa [(hL.coprime_two_left.pow_left (r * 2)).symm.gcd_eq_one, Nat.cast_one] at hg
    have hann : (L.discriminant * q) • z = 0 := hcardAq ▸ card_nsmul_eq_zero'
    have hx2 : (Nat.gcdA L.discriminant q * (L.discriminant : ℤ)) • z ∈ P₂ := by
      refine AddCommGroup.mem_primaryComponent.mpr ⟨r * 2, ?_⟩
      calc q • ((Nat.gcdA L.discriminant q * (L.discriminant : ℤ)) • z)
          = ((q : ℤ) * (Nat.gcdA L.discriminant q * L.discriminant)) • z := by
              rw [← natCast_zsmul, ← mul_zsmul]
        _ = Nat.gcdA L.discriminant q • (((L.discriminant * q : ℕ) : ℤ) • z) := by
              rw [← mul_zsmul]; congr 1; push_cast; ring
        _ = 0 := by rw [natCast_zsmul, hann, smul_zero]
    have hyK : (Nat.gcdB L.discriminant q * (q : ℤ)) • z ∈ K := by
      -- Unfold membership in `evenSublatticeOddSubgroup` as `L.discriminant • · = 0`.
      change L.discriminant • ((Nat.gcdB L.discriminant q * (q : ℤ)) • z) = 0
      calc L.discriminant • ((Nat.gcdB L.discriminant q * (q : ℤ)) • z)
          = ((L.discriminant : ℤ) * (Nat.gcdB L.discriminant q * q)) • z := by
              rw [← natCast_zsmul, ← mul_zsmul]
        _ = Nat.gcdB L.discriminant q • (((L.discriminant * q : ℕ) : ℤ) • z) := by
              rw [← mul_zsmul]; congr 1; push_cast; ring
        _ = 0 := by rw [natCast_zsmul, hann, smul_zero]
    have h1 : Nat.gcdA L.discriminant q * (L.discriminant : ℤ) +
        Nat.gcdB L.discriminant q * q = 1 := by linarith
    refine ⟨(⟨_, hx2⟩, ⟨_, hyK⟩), ?_⟩
    rw [evenSublatticeProdAddMonoidHom_apply, ← add_zsmul, h1, one_zsmul]

/-- On an odd-discriminant lattice `L`, Bézout's identity for `L.discriminant` and the `2`-power
order of `P₂` splits `q_N` (`N = L.evenSublattice`) as `(q_N)|_{P₂} ⊥ (q_N)|_K`. -/
private theorem nonempty_evenSublatticeProdIsometry [L.IsNondegenerate]
    (hL : Odd L.discriminant) :
    Nonempty (FiniteQuadraticModule.Isometry
      (((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
          (AddCommGroup.primaryComponent
            (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).prod
        ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
          (evenSublatticeOddSubgroup L)))
      (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice)) := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P₂ := AddCommGroup.primaryComponent A 2
  let K := evenSublatticeOddSubgroup L
  have hadd (x : P₂) (y : K) :
      A.quadratic (x.val + y.val) = A.quadratic x.val + A.quadratic y.val := by
    rw [QuadraticMap.map_add A.quadratic, A.polar_eq_pairing,
      pairing_primaryComponent_two_evenSublatticeOddSubgroup L hL x.property y.property, add_zero]
  exact ⟨
    { toLinearEquiv :=
        (AddEquiv.ofBijective (evenSublatticeProdAddMonoidHom L)
          (bijective_evenSublatticeProdAddMonoidHom L hL)).toIntLinearEquiv
      map_app' := fun p ↦ (hadd p.1 p.2).trans (congrArg₂ (· + ·)
        (A.restrict_quadratic P₂ p.1).symm (A.restrict_quadratic K p.2).symm) }⟩

/-- Via the overlattice quotient `H⊥ / H ≅ b_L`, the `d`-torsion subgroup `K` of `b_N` maps
isometrically onto `b_L`. -/
private theorem nonempty_evenSublatticeOddSubgroupBilinearIsometry [L.IsNondegenerate]
    (hL : Odd L.discriminant) :
    Nonempty (FiniteBilinearModule.Isometry
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (evenSublatticeOddSubgroup L)).toFiniteBilinearModule
      L.discriminantBilinearModule) := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let K := evenSublatticeOddSubgroup L
  obtain ⟨hcardA, hcard2, r, hr⟩ := natCard_evenSublattice_discriminantGroup_of_odd L hL
  obtain ⟨eProd⟩ := nonempty_evenSublatticeProdIsometry L hL
  have hcardK : Nat.card K = L.discriminant := by
    have hmul := Nat.card_congr eProd.toLinearEquiv.toEquiv
    -- Expose the product carrier type in `Nat.card` as `P₂ × K`.
    change Nat.card (AddCommGroup.primaryComponent A 2 × K) = Nat.card A at hmul
    rw [Nat.card_prod, hcard2, hcardA, mul_comm L.discriminant] at hmul
    exact Nat.mul_left_cancel (by rw [hr]; positivity) hmul
  have hI := L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm
    L.evenSublattice_carrier_le
  let H := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  let HA : AddSubgroup A := H
  have hHle : HA ≤ AddCommGroup.primaryComponent A 2 := fun x hx ↦
    AddCommGroup.mem_primaryComponent.mpr
      ⟨1, two_nsmul_eq_zero_of_mem_evenSublattice_discriminantSubgroup L hx⟩
  have hKperp (y : K) :
      y.val ∈ L.evenSublattice.discriminantBilinearModule.orthogonalComplement H :=
    (L.evenSublattice.discriminantBilinearModule.mem_orthogonalComplement_iff H y.val).mpr
      fun h hh ↦ (A.toFiniteBilinearModule.pairing_comm y.val h).trans
        (pairing_primaryComponent_two_evenSublatticeOddSubgroup L hL (hHle hh) y.property)
  let qIso := (IntermediateCarrier.discriminantBilinearOrthogonalQuotientIsometry hI).symm.trans
    (Isometry.ofEq (L.toIntegralLattice_toIntermediateCarrier _ _ hI)).discriminantBilinearIsometry
  let φ : K →+ L.discriminantBilinearModule :=
    qIso.toAddEquiv.toAddMonoidHom.comp
      ((L.evenSublattice.discriminantBilinearModule.orthogonalQuotientMk H).comp
        { toFun := fun y ↦ ⟨y.val, hKperp y⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl })
  have hφ_inj : Function.Injective φ := fun x y hxy ↦ by
    have hmk := qIso.toAddEquiv.injective hxy
    have hmem : x.val - y.val ∈ HA :=
      (L.evenSublattice.discriminantBilinearModule.orthogonalQuotientMk_eq_iff H _ _).mp hmk
    exact Subtype.ext (sub_eq_zero.mp
      (disjoint_primaryComponent_two_evenSublatticeOddSubgroup L hL
        (hHle hmem) (sub_mem x.property y.property)))
  have hφ_bij : Function.Bijective φ := by
    let _ := Fintype.ofFinite K
    let _ := Fintype.ofFinite L.discriminantBilinearModule
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardK]
    -- `L.discriminantBilinearModule` is exposed with carrier `L.DiscriminantGroup`.
    change L.discriminant = Nat.card L.DiscriminantGroup
    exact L.natCard_discriminantGroup.symm
  exact ⟨
    { toAddEquiv := AddEquiv.ofBijective φ hφ_bij
      map_pairing' := fun x y ↦
        (qIso.map_pairing _ _).trans
          (L.evenSublattice.discriminantBilinearModule.orthogonalQuotient_pairing_mk H _ _) }⟩

/-- On a lattice `L` of odd discriminant `d`, splitting `q_N` (`N = L.evenSublattice`) into its
`2`-primary component and its `d`-torsion subgroup gives the sum of their Gauss-sum invariants. -/
private theorem gaussSign_evenSublattice_eq_add_odd [L.IsNondegenerate]
    (hL : Odd L.discriminant) :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).gaussSign =
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (AddCommGroup.primaryComponent
          (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).gaussSign +
      (L.discriminantBilinearModule.quadraticRefinement
        (L.odd_natCard_discriminantBilinearModule hL)).gaussSign := by
  obtain ⟨eProd⟩ := nonempty_evenSublatticeProdIsometry L hL
  obtain ⟨fBilin⟩ := nonempty_evenSublatticeOddSubgroupBilinearIsometry L hL
  have hA_nondeg :=
    L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice
  obtain ⟨hP₂_nondeg, hK_nondeg⟩ :=
    FiniteQuadraticModule.isNondegenerate_prod _ _ |>.mp (eProd.isNondegenerate_iff.mpr hA_nondeg)
  have hoddK : Odd (Nat.card ((L.evenSublattice.discriminantQuadraticModule
      L.isEven_evenSublattice).restrict (evenSublatticeOddSubgroup L))) := by
    have hcard := Nat.card_congr fBilin.toAddEquiv.toEquiv
    exact hcard.symm ▸ L.odd_natCard_discriminantBilinearModule hL
  have hK_sign : ((L.evenSublattice.discriminantQuadraticModule
      L.isEven_evenSublattice).restrict (evenSublatticeOddSubgroup L)).gaussSign =
      (L.discriminantBilinearModule.quadraticRefinement
        (L.odd_natCard_discriminantBilinearModule hL)).gaussSign :=
    (FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd
      (B := L.discriminantBilinearModule.quadraticRefinement
        (L.odd_natCard_discriminantBilinearModule hL)) hoddK fBilin).gaussSign_eq
  rw [← eProd.gaussSign_eq, FiniteQuadraticModule.gaussSign_prod hP₂_nondeg hK_nondeg, hK_sign]

/-- **Van der Blij–Milgram identity for odd-discriminant lattices.** For any nondegenerate integral
lattice `L` with odd discriminant and any characteristic vector `w` of `L`, the signature
difference modulo eight equals `w²` plus the Gauss-sum invariant of the canonical quadratic
refinement of `b_L`. -/
theorem sigPos_sub_sigNeg_eq_integralNorm_add_gaussSign [L.IsNondegenerate]
    (hL : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    ((L.sigPos : ZMod 8) - L.sigNeg) = (L.integralNorm w : ZMod 8) +
      (L.discriminantBilinearModule.quadraticRefinement
        (L.odd_natCard_discriminantBilinearModule hL)).gaussSign := by
  have := L.finiteDimensional
  have hm := L.evenSublattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg
    L.isEven_evenSublattice
  have hs := L.evenSublattice_signature
  simp only [signature, Prod.mk.injEq] at hs
  rw [hs.1, hs.2.2] at hm
  rw [← hm, gaussSign_evenSublattice_eq_add_odd L hL,
    gaussSign_primaryComponent_two_evenSublattice L hL hw]

/-- **Odd-discriminant lattices with equal signatures and isometric discriminant bilinear modules
have congruent characteristic norms modulo eight.** -/
theorem integralNorm_characteristicVector_modEq_of_odd_discriminant [L.IsNondegenerate]
    {W : Type v} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W} [M.IsNondegenerate]
    (hL : Odd L.discriminant) (hsig : L.signature = M.signature)
    {w : L} {w' : M} (hw : L.IsCharacteristicVector w) (hw' : M.IsCharacteristicVector w')
    (f : FiniteBilinearModule.Isometry L.discriminantBilinearModule M.discriminantBilinearModule) :
    L.integralNorm w ≡ M.integralNorm w' [ZMOD 8] := by
  have hcard : L.discriminant = M.discriminant := by
    rw [← L.natCard_discriminantGroup, ← M.natCard_discriminantGroup]
    exact Nat.card_congr f.toAddEquiv.toEquiv
  have hM : Odd M.discriminant := hcard ▸ hL
  have hL_eq := L.sigPos_sub_sigNeg_eq_integralNorm_add_gaussSign hL hw
  have hM_eq := M.sigPos_sub_sigNeg_eq_integralNorm_add_gaussSign hM hw'
  have hsign : (L.discriminantBilinearModule.quadraticRefinement
      (L.odd_natCard_discriminantBilinearModule hL)).gaussSign =
      (M.discriminantBilinearModule.quadraticRefinement
        (M.odd_natCard_discriminantBilinearModule hM)).gaussSign :=
    (FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd
      (A := L.discriminantBilinearModule.quadraticRefinement
        (L.odd_natCard_discriminantBilinearModule hL))
      (B := M.discriminantBilinearModule.quadraticRefinement
        (M.odd_natCard_discriminantBilinearModule hM))
      (L.odd_natCard_discriminantBilinearModule hL) f).gaussSign_eq
  simp only [signature, Prod.mk.injEq] at hsig
  rw [hsig.1, hsig.2.2, hsign] at hL_eq
  exact (ZMod.intCast_eq_intCast_iff _ _ 8).mp (add_right_cancel (hL_eq.symm.trans hM_eq))

/-- **Van der Blij's congruence:** the signature difference of a unimodular
integral lattice is congruent modulo eight to the norm of any characteristic vector. -/
theorem vanDerBlij (hL : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    ((L.sigPos : ℤ) - L.sigNeg) ≡ L.integralNorm w [ZMOD 8] := by
  let _ : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have hodd : Odd L.discriminant := (L.isUnimodular_iff_discriminant_eq_one.mp hL) ▸ odd_one
  have : Subsingleton (L.discriminantBilinearModule.quadraticRefinement
      (L.odd_natCard_discriminantBilinearModule hodd)) :=
    (L.isUnimodular_iff_subsingleton_discriminantGroup).mp hL
  have h := L.sigPos_sub_sigNeg_eq_integralNorm_add_gaussSign hodd hw
  rw [FiniteQuadraticModule.gaussSign_eq_zero_of_subsingleton, add_zero] at h
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  simpa only [Int.cast_sub, Int.cast_natCast] using h

end TauCeti.IntegralLattice
