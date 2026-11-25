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
import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Splitting
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
`2`-primary component `P₂` and the orthogonal complement `P₂⊥`. On `P₂`, `H = L/N` is a bilinear
Lagrangian, and `w/2` defines a `2`-primary class on whose `H`-coset `q_N` takes the constant value
`w²/8`, giving Gauss-sum invariant `w² mod 8`. On `P₂⊥`, which has odd order `d` and lies in `H⊥`,
the orthogonal-quotient comparison `b_L ≅ H⊥ / H` restricts to a bilinear isometry onto `b_L`, hence
a quadratic isometry onto the canonical quadratic refinement of `b_L`. Milgram's theorem identifies
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
private theorem evenSublattice_discriminantSubgroup_le_primaryComponent_two :
    L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) ≤
    AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2 := by
  intro x hx
  refine AddCommGroup.mem_primaryComponent.mpr ⟨1, ?_⟩
  rw [pow_one]
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
  have hHle : H ≤ AddCommGroup.primaryComponent A 2 :=
    evenSublattice_discriminantSubgroup_le_primaryComponent_two L
  have hdvd : Nat.card H ∣ 2 ^ (Nat.card A).factorization 2 := by
    rw [← TauCeti.AddCommGroup.natCard_primaryComponent A Nat.prime_two,
      ← H.natCard_primaryPart_of_le hHle]
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
  have hHle : H ≤ P₂ := evenSublattice_discriminantSubgroup_le_primaryComponent_two L
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
  have hcardH₂ : Nat.card H₂ ^ 2 = Nat.card A₂ :=
    (congrArg (· ^ 2) (H.natCard_primaryPart_of_le hHle)).trans hcard2.symm
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

/-- In `b_N` (`N = L.evenSublattice`), the orthogonal complement `P₂⊥` of the `2`-primary
component has cardinality `L.discriminant`. -/
private theorem natCard_orthogonalComplement_primaryComponent_two_evenSublattice
    [L.IsNondegenerate] (hL : Odd L.discriminant) :
    Nat.card (L.evenSublattice.discriminantBilinearModule.orthogonalComplement
      (AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2)) =
      L.discriminant := by
  obtain ⟨hcardA, hcard2, r, hr⟩ := natCard_evenSublattice_discriminantGroup_of_odd L hL
  have hmul := FiniteBilinearModule.IsNondegenerate.card_mul_card_orthogonalComplement
    L.evenSublattice.discriminantBilinearModule
    L.evenSublattice.isNondegenerate_discriminantBilinearModule
    (AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2)
  change Nat.card (AddCommGroup.primaryComponent
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2) * _ =
    Nat.card (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) at hmul
  rw [hcard2, hcardA, mul_comm L.discriminant] at hmul
  exact Nat.mul_left_cancel (by rw [hr]; positivity) hmul

/-- Via the overlattice quotient `H⊥ / H ≅ b_L`, the orthogonal complement `P₂⊥` of the `2`-primary
component in `b_N` (`N = L.evenSublattice`) maps isometrically onto `b_L`. -/
private theorem nonempty_orthogonalComplement_primaryComponent_two_bilinearIsometry
    [L.IsNondegenerate] (hL : Odd L.discriminant) :
    Nonempty (FiniteBilinearModule.Isometry
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (L.evenSublattice.discriminantBilinearModule.orthogonalComplement
          (AddCommGroup.primaryComponent
            L.evenSublattice.DiscriminantGroup 2))).toFiniteBilinearModule
      L.discriminantBilinearModule) := by
  -- Outline:
  -- 1. `H ≤ P₂` reverses under orthogonal complementation to `K := P₂⊥ ≤ H⊥`.
  -- 2. Composing `K → H⊥ → H⊥ / H ≅ b_L` gives a pairing-preserving homomorphism `φ : K →+ b_L`.
  -- 3. Since `P₂` is nondegenerate, `P₂ ∩ P₂⊥ = ⊥`, so `ker φ = K ∩ H = ⊥` (`φ` is injective).
  -- 4. `#K = L.discriminant = #b_L` upgrades injectivity to bijectivity.
  let B := L.evenSublattice.discriminantBilinearModule
  let P₂ := AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2
  let K := B.orthogonalComplement P₂
  have hI := L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm
    L.evenSublattice_carrier_le
  let H := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  have hHle : H ≤ P₂ := evenSublattice_discriminantSubgroup_le_primaryComponent_two L
  have hKperp : K ≤ B.orthogonalComplement H := B.orthogonalComplement_anti hHle
  have hdisj : Disjoint P₂ K :=
    (B.isCompl_orthogonalComplement
      (B.isNondegenerate_restrict_primaryComponent
        L.evenSublattice.isNondegenerate_discriminantBilinearModule Nat.prime_two)).disjoint
  let qIso := (IntermediateCarrier.discriminantBilinearOrthogonalQuotientIsometry hI).symm.trans
    (Isometry.ofEq (L.toIntegralLattice_toIntermediateCarrier _ _ hI)).discriminantBilinearIsometry
  let φ : K →+ L.discriminantBilinearModule :=
    qIso.toAddEquiv.toAddMonoidHom.comp
      ((B.orthogonalQuotientMk H).comp (AddSubgroup.inclusion hKperp))
  have hφ_inj : Function.Injective φ := fun x y hxy ↦ by
    have hmem : x.val - y.val ∈ H :=
      (B.orthogonalQuotientMk_eq_iff H _ _).mp (qIso.toAddEquiv.injective hxy)
    exact Subtype.ext (sub_eq_zero.mp
      (AddSubgroup.disjoint_def.mp hdisj (hHle hmem) (sub_mem x.property y.property)))
  have hφ_bij : Function.Bijective φ := by
    let _ := Fintype.ofFinite K
    let _ := Fintype.ofFinite L.discriminantBilinearModule
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      natCard_orthogonalComplement_primaryComponent_two_evenSublattice L hL,
      L.natCard_discriminantBilinearModule]
  exact ⟨
    { toAddEquiv := AddEquiv.ofBijective φ hφ_bij
      map_pairing' := fun x y ↦
        (qIso.map_pairing _ _).trans (B.orthogonalQuotient_pairing_mk H _ _) }⟩

/-- On a lattice `L` of odd discriminant `d`, splitting `q_N` (`N = L.evenSublattice`) along its
nondegenerate `2`-primary component `P₂` gives the sum of the Gauss-sum invariants of `(q_N)|_{P₂}`
and of the canonical quadratic refinement of `b_L`. -/
private theorem gaussSign_evenSublattice_eq_add_odd [L.IsNondegenerate]
    (hL : Odd L.discriminant) :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).gaussSign =
      ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
        (AddCommGroup.primaryComponent
          (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).gaussSign +
      (L.discriminantBilinearModule.quadraticRefinement
        (L.odd_natCard_discriminantBilinearModule hL)).gaussSign := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  have hA_nondeg :=
    L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice
  have hP₂_nondeg := A.isNondegenerate_restrict_primaryComponent hA_nondeg Nat.prime_two
  let eProd := A.restrictProdOrthogonalComplementIsometry hP₂_nondeg
  have hK_nondeg : (A.restrict (A.toFiniteBilinearModule.orthogonalComplement
      (AddCommGroup.primaryComponent A 2))).IsNondegenerate :=
    hA_nondeg.isNondegenerate_restrict_orthogonalComplement hP₂_nondeg
  obtain ⟨fBilin⟩ := nonempty_orthogonalComplement_primaryComponent_two_bilinearIsometry L hL
  have hoddK : Odd (Nat.card (A.restrict (A.toFiniteBilinearModule.orthogonalComplement
      (AddCommGroup.primaryComponent A 2)))) := by
    have hcard := Nat.card_congr fBilin.toAddEquiv.toEquiv
    exact hcard.symm ▸ L.odd_natCard_discriminantBilinearModule hL
  have hK_sign : (A.restrict (A.toFiniteBilinearModule.orthogonalComplement
      (AddCommGroup.primaryComponent A 2))).gaussSign =
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
  have hM : Odd M.discriminant :=
    discriminant_eq_of_isometry_discriminantBilinearModule f ▸ hL
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
  have h1 : L.discriminant = 1 := L.isUnimodular_iff_discriminant_eq_one.mp hL
  have hodd : Odd L.discriminant := h1 ▸ odd_one
  have : Subsingleton (L.discriminantBilinearModule.quadraticRefinement
      (L.odd_natCard_discriminantBilinearModule hodd)) :=
    Finite.card_le_one_iff_subsingleton.mp (by
      simp [FiniteBilinearModule.quadraticRefinement_toFiniteBilinearModule, h1])
  have h := L.sigPos_sub_sigNeg_eq_integralNorm_add_gaussSign hodd hw
  rw [FiniteQuadraticModule.gaussSign_eq_zero_of_subsingleton, add_zero] at h
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  simpa only [Int.cast_sub, Int.cast_natCast] using h

end TauCeti.IntegralLattice
