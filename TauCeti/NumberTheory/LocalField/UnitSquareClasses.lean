/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.SquareClass
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# Unit square classes of a local field

The image of the integer-ring units in `Kˣ / (Kˣ)²` consists exactly of the classes of even
normalized valuation. The valuation modulo two descends to a surjective homomorphism on square
classes, with this image as its kernel. Consequently the unit square classes have index two,
including in residue characteristic two.

This subgroup is the intended comparison target for the almost-everywhere reference images of
the standard integral special orthogonal family in dimension at least three. Its index
distinguishes it from the whole square-class group; a uniformizer never belongs to it. The
construction is independent of a uniformizer, although a uniformizer gives a splitting of the
valuation homomorphism.

All groups use their canonical topologies.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A and §101.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The subgroup of square classes represented by units of the ring of integers. -/
def unitSquareClasses : Subgroup (Kˣ ⧸ Subgroup.square Kˣ) :=
  ((QuotientGroup.mk' (Subgroup.square Kˣ)).comp
    (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K))).range

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Membership in the unit square classes means having an integer-unit representative. -/
theorem mem_unitSquareClasses_iff (c : Kˣ ⧸ Subgroup.square Kˣ) :
    c ∈ unitSquareClasses K ↔ ∃ u : 𝒪[K]ˣ,
      QuotientGroup.mk' (Subgroup.square Kˣ)
        (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) = c := Iff.rfl

/-- Normalized valuation modulo two, descended to the multiplicative square-class quotient. -/
def squareClassValuation :
    (Kˣ ⧸ Subgroup.square Kˣ) →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift (Subgroup.square Kˣ)
    (normalizedValuationMod K 2).toMultiplicativeRight (by
      intro a ha
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      simpa only [AddMonoidHom.coe_toMultiplicativeRight, Function.comp_apply,
        normalizedValuationMod_ofMul, toAdd_ofAdd, toAdd_one] using
        (even_toAdd_normalizedValuation_of_isSquare
        (Subgroup.mem_square.mp ha)).intCast_zmod_two)

/-- The valuation of a square class is the normalized valuation of a representative modulo two. -/
@[simp]
theorem squareClassValuation_mk (a : Kˣ) :
    squareClassValuation K (a : Kˣ ⧸ Subgroup.square Kˣ) =
      Multiplicative.ofAdd ((normalizedValuation K a).toAdd : ZMod 2) := by
  exact congrArg Multiplicative.ofAdd (normalizedValuationMod_ofMul (K := K) 2 a)

/-- The valuation map on square classes is surjective. -/
theorem squareClassValuation_surjective : Function.Surjective (squareClassValuation K) := by
  apply QuotientGroup.lift_surjective_of_surjective
  exact Multiplicative.ofAdd.surjective.comp
    ((normalizedValuationMod_surjective (K := K) 2).comp Additive.ofMul.surjective)

/-- A unit of the field has an integer-unit square-class representative exactly when its
normalized valuation is even. -/
@[simp]
theorem mk_mem_unitSquareClasses_iff (a : Kˣ) :
    (a : Kˣ ⧸ Subgroup.square Kˣ) ∈ unitSquareClasses K ↔
      Even (normalizedValuation K a).toAdd := by
  constructor
  · rintro ⟨u, hu⟩
    have h := congrArg (squareClassValuation K) hu
    simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      squareClassValuation_mk, normalizedValuation_integerUnits, toAdd_one, Int.cast_zero] at h
    exact ZMod.intCast_eq_zero_iff_even.mp (Multiplicative.ofAdd.injective h.symm)
  · intro ha
    obtain ⟨π, hπ⟩ := exists_isUniformizer K
    have hv := (isUniformizer_def π).mp hπ
    let b := a * π ^ (-(normalizedValuation K a).toAdd)
    obtain ⟨u, -, hu⟩ := mem_unitFiltration_iff_exists.mp
      (mul_zpow_neg_mem_unitFiltration_zero hv a)
    have hub : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u = b := Units.ext hu
    refine (mem_unitSquareClasses_iff K _).mpr ⟨u, ?_⟩
    rw [hub]
    have hs : QuotientGroup.mk' (Subgroup.square Kˣ)
        (π ^ (-(normalizedValuation K a).toAdd)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_square]
      exact ha.neg.isSquare_zpow π
    dsimp only [b]
    rw [map_mul, hs, mul_one, QuotientGroup.mk'_apply]

/-- Unit square classes are the kernel of valuation modulo two. -/
theorem unitSquareClasses_eq_ker_squareClassValuation :
    unitSquareClasses K = (squareClassValuation K).ker := by
  ext c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.square Kˣ) c
  simp [MonoidHom.mem_ker, ofAdd_eq_one, ZMod.intCast_eq_zero_iff_even]

/-- The unit square classes have index two in every nonarchimedean local field. -/
@[simp]
theorem unitSquareClasses_index : (unitSquareClasses K).index = 2 := by
  rw [unitSquareClasses_eq_ker_squareClassValuation, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (squareClassValuation_surjective K), Subgroup.card_top]
  exact Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)
    |>.trans (by simp)

/-- A uniformizer's class does not belong to the unit square classes. -/
theorem mk_notMem_unitSquareClasses_of_isUniformizer {π : Kˣ} (hπ : IsUniformizer K π) :
    QuotientGroup.mk' (Subgroup.square Kˣ) π ∉ unitSquareClasses K := by
  rw [QuotientGroup.mk'_apply, mk_mem_unitSquareClasses_iff, (isUniformizer_def π).mp hπ]
  norm_num

/-- Unit square classes are a proper subgroup, also in residue characteristic two. -/
theorem unitSquareClasses_ne_top : unitSquareClasses K ≠ ⊤ := by
  intro h
  have := unitSquareClasses_index K
  simp [h] at this

/-- The unit square classes are open in the local square-class quotient. -/
theorem isOpen_unitSquareClasses :
    IsOpen (unitSquareClasses K : Set (Kˣ ⧸ Subgroup.square Kˣ)) := by
  rw [← (QuotientGroup.isQuotientMap_mk (Subgroup.square Kˣ)).isOpen_preimage]
  simpa only [Set.preimage, Set.mem_ofPred_eq, SetLike.mem_coe,
    mk_mem_unitSquareClasses_iff] using
    (isOpen_discrete {n : Multiplicative ℤ | Even n.toAdd}).preimage
      (continuous_normalizedValuation K)

/-- When two is nonzero, the number of unit square classes is twice the residue-field
cardinality raised to the normalized valuation of two. -/
theorem card_unitSquareClasses (h2 : (2 : K) ≠ 0) :
    Nat.card (unitSquareClasses K) = 2 * Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  have h := (unitSquareClasses K).card_mul_index
  rw [unitSquareClasses_index, card_squareClass h2] at h
  omega

/-- Away from residue characteristic two, there are two unit square classes. -/
theorem card_unitSquareClasses_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (unitSquareClasses K) = 2 := by
  rw [card_unitSquareClasses K (two_ne_zero_of_isUnit_two h2),
    natCastValuation_eq_zero_of_isUnit K _ (by exact_mod_cast h2), pow_zero, mul_one]

/-- A finite compatible extension of `ℚ₂` has `2 · #𝓀[K] ^ e(K/ℚ₂)` unit square classes. -/
theorem card_unitSquareClasses_dyadic [FinitePadicExtension K 2] :
    Nat.card (unitSquareClasses K) =
      2 * Nat.card 𝓀[K] ^ absoluteRamificationIndex K 2 := by
  rw [absoluteRamificationIndex_eq_natCastValuation]
  exact card_unitSquareClasses K _

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Over `ℚ_p`, the unit square classes are exactly the image of `ℤ_pˣ` in the square-class
quotient, using the usual inclusion of the p-adic integers. -/
theorem unitSquareClasses_padic_eq_range :
    unitSquareClasses ℚ_[p] =
      ((QuotientGroup.mk' (Subgroup.square ℚ_[p]ˣ)).comp
        (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom)).range := by
  ext c
  rw [mem_unitSquareClasses_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Units.mapEquiv (Padic.integerRingEquiv p) u, ?_⟩
    apply congrArg (QuotientGroup.mk' (Subgroup.square ℚ_[p]ˣ))
    apply Units.ext
    exact Padic.coe_integerRingEquiv_apply p (u : 𝒪[ℚ_[p]])
  · rintro ⟨u, rfl⟩
    refine ⟨Units.mapEquiv (Padic.integerRingEquiv p).symm u, ?_⟩
    apply congrArg (QuotientGroup.mk' (Subgroup.square ℚ_[p]ˣ))
    apply Units.ext
    exact Padic.coe_integerRingEquiv_symm_apply p (u : ℤ_[p])

/-- For p-adic fields the unit square-class test is the parity of the usual p-adic valuation. -/
@[simp high]
theorem mk_mem_unitSquareClasses_padic_iff (a : ℚ_[p]ˣ) :
    (a : ℚ_[p]ˣ ⧸ Subgroup.square ℚ_[p]ˣ) ∈ unitSquareClasses ℚ_[p] ↔
      Even (a : ℚ_[p]).valuation := by
  rw [mk_mem_unitSquareClasses_iff, Padic.toAdd_normalizedValuation_eq_valuation]

end Padic

/-- The dyadic field `ℚ₂` has four unit square classes, rather than two. -/
theorem card_unitSquareClasses_padic_two : Nat.card (unitSquareClasses ℚ_[2]) = 4 := by
  rw [card_unitSquareClasses_dyadic, Padic.natCard_residueField,
    absoluteRamificationIndex_padic]
  norm_num

end TauCeti
