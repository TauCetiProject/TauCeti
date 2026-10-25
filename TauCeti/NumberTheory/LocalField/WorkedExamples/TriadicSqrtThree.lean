/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Basic
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
public import TauCeti.NumberTheory.LocalField.Norm.Herbrand
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.RingTheory.AdjoinRoot
import TauCeti.FieldTheory.Galois.SquareRoot
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The tame quadratic extension `ℚ₃(√3)` and the Herbrand shift of the norm

Adjoining a root of `X² - 3` gives a totally ramified quadratic extension of `ℚ₃`. Since the
residue characteristic `3` does not divide the ramification index `2`, it is tamely ramified.
Its root `√3` is a uniformizer generating the ring of integers, and the nonidentity automorphism
moves it by `-2√3`, of valuation one. So the lower ramification groups are the whole Galois group
at index zero and trivial from index one, the different and discriminant exponents are both one,
and the integral inverse Herbrand function is `ψℕ(n) = 2n`.

This is the standard witness that the norm does not respect the unit filtration without a shift.
The unit `4 = 1 + (√3)²` lies in `U(L,2)`, but its norm `16 = 1 + 3 · 5` is not in `U(ℚ₃,2)`,
so `N(U(L,2)) ⊄ U(ℚ₃,2)`. The shifted inclusion `N(U(L, ψℕ(n))) ⊆ U(ℚ₃, n)` of
`TauCeti.map_normUnits_unitFiltration_psiNat_le` reads `N(U(L, 2n)) ⊆ U(ℚ₃, n)` here, and at
`n = 1` it carries the same unit `4 ∈ U(L,2)` to `16 ∈ U(ℚ₃,1)`.

## Main definitions

* `TauCeti.TriadicSqrtThree`: the local field `ℚ₃(√3)`.
* `TauCeti.TriadicSqrtThree.sqrtThree`: its distinguished square root of three.
* `TauCeti.TriadicSqrtThree.integerSqrtThree`: the same generator in its ring of integers.

## Main results

* `TauCeti.TriadicSqrtThree.irreducible_integerSqrtThree` and
  `TauCeti.TriadicSqrtThree.adjoin_integerSqrtThree_eq_top`: the generator is a uniformizer and
  generates the ring of integers.
* `TauCeti.TriadicSqrtThree.ramificationIndex_eq_two`,
  `TauCeti.TriadicSqrtThree.inertiaDegree_eq_one`,
  `TauCeti.TriadicSqrtThree.natCard_residueField` and
  `TauCeti.TriadicSqrtThree.isTamelyRamified`: the extension is totally and tamely ramified.
* `TauCeti.TriadicSqrtThree.lowerRamificationGroup_eq`: the complete lower filtration.
* `TauCeti.TriadicSqrtThree.differentExponent_eq_one` and
  `TauCeti.TriadicSqrtThree.discriminantExponent_eq_one`: both exponents are one.
* `TauCeti.TriadicSqrtThree.psiNat_eq`: the integral inverse Herbrand function is `n ↦ 2n`.
* `TauCeti.TriadicSqrtThree.not_map_normUnits_unitFiltration_two_le`: the explicit failure
  `N(U(L,2)) ⊄ U(ℚ₃,2)`, witnessed by the unit `4`.
* `TauCeti.TriadicSqrtThree.map_normUnits_unitFiltration_two_mul_le`: the shifted inclusion
  `N(U(L,2n)) ⊆ U(ℚ₃,n)`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1–3 and Chapter V, §§2–3 and §6.

## Formal sources

The construction is adapted from
`TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Two`.
-/

public section
noncomputable section

open Polynomial ValuativeRel IsLocalRing
open scoped IntermediateField

namespace TauCeti

/-- The local field `ℚ₃(√3)`, obtained by adjoining a root of `X² - 3` to `ℚ₃`. -/
def TriadicSqrtThree : Type := AdjoinRoot (X ^ 2 - C 3 : ℚ_[3][X])

namespace TriadicSqrtThree

local instance : Fact (Irreducible (X ^ 2 - C 3 : ℚ_[3][X])) :=
  ⟨by
    have h := X_pow_sub_C_irreducible_of_irreducible (R := ℤ_[3]) (K := ℚ_[3])
      PadicInt.irreducible_p two_ne_zero
    rw [map_natCast, Nat.cast_ofNat] at h
    exact h⟩

instance : Field TriadicSqrtThree :=
  inferInstanceAs (Field (AdjoinRoot (X ^ 2 - C 3 : ℚ_[3][X])))

instance : Algebra ℚ_[3] TriadicSqrtThree :=
  inferInstanceAs (Algebra ℚ_[3] (AdjoinRoot (X ^ 2 - C 3 : ℚ_[3][X])))

private def powerBasis : PowerBasis ℚ_[3] TriadicSqrtThree :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 2 - C 3 : ℚ_[3][X])).ne_zero

instance : FiniteDimensional ℚ_[3] TriadicSqrtThree := powerBasis.finite

instance : CharZero TriadicSqrtThree :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[3] TriadicSqrtThree).injective

instance : ValuativeRel TriadicSqrtThree := algebraicExtensionValuativeRel ℚ_[3] TriadicSqrtThree

instance : TopologicalSpace TriadicSqrtThree :=
  algebraicExtensionNormedFieldTopology ℚ_[3] TriadicSqrtThree

instance : ValuativeExtension ℚ_[3] TriadicSqrtThree :=
  algebraicExtension_valuativeExtension ℚ_[3] TriadicSqrtThree

instance : IsNonarchimedeanLocalField TriadicSqrtThree :=
  finiteExtension_isNonarchimedeanLocalField ℚ_[3] TriadicSqrtThree

/-- The square root `√3` generating `ℚ₃(√3)`, the class of `X`. -/
def sqrtThree : TriadicSqrtThree := AdjoinRoot.root (X ^ 2 - C 3 : ℚ_[3][X])

/-- The defining equation of the generator `√3`. -/
@[simp]
theorem sqrtThree_sq : sqrtThree ^ 2 = 3 :=
  (TauCeti.AdjoinRoot.root_sq (3 : ℚ_[3])).trans (map_ofNat _ 3)

/-- The minimal polynomial of `√3` over `ℚ₃` is `X² - 3`. -/
@[simp]
theorem minpoly_sqrtThree : minpoly ℚ_[3] sqrtThree = X ^ 2 - C 3 :=
  (AdjoinRoot.minpoly_root
    (Fact.out : Irreducible (X ^ 2 - C 3 : ℚ_[3][X])).ne_zero).trans
    (by simp [leadingCoeff_X_pow_sub_C (by norm_num : 0 < (2 : ℕ))])

/-- `√3` generates `ℚ₃(√3)` as a field extension of `ℚ₃`. -/
theorem adjoin_sqrtThree_eq_top : ℚ_[3]⟮sqrtThree⟯ = ⊤ :=
  IntermediateField.adjoin_root_eq_top _

/-- The degree of `ℚ₃(√3)/ℚ₃` is two. -/
@[simp]
theorem finrank_eq_two : Module.finrank ℚ_[3] TriadicSqrtThree = 2 := by
  rw [powerBasis.finrank, powerBasis, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

instance : Algebra.IsQuadraticExtension ℚ_[3] TriadicSqrtThree := ⟨finrank_eq_two⟩

private theorem integral_sqrtThree : IsIntegral 𝒪[ℚ_[3]] sqrtThree :=
  ⟨X ^ 2 - C 3, by monicity!, by simp [map_ofNat]⟩

/-- `√3`, viewed as an element of the ring of integers. -/
def integerSqrtThree : 𝒪[TriadicSqrtThree] :=
  ⟨sqrtThree, (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation ℚ_[3])) _).1 integral_sqrtThree⟩

@[simp]
theorem coe_integerSqrtThree : (integerSqrtThree : TriadicSqrtThree) = sqrtThree := (rfl)

@[simp]
private theorem coe_ofNat_two : ((2 : 𝒪[TriadicSqrtThree]) : TriadicSqrtThree) = 2 :=
  map_ofNat (Subring.subtype 𝒪[TriadicSqrtThree]) 2

@[simp]
private theorem coe_ofNat_three : ((3 : 𝒪[TriadicSqrtThree]) : TriadicSqrtThree) = 3 :=
  map_ofNat (Subring.subtype 𝒪[TriadicSqrtThree]) 3

/-- The integer generator `√3` is a root of `X² - 3` over `𝒪[ℚ₃]`. -/
theorem isRoot_integerSqrtThree :
    ((X ^ 2 - C 3 : 𝒪[ℚ_[3]][X]).map
      (algebraMap 𝒪[ℚ_[3]] 𝒪[TriadicSqrtThree])).IsRoot integerSqrtThree := by
  apply Subtype.ext
  simp [map_ofNat]

/-- The polynomial `X² - 3` is Eisenstein over the integer ring of `ℚ₃`. -/
theorem isEisensteinAt_X_sq_sub_three :
    (X ^ 2 - C 3 : 𝒪[ℚ_[3]][X]).IsEisensteinAt 𝓂[ℚ_[3]] :=
  isEisensteinAt_X_pow_sub_C_of_irreducible (Padic.irreducible_natCast_self 3) (by decide)

/-- `√3` is a uniformizer of the integer ring of `ℚ₃(√3)`. -/
theorem irreducible_integerSqrtThree : Irreducible integerSqrtThree :=
  irreducible_of_eisenstein_adjoin_eq_top _ isEisensteinAt_X_sq_sub_three _
    isRoot_integerSqrtThree adjoin_sqrtThree_eq_top

/-- The ring of integers is `𝒪[ℚ₃][√3]`. -/
theorem adjoin_integerSqrtThree_eq_top : Algebra.adjoin 𝒪[ℚ_[3]] {integerSqrtThree} = ⊤ :=
  algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top
    isEisensteinAt_X_sq_sub_three isRoot_integerSqrtThree adjoin_sqrtThree_eq_top

/-- The ramification index of `ℚ₃(√3)/ℚ₃` is two. -/
@[simp]
theorem ramificationIndex_eq_two : ramificationIndex ℚ_[3] TriadicSqrtThree = 2 := by
  simpa using ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top
    _ isEisensteinAt_X_sq_sub_three _ isRoot_integerSqrtThree adjoin_sqrtThree_eq_top

/-- The residue degree of `ℚ₃(√3)/ℚ₃` is one. -/
@[simp]
theorem inertiaDegree_eq_one : inertiaDegree ℚ_[3] TriadicSqrtThree = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _ isEisensteinAt_X_sq_sub_three _
    isRoot_integerSqrtThree adjoin_sqrtThree_eq_top

/-- `ℚ₃(√3)/ℚ₃` is totally ramified. -/
theorem isTotallyRamified : IsTotallyRamified ℚ_[3] TriadicSqrtThree :=
  (isTotallyRamified_iff_inertiaDegree_eq_one _ _).2 inertiaDegree_eq_one

/-- The residue field of `ℚ₃(√3)` has three elements. -/
@[simp high]
theorem natCard_residueField : Nat.card 𝓀[TriadicSqrtThree] = 3 := by
  rw [TauCeti.natCard_residueField (K := ℚ_[3]), inertiaDegree_eq_one,
    Padic.natCard_residueField, pow_one]

/-- The extension `ℚ₃(√3)/ℚ₃` is ramified. -/
theorem not_isUnramified : ¬IsUnramified ℚ_[3] TriadicSqrtThree := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_eq_two]
  norm_num

/-- The extension `ℚ₃(√3)/ℚ₃` is tamely ramified: its ramification index `2` is a unit in the
residue field `𝔽₃`. -/
theorem isTamelyRamified : IsTamelyRamified ℚ_[3] TriadicSqrtThree := by
  rw [isTamelyRamified_iff_natCast_ne_zero, ramificationIndex_eq_two, Nat.cast_ofNat,
    ← map_ofNat (residue 𝒪[ℚ_[3]]) 2]
  exact ((Padic.isUnit_two_integerRing (p := 3) (by norm_num)).map _).ne_zero

/-! ### The automorphism and the lower filtration -/

/-- Every nonidentity automorphism sends `√3` to `-√3`. -/
@[simp]
theorem apply_sqrtThree_of_ne_one {σ : TriadicSqrtThree ≃ₐ[ℚ_[3]] TriadicSqrtThree}
    (hσ : σ ≠ 1) : σ sqrtThree = -sqrtThree := by
  refine (AlgEquiv.apply_eq_or_eq_neg_of_sq_eq σ
    (c := (3 : ℚ_[3])) (by simpa only [map_ofNat] using sqrtThree_sq)).resolve_left fun h ↦ hσ ?_
  exact AlgEquiv.coe_toAlgHom_injective (AdjoinRoot.algHom_ext h)

/-- The displacement of any nonidentity automorphism at the integral generator has valuation
one: `v(-√3 - √3) = v(2) + v(√3) = 0 + 1`, since `2` is a unit in residue characteristic `3`. -/
@[simp]
theorem addVal_smul_sub_integerSqrtThree_of_ne_one
    {σ : TriadicSqrtThree ≃ₐ[ℚ_[3]] TriadicSqrtThree} (hσ : σ ≠ 1) :
    IsDiscreteValuationRing.addVal 𝒪[TriadicSqrtThree]
      (σ • integerSqrtThree - integerSqrtThree) = 1 := by
  have h : σ • integerSqrtThree - integerSqrtThree =
      -(algebraMap 𝒪[ℚ_[3]] 𝒪[TriadicSqrtThree] 2 * integerSqrtThree) := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AlgEquiv.coe_smul_integerRing, coe_integerSqrtThree,
      apply_sqrtThree_of_ne_one hσ, Subring.coe_neg, Subring.coe_mul, map_ofNat, coe_ofNat_two]
    ring
  have h2 := IsDiscreteValuationRing.addVal_eq_zero_of_unit
    (Padic.isUnit_two_integerRing (p := 3) (by norm_num)).unit
  rw [IsUnit.unit_spec] at h2
  rw [h, AddValuation.map_neg, IsDiscreteValuationRing.addVal_mul, addVal_algebraMap, h2,
    IsDiscreteValuationRing.addVal_uniformizer irreducible_integerSqrtThree]
  simp

/-- Every nonidentity automorphism has lower index one. -/
@[simp]
theorem lowerIndex_of_ne_one {σ : TriadicSqrtThree ≃ₐ[ℚ_[3]] TriadicSqrtThree} (hσ : σ ≠ 1) :
    TauCeti.IsLocalRing.lowerIndex 𝒪[TriadicSqrtThree] σ = 1 := by
  rw [TauCeti.IsLocalRing.lowerIndex_eq_addVal_of_adjoin_singleton_eq_top
    adjoin_integerSqrtThree_eq_top, addVal_smul_sub_integerSqrtThree_of_ne_one hσ]

/-- The lower ramification groups are the whole Galois group through index zero and trivial
from index one, including the negative-index convention. -/
@[simp]
theorem lowerRamificationGroup_eq (i : ℤ) :
    LocalFieldsRamification.lowerRamificationGroup ℚ_[3] TriadicSqrtThree i =
      if i ≤ 0 then ⊤ else ⊥ := by
  classical
  ext σ
  rw [LocalFieldsRamification.mem_lowerRamificationGroup_iff_le_lowerIndex]
  by_cases hσ : σ = 1
  · subst σ
    simp
  · rw [lowerIndex_of_ne_one hσ]
    split_ifs with hi
    · simp only [Subgroup.mem_top, iff_true]
      norm_cast
      omega
    · simp only [Subgroup.mem_bot, hσ, iff_false, not_le]
      norm_cast
      omega

/-- The different exponent of the tame extension `ℚ₃(√3)/ℚ₃` is `e - 1 = 1`. -/
@[simp]
theorem differentExponent_eq_one : differentExponent ℚ_[3] TriadicSqrtThree = 1 := by
  simpa using (differentExponent_eq_ramificationIndex_sub_one_iff ℚ_[3] TriadicSqrtThree).2
    isTamelyRamified

/-- The local discriminant exponent of `ℚ₃(√3)/ℚ₃` is one. -/
@[simp]
theorem discriminantExponent_eq_one : discriminantExponent ℚ_[3] TriadicSqrtThree = 1 := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, inertiaDegree_eq_one,
    differentExponent_eq_one, one_mul]

/-- The integral inverse Herbrand function of `ℚ₃(√3)/ℚ₃` doubles every depth: the unique
lower break is at zero, after which the Herbrand function has slope one half. -/
@[simp]
theorem psiNat_eq (n : ℕ) : LocalFieldsRamification.psiNat ℚ_[3] TriadicSqrtThree n = 2 * n := by
  have h := LocalFieldsRamification.psiNat_eq_add_card_mul_sub ℚ_[3] TriadicSqrtThree
    (t := 0) (v := n) (by simp) (by simp) n.zero_le
  rwa [LocalFieldsRamification.natCard_lowerRamificationGroup_zero, ramificationIndex_eq_two,
    zero_add, Nat.sub_zero] at h

/-! ### The norm on the unit filtration -/

/-- The norm of `4` is `4² = 16`. -/
@[simp]
theorem norm_four : Algebra.norm ℚ_[3] (4 : TriadicSqrtThree) = 16 := by
  rw [← map_ofNat (algebraMap ℚ_[3] TriadicSqrtThree) 4, Algebra.norm_algebraMap, finrank_eq_two]
  norm_num

/-- The unit `4 = 1 + (√3)²` lies in `U(L,2)`. -/
theorem mk0_four_mem_unitFiltration_two :
    Units.mk0 (4 : TriadicSqrtThree) (by norm_num) ∈ unitFiltration TriadicSqrtThree 2 := by
  rw [mem_unitFiltration_succ_valuation 1 _ _ irreducible_integerSqrtThree, coe_integerSqrtThree,
    sqrtThree_sq, Units.val_mk0]
  norm_num

/-- The unit `16 = 1 + 3 · 5` of `ℚ₃` does not lie in `U(ℚ₃,2)`. -/
theorem mk0_sixteen_not_mem_unitFiltration_two :
    Units.mk0 (16 : ℚ_[3]) (by norm_num) ∉ unitFiltration ℚ_[3] 2 := by
  rw [mem_unitFiltration_iff_exists]
  rintro ⟨u, hu, hu16⟩
  have hu' : (u : 𝒪[ℚ_[3]]) = 16 := by
    apply Subtype.ext
    rw [hu16, Units.val_mk0]
    exact (map_ofNat (Subring.subtype 𝒪[ℚ_[3]]) 16).symm
  have hπ := Padic.irreducible_natCast_self 3
  rw [hu', hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  -- `3² ∣ 3 · 5` would force `3 ∣ 5`, but `5` is a unit of `𝒪[ℚ₃]`.
  have h5 : IsUnit (5 : 𝒪[ℚ_[3]]) := by
    simpa using Padic.isUnit_intCast_integerRing (p := 3) (m := 5) (by norm_num)
  have h : ((3 : ℕ) : 𝒪[ℚ_[3]]) * 3 ∣ (3 : ℕ) * 5 := by
    convert hu using 1 <;> push_cast <;> ring
  exact hπ.not_isUnit (isUnit_of_dvd_unit
    (by simpa using (mul_dvd_mul_iff_left hπ.ne_zero).1 h) h5)

/-- The norm carries the unit `4` of `ℚ₃(√3)` to the unit `16` of `ℚ₃`. -/
@[simp]
theorem normUnits_mk0_four :
    Algebra.normUnits ℚ_[3] (Units.mk0 (4 : TriadicSqrtThree) (by norm_num)) =
      Units.mk0 (16 : ℚ_[3]) (by norm_num) :=
  Units.ext (by rw [Algebra.coe_normUnits, Units.val_mk0, Units.val_mk0, norm_four])

/-- **The unshifted norm inclusion fails.** In the tame quadratic extension `ℚ₃(√3)/ℚ₃` the
norm does not carry `U(L,2)` into `U(ℚ₃,2)`: the norm of `4 ∈ U(L,2)` is `16 ∉ U(ℚ₃,2)`. -/
theorem not_map_normUnits_unitFiltration_two_le :
    ¬(unitFiltration TriadicSqrtThree 2).map (Algebra.normUnits ℚ_[3]) ≤
      unitFiltration ℚ_[3] 2 := fun h ↦
  mk0_sixteen_not_mem_unitFiltration_two <| normUnits_mk0_four ▸
    h (Subgroup.mem_map_of_mem _ mk0_four_mem_unitFiltration_two)

/-- **The shifted norm inclusion.** Since `ψℕ(n) = 2n` for `ℚ₃(√3)/ℚ₃`, the norm carries
`U(L, 2n)` into `U(ℚ₃, n)`. -/
theorem map_normUnits_unitFiltration_two_mul_le (n : ℕ) :
    (unitFiltration TriadicSqrtThree (2 * n)).map (Algebra.normUnits ℚ_[3]) ≤
      unitFiltration ℚ_[3] n := by
  simpa using map_normUnits_unitFiltration_psiNat_le ℚ_[3] TriadicSqrtThree n

end TriadicSqrtThree

end TauCeti
