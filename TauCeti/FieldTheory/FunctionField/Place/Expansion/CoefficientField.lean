/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.CoefficientField
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.PowerSeries

/-!
# The completed valuation ring at a place with separable residue field

Let `P` be a place of `F / k` whose residue field `F_P` is separable over `k`, and let `t` be a
uniformizer of the completion `F̂_P`. Then the completed valuation ring `𝒪̂_P` is the power-series
ring `F_P[[T]]`: every completed integral function has a unique expansion `∑ aᵢ tⁱ` with
coefficients `aᵢ` in the coefficient field of `𝒪̂_P`
(`TauCeti.Place.completionResidueFieldSection`), the lift of `F_P` to `𝒪̂_P`.

This is the identification of a completed valuation ring with `k[[T]]` at a rational place
(`TauCeti.Place.completionIntegersEquivPowerSeries`) carried over to places of arbitrary degree.
The coefficients lie in `F_P` rather than `k`, which is what makes the `t⁻¹`-coefficient of a
Laurent expansion, the residue at `P`, an element of `F_P`.

The proof views `F̂_P` as an `F_P`-algebra through the coefficient field. The completed place is
then trivial on `F_P`, and its residue field is `F_P` itself, so it is a *rational* place over
`F_P`. The uniformizer expansions at rational places
(`TauCeti.Place.powerSeriesExpansion`) and the completeness of `F̂_P`
(`TauCeti.Place.powerSeriesExpansion_surjective`) apply to it verbatim.

## Main definitions

* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`: the isomorphism
  `𝒪̂_P ≃ₐ[k] F_P[[T]]` determined by the coefficient field and the uniformizer `t`.

## Main results

* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_eq_iff`: the expansion of `x` is
  the power series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} aᵢ tⁱ` vanishes to order `n` for every
  `n`.
* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection` and
  `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_uniformizer`: the coefficient field
  expands to the constant power series and `t` to `T`.
* `TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesResidueField`: the constant
  coefficient is the value at `P`, also for functions of `F` regular at `P`.
* `TauCeti.Place.order_completionIntegersEquivPowerSeriesResidueField`: the expansion preserves
  orders.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

public section

open IsLocalRing

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)
  [Algebra.IsSeparable k P.ResidueField]

/-! ### The completion as a rational place over its coefficient field -/

/-- The residue field acts on the completion through the coefficient field. -/
private noncomputable abbrev residueFieldAlgebraCompletion :
    Algebra P.ResidueField P.Completion :=
  (P.completionPlace.integers.subtype.comp P.completionResidueFieldSection.toRingHom).toAlgebra

attribute [local instance] residueFieldAlgebraCompletion

private theorem algebraMap_residueField_completion (a : P.ResidueField) :
    algebraMap P.ResidueField P.Completion a = P.completionResidueFieldSection a := (rfl)

/-- The completed place, viewed as a place over the residue field through the coefficient field:
a nonzero element of the coefficient field is a unit of `𝒪̂_P`, so it has valuation one. -/
private noncomputable def residueFieldPlace : Place P.ResidueField P.Completion where
  valuation := P.completionPlace.valuation
  valuation_surjective := P.completionPlace.valuation_surjective
  isTrivialOn := ⟨fun a ha ↦ P.completionPlace.isUnit_iff_valuation_eq_one.mp
    ((IsUnit.mk0 a ha).map P.completionResidueFieldSection)⟩

/-- Changing the constants to the coefficient field does not change the valuation. -/
private theorem residueFieldPlace_valuation :
    P.residueFieldPlace.valuation = P.completionPlace.valuation := (rfl)

/-- Changing the constants to the coefficient field does not change the filtration. -/
private theorem mem_residueFieldPlace_filtration_iff {a : ℤ} {x : P.Completion} :
    x ∈ P.residueFieldPlace.filtration a ↔ x ∈ P.completionPlace.filtration a := by
  simp only [mem_filtration_iff, residueFieldPlace_valuation]

/-- Changing the constants to the coefficient field does not change orders. -/
private theorem ord_residueFieldPlace (x : P.Completion) :
    P.residueFieldPlace.ord x = P.completionPlace.ord x := by
  simp only [ord_def, residueFieldPlace_valuation]

/-- Changing the constants to the coefficient field does not change the valuation ring. -/
private theorem residueFieldPlace_integers :
    P.residueFieldPlace.integers = P.completionPlace.integers :=
  SetLike.ext fun _ ↦ by simp only [mem_integers_iff, residueFieldPlace_valuation]

/-- The two views of the completed valuation ring, as rings of functions with the same
underlying elements. -/
private noncomputable def integersEquivResidueFieldPlace :
    P.completionPlace.integers ≃+* P.residueFieldPlace.integers :=
  RingEquiv.subringCongr (congrArg ValuationSubring.toSubring P.residueFieldPlace_integers.symm)

@[simp]
private theorem coe_integersEquivResidueFieldPlace (x : P.completionPlace.integers) :
    (P.integersEquivResidueFieldPlace x : P.Completion) = x := (rfl)

@[simp]
private theorem coe_integersEquivResidueFieldPlace_symm (x : P.residueFieldPlace.integers) :
    (P.integersEquivResidueFieldPlace.symm x : P.Completion) = x := (rfl)

/-- Changing the constants to the coefficient field does not change when two integral functions
have the same residue. -/
private theorem residue_integersEquivResidueFieldPlace_eq_iff
    {y z : P.completionPlace.integers} :
    residue P.residueFieldPlace.integers (P.integersEquivResidueFieldPlace y) =
        residue P.residueFieldPlace.integers (P.integersEquivResidueFieldPlace z) ↔
      residue P.completionPlace.integers y = residue P.completionPlace.integers z := by
  simp only [residue_eq_iff_sub_mem_filtration_one, coe_integersEquivResidueFieldPlace,
    mem_residueFieldPlace_filtration_iff]

/-- The coefficient field is the image of the constants of the completed place over `F_P`. -/
private theorem integersEquivResidueFieldPlace_completionResidueFieldSection
    (a : P.ResidueField) :
    P.integersEquivResidueFieldPlace (P.completionResidueFieldSection a) =
      algebraMap P.ResidueField P.residueFieldPlace.integers a :=
  Subtype.ext (P.residueFieldPlace.coe_algebraMap_constants a).symm

/-- Over its coefficient field, the completed place is rational: reduction of the coefficient
field is the identification of `F_P` with the residue field of the completion. -/
private theorem degree_residueFieldPlace : P.residueFieldPlace.degree = 1 := by
  refine P.residueFieldPlace.degree_eq_one_iff_algebraMap_surjective.mpr fun y ↦ ?_
  obtain ⟨z, rfl⟩ := residue_surjective y
  let w := P.integersEquivResidueFieldPlace.symm z
  refine ⟨P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers w), ?_⟩
  have h := P.residue_integersEquivResidueFieldPlace_eq_iff.mpr
    (P.residue_completionResidueFieldSection
      (P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers w)) |>.trans
      (P.residueFieldEquivCompletion.apply_symm_apply _))
  rwa [integersEquivResidueFieldPlace_completionResidueFieldSection,
    RingEquiv.apply_symm_apply, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply] at h

variable {t : P.Completion} (ht : P.completionPlace.ord t = 1)
include ht

private theorem ord_residueFieldPlace_uniformizer : P.residueFieldPlace.ord t = 1 := by
  rwa [ord_residueFieldPlace]

/-- The uniformizer expansion over the coefficient field is a bijection onto `F_P[[T]]`. -/
private theorem bijective_residueFieldPlace_powerSeriesExpansion :
    Function.Bijective (P.residueFieldPlace.powerSeriesExpansion P.degree_residueFieldPlace
      (P.ord_residueFieldPlace_uniformizer ht)) :=
  ⟨P.residueFieldPlace.powerSeriesExpansion_injective _ _,
    P.residueFieldPlace.powerSeriesExpansion_surjective _ _ fun _ hg ↦ by
      simp only [mem_residueFieldPlace_filtration_iff] at hg ⊢
      exact P.exists_forall_sub_mem_completionPlace_filtration hg⟩

/-! ### Power-series expansions with coefficients in the residue field -/

/-- **The completed valuation ring at a place with separable residue field is `F_P[[T]]`.** The
isomorphism sends a completed integral function to its expansion `∑ aᵢ Tⁱ` in the uniformizer
`t`, with coefficients `aᵢ ∈ F_P` read in the coefficient field
`TauCeti.Place.completionResidueFieldSection`; it is characterized by
`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_eq_iff`. -/
noncomputable def completionIntegersEquivPowerSeriesResidueField :
    P.completionPlace.integers ≃ₐ[k] PowerSeries P.ResidueField :=
  AlgEquiv.ofRingEquiv (f := P.integersEquivResidueFieldPlace.trans
    (AlgEquiv.ofBijective _ (P.bijective_residueFieldPlace_powerSeriesExpansion ht)).toRingEquiv)
    fun c ↦ by
      have h : P.integersEquivResidueFieldPlace (algebraMap k _ c) =
          algebraMap P.ResidueField _ (algebraMap k P.ResidueField c) :=
        Subtype.ext (by
          rw [coe_integersEquivResidueFieldPlace, P.residueFieldPlace.coe_algebraMap_constants,
            algebraMap_residueField_completion, P.completionResidueFieldSection.commutes c])
      simp [h, PowerSeries.algebraMap_apply]

private theorem completionIntegersEquivPowerSeriesResidueField_apply
    (x : P.completionPlace.integers) :
    P.completionIntegersEquivPowerSeriesResidueField ht x =
      P.residueFieldPlace.powerSeriesExpansion P.degree_residueFieldPlace
        (P.ord_residueFieldPlace_uniformizer ht) (P.integersEquivResidueFieldPlace x) := (rfl)

/-- **The expansion is characterized by its truncations**: the expansion of `x` is the power
series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} aᵢ tⁱ` vanishes to order `n` for every `n`, the
coefficients `aᵢ` being read in the coefficient field. -/
theorem completionIntegersEquivPowerSeriesResidueField_eq_iff (x : P.completionPlace.integers)
    (f : PowerSeries P.ResidueField) :
    P.completionIntegersEquivPowerSeriesResidueField ht x = f ↔
      ∀ n : ℕ, (x : P.Completion) - ∑ i : Fin n,
        (P.completionResidueFieldSection (PowerSeries.coeff i f) : P.Completion) * t ^ (i : ℕ) ∈
          P.completionPlace.filtration n := by
  rw [completionIntegersEquivPowerSeriesResidueField_apply]
  constructor
  · rintro rfl n
    have h := P.residueFieldPlace.sub_sum_coeff_powerSeriesExpansion_mem_filtration
      P.degree_residueFieldPlace (P.ord_residueFieldPlace_uniformizer ht) n
      (P.integersEquivResidueFieldPlace x)
    simpa only [coe_integersEquivResidueFieldPlace, algebraMap_residueField_completion,
      mem_residueFieldPlace_filtration_iff] using h
  · intro h
    ext n
    rw [P.residueFieldPlace.coeff_powerSeriesExpansion _ _ (n + 1) _ ⟨n, by omega⟩]
    refine congrFun ((P.residueFieldPlace.truncatedExpansion_eq_iff _ _ (n + 1) _
      fun i ↦ PowerSeries.coeff i f).mpr ?_) ⟨n, by omega⟩
    simpa only [coe_integersEquivResidueFieldPlace, algebraMap_residueField_completion,
      mem_residueFieldPlace_filtration_iff] using h (n + 1)

/-- Removing the first `n` terms of the expansion of a completed integral function leaves a
function vanishing to order at least `n`. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration
    (x : P.completionPlace.integers) (n : ℕ) :
    (x : P.Completion) - ∑ i : Fin n, (P.completionResidueFieldSection
      (PowerSeries.coeff i (P.completionIntegersEquivPowerSeriesResidueField ht x)) :
        P.Completion) * t ^ (i : ℕ) ∈ P.completionPlace.filtration n :=
  (P.completionIntegersEquivPowerSeriesResidueField_eq_iff ht x _).mp rfl n

/-- The inverse isomorphism realizes a power series over the residue field to every finite
order. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_symm_mem_filtration
    (f : PowerSeries P.ResidueField) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeriesResidueField ht).symm f : P.Completion) -
      ∑ i : Fin n, (P.completionResidueFieldSection (PowerSeries.coeff i f) : P.Completion) *
        t ^ (i : ℕ) ∈ P.completionPlace.filtration n :=
  (P.completionIntegersEquivPowerSeriesResidueField_eq_iff ht _ f).mp
    (AlgEquiv.apply_symm_apply _ f) n

/-- The coefficient field expands to the constant power series. -/
@[simp]
theorem completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection
    (a : P.ResidueField) :
    P.completionIntegersEquivPowerSeriesResidueField ht (P.completionResidueFieldSection a) =
      PowerSeries.C a := by
  have h : P.integersEquivResidueFieldPlace (P.completionResidueFieldSection a) =
      algebraMap P.ResidueField _ a :=
    Subtype.ext (by rw [coe_integersEquivResidueFieldPlace, coe_algebraMap_constants,
      algebraMap_residueField_completion])
  rw [completionIntegersEquivPowerSeriesResidueField_apply, h, AlgHom.commutes,
    PowerSeries.algebraMap_eq]

/-- The uniformizer expands as the power-series variable. -/
@[simp]
theorem completionIntegersEquivPowerSeriesResidueField_uniformizer :
    P.completionIntegersEquivPowerSeriesResidueField ht
      ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ = PowerSeries.X := by
  rw [completionIntegersEquivPowerSeriesResidueField_apply]
  exact P.residueFieldPlace.powerSeriesExpansion_uniformizer _ _

/-- The constant coefficient of the expansion is the value at `P`, read in `F_P`. -/
@[simp]
theorem constantCoeff_completionIntegersEquivPowerSeriesResidueField
    (x : P.completionPlace.integers) :
    PowerSeries.constantCoeff (P.completionIntegersEquivPowerSeriesResidueField ht x) =
      P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers x) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AlgEquiv.eq_symm_apply,
    ← residue_completionResidueFieldSection, eq_comm]
  apply P.completionPlace.residue_eq_iff_sub_mem_filtration_one.mpr
  simpa using P.sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration ht x 1

/-- The constant coefficient of the expansion of a function regular at `P` is its value at `P`. -/
theorem constantCoeff_completionIntegersEquivPowerSeriesResidueField_completionIntegersEmbedding
    (x : P.integers) :
    PowerSeries.constantCoeff (P.completionIntegersEquivPowerSeriesResidueField ht
      (P.completionIntegersEmbedding x)) = residue P.integers x := by
  simp

/-- Vanishing to order `n` is vanishing of the first `n` coefficients of the expansion. -/
theorem mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField (n : ℕ)
    (x : P.completionPlace.integers) :
    (x : P.Completion) ∈ P.completionPlace.filtration n ↔
      (n : ℕ∞) ≤ (P.completionIntegersEquivPowerSeriesResidueField ht x).order := by
  rw [← P.mem_residueFieldPlace_filtration_iff, ← coe_integersEquivResidueFieldPlace,
    completionIntegersEquivPowerSeriesResidueField_apply]
  exact P.residueFieldPlace.mem_filtration_iff_le_order_powerSeriesExpansion _ _ n _

/-- The order of a nonzero completed integral function is the first nonzero degree of its
expansion. -/
theorem order_completionIntegersEquivPowerSeriesResidueField (x : P.completionPlace.integers)
    (hx : x ≠ 0) :
    (P.completionIntegersEquivPowerSeriesResidueField ht x).order =
      ((P.completionPlace.ord (x : P.Completion)).toNat : ℕ∞) := by
  rw [completionIntegersEquivPowerSeriesResidueField_apply, ← ord_residueFieldPlace,
    ← coe_integersEquivResidueFieldPlace]
  exact P.residueFieldPlace.order_powerSeriesExpansion _ _ _
    ((map_ne_zero_iff _ P.integersEquivResidueFieldPlace.injective).mpr hx)

end TauCeti.Place
