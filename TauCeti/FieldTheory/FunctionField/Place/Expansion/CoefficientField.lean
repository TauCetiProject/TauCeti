/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.CoefficientField
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.PowerSeries

/-!
# The completed valuation ring at a place is a power-series ring over the residue field

Let `P` be a place of `F / k`, let `s : F_P → 𝒪̂_P` be a coefficient field of the completed
valuation ring, that is, a ring embedding of the residue field `F_P` lifting it, and let `t` be a
uniformizer of the completion `F̂_P`. Then `𝒪̂_P` is the power-series ring `F_P[[T]]`: every
completed integral function has a unique expansion `∑ s(aᵢ) tⁱ` with coefficients `aᵢ ∈ F_P`.

Coefficient fields exist at every place (`TauCeti.Place.exists_completionResidueFieldSection`), so
`𝒪̂_P ≃ F_P[[T]]` as rings at every place. When `F_P` is separable over `k` there is a unique
coefficient field over `k` (`TauCeti.Place.completionResidueFieldSection`), and the expansion is a
`k`-algebra isomorphism. When `F_P` is inseparable over `k` there may be no coefficient field over
`k`, and then `𝒪̂_P` is not `k`-isomorphic to `F_P[[T]]` at all
(`TauCeti.Place.isEmpty_completionIntegers_algEquiv_powerSeries`); the ring isomorphism still
exists, but it depends on the choice of the coefficient field.

This is the identification of a completed valuation ring with `k[[T]]` at a rational place
(`TauCeti.Place.completionIntegersEquivPowerSeries`) carried over to places of arbitrary degree.
The coefficients lie in `F_P` rather than `k`, which is what makes the `t⁻¹`-coefficient of a
Laurent expansion, the residue at `P`, an element of `F_P`.

The proof views `F̂_P` as an `F_P`-algebra through the coefficient field. The completed place is
then trivial on `F_P`, and its residue field is `F_P` itself, so it is a *rational* place over
`F_P`. The uniformizer expansions at rational places (`TauCeti.Place.powerSeriesExpansion`) and
the completeness of `F̂_P` (`TauCeti.Place.powerSeriesExpansion_surjective`) apply to it verbatim.

## Main definitions

* `TauCeti.Place.completionIntegersEquivPowerSeriesOfSection`: the ring isomorphism
  `𝒪̂_P ≃ F_P[[T]]` determined by a coefficient field `s` and a uniformizer `t`.
* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`: the `k`-algebra isomorphism
  `𝒪̂_P ≃ₐ[k] F_P[[T]]` at a place with separable residue field, through the coefficient field over
  `k`.

## Main results

* `TauCeti.Place.completionIntegersEquivPowerSeriesOfSection_eq_iff`: the expansion of `x` is the
  power series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} s(aᵢ) tⁱ` vanishes to order `n` for every `n`.
* `TauCeti.Place.completionIntegersEquivPowerSeriesOfSection_section` and
  `TauCeti.Place.completionIntegersEquivPowerSeriesOfSection_uniformizer`: the coefficient field
  expands to the constant power series and `t` to `T`.
* `TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesOfSection`: the constant
  coefficient is the value at `P`.
* `TauCeti.Place.order_completionIntegersEquivPowerSeriesOfSection`: the expansion preserves
  orders.
* `TauCeti.Place.nonempty_completionIntegers_ringEquiv_powerSeries`: at every place, separable
  residue field or not, `𝒪̂_P` is isomorphic to `F_P[[T]]`.

The same statements hold for the `k`-algebra isomorphism at a place with separable residue field,
under the names with `ResidueField` in place of `OfSection`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

public section

open IsLocalRing

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-! ### The completion as a rational place over a coefficient field -/

section RationalPlace

/- The construction views `F̂_P` as an `F_P`-algebra through the coefficient field `s`. It takes
this algebra structure as an instance, identified with `s` by `hA`, so that the public statements
below, which do not mention it, can supply it locally. -/
variable [Algebra P.ResidueField P.Completion] {s : P.ResidueField →+* P.completionPlace.integers}
  (hA : ∀ a, algebraMap P.ResidueField P.Completion a = s a)

/-- The completed place, viewed as a place over the residue field through the coefficient field:
a nonzero element of the coefficient field is a unit of `𝒪̂_P`, so it has valuation one. -/
private noncomputable def residueFieldPlace : Place P.ResidueField P.Completion where
  valuation := P.completionPlace.valuation
  valuation_surjective := P.completionPlace.valuation_surjective
  isTrivialOn := ⟨fun a ha ↦ by
    rw [hA]
    exact P.completionPlace.isUnit_iff_valuation_eq_one.mp ((IsUnit.mk0 a ha).map s)⟩

/-- Changing the constants to the coefficient field does not change the valuation. -/
private theorem residueFieldPlace_valuation :
    (P.residueFieldPlace hA).valuation = P.completionPlace.valuation := (rfl)

/-- Changing the constants to the coefficient field does not change the filtration. -/
private theorem mem_residueFieldPlace_filtration_iff {a : ℤ} {x : P.Completion} :
    x ∈ (P.residueFieldPlace hA).filtration a ↔ x ∈ P.completionPlace.filtration a := by
  simp only [mem_filtration_iff, residueFieldPlace_valuation]

/-- Changing the constants to the coefficient field does not change orders. -/
private theorem ord_residueFieldPlace (x : P.Completion) :
    (P.residueFieldPlace hA).ord x = P.completionPlace.ord x := by
  simp only [ord_def, residueFieldPlace_valuation]

/-- Changing the constants to the coefficient field does not change the valuation ring. -/
private theorem residueFieldPlace_integers :
    (P.residueFieldPlace hA).integers = P.completionPlace.integers :=
  SetLike.ext fun _ ↦ by simp only [mem_integers_iff, residueFieldPlace_valuation]

/-- The two views of the completed valuation ring, as rings of functions with the same
underlying elements. -/
private noncomputable def integersEquivResidueFieldPlace :
    P.completionPlace.integers ≃+* (P.residueFieldPlace hA).integers :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (P.residueFieldPlace_integers hA).symm)

@[simp]
private theorem coe_integersEquivResidueFieldPlace (x : P.completionPlace.integers) :
    (P.integersEquivResidueFieldPlace hA x : P.Completion) = x := (rfl)

/-- The coefficient field is the image of the constants of the completed place over `F_P`. -/
private theorem integersEquivResidueFieldPlace_section (a : P.ResidueField) :
    P.integersEquivResidueFieldPlace hA (s a) =
      algebraMap P.ResidueField (P.residueFieldPlace hA).integers a :=
  Subtype.ext (by rw [coe_integersEquivResidueFieldPlace, coe_algebraMap_constants, hA])

/-- Changing the constants to the coefficient field does not change when two integral functions
have the same residue. -/
private theorem residue_integersEquivResidueFieldPlace_eq_iff
    {y z : P.completionPlace.integers} :
    residue (P.residueFieldPlace hA).integers (P.integersEquivResidueFieldPlace hA y) =
        residue (P.residueFieldPlace hA).integers (P.integersEquivResidueFieldPlace hA z) ↔
      residue P.completionPlace.integers y = residue P.completionPlace.integers z := by
  simp only [residue_eq_iff_sub_mem_filtration_one, coe_integersEquivResidueFieldPlace,
    mem_residueFieldPlace_filtration_iff]

private theorem ord_residueFieldPlace_uniformizer {t : P.Completion}
    (ht : P.completionPlace.ord t = 1) : (P.residueFieldPlace hA).ord t = 1 := by
  rwa [ord_residueFieldPlace]

variable (hs : ∀ a, residue P.completionPlace.integers (s a) = P.residueFieldEquivCompletion a)
include hs

/-- Over its coefficient field, the completed place is rational: reduction of the coefficient
field is the identification of `F_P` with the residue field of the completion. -/
private theorem degree_residueFieldPlace : (P.residueFieldPlace hA).degree = 1 := by
  refine (P.residueFieldPlace hA).degree_eq_one_iff_algebraMap_surjective.mpr fun y ↦ ?_
  obtain ⟨z, rfl⟩ := residue_surjective y
  let w := (P.integersEquivResidueFieldPlace hA).symm z
  refine ⟨P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers w), ?_⟩
  have h := (P.residue_integersEquivResidueFieldPlace_eq_iff hA).mpr
    ((hs (P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers w))).trans
      (P.residueFieldEquivCompletion.apply_symm_apply _))
  rwa [integersEquivResidueFieldPlace_section, RingEquiv.apply_symm_apply,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h

variable {t : P.Completion} (ht : P.completionPlace.ord t = 1)
include ht

/-- The uniformizer expansion over the coefficient field is a bijection onto `F_P[[T]]`. -/
private theorem bijective_residueFieldPlace_powerSeriesExpansion :
    Function.Bijective ((P.residueFieldPlace hA).powerSeriesExpansion
      (P.degree_residueFieldPlace hA hs) (P.ord_residueFieldPlace_uniformizer hA ht)) :=
  ⟨(P.residueFieldPlace hA).powerSeriesExpansion_injective _ _,
    (P.residueFieldPlace hA).powerSeriesExpansion_surjective _ _ fun _ hg ↦ by
      simp only [mem_residueFieldPlace_filtration_iff] at hg ⊢
      exact P.exists_forall_sub_mem_completionPlace_filtration hg⟩

/-- The uniformizer expansion over the coefficient field, as a ring isomorphism of the completed
valuation ring with `F_P[[T]]`. -/
private noncomputable def ringEquivPowerSeries :
    P.completionPlace.integers ≃+* PowerSeries P.ResidueField :=
  (P.integersEquivResidueFieldPlace hA).trans
    (AlgEquiv.ofBijective _
      (P.bijective_residueFieldPlace_powerSeriesExpansion hA hs ht)).toRingEquiv

private theorem ringEquivPowerSeries_apply (x : P.completionPlace.integers) :
    P.ringEquivPowerSeries hA hs ht x =
      (P.residueFieldPlace hA).powerSeriesExpansion (P.degree_residueFieldPlace hA hs)
        (P.ord_residueFieldPlace_uniformizer hA ht) (P.integersEquivResidueFieldPlace hA x) :=
  (rfl)

private theorem ringEquivPowerSeries_eq_iff (x : P.completionPlace.integers)
    (f : PowerSeries P.ResidueField) :
    P.ringEquivPowerSeries hA hs ht x = f ↔
      ∀ n : ℕ, (x : P.Completion) - ∑ i : Fin n,
        (s (PowerSeries.coeff i f) : P.Completion) * t ^ (i : ℕ) ∈
          P.completionPlace.filtration n := by
  rw [ringEquivPowerSeries_apply]
  constructor
  · rintro rfl n
    have h := (P.residueFieldPlace hA).sub_sum_coeff_powerSeriesExpansion_mem_filtration
      (P.degree_residueFieldPlace hA hs) (P.ord_residueFieldPlace_uniformizer hA ht) n
      (P.integersEquivResidueFieldPlace hA x)
    simpa only [coe_integersEquivResidueFieldPlace, hA, mem_residueFieldPlace_filtration_iff]
      using h
  · intro h
    ext n
    rw [(P.residueFieldPlace hA).coeff_powerSeriesExpansion _ _ (n + 1) _ ⟨n, by omega⟩]
    refine congrFun (((P.residueFieldPlace hA).truncatedExpansion_eq_iff _ _ (n + 1) _
      fun i ↦ PowerSeries.coeff i f).mpr ?_) ⟨n, by omega⟩
    simpa only [coe_integersEquivResidueFieldPlace, hA, mem_residueFieldPlace_filtration_iff]
      using h (n + 1)

private theorem ringEquivPowerSeries_uniformizer :
    P.ringEquivPowerSeries hA hs ht
      ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ = PowerSeries.X := by
  rw [ringEquivPowerSeries_apply]
  exact (P.residueFieldPlace hA).powerSeriesExpansion_uniformizer _ _

private theorem mem_filtration_iff_le_order_ringEquivPowerSeries (n : ℕ)
    (x : P.completionPlace.integers) :
    (x : P.Completion) ∈ P.completionPlace.filtration n ↔
      (n : ℕ∞) ≤ (P.ringEquivPowerSeries hA hs ht x).order := by
  rw [← P.mem_residueFieldPlace_filtration_iff hA, ← P.coe_integersEquivResidueFieldPlace hA,
    ringEquivPowerSeries_apply]
  exact (P.residueFieldPlace hA).mem_filtration_iff_le_order_powerSeriesExpansion _ _ n _

private theorem order_ringEquivPowerSeries (x : P.completionPlace.integers) (hx : x ≠ 0) :
    (P.ringEquivPowerSeries hA hs ht x).order =
      ((P.completionPlace.ord (x : P.Completion)).toNat : ℕ∞) := by
  rw [ringEquivPowerSeries_apply, ← P.ord_residueFieldPlace hA,
    ← P.coe_integersEquivResidueFieldPlace hA]
  exact (P.residueFieldPlace hA).order_powerSeriesExpansion _ _ _
    ((map_ne_zero_iff _ (P.integersEquivResidueFieldPlace hA).injective).mpr hx)

end RationalPlace

/-! ### Power-series expansions over a coefficient field -/

section OfSection

variable (s : P.ResidueField →+* P.completionPlace.integers)
  (hs : ∀ a, residue P.completionPlace.integers (s a) = P.residueFieldEquivCompletion a)
  {t : P.Completion} (ht : P.completionPlace.ord t = 1)

/-- The residue field acts on the completion through the coefficient field `s`. For this action
`algebraMap a = s a` holds by definition, which is the hypothesis `hA` of the construction above. -/
private noncomputable abbrev algebraOfSection : Algebra P.ResidueField P.Completion :=
  (P.completionPlace.integers.subtype.comp s).toAlgebra

/-- **The completed valuation ring at a place is `F_P[[T]]`.** Given a coefficient field `s` of
`𝒪̂_P`, a ring embedding of the residue field `F_P` lifting it, and a uniformizer `t`, the
isomorphism sends a completed integral function to its expansion `∑ aᵢ Tⁱ` in `t`, with
coefficients `aᵢ ∈ F_P` read through `s`; it is characterized by
`TauCeti.Place.completionIntegersEquivPowerSeriesOfSection_eq_iff`. -/
noncomputable def completionIntegersEquivPowerSeriesOfSection :
    P.completionPlace.integers ≃+* PowerSeries P.ResidueField :=
  letI := P.algebraOfSection s
  P.ringEquivPowerSeries (s := s) (fun _ ↦ rfl) hs ht

/-- **The expansion is characterized by its truncations**: the expansion of `x` is the power
series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} s(aᵢ) tⁱ` vanishes to order `n` for every `n`. -/
theorem completionIntegersEquivPowerSeriesOfSection_eq_iff (x : P.completionPlace.integers)
    (f : PowerSeries P.ResidueField) :
    P.completionIntegersEquivPowerSeriesOfSection s hs ht x = f ↔
      ∀ n : ℕ, (x : P.Completion) - ∑ i : Fin n,
        (s (PowerSeries.coeff i f) : P.Completion) * t ^ (i : ℕ) ∈
          P.completionPlace.filtration n :=
  letI := P.algebraOfSection s
  P.ringEquivPowerSeries_eq_iff (s := s) (fun _ ↦ rfl) hs ht x f

/-- Removing the first `n` terms of the expansion of a completed integral function leaves a
function vanishing to order at least `n`. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesOfSection_mem_filtration
    (x : P.completionPlace.integers) (n : ℕ) :
    (x : P.Completion) - ∑ i : Fin n, (s (PowerSeries.coeff i
      (P.completionIntegersEquivPowerSeriesOfSection s hs ht x)) : P.Completion) * t ^ (i : ℕ) ∈
        P.completionPlace.filtration n :=
  (P.completionIntegersEquivPowerSeriesOfSection_eq_iff s hs ht x _).mp rfl n

/-- The inverse isomorphism realizes a power series over the residue field to every finite
order. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesOfSection_symm_mem_filtration
    (f : PowerSeries P.ResidueField) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeriesOfSection s hs ht).symm f : P.Completion) -
      ∑ i : Fin n, (s (PowerSeries.coeff i f) : P.Completion) * t ^ (i : ℕ) ∈
        P.completionPlace.filtration n :=
  (P.completionIntegersEquivPowerSeriesOfSection_eq_iff s hs ht _ f).mp
    (RingEquiv.apply_symm_apply _ f) n

/-- The coefficient field expands to the constant power series. -/
@[simp]
theorem completionIntegersEquivPowerSeriesOfSection_section (a : P.ResidueField) :
    P.completionIntegersEquivPowerSeriesOfSection s hs ht (s a) = PowerSeries.C a := by
  refine (P.completionIntegersEquivPowerSeriesOfSection_eq_iff s hs ht _ _).mpr fun n ↦ ?_
  rcases n with _ | n
  · simpa using P.completionPlace.mem_filtration_zero_iff.mpr (s a).2
  · rw [Fin.sum_univ_succ]
    simp [PowerSeries.coeff_C]

/-- The uniformizer expands as the power-series variable. -/
@[simp]
theorem completionIntegersEquivPowerSeriesOfSection_uniformizer :
    P.completionIntegersEquivPowerSeriesOfSection s hs ht
      ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ = PowerSeries.X :=
  letI := P.algebraOfSection s
  P.ringEquivPowerSeries_uniformizer (s := s) (fun _ ↦ rfl) hs ht

/-- The constant coefficient of the expansion is the value at `P`, read in `F_P`. -/
@[simp]
theorem constantCoeff_completionIntegersEquivPowerSeriesOfSection
    (x : P.completionPlace.integers) :
    PowerSeries.constantCoeff (P.completionIntegersEquivPowerSeriesOfSection s hs ht x) =
      P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers x) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AlgEquiv.eq_symm_apply, ← hs, eq_comm]
  apply P.completionPlace.residue_eq_iff_sub_mem_filtration_one.mpr
  simpa using
    P.sub_sum_coeff_completionIntegersEquivPowerSeriesOfSection_mem_filtration s hs ht x 1

/-- Vanishing to order `n` is vanishing of the first `n` coefficients of the expansion. -/
theorem mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesOfSection (n : ℕ)
    (x : P.completionPlace.integers) :
    (x : P.Completion) ∈ P.completionPlace.filtration n ↔
      (n : ℕ∞) ≤ (P.completionIntegersEquivPowerSeriesOfSection s hs ht x).order :=
  letI := P.algebraOfSection s
  P.mem_filtration_iff_le_order_ringEquivPowerSeries (s := s) (fun _ ↦ rfl) hs ht n x

/-- The order of a nonzero completed integral function is the first nonzero degree of its
expansion. -/
theorem order_completionIntegersEquivPowerSeriesOfSection (x : P.completionPlace.integers)
    (hx : x ≠ 0) :
    (P.completionIntegersEquivPowerSeriesOfSection s hs ht x).order =
      ((P.completionPlace.ord (x : P.Completion)).toNat : ℕ∞) :=
  letI := P.algebraOfSection s
  P.order_ringEquivPowerSeries (s := s) (fun _ ↦ rfl) hs ht x hx

end OfSection

/-- **At every place the completed valuation ring is `F_P[[T]]`**, separable residue field or
not: a coefficient field exists by Cohen's theorem
(`TauCeti.Place.exists_completionResidueFieldSection`) and a uniformizer exists because the
valuation is normalized. When `F_P` is inseparable over `k` there may be no `k`-linear such
isomorphism (`TauCeti.Place.isEmpty_completionIntegers_algEquiv_powerSeries`). -/
theorem nonempty_completionIntegers_ringEquiv_powerSeries :
    Nonempty (P.completionPlace.integers ≃+* PowerSeries P.ResidueField) := by
  obtain ⟨s, hs⟩ := P.exists_completionResidueFieldSection
  obtain ⟨t, -, ht⟩ := P.completionPlace.exists_ne_zero_ord_eq 1
  exact ⟨P.completionIntegersEquivPowerSeriesOfSection s hs ht⟩

/-! ### The `k`-linear expansion at a place with separable residue field -/

section Separable

variable [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1)

/-- **The completed valuation ring at a place with separable residue field is `F_P[[T]]` over
`k`.** The isomorphism sends a completed integral function to its expansion `∑ aᵢ Tⁱ` in the
uniformizer `t`, with coefficients `aᵢ ∈ F_P` read in the coefficient field
`TauCeti.Place.completionResidueFieldSection` over `k`; it is
`TauCeti.Place.completionIntegersEquivPowerSeriesOfSection` for that coefficient field. -/
noncomputable def completionIntegersEquivPowerSeriesResidueField :
    P.completionPlace.integers ≃ₐ[k] PowerSeries P.ResidueField :=
  AlgEquiv.ofRingEquiv (f := P.completionIntegersEquivPowerSeriesOfSection
    P.completionResidueFieldSection P.residue_completionResidueFieldSection ht) fun c ↦ by
      simpa [PowerSeries.algebraMap_apply] using
        P.completionIntegersEquivPowerSeriesOfSection_section _
          P.residue_completionResidueFieldSection ht (algebraMap k P.ResidueField c)

/-- The `k`-linear expansion is the expansion through the coefficient field over `k`. -/
theorem completionIntegersEquivPowerSeriesResidueField_apply (x : P.completionPlace.integers) :
    P.completionIntegersEquivPowerSeriesResidueField ht x =
      P.completionIntegersEquivPowerSeriesOfSection P.completionResidueFieldSection
        P.residue_completionResidueFieldSection ht x := (rfl)

/-- **The expansion is characterized by its truncations**: the expansion of `x` is the power
series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} aᵢ tⁱ` vanishes to order `n` for every `n`, the
coefficients `aᵢ` being read in the coefficient field. -/
theorem completionIntegersEquivPowerSeriesResidueField_eq_iff (x : P.completionPlace.integers)
    (f : PowerSeries P.ResidueField) :
    P.completionIntegersEquivPowerSeriesResidueField ht x = f ↔
      ∀ n : ℕ, (x : P.Completion) - ∑ i : Fin n,
        (P.completionResidueFieldSection (PowerSeries.coeff i f) : P.Completion) * t ^ (i : ℕ) ∈
          P.completionPlace.filtration n :=
  P.completionIntegersEquivPowerSeriesOfSection_eq_iff _
    P.residue_completionResidueFieldSection ht x f

/-- Removing the first `n` terms of the expansion of a completed integral function leaves a
function vanishing to order at least `n`. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration
    (x : P.completionPlace.integers) (n : ℕ) :
    (x : P.Completion) - ∑ i : Fin n, (P.completionResidueFieldSection
      (PowerSeries.coeff i (P.completionIntegersEquivPowerSeriesResidueField ht x)) :
        P.Completion) * t ^ (i : ℕ) ∈ P.completionPlace.filtration n :=
  P.sub_sum_coeff_completionIntegersEquivPowerSeriesOfSection_mem_filtration _
    P.residue_completionResidueFieldSection ht x n

/-- The inverse isomorphism realizes a power series over the residue field to every finite
order. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_symm_mem_filtration
    (f : PowerSeries P.ResidueField) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeriesResidueField ht).symm f : P.Completion) -
      ∑ i : Fin n, (P.completionResidueFieldSection (PowerSeries.coeff i f) : P.Completion) *
        t ^ (i : ℕ) ∈ P.completionPlace.filtration n :=
  P.sub_sum_coeff_completionIntegersEquivPowerSeriesOfSection_symm_mem_filtration _
    P.residue_completionResidueFieldSection ht f n

/-- The coefficient field expands to the constant power series. -/
@[simp]
theorem completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection
    (a : P.ResidueField) :
    P.completionIntegersEquivPowerSeriesResidueField ht (P.completionResidueFieldSection a) =
      PowerSeries.C a :=
  P.completionIntegersEquivPowerSeriesOfSection_section _
    P.residue_completionResidueFieldSection ht a

/-- The uniformizer expands as the power-series variable. -/
@[simp]
theorem completionIntegersEquivPowerSeriesResidueField_uniformizer :
    P.completionIntegersEquivPowerSeriesResidueField ht
      ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ = PowerSeries.X :=
  P.completionIntegersEquivPowerSeriesOfSection_uniformizer _
    P.residue_completionResidueFieldSection ht

/-- The constant coefficient of the expansion is the value at `P`, read in `F_P`. -/
@[simp]
theorem constantCoeff_completionIntegersEquivPowerSeriesResidueField
    (x : P.completionPlace.integers) :
    PowerSeries.constantCoeff (P.completionIntegersEquivPowerSeriesResidueField ht x) =
      P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers x) :=
  P.constantCoeff_completionIntegersEquivPowerSeriesOfSection _
    P.residue_completionResidueFieldSection ht x

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
      (n : ℕ∞) ≤ (P.completionIntegersEquivPowerSeriesResidueField ht x).order :=
  P.mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesOfSection _
    P.residue_completionResidueFieldSection ht n x

/-- The order of a nonzero completed integral function is the first nonzero degree of its
expansion. -/
theorem order_completionIntegersEquivPowerSeriesResidueField (x : P.completionPlace.integers)
    (hx : x ≠ 0) :
    (P.completionIntegersEquivPowerSeriesResidueField ht x).order =
      ((P.completionPlace.ord (x : P.Completion)).toNat : ℕ∞) :=
  P.order_completionIntegersEquivPowerSeriesOfSection _
    P.residue_completionResidueFieldSection ht x hx

end Separable

end TauCeti.Place
