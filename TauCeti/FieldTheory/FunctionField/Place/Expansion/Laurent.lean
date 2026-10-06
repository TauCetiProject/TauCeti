/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Completion
public import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent expansions and residues at rational places

Let `P` be a rational place of `F / k` and let `t` have order one at `P`. Passing to fraction
fields, the identification of the completed valuation ring with `k[[T]]` becomes a
`k`-algebra isomorphism of the completion of `F` at `P` with the Laurent-series field
`k((T))`, sending `t` to `T`. It carries the valuation of `P` to the `T`-adic valuation.

Composing with the completion map gives the Laurent expansion of every function in `F`.
Its coefficients below `m` depend only on the function modulo the `m`-th order filtration,
and a finite sum `∑ cᵢ tⁱ` congruent to the function modulo that filtration has exactly the
coefficients `cᵢ`. The coefficient of `T⁻¹` is the residue `res_{P,t}` of a function with
respect to `t`. It vanishes on functions integral at `P` and is read off the power-series
expansion of `t ^ (n + 1) * z` whenever this product is integral.

## Main definitions

* `TauCeti.Place.completionEquivLaurentSeries`: the completion at a rational place is `k((T))`.
* `TauCeti.Place.laurentSeriesExpansion`: the Laurent expansion of functions at `P` in `t`.
* `TauCeti.Place.residue`: the residue `res_{P,t}`, the coefficient of `t⁻¹`.

## Main results

* `TauCeti.Place.valuation_completionEquivLaurentSeries`: the isomorphism with `k((T))`
  identifies the valuation of `P` with the `T`-adic valuation.
* `TauCeti.Place.coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration`: uniqueness of
  finite Laurent expansions.
* `TauCeti.Place.residue_eq_coeff_powerSeriesExpansion`: the residue as a power-series
  coefficient.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Definition 4.2.8.
-/

public section

open scoped WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-! ### The completion as a Laurent-series field -/

/-- At a rational place with a chosen uniformizer, uniformizer expansion identifies the
completion with the Laurent-series field over the constants. It is the fraction-field
extension of `TauCeti.Place.completionIntegersEquivPowerSeries`. -/
noncomputable def completionEquivLaurentSeries : P.Completion ≃ₐ[k] LaurentSeries k :=
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv
    (P.completionIntegersEquivPowerSeries hP ht).toRingEquiv) fun c ↦ by
    rw [← P.completionPlace.coe_algebraMap_constants, ← ValuationSubring.algebraMap_apply,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.commutes, LaurentSeries.coe_algebraMap, HahnSeries.algebraMap_apply']

/-- On the completed valuation ring, the Laurent expansion is the power-series expansion. -/
@[simp]
theorem completionEquivLaurentSeries_coe (x : P.completionPlace.integers) :
    P.completionEquivLaurentSeries hP ht x =
      HahnSeries.ofPowerSeries ℤ k (P.completionIntegersEquivPowerSeries hP ht x) := by
  rw [← ValuationSubring.algebraMap_apply, completionEquivLaurentSeries,
    AlgEquiv.ofRingEquiv_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    LaurentSeries.coe_algebraMap, AlgEquiv.coe_toRingEquiv]

/-- The inverse identification realizes a power series in the completed valuation ring. -/
theorem completionEquivLaurentSeries_symm_ofPowerSeries (f : PowerSeries k) :
    (P.completionEquivLaurentSeries hP ht).symm (HahnSeries.ofPowerSeries ℤ k f) =
      ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) := by
  rw [AlgEquiv.symm_apply_eq, completionEquivLaurentSeries_coe, AlgEquiv.apply_symm_apply]

/-- The chosen uniformizer is sent to the Laurent variable `T`. -/
@[simp]
theorem completionEquivLaurentSeries_completionEmbedding_uniformizer :
    P.completionEquivLaurentSeries hP ht (P.completionEmbedding t) =
      HahnSeries.single 1 1 := by
  rw [← P.completionIntegersEmbedding_apply ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩,
    completionEquivLaurentSeries_coe, completionIntegersEquivPowerSeries_uniformizer,
    HahnSeries.ofPowerSeries_X]

/-- A unit of the completed valuation ring has Laurent expansion of `T`-adic valuation one. -/
private theorem valuation_completionEquivLaurentSeries_unit
    (u : P.completionPlace.integersˣ) :
    Valued.v (P.completionEquivLaurentSeries hP ht (u : P.completionPlace.integers)) = 1 := by
  have hle (x : P.completionPlace.integers) :
      Valued.v (P.completionEquivLaurentSeries hP ht x) ≤ 1 := by
    rw [completionEquivLaurentSeries_coe]
    exact (LaurentSeries.val_le_one_iff_eq_coe k _).mpr ⟨_, rfl⟩
  have hmul : Valued.v (P.completionEquivLaurentSeries hP ht (u : P.completionPlace.integers)) *
      Valued.v (P.completionEquivLaurentSeries hP ht
        ((u⁻¹ : P.completionPlace.integersˣ) : P.completionPlace.integers)) = 1 := by
    rw [← map_mul, ← map_mul, ← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one, map_one,
      map_one]
  refine le_antisymm (hle _) ?_
  calc (1 : ℤᵐ⁰) = _ := hmul.symm
    _ ≤ _ := mul_le_of_le_one_right' (hle _)

/-- The identification with `k((T))` carries the valuation of `P` on the completion to the
`T`-adic valuation of Laurent series. -/
@[simp]
theorem valuation_completionEquivLaurentSeries (x : P.Completion) :
    Valued.v (P.completionEquivLaurentSeries hP ht x) = P.completionPlace.valuation x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hπ : P.completionPlace.valuation.IsUniformizer (P.completionEmbedding t) :=
    (P.isUniformizer_completionEmbedding_iff t).mpr (P.isUniformizer_iff_ord_eq_one.mpr ht)
  obtain ⟨u, hu⟩ := P.completionPlace.exists_eq_zpow_mul_unit hπ hx
  have ht0 : P.completionEmbedding t ≠ 0 := hπ.ne_zero
  rw [hu]
  simp only [map_mul, map_zpow₀]
  rw [P.valuation_completionEquivLaurentSeries_unit,
    completionEquivLaurentSeries_completionEmbedding_uniformizer,
    LaurentSeries.valuation_single_zpow k 1,
    (P.completionPlace.isUnit_iff_valuation_eq_one).mp u.isUnit,
    P.completionPlace.valuation_eq_exp_neg_ord ht0, ord_completionEmbedding, ht]

/-! ### Laurent expansions of functions -/

/-- The Laurent expansion of a function at a rational place in a chosen uniformizer: the image
of the function under completion and `TauCeti.Place.completionEquivLaurentSeries`. -/
noncomputable def laurentSeriesExpansion : F →ₐ[k] LaurentSeries k :=
  (P.completionEquivLaurentSeries hP ht).toAlgHom.comp P.completionEmbedding

/-- The Laurent expansion of a function is the Laurent expansion of its image in the
completion. -/
theorem laurentSeriesExpansion_apply (z : F) :
    P.laurentSeriesExpansion hP ht z =
      P.completionEquivLaurentSeries hP ht (P.completionEmbedding z) := (rfl)

/-- The Laurent expansion of an integral function is its power-series expansion. -/
@[simp]
theorem laurentSeriesExpansion_coe (x : P.integers) :
    P.laurentSeriesExpansion hP ht x =
      HahnSeries.ofPowerSeries ℤ k (P.powerSeriesExpansion hP ht x) := by
  rw [laurentSeriesExpansion_apply, ← P.completionIntegersEmbedding_apply,
    completionEquivLaurentSeries_coe,
    completionIntegersEquivPowerSeries_completionIntegersEmbedding]

/-- Every integer power of the chosen uniformizer expands as the corresponding monomial. -/
theorem laurentSeriesExpansion_zpow_uniformizer (n : ℤ) :
    P.laurentSeriesExpansion hP ht (t ^ n) = HahnSeries.single n 1 := by
  rw [map_zpow₀, laurentSeriesExpansion_apply,
    completionEquivLaurentSeries_completionEmbedding_uniformizer]
  exact (RatFunc.single_zpow n).symm

/-- The chosen uniformizer expands as the Laurent variable `T`. -/
@[simp]
theorem laurentSeriesExpansion_uniformizer :
    P.laurentSeriesExpansion hP ht t = HahnSeries.single 1 1 := by
  simpa using P.laurentSeriesExpansion_zpow_uniformizer hP ht 1

/-- Laurent expansion carries the valuation of `P` to the `T`-adic valuation. -/
@[simp]
theorem valuation_laurentSeriesExpansion (z : F) :
    Valued.v (P.laurentSeriesExpansion hP ht z) = P.valuation z := by
  rw [laurentSeriesExpansion_apply, valuation_completionEquivLaurentSeries,
    completionPlace_valuation, valuation_completionEmbedding]

/-- A function vanishing to order at least `m` has no Laurent coefficients below `m`. -/
theorem coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansion hP ht z).coeff i = 0 := by
  apply LaurentSeries.coeff_zero_of_lt_valuation k _ hi
  rwa [valuation_laurentSeriesExpansion, ← mem_filtration_iff]

/-- The Laurent coefficients below `m` depend only on the function modulo the `m`-th order
filtration. -/
theorem coeff_laurentSeriesExpansion_eq_of_sub_mem_filtration {m : ℤ} {z w : F}
    (h : z - w ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansion hP ht z).coeff i = (P.laurentSeriesExpansion hP ht w).coeff i := by
  have h0 := P.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration hP ht h hi
  rwa [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h0

/-- A finite Laurent polynomial in the uniformizer expands with its own coefficients. -/
theorem coeff_laurentSeriesExpansion_sum (s : Finset ℤ) (c : ℤ → k) (i : ℤ) :
    (P.laurentSeriesExpansion hP ht (∑ j ∈ s, algebraMap k F (c j) * t ^ j)).coeff i =
      if i ∈ s then c i else 0 := by
  -- `HahnSeries.coeff_single` is stated with classical decidability of equality.
  simp only [map_sum, map_mul, AlgHom.commutes, laurentSeriesExpansion_zpow_uniformizer,
    HahnSeries.coeff_sum, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    HahnSeries.coeff_single, smul_eq_mul, mul_ite, mul_one, mul_zero]
  convert Finset.sum_ite_eq s i c

/-- Uniqueness of finite Laurent expansions: if a function agrees with `∑ cⱼ tʲ` modulo the
`m`-th order filtration, then its Laurent coefficients below `m` are the `cⱼ`, read as zero
outside the summation range. -/
theorem coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration {m : ℤ} {z : F}
    (s : Finset ℤ) (c : ℤ → k) (h : z - ∑ j ∈ s, algebraMap k F (c j) * t ^ j ∈ P.filtration m)
    {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansion hP ht z).coeff i = if i ∈ s then c i else 0 := by
  rw [P.coeff_laurentSeriesExpansion_eq_of_sub_mem_filtration hP ht h hi,
    coeff_laurentSeriesExpansion_sum]

/-- Multiplying by `t ^ n` to make a function integral shifts its Laurent coefficients onto
the coefficients of a power-series expansion. -/
theorem coeff_laurentSeriesExpansion_sub_natCast (n : ℕ) {z : F}
    (hz : t ^ n * z ∈ P.integers) (i : ℕ) :
    (P.laurentSeriesExpansion hP ht z).coeff ((i : ℤ) - n) =
      PowerSeries.coeff i (P.powerSeriesExpansion hP ht ⟨t ^ n * z, hz⟩) := by
  rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), ← laurentSeriesExpansion_coe]
  -- Reduce the coercion of the anonymous-constructor element of `P.integers`.
  dsimp only
  rw [map_mul, ← zpow_natCast, laurentSeriesExpansion_zpow_uniformizer,
    HahnSeries.coeff_single_mul, one_mul]

/-! ### Residues -/

/-- The residue `res_{P,t}` of a function at a rational place with respect to a chosen
uniformizer: the coefficient of `t⁻¹` in its Laurent expansion (Stichtenoth,
Definition 4.2.8). It is `k`-linear. -/
noncomputable def residue : F →ₗ[k] k where
  toFun z := (P.laurentSeriesExpansion hP ht z).coeff (-1)
  map_add' z w := by simp
  map_smul' c z := by
    simp [Algebra.smul_def, HahnSeries.algebraMap_apply']

/-- The residue is the coefficient of `T⁻¹` in the Laurent expansion. -/
theorem residue_apply (z : F) :
    P.residue hP ht z = (P.laurentSeriesExpansion hP ht z).coeff (-1) := (rfl)

/-- Functions integral at the place have residue zero. -/
theorem residue_eq_zero_of_mem_integers {z : F} (hz : z ∈ P.integers) :
    P.residue hP ht z = 0 :=
  P.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration hP ht
    (P.mem_filtration_zero_iff.mpr hz) (by omega)

/-- The residue depends only on the function modulo integral functions. -/
theorem residue_eq_of_sub_mem_integers {z w : F} (h : z - w ∈ P.integers) :
    P.residue hP ht z = P.residue hP ht w := by
  rw [← sub_eq_zero, ← map_sub, P.residue_eq_zero_of_mem_integers hP ht h]

/-- The residue of an integer power of the uniformizer. -/
@[simp]
theorem residue_zpow_uniformizer (n : ℤ) :
    P.residue hP ht (t ^ n) = if n = -1 then 1 else 0 := by
  rw [residue_apply, laurentSeriesExpansion_zpow_uniformizer, HahnSeries.coeff_single]
  simp only [eq_comm]

/-- The inverse of the uniformizer has residue one. -/
@[simp]
theorem residue_inv_uniformizer : P.residue hP ht t⁻¹ = 1 := by
  simpa using P.residue_zpow_uniformizer hP ht (-1)

/-- If `t ^ (n + 1) * z` is integral, the residue of `z` is the degree-`n` coefficient of the
power-series expansion of `t ^ (n + 1) * z`. -/
theorem residue_eq_coeff_powerSeriesExpansion (n : ℕ) {z : F}
    (hz : t ^ (n + 1) * z ∈ P.integers) :
    P.residue hP ht z =
      PowerSeries.coeff n (P.powerSeriesExpansion hP ht ⟨t ^ (n + 1) * z, hz⟩) := by
  rw [residue_apply, ← P.coeff_laurentSeriesExpansion_sub_natCast hP ht (n + 1) hz n]
  congr 1
  omega

end TauCeti.Place
