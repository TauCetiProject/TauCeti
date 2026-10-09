/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Series

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

/-- The `n`-th Laurent coefficient of a function at the rational place, with respect to `t`. -/
noncomputable def laurentCoeff (n : ℤ) : F →ₗ[k] k :=
  (P.completionLaurentCoeff hP ht n).comp P.completionEmbedding.toLinearMap

/-- The Laurent coefficient is the corresponding coefficient of the Laurent expansion. -/
@[simp]
theorem laurentCoeff_apply (n : ℤ) (z : F) :
    P.laurentCoeff hP ht n z = (P.laurentSeriesExpansion hP ht z).coeff n := by
  change P.completionLaurentCoeff hP ht n (P.completionEmbedding z) = _
  rw [completionLaurentCoeff_apply, laurentSeriesExpansion_apply]

/-- Completion preserves the Laurent coefficients of a function. -/
-- Not `@[simp]`: `completionLaurentCoeff_apply` already simplifies the left-hand side.
theorem completionLaurentCoeff_completionEmbedding (n : ℤ) (z : F) :
    P.completionLaurentCoeff hP ht n (P.completionEmbedding z) =
      P.laurentCoeff hP ht n z :=
  (rfl)

/-- The Laurent expansion of an integral function is its power-series expansion. -/
@[simp]
theorem laurentSeriesExpansion_coe (x : P.integers) :
    P.laurentSeriesExpansion hP ht x =
      HahnSeries.ofPowerSeries ℤ k (P.powerSeriesExpansion hP ht x) := by
  rw [laurentSeriesExpansion_apply, ← P.completionIntegersEmbedding_apply,
    completionEquivLaurentSeries_apply_integer,
    completionIntegersEquivPowerSeries_completionIntegersEmbedding]

/-- Every integer power of the chosen uniformizer expands as the corresponding monomial. -/
-- The left side already simplifies by `map_zpow₀` and `laurentSeriesExpansion_uniformizer`.
-- A `simp` annotation here is rejected by the `simpNF` linter.
theorem laurentSeriesExpansion_zpow_uniformizer (n : ℤ) :
    P.laurentSeriesExpansion hP ht (t ^ n) = HahnSeries.single n 1 := by
  rw [map_zpow₀, laurentSeriesExpansion_apply,
    completionEquivLaurentSeries_uniformizer, HahnSeries.ofPowerSeries_X]
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
theorem coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion (n : ℤ) {z : F}
    (hz : t ^ n * z ∈ P.integers) (i : ℕ) :
    (P.laurentSeriesExpansion hP ht z).coeff ((i : ℤ) - n) =
      PowerSeries.coeff i (P.powerSeriesExpansion hP ht ⟨t ^ n * z, hz⟩) := by
  rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), ← laurentSeriesExpansion_coe]
  -- Reduce the coercion of the anonymous-constructor element of `P.integers`.
  dsimp only
  rw [map_mul, laurentSeriesExpansion_zpow_uniformizer,
    HahnSeries.coeff_single_mul, one_mul]

/-- Functions are equal exactly when all coefficients of their Laurent expansions at a rational
place agree. -/
theorem laurentCoeff_ext_iff {x y : F} :
    x = y ↔ ∀ n : ℤ, P.laurentCoeff hP ht n x = P.laurentCoeff hP ht n y := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply P.completionEmbedding.injective
    apply (P.completionLaurentCoeff_ext_iff hP ht).2
    intro n
    simpa only [completionLaurentCoeff_completionEmbedding] using h n

/-! ### Residues -/

/-- The residue `res_{P,t}` of a function at a rational place with respect to a chosen
uniformizer: the coefficient of `t⁻¹` in its Laurent expansion (Stichtenoth,
Definition 4.2.8). It is `k`-linear. -/
noncomputable def residue : F →ₗ[k] k :=
  (P.completionResidue hP ht).comp P.completionEmbedding.toLinearMap

/-- The residue is the coefficient of `T⁻¹` in the Laurent expansion. -/
theorem residue_apply (z : F) :
    P.residue hP ht z = (P.laurentSeriesExpansion hP ht z).coeff (-1) := by
  change P.completionResidue hP ht (P.completionEmbedding z) = _
  rw [completionResidue_apply, laurentSeriesExpansion_apply]

/-- Completion preserves the residue of a function at the chosen uniformizer. -/
-- Not `@[simp]`: `completionResidue_apply` already simplifies the left-hand side.
theorem completionResidue_completionEmbedding (z : F) :
    P.completionResidue hP ht (P.completionEmbedding z) = P.residue hP ht z := by
  rw [completionResidue_apply, residue_apply, laurentSeriesExpansion_apply]

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
  have h := P.coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion
    hP ht ((n + 1 : ℕ) : ℤ)
    (by simpa only [zpow_natCast] using hz) n
  simp only [zpow_natCast] at h
  rw [residue_apply, ← h]
  congr 1
  omega

end TauCeti.Place
