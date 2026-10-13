/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.CoefficientField
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic

/-!
# Laurent expansions and residues at places with separable residue field

Let `P` be a place of `F / k` whose residue field `F_P` is separable over `k`, and let `t` have
order one at `P`. The identification of the completed valuation ring with `F_P[[T]]` through the
coefficient field (`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`) extends to
fraction fields: the completion of `F` at `P` is the Laurent-series field `F_P((T))`, with `t`
sent to `T`. Every function `z ∈ F` therefore has a Laurent expansion `∑ aᵢ tⁱ` with
coefficients `aᵢ ∈ F_P`, and its coefficient of `t⁻¹` is the residue `res_{P,t}(z) ∈ F_P`.
Composing with the trace of `F_P / k` gives a `k`-valued residue, the form in which residues at
places of arbitrary degree enter the residue theorem and the comparison of Weil differentials with
differentials.

At a rational place the coefficient field is `k` itself, and these expansions and residues are
the ones of `TauCeti.Place.laurentSeriesExpansion` and `TauCeti.Place.residue`, read in `F_P`
(`TauCeti.Place.residueResidueField_eq_algebraMap_residue`); the trace of the residue is then the
residue (`TauCeti.Place.traceResidue_eq_residue`).

## Main definitions

* `TauCeti.Place.completionEquivLaurentSeriesResidueField`: the completion at `P` is `F_P((T))`.
* `TauCeti.Place.laurentSeriesExpansionResidueField`: the Laurent expansion of functions at `P`
  in `t`, with coefficients in `F_P`.
* `TauCeti.Place.residueResidueField`: the residue `res_{P,t} : F → F_P`, the coefficient of
  `t⁻¹`.
* `TauCeti.Place.traceResidue`: the `k`-valued residue `Tr_{F_P/k} ∘ res_{P,t}`.
* `TauCeti.Place.traceResidue_mul_inv_uniformizer`: for an integral numerator `u`, the
  `k`-valued residue of `u / t` is the trace of its value at `P`.

## Main results

* `TauCeti.Place.mem_filtration_iff_le_order_powerSeriesExpansionResidueField`: a regular
  function vanishes to order `n` exactly when its expansion has order at least `n`.
* `TauCeti.Place.exists_trunc_powerSeriesExpansionResidueField_eq`: every power series over
  `F_P` is the expansion of a regular function up to any prescribed order.
* `TauCeti.Place.valuation_laurentSeriesExpansionResidueField`: Laurent expansion carries the
  valuation of `P` to the `T`-adic valuation.
* `TauCeti.Place.coeff_zero_laurentSeriesExpansionResidueField`: the constant coefficient of a
  function regular at `P` is its value at `P`.
* `TauCeti.Place.residueResidueField_mul_inv_uniformizer`: `res_{P,t}(u / t) = u(P)` for `u`
  regular at `P`.
* `TauCeti.Place.residueResidueField_eq_algebraMap_residue` and
  `TauCeti.Place.traceResidue_eq_residue`: at a rational place these residues are the residue
  `TauCeti.Place.residue` with coefficients in `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Definition 4.2.8, and Remark 4.3.7.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

public section

open scoped LaurentSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)
  [Algebra.IsSeparable k P.ResidueField]

/-! ### Laurent expansions in the completion -/

section Completion

variable {t : P.Completion} (ht : P.completionPlace.ord t = 1)

/-- **The completion at a place with separable residue field is `F_P((T))`.** A uniformizer `t`
of the completion identifies it with the Laurent-series field over the residue field, sending `t`
to `T`; this is the fraction-field extension of
`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`. -/
noncomputable def completionEquivLaurentSeriesResidueField :
    P.Completion ≃ₐ[k] LaurentSeries P.ResidueField :=
  IsFractionRing.algEquivOfAlgEquiv (P.completionIntegersEquivPowerSeriesResidueField ht)

/-- Laurent-series expansion restricts to power-series expansion on the completed valuation
ring. -/
@[simp]
theorem completionEquivLaurentSeriesResidueField_apply_integer
    (x : P.completionPlace.integers) :
    P.completionEquivLaurentSeriesResidueField ht (x : P.Completion) =
      (P.completionIntegersEquivPowerSeriesResidueField ht x :
        LaurentSeries P.ResidueField) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ x

/-- A completed function is integral exactly when its Laurent expansion comes from a power
series. -/
theorem exists_powerSeries_eq_completionEquivLaurentSeriesResidueField_iff_mem_integers
    (z : P.Completion) :
    (∃ f : PowerSeries P.ResidueField,
        (f : LaurentSeries P.ResidueField) = P.completionEquivLaurentSeriesResidueField ht z) ↔
      z ∈ P.completionPlace.integers :=
  P.exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers _ z

/-- The uniformizer expands as the Laurent variable `T`. -/
@[simp]
theorem completionEquivLaurentSeriesResidueField_uniformizer :
    P.completionEquivLaurentSeriesResidueField ht t = HahnSeries.single 1 1 := by
  have h := P.completionEquivLaurentSeriesResidueField_apply_integer ht
    ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  rw [completionIntegersEquivPowerSeriesResidueField_uniformizer,
    HahnSeries.ofPowerSeries_X] at h
  exact h

/-- Laurent-series expansion preserves the normalized valuation. -/
@[simp]
theorem valuation_completionEquivLaurentSeriesResidueField (x : P.Completion) :
    Valued.v (P.completionEquivLaurentSeriesResidueField ht x) =
      P.completionPlace.valuation x :=
  P.valuation_algEquivOfAlgEquiv _ x

end Completion

/-! ### Expansions of functions -/

variable {t : F} (ht : P.ord t = 1)

/-- The power-series expansion of a function regular at a place with separable residue field in a
chosen uniformizer `t`, with coefficients in the residue field: the image of the function under
completion and `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`. -/
noncomputable def powerSeriesExpansionResidueField : P.integers →ₐ[k] PowerSeries P.ResidueField :=
  (P.completionIntegersEquivPowerSeriesResidueField
    (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])).toAlgHom.comp
    P.completionIntegersEmbedding

/-- The power-series expansion of a function is the expansion of its image in the completed
valuation ring. -/
theorem powerSeriesExpansionResidueField_apply (x : P.integers) :
    P.powerSeriesExpansionResidueField ht x =
      P.completionIntegersEquivPowerSeriesResidueField
        (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])
        (P.completionIntegersEmbedding x) := (rfl)

/-- The constant coefficient of the power-series expansion of a function regular at `P` is its
value at `P`. -/
@[simp]
theorem constantCoeff_powerSeriesExpansionResidueField (x : P.integers) :
    PowerSeries.constantCoeff (P.powerSeriesExpansionResidueField ht x) =
      IsLocalRing.residue P.integers x :=
  P.constantCoeff_completionIntegersEquivPowerSeriesResidueField_completionIntegersEmbedding
    (by rwa [ord_completionEmbedding]) x

/-- A function regular at `P` vanishes to order at least `n` exactly when its power-series
expansion has order at least `n`. -/
theorem mem_filtration_iff_le_order_powerSeriesExpansionResidueField (n : ℕ) (x : P.integers) :
    (x : F) ∈ P.filtration n ↔ (n : ℕ∞) ≤ (P.powerSeriesExpansionResidueField ht x).order := by
  rw [powerSeriesExpansionResidueField_apply,
    ← mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField,
    completionIntegersEmbedding_apply, completionEmbedding_mem_filtration_iff]

/-- The chosen uniformizer expands as the power-series variable. -/
@[simp]
theorem powerSeriesExpansionResidueField_uniformizer :
    P.powerSeriesExpansionResidueField ht ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      PowerSeries.X := by
  rw [powerSeriesExpansionResidueField_apply]
  convert P.completionIntegersEquivPowerSeriesResidueField_uniformizer
    (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding]) using 2
  exact Subtype.ext (completionIntegersEmbedding_apply _ _)

/-- **Expansions are onto modulo `Tⁿ`**: every power series over the residue field agrees with
the expansion of some function regular at `P` up to order `n`. -/
theorem exists_trunc_powerSeriesExpansionResidueField_eq (g : PowerSeries P.ResidueField)
    (n : ℕ) : ∃ x : P.integers,
      PowerSeries.trunc n (P.powerSeriesExpansionResidueField ht x) = PowerSeries.trunc n g := by
  have ht' : P.completionPlace.ord (P.completionEmbedding t) = 1 := by
    rwa [ord_completionEmbedding]
  set e := P.completionIntegersEquivPowerSeriesResidueField ht'
  -- Approximate the completed function with expansion `g` by a function regular at `P`.
  obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem (b := n) (Nat.cast_nonneg n)
    ⟨(e.symm g : P.Completion), P.completionPlace.mem_filtration_zero_iff.mpr (e.symm g).2⟩
  have hyint : (y : F) ∈ P.integers := P.mem_filtration_zero_iff.mp y.2
  refine ⟨⟨y, hyint⟩, ?_⟩
  have hdiff : ((e.symm g - P.completionIntegersEmbedding ⟨y, hyint⟩ :
      P.completionPlace.integers) : P.Completion) ∈ P.completionPlace.filtration n := by
    simpa using hy
  rw [mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField _ ht' n,
    map_sub, AlgEquiv.apply_symm_apply, PowerSeries.nat_le_order_iff] at hdiff
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, powerSeriesExpansionResidueField_apply]
  split_ifs with hi
  · exact (sub_eq_zero.mp (by simpa using hdiff i hi)).symm
  · rfl

/-- The Laurent expansion of a function at a place with separable residue field in a chosen
uniformizer `t`, with coefficients in the residue field: the image of the function under
completion and `TauCeti.Place.completionEquivLaurentSeriesResidueField`. -/
noncomputable def laurentSeriesExpansionResidueField : F →ₐ[k] LaurentSeries P.ResidueField :=
  (P.completionEquivLaurentSeriesResidueField
    (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])).toAlgHom.comp
    P.completionEmbedding

/-- The Laurent expansion of a function is the Laurent expansion of its image in the
completion. -/
theorem laurentSeriesExpansionResidueField_apply (z : F) :
    P.laurentSeriesExpansionResidueField ht z =
      P.completionEquivLaurentSeriesResidueField
        (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])
        (P.completionEmbedding z) := (rfl)

/-- The Laurent expansion of a function regular at `P` is its power-series expansion. -/
@[simp]
theorem laurentSeriesExpansionResidueField_coe (x : P.integers) :
    P.laurentSeriesExpansionResidueField ht x =
      HahnSeries.ofPowerSeries ℤ P.ResidueField (P.powerSeriesExpansionResidueField ht x) := by
  rw [laurentSeriesExpansionResidueField_apply, ← completionIntegersEmbedding_apply,
    completionEquivLaurentSeriesResidueField_apply_integer, powerSeriesExpansionResidueField_apply]

/-- Every integer power of the chosen uniformizer expands as the corresponding monomial. -/
-- Not `@[simp]`: the left side already simplifies by `map_zpow₀` and
-- `laurentSeriesExpansionResidueField_uniformizer`.
theorem laurentSeriesExpansionResidueField_zpow_uniformizer (n : ℤ) :
    P.laurentSeriesExpansionResidueField ht (t ^ n) = HahnSeries.single n 1 := by
  rw [map_zpow₀, laurentSeriesExpansionResidueField_apply,
    completionEquivLaurentSeriesResidueField_uniformizer]
  exact (RatFunc.single_zpow n).symm

/-- The chosen uniformizer expands as the Laurent variable `T`. -/
@[simp]
theorem laurentSeriesExpansionResidueField_uniformizer :
    P.laurentSeriesExpansionResidueField ht t = HahnSeries.single 1 1 := by
  simpa using P.laurentSeriesExpansionResidueField_zpow_uniformizer ht 1

/-- Laurent expansion carries the valuation of `P` to the `T`-adic valuation. -/
@[simp]
theorem valuation_laurentSeriesExpansionResidueField (z : F) :
    Valued.v (P.laurentSeriesExpansionResidueField ht z) = P.valuation z := by
  rw [laurentSeriesExpansionResidueField_apply,
    valuation_completionEquivLaurentSeriesResidueField, completionPlace_valuation,
    valuation_completionEmbedding]

/-- A function vanishing to order at least `m` has no Laurent coefficients below `m`. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansionResidueField ht z).coeff i = 0 := by
  apply LaurentSeries.coeff_zero_of_lt_valuation P.ResidueField _ hi
  rwa [valuation_laurentSeriesExpansionResidueField, ← mem_filtration_iff]

/-- The Laurent coefficients below `m` depend only on the function modulo the `m`-th order
filtration. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_of_sub_mem_filtration {m : ℤ} {z w : F}
    (h : z - w ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansionResidueField ht z).coeff i =
      (P.laurentSeriesExpansionResidueField ht w).coeff i := by
  have h0 := P.coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration ht h hi
  rwa [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h0

/-- Multiplying by `t ^ n` to make a function integral shifts its Laurent coefficients onto the
coefficients of the power-series expansion of the product. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField
    (n : ℤ) {z : F} (hz : t ^ n * z ∈ P.integers) (i : ℕ) :
    (P.laurentSeriesExpansionResidueField ht z).coeff ((i : ℤ) - n) =
      PowerSeries.coeff i (P.powerSeriesExpansionResidueField ht ⟨t ^ n * z, hz⟩) := by
  rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), ← laurentSeriesExpansionResidueField_coe,
    map_mul, laurentSeriesExpansionResidueField_zpow_uniformizer, HahnSeries.coeff_single_mul,
    one_mul]

/-- The constant coefficient of the Laurent expansion of a function regular at `P` is its value
at `P`. -/
theorem coeff_zero_laurentSeriesExpansionResidueField (x : P.integers) :
    (P.laurentSeriesExpansionResidueField ht x).coeff 0 = IsLocalRing.residue P.integers x := by
  rw [laurentSeriesExpansionResidueField_coe, ← Nat.cast_zero,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_powerSeriesExpansionResidueField]

/-! ### Residues -/

/-- The residue `res_{P,t}` of a function at a place with separable residue field with respect to
a chosen uniformizer: the coefficient of `t⁻¹` in its Laurent expansion, an element of the
residue field `F_P` (Stichtenoth, Definition 4.2.8). It is `k`-linear. -/
noncomputable def residueResidueField : F →ₗ[k] P.ResidueField where
  toFun z := (P.laurentSeriesExpansionResidueField ht z).coeff (-1)
  map_add' z w := by rw [map_add, HahnSeries.coeff_add]
  map_smul' c z := by
    simp [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]

/-- The residue is the coefficient of `T⁻¹` in the Laurent expansion. -/
theorem residueResidueField_apply (z : F) :
    P.residueResidueField ht z = (P.laurentSeriesExpansionResidueField ht z).coeff (-1) := (rfl)

/-- Functions integral at the place have residue zero. -/
theorem residueResidueField_eq_zero_of_mem_integers {z : F} (hz : z ∈ P.integers) :
    P.residueResidueField ht z = 0 :=
  P.coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration ht
    (P.mem_filtration_zero_iff.mpr hz) (by omega)

/-- The residue depends only on the function modulo integral functions. -/
theorem residueResidueField_eq_of_sub_mem_integers {z w : F} (h : z - w ∈ P.integers) :
    P.residueResidueField ht z = P.residueResidueField ht w := by
  rw [← sub_eq_zero, ← map_sub, P.residueResidueField_eq_zero_of_mem_integers ht h]

/-- The residue of an integer power of the uniformizer. -/
@[simp]
theorem residueResidueField_zpow_uniformizer (n : ℤ) :
    P.residueResidueField ht (t ^ n) = if n = -1 then 1 else 0 := by
  rw [residueResidueField_apply, laurentSeriesExpansionResidueField_zpow_uniformizer,
    HahnSeries.coeff_single]
  simp only [eq_comm]

/-- The inverse of the uniformizer has residue one. -/
@[simp]
theorem residueResidueField_inv_uniformizer : P.residueResidueField ht t⁻¹ = 1 := by
  simpa using P.residueResidueField_zpow_uniformizer ht (-1)

/-- If `t ^ (n + 1) * z` is integral, the residue of `z` is the degree-`n` coefficient of the
power-series expansion of `t ^ (n + 1) * z`. -/
theorem residueResidueField_eq_coeff_powerSeriesExpansionResidueField (n : ℕ) {z : F}
    (hz : t ^ (n + 1) * z ∈ P.integers) :
    P.residueResidueField ht z =
      PowerSeries.coeff n (P.powerSeriesExpansionResidueField ht ⟨t ^ (n + 1) * z, hz⟩) := by
  have h := P.coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField
    ht ((n + 1 : ℕ) : ℤ) (by simpa only [zpow_natCast] using hz) n
  simp only [zpow_natCast] at h
  rw [residueResidueField_apply, ← h]
  congr 1
  omega

/-- **The residue of `u / t` is the value of `u` at `P`** for a function `u` regular at `P`. -/
@[simp]
theorem residueResidueField_mul_inv_uniformizer (u : P.integers) :
    P.residueResidueField ht (u * t⁻¹) = IsLocalRing.residue P.integers u := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hu : t ^ (0 + 1) * (u * t⁻¹) = u := by
    rw [zero_add, pow_one, mul_left_comm, mul_inv_cancel₀ ht0, mul_one]
  have hmem : t ^ (0 + 1) * (u * t⁻¹) ∈ P.integers := by rw [hu]; exact u.2
  -- The power-series expansion is taken of `t ^ (0 + 1) * (u * t⁻¹)` as an element of
  -- `P.integers`; identify that element with `u`.
  have hsub : (⟨t ^ (0 + 1) * (u * t⁻¹), hmem⟩ : P.integers) = u := Subtype.ext hu
  rw [P.residueResidueField_eq_coeff_powerSeriesExpansionResidueField ht 0 hmem, hsub,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_powerSeriesExpansionResidueField]

/-- The `k`-valued residue at a place with separable residue field: the trace from `F_P` to `k`
of the residue `res_{P,t}` (Stichtenoth, Remark 4.3.7).

This is the classical residue-field trace precisely when `Module.Finite k P.ResidueField`, which
`TauCeti.Place.finiteDimensional_residueField` supplies for every place of a function field.
Absent that, `Algebra.trace` is the junk value `0` (`Algebra.trace_eq_zero_of_not_exists_basis`),
the convention `TauCeti.Place.normResidue` and `TauCeti.Place.degree` follow as well. -/
-- Finiteness is documented rather than assumed: `Algebra.trace` consumes no such argument, so a
-- hypothesis here would be unused, which `unusedArguments` rejects.
noncomputable def traceResidue : F →ₗ[k] k :=
  (Algebra.trace k P.ResidueField).comp (P.residueResidueField ht)

/-- The `k`-valued residue is the trace of the residue. -/
theorem traceResidue_apply (z : F) :
    P.traceResidue ht z = Algebra.trace k P.ResidueField (P.residueResidueField ht z) := (rfl)

/-- **The trace residue of `u / t` is the trace of the value of `u` at `P`**, for a function `u`
regular at `P`. This is the `k`-valued form of
`TauCeti.Place.residueResidueField_mul_inv_uniformizer`, used when local components are expressed
as trace residues at places with nontrivial residue field. -/
theorem traceResidue_mul_inv_uniformizer (u : P.integers) :
    P.traceResidue ht (u * t⁻¹) =
      Algebra.trace k P.ResidueField (IsLocalRing.residue P.integers u) := by
  rw [traceResidue_apply, residueResidueField_mul_inv_uniformizer]

/-! ### Comparison with residues at rational places -/

section Rational

variable (hP : P.degree = 1)

/-- **At a rational place, the power-series expansion in the residue field is the power-series
expansion over `k`**, read in `F_P`. -/
theorem powerSeriesExpansionResidueField_eq_map (x : P.integers) :
    P.powerSeriesExpansionResidueField ht x =
      PowerSeries.map (algebraMap k P.ResidueField) (P.powerSeriesExpansion hP ht x) := by
  rw [powerSeriesExpansionResidueField_apply,
    ← completionIntegersEquivPowerSeries_completionIntegersEmbedding]
  refine (P.completionIntegersEquivPowerSeriesResidueField_eq_iff _ _ _).mpr fun n ↦ ?_
  have h := P.sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration hP ht
    (P.completionIntegersEquivPowerSeries hP ht (P.completionIntegersEmbedding x)) n
  rw [AlgEquiv.symm_apply_apply] at h
  simpa only [PowerSeries.coeff_map, AlgHom.commutes, coe_algebraMap_constants] using h

/-- **At a rational place, Laurent coefficients in the residue field are the Laurent coefficients
over `k`**, read in `F_P`. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_algebraMap (z : F) (n : ℤ) :
    (P.laurentSeriesExpansionResidueField ht z).coeff n =
      algebraMap k P.ResidueField ((P.laurentSeriesExpansion hP ht z).coeff n) := by
  -- Shift `z` by a power of `t` making it integral, with the shift large enough that `n`
  -- becomes a nonnegative index, and compare the two power-series expansions.
  have hz : t ^ (-min (P.ord z) n) * z ∈ P.integers :=
    P.mul_mem_integers_of_mem_filtration (by simp [ht])
      (P.filtration_antitone (min_le_left (P.ord z) n) (P.mem_filtration_ord z))
  have hn : (((n - min (P.ord z) n).toNat : ℕ) : ℤ) - -min (P.ord z) n = n := by omega
  rw [← hn,
    P.coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField ht _ hz,
    P.coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion hP ht _ hz,
    P.powerSeriesExpansionResidueField_eq_map ht hP, PowerSeries.coeff_map]

/-- **At a rational place the residue in the residue field is the residue over `k`**, read in
`F_P`. -/
theorem residueResidueField_eq_algebraMap_residue (z : F) :
    P.residueResidueField ht z = algebraMap k P.ResidueField (P.residue hP ht z) := by
  rw [residueResidueField_apply, residue_apply,
    P.coeff_laurentSeriesExpansionResidueField_eq_algebraMap ht hP]

/-- **At a rational place the `k`-valued residue is the residue over `k`.** -/
theorem traceResidue_eq_residue (z : F) : P.traceResidue ht z = P.residue hP ht z := by
  rw [traceResidue_apply, P.residueResidueField_eq_algebraMap_residue ht hP,
    Algebra.trace_algebraMap, ← degree_eq_finrank, hP, one_smul]

end Rational

end TauCeti.Place
