/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
public import TauCeti.NumberTheory.Padics.Measure.MahlerDuality
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.NumberTheory.Padics.Measure.Dirac

/-!
# Integral measures on `ℤ_p` and the dual unit ball

On any compact space, a `ℤ_p`-valued measure is `1`-Lipschitz for the supremum norm
(`AbstractMeasure.norm_apply_le`): a test function of norm at most `p⁻ᵏ` is `pᵏ` times a test
function, so its integral is divisible by `pᵏ`. This is the uniform bound that makes the integral
measures behave like a dual unit ball.

A `ℚ_p`-valued measure `ν` on `ℤ_p` is integral when it is the extension of coefficients of a
`ℤ_p`-valued measure `μ`, that is, when `ν (f) = μ (f)` for every `ℤ_p`-valued test function `f`.
This file identifies the integral measures with the closed unit ball for the operator norm, and
describes that ball on the side of the Amice transform:

* extension of coefficients along a continuous `ℤ_[p]`-algebra map `j` applies `j` to the
  coefficients of the Amice transform (`AbstractMeasure.amiceTransform_extendCoefficients`). For
  `ℤ_p ⊆ ℚ_p` this is the compatibility of Mathlib's integral Amice equivalence
  `AbstractMeasure.amiceTransformEquiv` with extension to `ℚ_p`
  (`AbstractMeasure.amiceTransform_extendCoefficients_coe_ringHom`);
* a `ℚ_p`-valued measure has operator norm at most `1` exactly when it is the unique extension of
  a `ℤ_p`-valued measure (`AbstractMeasure.existsUnique_integral_iff_norm_le_one`), and exactly when
  its Amice transform has coefficients in `ℤ_p`
  (`AbstractMeasure.norm_toCLMEquiv_le_one_iff_exists_amiceTransform_eq_map`).

The first characterisation is the case `j : ℤ_[p] → ℚ_[p]` of
`AbstractMeasure.existsUnique_apply_comp_eq_iff_norm_le_one`: a measure of norm at most `1` sends
`ℤ_p`-valued test functions, of norm at most `1`, into `ℤ_p`. The second combines it with Mahler
duality, which computes the operator norm as the supremum of the norms of the moments.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, §3, Remark 3.28.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3 and §II.2.
-/

public section

open scoped AbstractMeasure PowerSeries

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

section Lipschitz

variable {X : Type*} [TopologicalSpace X]

/-- A test function whose values all have norm at most `p⁻ᵏ` is `pᵏ` times a `ℤ_p`-valued test
function, so its integral has norm at most `p⁻ᵏ`. -/
private theorem norm_apply_le_of_forall_norm_le (μ : D(X, ℤ_[p])) {f : C(X, ℤ_[p])} {k : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ (p : ℝ) ^ (-k : ℤ)) : ‖μ f‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  -- Divide `f` by `p ^ k` inside `ℚ_p`; the quotient still takes values in `ℤ_p`.
  have hmem : ∀ x, ‖(f x : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1 := fun x ↦ by
    rw [norm_div, norm_pow, Padic.norm_p, ← PadicInt.norm_def, div_le_one (by positivity),
      inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hf x
  let g : C(X, ℤ_[p]) := ⟨fun x ↦ Padic.lift _ (hmem x),
    ((continuous_subtype_val.comp f.continuous).div_const _).subtype_mk hmem⟩
  have hg : ∀ x, (g x : ℚ_[p]) = f x / (p : ℚ_[p]) ^ k := fun _ ↦ rfl
  have hfg : f = (p : ℤ_[p]) ^ k • g := by
    ext x
    have : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ (mod_cast (Fact.out : p.Prime).ne_zero)
    simp [hg, mul_div_cancel₀ _ this]
  rw [hfg, map_smul, smul_eq_mul, norm_mul, PadicInt.norm_p_pow]
  exact mul_le_of_le_one_right (zpow_nonneg hp.le _) (PadicInt.norm_le_one _)

/-- **Integral measures are `1`-Lipschitz.** On a compact space, every `ℤ_p`-valued measure
satisfies `‖μ f‖ ≤ ‖f‖` for the supremum norm on test functions. -/
theorem norm_apply_le [CompactSpace X] (μ : D(X, ℤ_[p])) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖ := by
  by_contra! h
  have hμf : μ f ≠ 0 := by
    rintro h0
    rw [h0, norm_zero] at h
    exact (norm_nonneg f).not_gt h
  rw [PadicInt.norm_eq_zpow_neg_valuation hμf] at h
  -- Every value of `f` has norm below `‖μ f‖ = p ^ (-v)`, hence at most `p ^ (-(v + 1))`.
  have hle : ∀ x, ‖f x‖ ≤ (p : ℝ) ^ (-((μ f).valuation + 1 : ℕ) : ℤ) := fun x ↦ by
    rw [Nat.cast_succ, neg_add, ← sub_eq_add_neg]
    exact (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one _ _).mp
      ((f.norm_coe_le_norm x).trans_lt h)
  have hμ := norm_apply_le_of_forall_norm_le μ hle
  rw [PadicInt.norm_eq_zpow_neg_valuation hμf] at hμ
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  exact (zpow_lt_zpow_right₀ hp (by omega)).not_ge hμ

end Lipschitz

/-- Extension of coefficients along a continuous `ℤ_[p]`-algebra map `j` into the closed unit ball
applies `j` to the coefficients of the Amice transform. -/
@[simp]
theorem amiceTransform_extendCoefficients {O K : Type*} [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra ℤ_[p] K] [ContinuousSMul ℤ_[p] K]
    (j : O →ₐ[ℤ_[p]] K) (hjc : Continuous j) (hj : ∀ a, ‖j a‖ ≤ 1) (μ : D(ℤ_[p], O)) :
    (extendCoefficients (j : O →+* K) hj μ).amiceTransform =
      PowerSeries.map (j : O →+* K) μ.amiceTransform := by
  ext n
  simp only [coeff_amiceTransform, PowerSeries.coeff_map]
  rw [← extendCoefficients_apply_comp (j : O →+* K) μ hj hjc]
  congr 1
  ext x
  simp

/-- Extension of coefficients from `ℤ_p` to `ℚ_p` applies the inclusion to the coefficients of the
Amice transform. -/
@[simp]
theorem amiceTransform_extendCoefficients_coe_ringHom (μ : D(ℤ_[p], ℤ_[p])) :
    (extendCoefficients PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one μ).amiceTransform =
      PowerSeries.map PadicInt.Coe.ringHom μ.amiceTransform := by
  have hjc : Continuous (Algebra.ofId ℤ_[p] ℚ_[p]) := by
    rw [← RingHom.coe_coe, Algebra.toRingHom_ofId, PadicInt.algebraMap_eq_coe_ringHom]
    exact PadicInt.isEmbedding_coe_ringHom.continuous
  simpa only [Algebra.toRingHom_ofId, PadicInt.algebraMap_eq_coe_ringHom] using
    amiceTransform_extendCoefficients (Algebra.ofId ℤ_[p] ℚ_[p]) hjc
      (by simpa using PadicInt.norm_le_one) μ

/-- **The integral dual unit ball.** A `ℚ_p`-valued measure on `ℤ_p` has operator norm at most `1`
exactly when there is a unique `ℤ_p`-valued measure `μ` with `ν (f) = μ (f)` for every
`ℤ_p`-valued test function `f`. -/
theorem existsUnique_integral_iff_norm_le_one (ν : D(ℤ_[p], ℚ_[p])) :
    (∃! μ : D(ℤ_[p], ℤ_[p]), ∀ f : C(ℤ_[p], ℤ_[p]),
      ν ((⟨fun x : ℤ_[p] ↦ (x : ℚ_[p]), continuous_subtype_val⟩ : C(ℤ_[p], ℚ_[p])).comp f) =
        (μ f : ℚ_[p])) ↔ ‖toCLMEquiv ν‖ ≤ 1 :=
  -- The roadmap's test map `fun x ↦ (x : ℚ_[p])` is `PadicInt.Coe.ringHom` by definition.
  existsUnique_apply_comp_eq_iff_norm_le_one PadicInt.norm_coe_ringHom_le_one
    PadicInt.isEmbedding_coe_ringHom PadicInt.closedBall_subset_range_coe_ringHom ν

/-- A `ℚ_p`-valued measure on `ℤ_p` has operator norm at most `1` exactly when its Amice transform
has coefficients in `ℤ_p`. -/
theorem norm_toCLMEquiv_le_one_iff_exists_amiceTransform_eq_map (ν : D(ℤ_[p], ℚ_[p])) :
    ‖toCLMEquiv ν‖ ≤ 1 ↔
      ∃ F : ℤ_[p]⟦X⟧, ν.amiceTransform = PowerSeries.map PadicInt.Coe.ringHom F := by
  refine ⟨fun hν ↦ ?_, fun ⟨F, hF⟩ ↦ ?_⟩
  · obtain ⟨μ, rfl⟩ := (mem_range_extendCoefficients_iff PadicInt.norm_coe_ringHom_le_one
      PadicInt.isEmbedding_coe_ringHom PadicInt.closedBall_subset_range_coe_ringHom).mpr hν
    exact ⟨μ.amiceTransform, amiceTransform_extendCoefficients_coe_ringHom μ⟩
  · rw [norm_toCLMEquiv_le_iff_forall_norm_coeff_le, hF]
    intro n
    simpa using (F.coeff n).norm_le_one

/-! The checks of the integral dual unit ball: the zero measure and the Dirac measures are integral,
while `p⁻¹ δ₀` is not. -/

example : ‖toCLMEquiv (0 : D(ℤ_[p], ℚ_[p]))‖ ≤ 1 := by
  simp

example (x : ℤ_[p]) : ‖toCLMEquiv (dirac ℚ_[p] x)‖ ≤ 1 :=
  (TauCeti.AbstractMeasure.norm_dirac x).le

example : ¬ ∃! μ : D(ℤ_[p], ℤ_[p]), ∀ f : C(ℤ_[p], ℤ_[p]),
    ((p : ℚ_[p])⁻¹ • dirac ℚ_[p] (0 : ℤ_[p]))
        ((⟨fun x : ℤ_[p] ↦ (x : ℚ_[p]), continuous_subtype_val⟩ : C(ℤ_[p], ℚ_[p])).comp f) =
      (μ f : ℚ_[p]) := by
  rw [existsUnique_integral_iff_norm_le_one]
  simp only [map_smul, norm_smul, TauCeti.AbstractMeasure.norm_dirac, norm_inv, Padic.norm_p,
    mul_one, inv_inv, not_le]
  exact_mod_cast (Fact.out : p.Prime).one_lt

end AbstractMeasure
