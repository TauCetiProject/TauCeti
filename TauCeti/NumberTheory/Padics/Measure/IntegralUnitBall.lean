/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients
public import TauCeti.NumberTheory.Padics.Measure.MahlerDuality
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.NumberTheory.Padics.Measure.Dirac

/-!
# Integral measures on `ℤ_p` and the dual unit ball

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
