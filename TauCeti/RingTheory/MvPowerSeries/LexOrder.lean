/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.LexOrder

/-!
# Coefficient-subspace division for multivariate power series

Let `K` be a field, `A` a `K`-algebra, and `E` a `K`-submodule of `A`. Multiplying a formal power
series `U : MvPowerSeries σ A` on the left by `MvPowerSeries.map (algebraMap K A) D` for a nonzero
scalar power series `D : MvPowerSeries σ K` preserves and reflects membership of all coefficients in
`E` whenever `σ` carries a linear order with `WellFoundedGT σ` — and therefore unconditionally
whenever `σ` is finite.

This formalizes the power-series coefficient-membership step of
[Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.3.2, Theorem 1: if
a nonzero scalar power series multiplies a power series over an extension ring into series with
coefficients in a `K`-subspace `E`, then the original power series already has all coefficients in
`E`.

## Main results

* `MvPowerSeries.coeff_map_mul_mem`: over any commutative semiring `R` and `R`-algebra `A`, if all
  coefficients of `U` lie in `E : Submodule R A`, so do all coefficients of
  `MvPowerSeries.map (algebraMap R A) D * U`.
* `MvPowerSeries.coeff_mem_of_coeff_map_mul_mem_of_wellFoundedGT` and
  `MvPowerSeries.forall_coeff_map_mul_mem_iff_of_wellFoundedGT`: the converse and equivalence over a
  field `K` for nonzero `D` when `[LinearOrder σ] [WellFoundedGT σ]`.
* `MvPowerSeries.coeff_mem_of_coeff_map_mul_mem` and `MvPowerSeries.forall_coeff_map_mul_mem_iff`:
  the unconditional converse and equivalence for `[Finite σ]`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.3.2, Theorem 1.
-/

public section

namespace MvPowerSeries

section Semiring

variable {σ R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Multiplying `U : MvPowerSeries σ A` on the left by a scalar series
`MvPowerSeries.map (algebraMap R A) D` preserves membership of coefficients in an `R`-submodule
`E : Submodule R A`. -/
theorem coeff_map_mul_mem (D : MvPowerSeries σ R) {U : MvPowerSeries σ A} {E : Submodule R A}
    (hU : ∀ α, coeff α U ∈ E) (β : σ →₀ ℕ) :
    coeff β (MvPowerSeries.map (algebraMap R A) D * U) ∈ E := by
  classical
  rw [coeff_mul]
  refine E.sum_mem fun uv _ ↦ ?_
  rw [coeff_map, ← Algebra.smul_def]
  exact E.smul_mem _ (hU uv.2)

end Semiring

section Field

variable {σ K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- If `[LinearOrder σ] [WellFoundedGT σ]`, `D : MvPowerSeries σ K` is nonzero, and all coefficients
of `MvPowerSeries.map (algebraMap K A) D * U` lie in `E : Submodule K A`, then all coefficients of
`U` lie in `E`. -/
theorem coeff_mem_of_coeff_map_mul_mem_of_wellFoundedGT [LinearOrder σ] [WellFoundedGT σ]
    {D : MvPowerSeries σ K} (hD : D ≠ 0) {U : MvPowerSeries σ A} {E : Submodule K A}
    (hmul : ∀ β, coeff β (MvPowerSeries.map (algebraMap K A) D * U) ∈ E) (α : σ →₀ ℕ) :
    coeff α U ∈ E := by
  classical
  obtain ⟨p, hp⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hD
  have hp_ne : coeff p D ≠ 0 := coeff_ne_zero_of_lexOrder hp.symm
  suffices ∀ q : Lex (σ →₀ ℕ), coeff (ofLex q) U ∈ E from this (toLex α)
  intro q
  induction q using WellFoundedLT.induction with
  | ind q ih =>
    set d := ofLex q
    have hprod := hmul (p + d)
    rw [coeff_mul, ← Finset.add_sum_erase _ _ (a := (p, d)) (Finset.mem_antidiagonal.mpr rfl),
      coeff_map, ← Algebra.smul_def] at hprod
    have herase : ∑ uv ∈ (Finset.antidiagonal (p + d)).erase (p, d),
        coeff uv.1 (MvPowerSeries.map (algebraMap K A) D) * coeff uv.2 U ∈ E := by
      refine E.sum_mem fun uv huv ↦ ?_
      obtain ⟨hne, hadd⟩ := Finset.mem_erase.mp huv
      rw [Finset.mem_antidiagonal] at hadd
      rcases trichotomy_of_add_eq_add (congrArg toLex hadd) with h | h | h
      · exact False.elim (hne (Prod.ext (toLex.injective h.1) (toLex.injective h.2)))
      · have h0 : coeff uv.1 D = 0 :=
          coeff_eq_zero_of_lt_lexOrder (hp.symm ▸ WithTop.coe_lt_coe.mpr h)
        rw [coeff_map, h0, map_zero, zero_mul]
        exact E.zero_mem
      · rw [coeff_map, ← Algebra.smul_def]
        exact E.smul_mem _ (ih (toLex uv.2) h)
    have hsmul : coeff p D • coeff d U ∈ E := (add_mem_cancel_right herase).mp hprod
    simpa only [inv_smul_smul₀ hp_ne] using E.smul_mem (coeff p D)⁻¹ hsmul

/-- Under `[LinearOrder σ] [WellFoundedGT σ]`, multiplying on the left by a nonzero scalar power
series `D : MvPowerSeries σ K` preserves and reflects coefficient membership in `E : Submodule K A`.
-/
theorem forall_coeff_map_mul_mem_iff_of_wellFoundedGT [LinearOrder σ] [WellFoundedGT σ]
    {D : MvPowerSeries σ K} (hD : D ≠ 0) {U : MvPowerSeries σ A} {E : Submodule K A} :
    (∀ β, coeff β (MvPowerSeries.map (algebraMap K A) D * U) ∈ E) ↔ ∀ α, coeff α U ∈ E :=
  ⟨coeff_mem_of_coeff_map_mul_mem_of_wellFoundedGT hD, coeff_map_mul_mem D⟩

/-- In finitely many variables, if `D : MvPowerSeries σ K` is nonzero and all coefficients of
`MvPowerSeries.map (algebraMap K A) D * U` lie in `E : Submodule K A`, then all coefficients of `U`
lie in `E` ([bosch-guntzer-remmert], §5.3.2, Theorem 1). -/
theorem coeff_mem_of_coeff_map_mul_mem [Finite σ]
    {D : MvPowerSeries σ K} (hD : D ≠ 0) {U : MvPowerSeries σ A} {E : Submodule K A}
    (hmul : ∀ β, coeff β (MvPowerSeries.map (algebraMap K A) D * U) ∈ E) (α : σ →₀ ℕ) :
    coeff α U ∈ E := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  exact coeff_mem_of_coeff_map_mul_mem_of_wellFoundedGT hD hmul α

/-- In finitely many variables, multiplying on the left by a nonzero scalar power series
`D : MvPowerSeries σ K` preserves and reflects coefficient membership in `E : Submodule K A`. -/
theorem forall_coeff_map_mul_mem_iff [Finite σ]
    {D : MvPowerSeries σ K} (hD : D ≠ 0) {U : MvPowerSeries σ A} {E : Submodule K A} :
    (∀ β, coeff β (MvPowerSeries.map (algebraMap K A) D * U) ∈ E) ↔ ∀ α, coeff α U ∈ E :=
  ⟨coeff_mem_of_coeff_map_mul_mem hD, coeff_map_mul_mem D⟩

end Field

end MvPowerSeries
