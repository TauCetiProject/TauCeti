/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Completion
public import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent-series expansions at rational places

At a rational place with a chosen uniformizer `t`, uniformizer expansion identifies the
completed field with `k((T))`. This extends the power-series identification of the completed
valuation ring: an integral element has the same image whether it is first expanded in `k[[T]]`
or mapped directly to `k((T))`. In particular, the chosen uniformizer maps to `T`.

This is the field-level expansion needed to read Laurent coefficients of local functions, and
in particular to define residues as coefficients of degree `-1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

public section

open scoped LaurentSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- The constant scalars on `k((T))` factor through `k[[T]]`. The scalar actions are stated through
the algebra structures, since the `k`-algebra structure on `k((T))` is the one inherited from
`k[[T]]` rather than the coefficientwise action. -/
@[local instance]
private theorem isScalarTower_powerSeries_laurentSeries :
    @IsScalarTower k (PowerSeries k) (LaurentSeries k) Algebra.toSMul Algebra.toSMul
      Algebra.toSMul :=
  .of_algebraMap_eq' rfl

/-- Uniformizer expansion identifies the completed field at a rational place with the Laurent
series field over the constants. It is the unique extension to fraction fields of
`TauCeti.Place.completionIntegersEquivPowerSeries`. -/
noncomputable def completionEquivLaurentSeries : P.Completion ≃ₐ[k] LaurentSeries k :=
  IsFractionRing.algEquivOfAlgEquiv (P.completionIntegersEquivPowerSeries hP ht)

/-- On the completed valuation ring, Laurent expansion is the coercion of power-series
expansion. -/
@[simp]
theorem completionEquivLaurentSeries_apply (x : P.completionPlace.integers) :
    P.completionEquivLaurentSeries hP ht (x : P.Completion) =
      HahnSeries.ofPowerSeries ℤ k (P.completionIntegersEquivPowerSeries hP ht x) := by
  rw [completionEquivLaurentSeries]
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap _ x

/-- The inverse Laurent expansion sends an embedded power series to the corresponding element of
the completed valuation ring. -/
@[simp]
theorem completionEquivLaurentSeries_symm_apply (f : PowerSeries k) :
    (P.completionEquivLaurentSeries hP ht).symm
        (HahnSeries.ofPowerSeries ℤ k f) =
      ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) := by
  apply (P.completionEquivLaurentSeries hP ht).injective
  rw [AlgEquiv.apply_symm_apply, P.completionEquivLaurentSeries_apply hP ht,
    AlgEquiv.apply_symm_apply]

/-- A completed function is integral exactly when its Laurent expansion comes from a power
series. -/
theorem exists_powerSeries_eq_completionEquivLaurentSeries_iff_mem_integers
    (z : P.Completion) :
    (∃ f : PowerSeries k, algebraMap (PowerSeries k) (LaurentSeries k) f =
      P.completionEquivLaurentSeries hP ht z) ↔ z ∈ P.completionPlace.integers := by
  constructor
  · rintro ⟨f, hf⟩
    have hf' : HahnSeries.ofPowerSeries ℤ k f =
        P.completionEquivLaurentSeries hP ht z := by
      simpa only [LaurentSeries.coe_algebraMap] using hf
    have hz : z =
        ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) := by
      apply (P.completionEquivLaurentSeries hP ht).injective
      rw [hf'.symm, P.completionEquivLaurentSeries_apply hP ht,
        AlgEquiv.apply_symm_apply]
    rw [hz]
    exact Subtype.property _
  · intro hz
    refine ⟨P.completionIntegersEquivPowerSeries hP ht ⟨z, hz⟩, ?_⟩
    simpa only [LaurentSeries.coe_algebraMap] using
      (P.completionEquivLaurentSeries_apply hP ht ⟨z, hz⟩).symm

/-- The chosen uniformizer maps to the Laurent-series variable. -/
@[simp]
theorem completionEquivLaurentSeries_uniformizer :
    P.completionEquivLaurentSeries hP ht (P.completionEmbedding t) =
      HahnSeries.single (1 : ℤ) (1 : k) := by
  let tInt : P.completionPlace.integers :=
    P.completionIntegersEmbedding
      ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  have htInt : (tInt : P.Completion) = P.completionEmbedding t := by
    exact P.completionIntegersEmbedding_apply _
  have htExpansion :
      P.completionIntegersEquivPowerSeries hP ht tInt = PowerSeries.X :=
    P.completionIntegersEquivPowerSeries_uniformizer hP ht
  rw [← htInt, P.completionEquivLaurentSeries_apply hP ht, htExpansion,
    HahnSeries.ofPowerSeries_X]

end TauCeti.Place
