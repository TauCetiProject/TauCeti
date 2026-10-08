/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.LaurentSeries

/-!
# Laurent coefficients and residues at rational places

At a rational place `P`, a uniformizer `t` identifies the completed local function field with
`k((X))`.  This file extracts the resulting Laurent coefficients, both on the completion and on
the original function field.  The coefficient of `X⁻¹` is the local residue

`res_{P,t}(z) = a₋₁`  when  `z = ∑ aᵢ tⁱ`.

The residue vanishes on functions regular at `P`, takes the value `1` on `t⁻¹`, and kills formal
derivatives.  The last property is the basic calculation behind the change-of-uniformizer formula
and the eventual interpretation of residues as local components of Weil differentials.

## Main definitions

* `TauCeti.Place.completionLaurentCoeff`: Laurent coefficients on the completed local field.
* `TauCeti.Place.completionResidueAtUniformizer`: the completed coefficient of exponent `-1`.
* `TauCeti.Place.laurentCoeff`: Laurent coefficients of functions in the original field.
* `TauCeti.Place.residueAtUniformizer`: the coefficient of `t⁻¹` in a local expansion.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Definition 4.2.8 and
Proposition 4.2.9.
-/

public section

open scoped LaurentSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- The `n`-th Laurent coefficient on the completed local field, with respect to the uniformizer
`t`. -/
noncomputable def completionLaurentCoeff (n : ℤ) : P.Completion →ₗ[k] k :=
  { toFun := fun z ↦ (P.completionEquivLaurentSeries hP ht z).coeff n
    map_add' := fun x y ↦ by simp
    map_smul' := fun c x ↦ by
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
      simp [LaurentSeries.algebraMap_apply] }

/-- The completed Laurent coefficient is the corresponding coefficient of the Laurent-series
expansion. -/
@[simp]
theorem completionLaurentCoeff_apply (n : ℤ) (z : P.Completion) :
    P.completionLaurentCoeff hP ht n z =
      (P.completionEquivLaurentSeries hP ht z).coeff n :=
  (rfl)

/-- Elements of the completed local field are equal exactly when all their Laurent coefficients
are equal. -/
theorem eq_iff_forall_completionLaurentCoeff_eq {x y : P.Completion} :
    x = y ↔ ∀ n : ℤ,
      P.completionLaurentCoeff hP ht n x = P.completionLaurentCoeff hP ht n y := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply (P.completionEquivLaurentSeries hP ht).injective
    apply HahnSeries.ext
    funext n
    exact h n

/-- The coefficient of a Laurent monomial is zero away from its exponent. -/
theorem completionLaurentCoeff_symm_single (m n : ℤ) (c : k) :
    P.completionLaurentCoeff hP ht n
        ((P.completionEquivLaurentSeries hP ht).symm (HahnSeries.single m c)) =
      if n = m then c else 0 := by
  simp [completionLaurentCoeff_apply, HahnSeries.coeff_single]

/-- The negative Laurent coefficients of an integral element of the completed local field
vanish. -/
theorem completionLaurentCoeff_coe_integer_eq_zero (z : P.completionPlace.integers)
    {n : ℤ} (hn : n < 0) :
    P.completionLaurentCoeff hP ht n (z : P.Completion) = 0 := by
  rw [completionLaurentCoeff_apply, P.completionEquivLaurentSeries_apply_integer,
    HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨m, hm⟩
  have : 0 ≤ n := hm ▸ Int.natCast_nonneg m
  omega

/-- The completed residue with respect to `t`, given by the coefficient of exponent `-1`. -/
noncomputable def completionResidueAtUniformizer : P.Completion →ₗ[k] k :=
  P.completionLaurentCoeff hP ht (-1)

/-- The completed residue is the coefficient of exponent `-1`. -/
@[simp]
theorem completionResidueAtUniformizer_apply (z : P.Completion) :
    P.completionResidueAtUniformizer hP ht z =
      (P.completionEquivLaurentSeries hP ht z).coeff (-1) :=
  (rfl)

/-- The completed residue vanishes on the completed valuation ring. -/
theorem completionResidueAtUniformizer_coe_integer_eq_zero
    (z : P.completionPlace.integers) :
    P.completionResidueAtUniformizer hP ht (z : P.Completion) = 0 :=
  P.completionLaurentCoeff_coe_integer_eq_zero hP ht z (by omega)

/-- The `n`-th Laurent coefficient of a function at `P`, with respect to the uniformizer `t`.
This is the completed coefficient after the canonical embedding `F → F̂_P`. -/
noncomputable def laurentCoeff (n : ℤ) : F →ₗ[k] k :=
  (P.completionLaurentCoeff hP ht n).comp P.completionEmbedding.toLinearMap

/-- The Laurent coefficient of a function is read from its image in the completed local field. -/
@[simp]
theorem laurentCoeff_apply (n : ℤ) (z : F) :
    P.laurentCoeff hP ht n z =
      (P.completionEquivLaurentSeries hP ht (P.completionEmbedding z)).coeff n :=
  (rfl)

/-- Functions are equal exactly when all their Laurent coefficients at one rational place are
equal. -/
theorem eq_iff_forall_laurentCoeff_eq {x y : F} :
    x = y ↔ ∀ n : ℤ, P.laurentCoeff hP ht n x = P.laurentCoeff hP ht n y := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply P.completionEmbedding.injective
    rw [P.eq_iff_forall_completionLaurentCoeff_eq hP ht]
    exact h

/-- The Laurent expansion of a constant has only its coefficient of exponent zero. -/
theorem laurentCoeff_algebraMap (n : ℤ) (c : k) :
    P.laurentCoeff hP ht n (algebraMap k F c) = if n = 0 then c else 0 := by
  simp [laurentCoeff_apply, LaurentSeries.algebraMap_apply, HahnSeries.coeff_single]

/-- The chosen uniformizer has the single Laurent coefficient `1` at exponent one. -/
theorem laurentCoeff_uniformizer (n : ℤ) :
    P.laurentCoeff hP ht n t = if n = 1 then 1 else 0 := by
  rw [laurentCoeff_apply, P.completionEquivLaurentSeries_uniformizer]
  simp [HahnSeries.coeff_single]

/-- A function regular at `P` has no negative Laurent coefficients. -/
theorem laurentCoeff_eq_zero_of_mem_integers {z : F} (hz : z ∈ P.integers)
    {n : ℤ} (hn : n < 0) : P.laurentCoeff hP ht n z = 0 := by
  have h := P.completionLaurentCoeff_coe_integer_eq_zero hP ht
    (P.completionIntegersEmbedding ⟨z, hz⟩) hn
  rwa [completionIntegersEmbedding_apply, completionLaurentCoeff_apply,
    ← laurentCoeff_apply] at h

/-- The residue `res_{P,t}(z)` of a local function with respect to the uniformizer `t`: the
coefficient of `t⁻¹` in its Laurent expansion (Stichtenoth, Definition 4.2.8). -/
noncomputable def residueAtUniformizer : F →ₗ[k] k :=
  (P.completionResidueAtUniformizer hP ht).comp P.completionEmbedding.toLinearMap

/-- The residue is the coefficient of exponent `-1`. -/
@[simp]
theorem residueAtUniformizer_apply (z : F) :
    P.residueAtUniformizer hP ht z =
      (P.completionEquivLaurentSeries hP ht (P.completionEmbedding z)).coeff (-1) :=
  (rfl)

/-- A function regular at `P` has zero residue. -/
theorem residueAtUniformizer_eq_zero_of_mem_integers {z : F} (hz : z ∈ P.integers) :
    P.residueAtUniformizer hP ht z = 0 :=
  P.laurentCoeff_eq_zero_of_mem_integers hP ht hz (by omega)

/-- The residue of the inverse uniformizer is one: `res_{P,t}(t⁻¹) = 1`. -/
theorem residueAtUniformizer_inv_uniformizer :
    P.residueAtUniformizer hP ht t⁻¹ = 1 := by
  rw [residueAtUniformizer_apply, map_inv₀,
    map_inv₀ (P.completionEquivLaurentSeries hP ht),
    P.completionEquivLaurentSeries_uniformizer]
  simp

/-- The coefficient of `X⁻¹` in the formal derivative of a Laurent series is zero.  Equivalently,
the local residue kills formal derivatives. -/
theorem completionResidueAtUniformizer_symm_derivative (f : LaurentSeries k) :
    P.completionResidueAtUniformizer hP ht
        ((P.completionEquivLaurentSeries hP ht).symm (LaurentSeries.derivative k f)) = 0 := by
  simp [completionResidueAtUniformizer_apply, LaurentSeries.derivative_apply]

end TauCeti.Place
