/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.EffectiveBounds.QuadraticClassNumber
public import TauCeti.NumberTheory.EffectiveBounds.DiscriminantEquality
public import TauCeti.FieldTheory.Trace

/-!
# Worked examples: the effective bounds on the named quadratic fields

The effective-bounds roadmap keeps its estimates honest with two arithmetic worked examples,
each asking that a general bound be exercised on a *named* number field rather than a
same-shape analogue:

* the discriminant bound recovers `|d_{ℚ(i)}| = 4` from the basis `{1, i}`;
* the class-number bound is non-vacuous on `ℚ(√-5)`, giving `h ≤ 64·5`.

This file realises both on concrete `NumberField` instances.

For `ℚ(√-5)` we take `AdjoinRoot (X² + 5)` over `ℚ` (a field because `X² + 5` is irreducible,
having no rational root), a degree-two number field with a square root of `-5`, and feed it to
`TauCeti.NumberField.classNumber_le_natAbs_of_sq_intCast`.

For `ℚ(i)` the class-number-style *upper* bound `|d_K| ≤ 4` is not enough: the criterion asks
for the *exact* discriminant, which needs the ring of integers. We take `ℚ(i)` as the fourth
cyclotomic field `CyclotomicField 4 ℚ`, whose ring of integers `ℤ[ζ₄] = ℤ[i]` Mathlib supplies
via `IsPrimitiveRoot.integralPowerBasisOfPrimePow` (`4 = 2²`). Its integral power basis `{1, i}`
feeds `TauCeti.NumberField.discr_eq_of_integralBasis`, and the trace-form evaluation
`disc ℚ {1, i} = 4·i² = -4` (`TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap`) then pins
`d_{ℚ(i)} = -4`, hence `|d_{ℚ(i)}| = 4`.

## Main results

* `TauCeti.NumberField.WorkedExamples.classNumber_adjoinRoot_sqrt_neg_five_le`: `h ≤ 320` for
  `ℚ(√-5)`.
* `TauCeti.NumberField.WorkedExamples.discr_cyclotomicField_four`: `d_{ℚ(i)} = -4`, with
  `abs_discr_cyclotomicField_four` and `natAbs_discr_cyclotomicField_four` its absolute-value
  forms recovering `|d_{ℚ(i)}| = 4`.

## Provenance

No formal code is vendored. The effective bounds consumed here (`abs_discr_le_of_basis_isIntegral`,
`classNumber_le_bound`, and the quadratic and equality corollaries) carry their own attribution to
`kim-em/erdos-unit-distance`; the `NumberField` constructions and the arithmetic specialisations
are new.
-/

public section

open Polynomial Module
open scoped NumberField

namespace TauCeti.NumberField.WorkedExamples

/-! ### `ℚ(√-5)`: the class-number bound is non-vacuous -/

/-- `X² + 5` is irreducible over `ℚ`: a monic quadratic with no rational root (a rational
square is nonnegative, but `-5 < 0`). -/
instance : Fact (Irreducible (X ^ 2 - C (-5 : ℚ))) := ⟨by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_sub_C]; decide
  · intro x hx
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg x]⟩

/-- **The class-number bound on `ℚ(√-5)`.** The class number of `ℚ(√-5)`, modelled as
`AdjoinRoot (X² + 5)`, is at most `64·5 = 320`; this is the roadmap's non-vacuity worked
example for the effective class-number bound. -/
theorem classNumber_adjoinRoot_sqrt_neg_five_le :
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (-5 : ℚ))) ≤ 320 := by
  set f : ℚ[X] := X ^ 2 - C (-5 : ℚ) with hf
  have hfne : f ≠ 0 := (monic_X_pow_sub_C _ (two_ne_zero)).ne_zero
  -- `[K : ℚ] = 2`.
  have hfin : finrank ℚ (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hfne).finrank, AdjoinRoot.powerBasis_dim hfne, hf,
      natDegree_X_pow_sub_C]
  -- The image of `AdjoinRoot.root f` is a square root of `-5`.
  have hx2 : (AdjoinRoot.root f) ^ 2 = algebraMap ℤ (AdjoinRoot f) (-5 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root f
    rw [hf, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero]
      at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot f)]
    norm_num
  -- The root is not rational: else `-5` would be a rational square.
  have hx : AdjoinRoot.root f ∉ (algebraMap ℚ (AdjoinRoot f)).range := by
    rintro ⟨q, hq⟩
    have h1 : algebraMap ℚ (AdjoinRoot f) (q ^ 2) = algebraMap ℚ (AdjoinRoot f) (-5 : ℚ) := by
      rw [map_pow, hq, hx2, IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot f)]; norm_num
    nlinarith [sq_nonneg q, (algebraMap ℚ (AdjoinRoot f)).injective h1]
  have := classNumber_le_natAbs_of_sq_intCast hfin hx2 hx
  simpa using this

/-! ### `ℚ(i)`: the discriminant bound recovers `|d| = 4` -/

/-- **The discriminant of `ℚ(i)`.** Modelling `ℚ(i)` as the fourth cyclotomic field, the field
discriminant is exactly `-4`. Combined with the trace-form evaluation of `{1, i}` and the
integral basis supplied by the cyclotomic ring of integers, this is the roadmap's `ℚ(i)` worked
example for the effective discriminant bound. -/
theorem discr_cyclotomicField_four :
    NumberField.discr (CyclotomicField 4 ℚ) = -4 := by
  haveI : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  haveI hcyc4 : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have h42 : (2 : ℕ) ^ 2 = 4 := by norm_num
  haveI hcyc : IsCyclotomicExtension {(2 : ℕ) ^ 2} ℚ (CyclotomicField 4 ℚ) := by
    rw [h42]; exact hcyc4
  have hζ4 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ)) 4 :=
    IsCyclotomicExtension.zeta_spec 4 ℚ _
  set ζ : CyclotomicField 4 ℚ := IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ) with hζdef
  have hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ 2) := by rw [h42]; exact hζ4
  -- `[ℚ(i) : ℚ] = φ(4) = 2`.
  have hfin : finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
    rw [IsCyclotomicExtension.finrank _ (cyclotomic.irreducible_rat (n := 4) (by norm_num))]; decide
  -- `i² = -1`.
  have hsq : ζ ^ 2 = algebraMap ℚ (CyclotomicField 4 ℚ) (-1 : ℚ) := by
    have h4 : (ζ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hζ4.pow_eq_one
    have hne : ζ ^ 2 ≠ 1 := hζ4.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    rw [map_neg, map_one]
    exact (sq_eq_one_iff.mp h4).resolve_left hne
  -- `i ∉ ℚ`: else `-1` would be a rational square.
  have hnotmem : ζ ∉ (algebraMap ℚ (CyclotomicField 4 ℚ)).range := by
    rintro ⟨q, hq⟩
    have h1 : algebraMap ℚ (CyclotomicField 4 ℚ) (q ^ 2) =
        algebraMap ℚ (CyclotomicField 4 ℚ) (-1 : ℚ) := by rw [map_pow, hq, hsq]
    nlinarith [sq_nonneg q, (algebraMap ℚ (CyclotomicField 4 ℚ)).injective h1]
  -- The integral power basis `{1, i}` of the ring of integers `ℤ[i]`.
  let pb : PowerBasis ℤ (𝓞 (CyclotomicField 4 ℚ)) := hζ.integralPowerBasisOfPrimePow
  have hdim : pb.dim = 2 := by
    change hζ.integralPowerBasisOfPrimePow.dim = 2
    rw [IsPrimitiveRoot.integralPowerBasisOfPrimePow_dim]; decide
  have hgen : algebraMap (𝓞 (CyclotomicField 4 ℚ)) (CyclotomicField 4 ℚ) pb.gen = ζ := by
    change algebraMap _ _ hζ.integralPowerBasisOfPrimePow.gen = ζ
    rw [hζ.integralPowerBasisOfPrimePow_gen]; rfl
  let c : Basis (Fin 2) ℤ (𝓞 (CyclotomicField 4 ℚ)) := pb.basis.reindex (finCongr hdim)
  have hcfun : (fun i => algebraMap (𝓞 (CyclotomicField 4 ℚ)) (CyclotomicField 4 ℚ) (c i)) =
      ![1, ζ] := by
    funext i
    fin_cases i <;>
      simp [c, Basis.reindex_apply, pb.basis_eq_pow, hgen]
  have key := TauCeti.NumberField.discr_eq_of_integralBasis c
  rw [hcfun, TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap hfin hsq hnotmem] at key
  have hQ : (NumberField.discr (CyclotomicField 4 ℚ) : ℚ) = -4 := by rw [← key]; ring
  exact_mod_cast hQ

/-- The absolute value of the discriminant of `ℚ(i)` is `4`. -/
theorem abs_discr_cyclotomicField_four :
    |NumberField.discr (CyclotomicField 4 ℚ)| = 4 := by
  rw [discr_cyclotomicField_four]; decide

/-- `|d_{ℚ(i)}| = 4` in `natAbs` form. -/
theorem natAbs_discr_cyclotomicField_four :
    (NumberField.discr (CyclotomicField 4 ℚ)).natAbs = 4 := by
  rw [discr_cyclotomicField_four]; rfl

end TauCeti.NumberField.WorkedExamples
