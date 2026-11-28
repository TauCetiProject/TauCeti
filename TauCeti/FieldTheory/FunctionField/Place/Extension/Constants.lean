/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Restriction of constants and place extensions

Restricting the constant field of a place `P'` of `F' / k'` to a subfield `k ⊆ k'` preserves its
restriction to `F / k`, its ramification index `e(P' ∣ P)`, and its relative degree `f(P' ∣ P)`.

## Main results

* `TauCeti.Place.restrict_restrictConstants`:
  `(P'.restrictConstants k).restrict k F = P'.restrict k F`.
* `TauCeti.Place.ramificationIdx_restrictConstants`:
  `ramificationIdx F (P'.restrictConstants k₀) = ramificationIdx F P'`.
* `TauCeti.Place.relativeDegree_restrictConstants`:
  `relativeDegree k F (P'.restrictConstants k) = relativeDegree k F P'`.
-/

public section

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section

variable (k F) (P' : Place k' F')

/-- Restricting the constant field of `P'` to `k` does not change its restriction to `F / k`. -/
@[simp]
theorem restrict_restrictConstants [Algebra.IsIntegral F F'] :
    (P'.restrictConstants k).restrict k F = P'.restrict k F := by
  refine (restrict_eq_iff_integers_le k F (P'.restrictConstants k) (P'.restrict k F)).mpr
    fun f hf ↦ ?_
  rw [integers_restrictConstants]
  exact (mem_integers_restrict_iff k F P' f).mp hf

omit [Field k] [Algebra k F] [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- Restricting the constant field of `P'` does not change its ramification index over `F`. -/
@[simp]
theorem ramificationIdx_restrictConstants {k₀ : Type*} [Field k₀] [Algebra k₀ k']
    [Algebra k₀ F'] [IsScalarTower k₀ k' F'] :
    ramificationIdx F (P'.restrictConstants k₀) = ramificationIdx F P' := by
  simp [ramificationIdx_def]

/-- Restricting the constant field of `P'` to `k` does not change its relative degree over
`F / k`. -/
@[simp]
theorem relativeDegree_restrictConstants [Algebra.IsIntegral F F'] :
    relativeDegree k F (P'.restrictConstants k) = relativeDegree k F P' := by
  rw [relativeDegree_def, relativeDegree_def]
  have h₁ : ((P'.restrictConstants k).restrict k F).integers.toSubring =
      (P'.restrict k F).integers.toSubring :=
    congrArg (fun R : Place k F ↦ R.integers.toSubring) (restrict_restrictConstants k F P')
  have h₂ : (P'.restrictConstants k).integers.toSubring = P'.integers.toSubring :=
    congrArg ValuationSubring.toSubring (integers_restrictConstants P')
  refine finrank_residueField_eq_of_equiv_equiv
    (RingEquiv.subringCongr h₁) (RingEquiv.subringCongr h₂) (RingHom.ext fun _ ↦ rfl)

end

end TauCeti.Place
