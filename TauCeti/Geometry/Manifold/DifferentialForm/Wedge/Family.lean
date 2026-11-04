/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The wedge product of a finite family of one-forms

For one-forms `α 0, …, α (k - 1)` on a manifold, their wedge product
`α 0 ∧ ⋯ ∧ α (k - 1)` is the `k`-form whose value on tangent vectors `v 0, …, v (k - 1)` is the
determinant of the matrix `(α i (v j))` (`TauCeti.RoughForm.wedgeFamily`). It is built pointwise
from Mathlib's row determinant `Matrix.detRowAlternating`, precomposed with the linear map
`v ↦ (α i v)ᵢ`. For two one-forms it is the binary wedge product `α 0 ∧ α 1`
(`TauCeti.RoughForm.wedgeFamily_two`).

This is the form `dx₁ ∧ ⋯ ∧ dxₙ` of a family of coordinate one-forms, the standard way to produce a
top form, and hence a volume form or an orientation, from one-forms. The construction commutes
with pullback, multiplies by the sign of a permutation when the family is reordered, and by the
product of the factors when each one-form is rescaled. A family of `C^n` one-forms has a `C^n`
wedge product.

## Main definitions

* `TauCeti.RoughForm.wedgeFamily α`: the wedge product `α 0 ∧ ⋯ ∧ α (k - 1)` of a family of
  one-forms.
* `TauCeti.SmoothForm.wedgeFamily α`: the same for smooth one-forms, as a smooth form.

## Main results

* `TauCeti.RoughForm.wedgeFamily_apply`: the determinant formula.
* `TauCeti.RoughForm.wedgeFamily_two`, `TauCeti.SmoothForm.wedgeFamily_two`: agreement with the
  binary wedge product.
* `TauCeti.RoughForm.mpullback_wedgeFamily`: naturality under pullback.
* `TauCeti.RoughForm.wedgeFamily_comp_perm`: reordering the family multiplies by the sign of the
  permutation.
* `TauCeti.RoughForm.wedgeFamily_smul`: rescaling each one-form multiplies by the product of the
  factors.
* `TauCeti.IsSmoothForm.wedgeFamily`: regularity.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 14.11 (the determinant formula for a wedge product
  of covectors).
-/

public section

noncomputable section

open Bundle Matrix
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] {k : ℕ}

namespace RoughForm

/-- The **wedge product** `α 0 ∧ ⋯ ∧ α (k - 1)` of a family of one-forms: the `k`-form whose value
on tangent vectors `v 0, …, v (k - 1)` is the determinant of the matrix `(α i (v j))`
(`TauCeti.RoughForm.wedgeFamily_apply`). -/
def wedgeFamily (α : Fin k → RoughForm I M ℝ 1) : RoughForm I M ℝ k := fun x ↦
  (AlternatingMap.toContinuousAlternatingMap Matrix.detRowAlternating).compContinuousLinearMap
    (ContinuousLinearMap.pi fun i ↦
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)).symm (α i x))

/-- The wedge product of a family of one-forms is the determinant of the matrix of the one-forms
evaluated on the tangent vectors. -/
@[simp]
theorem wedgeFamily_apply (α : Fin k → RoughForm I M ℝ 1) (x : M)
    (v : Fin k → TangentSpace I x) :
    wedgeFamily α x v = (Matrix.of fun i j ↦ α i x ![v j]).det := by
  -- Mathlib defines `Matrix.det` as `Matrix.detRowAlternating` evaluated on the rows of the
  -- matrix; here the rows are `j ↦ (α i x (v j))ᵢ`.
  have hrows : wedgeFamily α x v = (Matrix.of fun j i ↦ α i x fun _ ↦ v j).det := by
    rw [wedgeFamily, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      AlternatingMap.coe_toContinuousAlternatingMap]
    rfl
  rw [hrows, ← det_transpose]
  congr 1
  ext i j
  rw [transpose_apply, of_apply, of_apply]
  exact congrArg (α i x) (funext fun l ↦ (Matrix.cons_val_fin_one (v j) ![] l).symm)

/-- The wedge product of two one-forms as a family is their binary wedge product. -/
theorem wedgeFamily_two (α : Fin 2 → RoughForm I M ℝ 1) :
    wedgeFamily α = (α 0).wedge (α 1) := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  rw [wedgeFamily_apply, det_fin_two, hv, wedge_apply_one_one]
  -- The entries of the `2 × 2` matrix are the four values `α i x ![v j]`.
  rfl

/-- Pullback commutes with the wedge product of a family of one-forms. -/
theorem mpullback_wedgeFamily (f : M → M') (α : Fin k → RoughForm I' M' ℝ 1) :
    mpullback I I' f (wedgeFamily α) = wedgeFamily fun i ↦ mpullback I I' f (α i) := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [mpullback_apply, wedgeFamily_apply]
  congr 1
  ext i j
  rw [of_apply, of_apply]
  exact congrArg (α i (f x))
    (funext fun l ↦ by rw [Matrix.cons_val_fin_one, Matrix.cons_val_fin_one])

/-- Reordering a family of one-forms by a permutation `σ` multiplies their wedge product by the
sign of `σ`. -/
theorem wedgeFamily_comp_perm (α : Fin k → RoughForm I M ℝ 1) (σ : Equiv.Perm (Fin k)) :
    wedgeFamily (α ∘ σ) = (Equiv.Perm.sign σ : ℝ) • wedgeFamily α := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, wedgeFamily_apply, wedgeFamily_apply,
    smul_eq_mul, ← det_permute]
  -- Permuting the rows of `(α i x ![v j])` by `σ` gives the matrix of the family `α ∘ σ`.
  rfl

/-- Rescaling each one-form `α i` by `c i` multiplies their wedge product by `∏ i, c i`. -/
theorem wedgeFamily_smul (c : Fin k → ℝ) (α : Fin k → RoughForm I M ℝ 1) :
    wedgeFamily (fun i ↦ c i • α i) = (∏ i, c i) • wedgeFamily α := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, wedgeFamily_apply, wedgeFamily_apply,
    smul_eq_mul, ← det_mul_column]
  -- Scaling the `i`-th row of `(α i x ![v j])` by `c i` gives the matrix of the family `c i • α i`.
  rfl

end RoughForm

/-- The wedge product of a family of `C^n` one-forms is `C^n`. -/
theorem IsSmoothForm.wedgeFamily [IsManifold I 1 M] [FiniteDimensional ℝ E] {n : WithTop ℕ∞}
    {α : Fin k → RoughForm I M ℝ 1} (hα : ∀ i, IsSmoothForm I n (α i)) :
    IsSmoothForm I n (RoughForm.wedgeFamily α) := by
  refine isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mpr fun x v ↦ ?_
  -- Each matrix entry is the value of a `C^n` one-form on a frame vector of the trivialization.
  have hentry (i j : Fin k) : ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ α i y ![(trivializationAt E (TangentSpace I) x).symmL ℝ y (v j)]) x := by
    refine (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp (hα i) x
      ![v j]).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    congr 1
    exact funext fun l ↦ by simp
  simp only [RoughForm.wedgeFamily_apply, det_apply']
  -- The determinant is a polynomial in the matrix entries.
  refine contMDiffAt_finsetSum fun σ _ ↦ contMDiffAt_const.mul ?_
  exact contMDiffAt_finsetProd fun i _ ↦ by
    simpa only [of_apply, Function.comp_apply] using hentry (σ i) i

namespace SmoothForm

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- The **wedge product** `α 0 ∧ ⋯ ∧ α (k - 1)` of a family of smooth one-forms, as a smooth
`k`-form. -/
def wedgeFamily (α : Fin k → SmoothForm I M ℝ 1) : SmoothForm I M ℝ k :=
  ⟨RoughForm.wedgeFamily fun i ↦ (α i).1,
    (IsSmoothForm.wedgeFamily fun i ↦ (α i).isSmoothForm).mem_smoothBundleForms⟩

/-- The underlying rough form of the wedge product of a family of smooth one-forms. -/
@[simp]
theorem coe_wedgeFamily (α : Fin k → SmoothForm I M ℝ 1) :
    (wedgeFamily α).1 = RoughForm.wedgeFamily fun i ↦ (α i).1 :=
  (rfl)

/-- The wedge product of a family of smooth one-forms is the determinant of the matrix of the
one-forms evaluated on the tangent vectors. -/
theorem wedgeFamily_apply (α : Fin k → SmoothForm I M ℝ 1) (x : M)
    (v : Fin k → TangentSpace I x) :
    (wedgeFamily α).1 x v = (Matrix.of fun i j ↦ (α i).1 x ![v j]).det :=
  RoughForm.wedgeFamily_apply _ x v

/-- The wedge product of two smooth one-forms as a family is their binary wedge product. -/
theorem wedgeFamily_two (α : Fin 2 → SmoothForm I M ℝ 1) :
    wedgeFamily α = wedge (α 0) (α 1) :=
  Subtype.ext (by rw [coe_wedgeFamily, coe_wedge, RoughForm.wedgeFamily_two])

/-- Smooth pullback commutes with the wedge product of a family of smooth one-forms. -/
theorem mpullback_wedgeFamily [IsManifold I' 1 M'] [FiniteDimensional ℝ E'] (f : M → M')
    (hf : ContMDiff I I' ∞ f) (α : Fin k → SmoothForm I' M' ℝ 1) :
    mpullback f hf (wedgeFamily α) = wedgeFamily fun i ↦ mpullback f hf (α i) :=
  Subtype.ext (by simp only [coe_mpullback, coe_wedgeFamily, RoughForm.mpullback_wedgeFamily])

/-- Reordering a family of smooth one-forms by a permutation `σ` multiplies their wedge product by
the sign of `σ`. -/
theorem wedgeFamily_comp_perm (α : Fin k → SmoothForm I M ℝ 1) (σ : Equiv.Perm (Fin k)) :
    wedgeFamily (α ∘ σ) = (Equiv.Perm.sign σ : ℝ) • wedgeFamily α :=
  Subtype.ext (RoughForm.wedgeFamily_comp_perm (fun i ↦ (α i).1) σ)

/-- Rescaling each smooth one-form `α i` by `c i` multiplies their wedge product by
`∏ i, c i`. -/
theorem wedgeFamily_smul (c : Fin k → ℝ) (α : Fin k → SmoothForm I M ℝ 1) :
    wedgeFamily (fun i ↦ c i • α i) = (∏ i, c i) • wedgeFamily α :=
  Subtype.ext (RoughForm.wedgeFamily_smul c fun i ↦ (α i).1)

end SmoothForm

end TauCeti
