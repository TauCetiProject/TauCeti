/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.AlgebraicGeometry.IntersectionNumber.NumericalClassGroup

/-!
# The rational and real numerical spaces `N¹(X/k)_ℚ` and `N¹(X/k)_ℝ`

For a proper morphism `f : X ⟶ S` the rational and real numerical spaces are the base changes
`N¹(X/S)_ℚ = ℚ ⊗ Num(X/S)` and `N¹(X/S)_ℝ = ℝ ⊗ Num(X/S)` of the relative numerical group, and
likewise `N¹(X/k)_ℚ` and `N¹(X/k)_ℝ` for a proper scheme `X` over a field `k`. Since the numerical
groups are torsion-free, hence flat over `ℤ`, the maps `Num ⟶ N¹_ℚ ⟶ N¹_ℝ` are injective.

Over a field, the intersection number `(α · C)` of a numerical class with an integral closed curve
`C ⊆ X` extends to a `ℚ`-linear form on `N¹(X/k)_ℚ` and an `ℝ`-linear form on `N¹(X/k)_ℝ`,
compatible with the inclusion `N¹(X/k)_ℚ ⟶ N¹(X/k)_ℝ`.

## Main definitions

* `LineBundleClass.RatNumericalClasses k x` and `LineBundleClass.RealNumericalClasses k x`:
  `N¹(X/k)_ℚ` and `N¹(X/k)_ℝ`;
* `LineBundleClass.RelRatNumericalClasses f` and `LineBundleClass.RelRealNumericalClasses f`:
  `N¹(X/S)_ℚ` and `N¹(X/S)_ℝ`;
* `LineBundleClass.toRatNumericalClasses` and `LineBundleClass.ratToRealNumericalClasses`, and
  their relative versions: the maps `Num ⟶ N¹_ℚ ⟶ N¹_ℝ`;
* `LineBundleClass.ratNumericalIntersectionNumber` and
  `LineBundleClass.realNumericalIntersectionNumber`: the linear extensions of the intersection
  number with a curve.

## Main results

* `LineBundleClass.toRatNumericalClasses_injective`,
  `LineBundleClass.ratToRealNumericalClasses_injective` and their relative versions.

## References

* B. Bhatt, L. Ma, Z. Patakfalvi, K. Schwede, K. Tucker, J. Waldron and J. Witaszek, *Globally
  `+`-regular varieties and the minimal model program for threefolds in mixed characteristic*,
  Publ. Math. IHÉS 138 (2023); arXiv:2012.15801v3, Remark 2.22, p. 19.
-/

public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.LineBundleClass

section Absolute

variable (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (.of k)) [IsProper x]

/-- The rational numerical space `N¹(X/k)_ℚ = ℚ ⊗ Num(X/k)` of a scheme `X` over a field `k`. -/
abbrev RatNumericalClasses :=
  ℚ ⊗[ℤ] Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)

/-- The real numerical space `N¹(X/k)_ℝ = ℝ ⊗ Num(X/k)` of a scheme `X` over a field `k`. -/
abbrev RealNumericalClasses :=
  ℝ ⊗[ℤ] Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)

/-- The map `Num(X/k) ⟶ N¹(X/k)_ℚ`, `α ↦ 1 ⊗ α`. -/
def toRatNumericalClasses :
    Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x) →ₗ[ℤ] RatNumericalClasses k x :=
  TensorProduct.mk ℤ ℚ _ 1

/-- The map `Num(X/k) ⟶ N¹(X/k)_ℚ` sends `α` to `1 ⊗ α`. -/
@[simp]
theorem toRatNumericalClasses_apply
    (α : Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    toRatNumericalClasses k x α = (1 : ℚ) ⊗ₜ α :=
  (rfl)

/-- The map `N¹(X/k)_ℚ ⟶ N¹(X/k)_ℝ`, base change of the inclusion `ℚ ⟶ ℝ`. -/
def ratToRealNumericalClasses : RatNumericalClasses k x →ₗ[ℚ] RealNumericalClasses k x :=
  AlgebraTensorModule.rTensor ℤ _ (Algebra.linearMap ℚ ℝ)

/-- The map `N¹(X/k)_ℚ ⟶ N¹(X/k)_ℝ` sends `q ⊗ α` to `q ⊗ α`. -/
@[simp]
theorem ratToRealNumericalClasses_tmul (q : ℚ)
    (α : Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    ratToRealNumericalClasses k x (q ⊗ₜ α) = (q : ℝ) ⊗ₜ α :=
  (rfl)

/-- **`Num(X/k)` embeds in `N¹(X/k)_ℚ`**, since `Num(X/k)` is torsion-free, hence flat over
`ℤ`. -/
theorem toRatNumericalClasses_injective : Function.Injective (toRatNumericalClasses k x) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap
    (M := Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x))
    (Algebra.linearMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  convert h.comp (TensorProduct.lid ℤ _).symm.injective using 1
  funext α
  simp

/-- **`N¹(X/k)_ℚ` embeds in `N¹(X/k)_ℝ`**, since `Num(X/k)` is flat over `ℤ`. -/
theorem ratToRealNumericalClasses_injective :
    Function.Injective (ratToRealNumericalClasses k x) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    (M := Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x))
    ((Algebra.linearMap ℚ ℝ).restrictScalars ℤ) (algebraMap ℚ ℝ).injective

variable {k} {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of k))] {i : C ⟶ X}
  [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1)

/-- The `ℚ`-linear intersection number `N¹(X/k)_ℚ ⟶ ℚ` with an integral closed curve `C ⊆ X`, the
base change of the intersection number on `Num(X/k)`. -/
def ratNumericalIntersectionNumber : RatNumericalClasses k x →ₗ[ℚ] ℚ :=
  (Algebra.TensorProduct.rid ℤ ℚ ℚ).toLinearMap ∘ₗ
    (numericalIntersectionNumberHom k hi hC).toIntLinearMap.baseChange ℚ

/-- The `ℚ`-linear intersection number of `q ⊗ α` is `q · (α · C)`. -/
@[simp]
theorem ratNumericalIntersectionNumber_tmul (q : ℚ)
    (α : Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    ratNumericalIntersectionNumber x hi hC (q ⊗ₜ α) =
      q * numericalIntersectionNumber k hi hC α.toMul := by
  simp [ratNumericalIntersectionNumber, mul_comm]

/-- The `ℝ`-linear intersection number `N¹(X/k)_ℝ ⟶ ℝ` with an integral closed curve `C ⊆ X`, the
base change of the intersection number on `Num(X/k)`. -/
def realNumericalIntersectionNumber : RealNumericalClasses k x →ₗ[ℝ] ℝ :=
  (Algebra.TensorProduct.rid ℤ ℝ ℝ).toLinearMap ∘ₗ
    (numericalIntersectionNumberHom k hi hC).toIntLinearMap.baseChange ℝ

/-- The `ℝ`-linear intersection number of `r ⊗ α` is `r · (α · C)`. -/
@[simp]
theorem realNumericalIntersectionNumber_tmul (r : ℝ)
    (α : Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    realNumericalIntersectionNumber x hi hC (r ⊗ₜ α) =
      r * numericalIntersectionNumber k hi hC α.toMul := by
  simp [realNumericalIntersectionNumber, mul_comm]

/-- The real intersection number of the image of a rational numerical class is its rational
intersection number. -/
theorem realNumericalIntersectionNumber_ratToRealNumericalClasses (v : RatNumericalClasses k x) :
    realNumericalIntersectionNumber x hi hC (ratToRealNumericalClasses k x v) =
      ratNumericalIntersectionNumber x hi hC v := by
  induction v using TensorProduct.inductionOn with
  | tmul q α => simp
  | add v w hv hw => simp only [map_add, hv, hw, Rat.cast_add]

end Absolute

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

/-- The rational numerical space `N¹(X/S)_ℚ = ℚ ⊗ Num(X/S)` of a morphism `f : X ⟶ S`. -/
abbrev RelRatNumericalClasses :=
  ℚ ⊗[ℤ] Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)

/-- The real numerical space `N¹(X/S)_ℝ = ℝ ⊗ Num(X/S)` of a morphism `f : X ⟶ S`. -/
abbrev RelRealNumericalClasses :=
  ℝ ⊗[ℤ] Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)

/-- The map `Num(X/S) ⟶ N¹(X/S)_ℚ`, `α ↦ 1 ⊗ α`. -/
def toRelRatNumericalClasses :
    Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f) →ₗ[ℤ]
      RelRatNumericalClasses f :=
  TensorProduct.mk ℤ ℚ _ 1

/-- The map `Num(X/S) ⟶ N¹(X/S)_ℚ` sends `α` to `1 ⊗ α`. -/
@[simp]
theorem toRelRatNumericalClasses_apply
    (α : Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)) :
    toRelRatNumericalClasses f α = (1 : ℚ) ⊗ₜ α :=
  (rfl)

/-- The map `N¹(X/S)_ℚ ⟶ N¹(X/S)_ℝ`, base change of the inclusion `ℚ ⟶ ℝ`. -/
def ratToRealRelNumericalClasses : RelRatNumericalClasses f →ₗ[ℚ] RelRealNumericalClasses f :=
  AlgebraTensorModule.rTensor ℤ _ (Algebra.linearMap ℚ ℝ)

/-- The map `N¹(X/S)_ℚ ⟶ N¹(X/S)_ℝ` sends `q ⊗ α` to `q ⊗ α`. -/
@[simp]
theorem ratToRealRelNumericalClasses_tmul (q : ℚ)
    (α : Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)) :
    ratToRealRelNumericalClasses f (q ⊗ₜ α) = (q : ℝ) ⊗ₜ α :=
  (rfl)

/-- **`Num(X/S)` embeds in `N¹(X/S)_ℚ`**, since `Num(X/S)` is torsion-free, hence flat over
`ℤ`. -/
theorem toRelRatNumericalClasses_injective :
    Function.Injective (toRelRatNumericalClasses f) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap
    (M := Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f))
    (Algebra.linearMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  convert h.comp (TensorProduct.lid ℤ _).symm.injective using 1
  funext α
  simp

/-- **`N¹(X/S)_ℚ` embeds in `N¹(X/S)_ℝ`**, since `Num(X/S)` is flat over `ℤ`. -/
theorem ratToRealRelNumericalClasses_injective :
    Function.Injective (ratToRealRelNumericalClasses f) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    (M := Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f))
    ((Algebra.linearMap ℚ ℝ).restrictScalars ℤ) (algebraMap ℚ ℝ).injective

end Relative

end TauCeti.AlgebraicGeometry.LineBundleClass
