/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.BaseChange
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
`C ⊆ X` extends to an `A`-linear form on `A ⊗ Num(X/k)` for every commutative ring `A`, compatible
with changes of coefficients; for `A = ℚ` and `A = ℝ` these are the `ℚ`-linear form on `N¹(X/k)_ℚ`
and the `ℝ`-linear form on `N¹(X/k)_ℝ`, compatible with the inclusion `N¹(X/k)_ℚ ⟶ N¹(X/k)_ℝ`.

## Main definitions

* `LineBundleClass.RatNumericalClasses k x` and `LineBundleClass.RealNumericalClasses k x`:
  `N¹(X/k)_ℚ` and `N¹(X/k)_ℝ`;
* `LineBundleClass.RelRatNumericalClasses f` and `LineBundleClass.RelRealNumericalClasses f`:
  `N¹(X/S)_ℚ` and `N¹(X/S)_ℝ`;
* `LineBundleClass.toRatNumericalClasses` and `LineBundleClass.ratToRealNumericalClasses`, and
  their relative versions: the maps `Num ⟶ N¹_ℚ ⟶ N¹_ℝ`;
* `LineBundleClass.numericalIntersectionNumberBaseChange`: the `A`-linear extension of the
  intersection number with a curve to `A ⊗ Num(X/k)`, for any commutative ring `A`.
* `LineBundleClass.relNumericalIntersectionNumberHom` and
  `LineBundleClass.relNumericalIntersectionNumberBaseChange`: the relative degree pairing of
  `Num(X/S)`, and of `A ⊗ Num(X/S)`, with an integral curve in a fibre of `f`.

## Main results

* `LineBundleClass.toRatNumericalClasses_injective`,
  `LineBundleClass.ratToRealNumericalClasses_injective` and their relative versions.
* `LineBundleClass.eq_zero_of_forall_relNumericalIntersectionNumberBaseChange_eq_zero`: the degree
  pairing of `N¹(X/S)_ℚ` with curves in fibres is nondegenerate.

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
    ratToRealNumericalClasses k x (q ⊗ₜ α) = (q : ℝ) ⊗ₜ α := by
  simp [ratToRealNumericalClasses]

/-- **`Num(X/k)` embeds in `N¹(X/k)_ℚ`**, since `Num(X/k)` is torsion-free, hence flat over
`ℤ`. -/
theorem toRatNumericalClasses_injective : Function.Injective (toRatNumericalClasses k x) :=
  Module.Flat.tensorProduct_mk_injective ℤ _ ℚ

/-- **`N¹(X/k)_ℚ` embeds in `N¹(X/k)_ℝ`**, since `Num(X/k)` is flat over `ℤ`. -/
theorem ratToRealNumericalClasses_injective :
    Function.Injective (ratToRealNumericalClasses k x) := by
  rw [ratToRealNumericalClasses, AlgebraTensorModule.coe_rTensor]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap ℚ ℝ).injective

variable {k} {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of k))] {i : C ⟶ X}
  [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1)

/-- The intersection number `A ⊗ Num(X/k) ⟶ A` with an integral closed curve `C ⊆ X`, for a
commutative ring `A`: the `A`-linear base change of the intersection number on `Num(X/k)`. For
`A = ℚ` and `A = ℝ` it is the intersection number on `N¹(X/k)_ℚ` and `N¹(X/k)_ℝ`. -/
def numericalIntersectionNumberBaseChange (A : Type*) [CommRing A] :
    A ⊗[ℤ] Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x) →ₗ[A] A :=
  Module.Dual.baseChange A (numericalIntersectionNumberHom k hi hC).toIntLinearMap

/-- The base-changed intersection number of `a ⊗ α` is `a · (α · C)`. -/
@[simp]
theorem numericalIntersectionNumberBaseChange_tmul {A : Type*} [CommRing A] (a : A)
    (α : Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    numericalIntersectionNumberBaseChange x hi hC A (a ⊗ₜ α) =
      a * numericalIntersectionNumber k hi hC α.toMul := by
  simp [numericalIntersectionNumberBaseChange, zsmul_eq_mul, mul_comm]

/-- The base-changed intersection number is compatible with a change of coefficients `A ⟶ B`. -/
@[simp]
theorem numericalIntersectionNumberBaseChange_rTensor {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (v : A ⊗[ℤ] Additive (LineBundleClass X ⧸ numericallyTrivialClasses k x)) :
    numericalIntersectionNumberBaseChange x hi hC B
        (((Algebra.linearMap A B).restrictScalars ℤ).rTensor _ v) =
      algebraMap A B (numericalIntersectionNumberBaseChange x hi hC A v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a α => simp
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The real intersection number of the image of a rational numerical class is its rational
intersection number. -/
@[simp]
theorem numericalIntersectionNumberBaseChange_ratToRealNumericalClasses
    (v : RatNumericalClasses k x) :
    numericalIntersectionNumberBaseChange x hi hC ℝ (ratToRealNumericalClasses k x v) =
      numericalIntersectionNumberBaseChange x hi hC ℚ v := by
  rw [ratToRealNumericalClasses, AlgebraTensorModule.coe_rTensor,
    numericalIntersectionNumberBaseChange_rTensor, eq_ratCast]

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
    ratToRealRelNumericalClasses f (q ⊗ₜ α) = (q : ℝ) ⊗ₜ α := by
  simp [ratToRealRelNumericalClasses]

/-- **`Num(X/S)` embeds in `N¹(X/S)_ℚ`**, since `Num(X/S)` is torsion-free, hence flat over
`ℤ`. -/
theorem toRelRatNumericalClasses_injective :
    Function.Injective (toRelRatNumericalClasses f) :=
  Module.Flat.tensorProduct_mk_injective ℤ _ ℚ

/-- **`N¹(X/S)_ℚ` embeds in `N¹(X/S)_ℝ`**, since `Num(X/S)` is flat over `ℤ`. -/
theorem ratToRealRelNumericalClasses_injective :
    Function.Injective (ratToRealRelNumericalClasses f) := by
  rw [ratToRealRelNumericalClasses, AlgebraTensorModule.coe_rTensor]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap ℚ ℝ).injective

variable {f} {s : S} {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of (S.residueField s)))]
  {i : C ⟶ f.fiber s} [IsClosedImmersion i]
  (hi : C ↘ Spec (.of (S.residueField s)) = i ≫ f.fiberToSpecResidueField s)
  (hC : topologicalKrullDim C = 1)

/-- The **relative intersection number** `Num(X/S) →+ ℤ` with an integral curve `C` in the
fibre `X_s` of `f` over a point `s`: restriction to `X_s` followed by the degree on `C` over the
residue field `κ(s)`. -/
def relNumericalIntersectionNumberHom :
    Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f) →+ ℤ :=
  (numericalIntersectionNumberHom (S.residueField s) hi hC).comp
    (numericalFiberRestriction f s).toAdditive

/-- The relative intersection number of the class of `a` is the degree on `C` of the pullback of
`a` to the fibre. -/
@[simp]
theorem relNumericalIntersectionNumberHom_mk (a : LineBundleClass X) :
    relNumericalIntersectionNumberHom hi hC
        (Additive.ofMul (a : LineBundleClass X ⧸ relNumericallyTrivialClasses f)) =
      intersectionNumber (S.residueField s) i (pullback (f.fiberι s) a) := by
  simp [relNumericalIntersectionNumberHom]

/-- The relative intersection number `A ⊗ Num(X/S) ⟶ A` with an integral curve in a fibre, for a
commutative ring `A`: for `A = ℚ` and `A = ℝ` the degree pairing of `N¹(X/S)_ℚ` and `N¹(X/S)_ℝ`
with curves in fibres. -/
def relNumericalIntersectionNumberBaseChange (A : Type*) [CommRing A] :
    A ⊗[ℤ] Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f) →ₗ[A] A :=
  Module.Dual.baseChange A (relNumericalIntersectionNumberHom hi hC).toIntLinearMap

/-- The base-changed relative intersection number of `a ⊗ α` is `a · (α · C)`. -/
@[simp]
theorem relNumericalIntersectionNumberBaseChange_tmul {A : Type*} [CommRing A] (a : A)
    (α : Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)) :
    relNumericalIntersectionNumberBaseChange hi hC A (a ⊗ₜ α) =
      a * relNumericalIntersectionNumberHom hi hC α := by
  simp [relNumericalIntersectionNumberBaseChange, zsmul_eq_mul, mul_comm]

variable (f) in
/-- **The degree pairing of `N¹(X/S)_ℚ` with curves in fibres is nondegenerate**: a rational
numerical class with zero degree on every integral curve in every fibre of `f` is zero. -/
theorem eq_zero_of_forall_relNumericalIntersectionNumberBaseChange_eq_zero
    (v : RelRatNumericalClasses f)
    (h : ∀ (s : S) (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of (S.residueField s)))]
      (i : C ⟶ f.fiber s) [IsClosedImmersion i]
      (hi : C ↘ Spec (.of (S.residueField s)) = i ≫ f.fiberToSpecResidueField s)
      (hC : topologicalKrullDim C = 1), relNumericalIntersectionNumberBaseChange hi hC ℚ v = 0) :
    v = 0 := by
  obtain ⟨⟨α, n⟩, hv⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)) 1) v
  simp only [TensorProduct.mk_apply] at hv
  rw [Submonoid.smul_def, ← Int.cast_smul_eq_zsmul ℚ] at hv
  have hα : α = 0 := by
    apply Additive.toMul.injective
    refine numericalFiberRestriction_injective f (funext fun s ↦ ?_)
    refine eq_of_forall_numericalIntersectionNumber_eq _ _ fun C _ _ i _ hi hC ↦ ?_
    have := h s C i hi hC
    have h2 := congrArg (relNumericalIntersectionNumberBaseChange hi hC ℚ) hv
    rw [map_smul, this, smul_zero, relNumericalIntersectionNumberBaseChange_tmul, one_mul,
      eq_comm, Int.cast_eq_zero] at h2
    simpa [relNumericalIntersectionNumberHom] using h2
  rw [hα, TensorProduct.tmul_zero] at hv
  exact (smul_eq_zero.mp hv).resolve_left (Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero n))

end Relative

end TauCeti.AlgebraicGeometry.LineBundleClass
