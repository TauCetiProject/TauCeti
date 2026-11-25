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
import TauCeti.Algebra.Group.TypeTags.Hom
import TauCeti.LinearAlgebra.Dual.BaseChange

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

Since these pairings are nondegenerate, `N¹(X/S)_ℚ` is also `Pic(X) ⊗ ℚ` modulo the kernel of the
`ℚ`-linear degree pairing with curves in fibres, and likewise over a field.

## Main definitions

* `LineBundleClass.RatNumericalClasses k x` and `LineBundleClass.RealNumericalClasses k x`:
  `N¹(X/k)_ℚ` and `N¹(X/k)_ℝ`;
* `LineBundleClass.RelRatNumericalClasses f` and `LineBundleClass.RelRealNumericalClasses f`:
  `N¹(X/S)_ℚ` and `N¹(X/S)_ℝ`;
* `LineBundleClass.toRatNumericalClasses` and `LineBundleClass.ratToRealNumericalClasses`, and
  their relative versions: the maps `Num ⟶ N¹_ℚ ⟶ N¹_ℝ`;
* `LineBundleClass.numericalIntersectionNumberBaseChange`: the `A`-linear extension of the
  intersection number with a curve to `A ⊗ Num(X/k)`, for any commutative ring `A`.
* `LineBundleClass.relNumericalIntersectionNumberBaseChange`: the `A`-linear extension to
  `A ⊗ Num(X/S)` of the relative degree pairing `LineBundleClass.relNumericalIntersectionNumberHom`
  with an integral curve in a fibre of `f`, compatible with changes of coefficients.
* `LineBundleClass.ratNumericallyTrivialClasses` and
  `LineBundleClass.relRatNumericallyTrivialClasses`: the kernels in `Pic(X) ⊗ ℚ` of the
  `ℚ`-linear degree pairings `LineBundleClass.picRatIntersectionNumber` and
  `LineBundleClass.picRatRelIntersectionNumber`.
* `LineBundleClass.picQuotientRatNumericallyTrivialEquiv` and
  `LineBundleClass.picQuotientRelRatNumericallyTrivialEquiv`: the isomorphisms
  `(Pic(X) ⊗ ℚ)/≡ ≃ N¹(X/k)_ℚ` and `(Pic(X) ⊗ ℚ)/≡_f ≃ N¹(X/S)_ℚ`.

## Main results

* `LineBundleClass.toRatNumericalClasses_injective`,
  `LineBundleClass.ratToRealNumericalClasses_injective` and their relative versions.
* `LineBundleClass.eq_zero_of_forall_relNumericalIntersectionNumberBaseChange_eq_zero`: the degree
  pairing of `N¹(X/S)_ℚ` with curves in fibres is nondegenerate, and
  `LineBundleClass.eq_zero_of_forall_numericalIntersectionNumberBaseChange_eq_zero` over a field.
* `LineBundleClass.ker_picToRatNumericalClasses`, `LineBundleClass.ker_picToRelRatNumericalClasses`:
  the kernel of `Pic(X) ⊗ ℚ ⟶ N¹_ℚ` is the kernel of the degree pairing.

## References

* B. Bhatt, L. Ma, Z. Patakfalvi, K. Schwede, K. Tucker, J. Waldron and J. Witaszek, *Globally
  `+`-regular varieties and the minimal model program for threefolds in mixed characteristic*,
  Publ. Math. IHÉS 138 (2023); arXiv:2012.15801v3, Remark 2.22, p. 19.
* C. Hacon and J. Witaszek, *On the relative minimal model program for fourfolds in positive and
  mixed characteristic*, Forum Math. Pi 11 (2023), §1: `N¹(X) = Pic(X) ⊗ ℚ / ≡`, the
  isomorphisms `LineBundleClass.picQuotientRatNumericallyTrivialEquiv` and
  `LineBundleClass.picQuotientRelRatNumericallyTrivialEquiv`.
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
      algebraMap A B (numericalIntersectionNumberBaseChange x hi hC A v) :=
  Module.Dual.baseChange_rTensor _ v

/-- The real intersection number of the image of a rational numerical class is its rational
intersection number. -/
@[simp]
theorem numericalIntersectionNumberBaseChange_ratToRealNumericalClasses
    (v : RatNumericalClasses k x) :
    numericalIntersectionNumberBaseChange x hi hC ℝ (ratToRealNumericalClasses k x v) =
      numericalIntersectionNumberBaseChange x hi hC ℚ v := by
  rw [ratToRealNumericalClasses, AlgebraTensorModule.coe_rTensor,
    numericalIntersectionNumberBaseChange_rTensor, eq_ratCast]

variable (k) in
/-- **The degree pairing of `N¹(X/k)_ℚ` with curves is nondegenerate**: a rational numerical
class with zero degree on every integral closed curve of `X` is zero. -/
theorem eq_zero_of_forall_numericalIntersectionNumberBaseChange_eq_zero
    (v : RatNumericalClasses k x)
    (h : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X)
      [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1),
        numericalIntersectionNumberBaseChange x hi hC ℚ v = 0) :
    v = 0 := by
  refine TauCeti.Module.Dual.eq_zero_of_forall_baseChange_eq_zero
    (Φ := {φ | ∃ (C : Scheme.{u}) (_ : IsIntegral C) (_ : C.Over (Spec (.of k))) (i : C ⟶ X)
      (_ : IsClosedImmersion i) (hi : C ↘ Spec (.of k) = i ≫ x)
      (hC : topologicalKrullDim C = 1),
        φ = (numericalIntersectionNumberHom k hi hC).toIntLinearMap})
    (fun α hα ↦ Additive.toMul.injective ?_) ?_
  · refine eq_of_forall_numericalIntersectionNumber_eq k x fun C _ _ i _ hi hC ↦ ?_
    simpa using hα _ ⟨C, _, _, i, _, hi, hC, rfl⟩
  · rintro φ ⟨C, _, _, i, _, hi, hC, rfl⟩
    exact h C i hi hC

variable (k) in
/-- The map `Pic(X) ⊗ ℚ ⟶ N¹(X/k)_ℚ` induced by the class map `Pic(X) ⟶ Num(X/k)`. -/
def picToRatNumericalClasses :
    ℚ ⊗[ℤ] Additive (LineBundleClass X) →ₗ[ℚ] RatNumericalClasses k x :=
  LinearMap.baseChange ℚ
    (QuotientGroup.mk' (numericallyTrivialClasses k x)).toAdditive.toIntLinearMap

/-- The map `Pic(X) ⊗ ℚ ⟶ N¹(X/k)_ℚ` sends `q ⊗ a` to `q ⊗ [a]`. -/
@[simp]
theorem picToRatNumericalClasses_tmul (q : ℚ) (a : Additive (LineBundleClass X)) :
    picToRatNumericalClasses k x (q ⊗ₜ a) =
      q ⊗ₜ Additive.ofMul (a.toMul : LineBundleClass X ⧸ numericallyTrivialClasses k x) :=
  (rfl)

variable (k) in
/-- The map `Pic(X) ⊗ ℚ ⟶ N¹(X/k)_ℚ` is surjective. -/
theorem picToRatNumericalClasses_surjective :
    Function.Surjective (picToRatNumericalClasses k x) :=
  LinearMap.baseChange_surjective ℚ <|
    MonoidHom.toAdditive_surjective_iff.2 (QuotientGroup.mk'_surjective _)

/-- The intersection number `Pic(X) ⊗ ℚ ⟶ ℚ` with an integral closed curve `C ⊆ X`: the
`ℚ`-linear degree pairing of `Pic(X) ⊗ ℚ` with `C`. -/
def picRatIntersectionNumber : ℚ ⊗[ℤ] Additive (LineBundleClass X) →ₗ[ℚ] ℚ :=
  numericalIntersectionNumberBaseChange x hi hC ℚ ∘ₗ picToRatNumericalClasses k x

/-- The rational intersection number of a class of `Pic(X) ⊗ ℚ` with `C` is the intersection
number of its image in `N¹(X/k)_ℚ`. -/
theorem picRatIntersectionNumber_apply (v : ℚ ⊗[ℤ] Additive (LineBundleClass X)) :
    picRatIntersectionNumber x hi hC v =
      numericalIntersectionNumberBaseChange x hi hC ℚ (picToRatNumericalClasses k x v) :=
  (rfl)

/-- The rational intersection number of `q ⊗ a` with `C` is `q · (a · C)`. -/
@[simp]
theorem picRatIntersectionNumber_tmul (q : ℚ) (a : Additive (LineBundleClass X)) :
    picRatIntersectionNumber x hi hC (q ⊗ₜ a) = q * intersectionNumber k i a.toMul := by
  simp [picRatIntersectionNumber]

variable (k) in
/-- The subspace of `Pic(X) ⊗ ℚ` of `ℚ`-numerically trivial classes, those with zero degree on
every integral closed curve of `X`: the kernel of the `ℚ`-linear degree pairing with curves. -/
def ratNumericallyTrivialClasses : Submodule ℚ (ℚ ⊗[ℤ] Additive (LineBundleClass X)) where
  carrier := {v | ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X)
      [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1),
        picRatIntersectionNumber x hi hC v = 0}
  add_mem' ha hb C _ _ i _ hi hC := by simp [ha C i hi hC, hb C i hi hC]
  zero_mem' _ _ _ _ _ _ _ := map_zero _
  smul_mem' c v hv C _ _ i _ hi hC := by simp [hv C i hi hC]

/-- A class of `Pic(X) ⊗ ℚ` is `ℚ`-numerically trivial iff it has zero degree on every integral
closed curve of `X`. -/
@[simp]
theorem mem_ratNumericallyTrivialClasses {v : ℚ ⊗[ℤ] Additive (LineBundleClass X)} :
    v ∈ ratNumericallyTrivialClasses k x ↔
      ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X)
        [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1),
          picRatIntersectionNumber x hi hC v = 0 :=
  Iff.rfl

variable (k) in
/-- **The kernel of `Pic(X) ⊗ ℚ ⟶ N¹(X/k)_ℚ` is the kernel of the degree pairing**: a class of
`Pic(X) ⊗ ℚ` vanishes in `N¹(X/k)_ℚ` iff it has zero degree on every integral closed curve. -/
theorem ker_picToRatNumericalClasses :
    LinearMap.ker (picToRatNumericalClasses k x) = ratNumericallyTrivialClasses k x := by
  ext v
  rw [mem_ratNumericallyTrivialClasses]
  refine ⟨fun hv C _ _ i _ hi hC ↦ ?_, fun hv ↦
    eq_zero_of_forall_numericalIntersectionNumberBaseChange_eq_zero k x _ hv⟩
  rw [LinearMap.mem_ker] at hv
  rw [picRatIntersectionNumber_apply, hv, map_zero]

variable (k) in
/-- **`N¹(X/k)_ℚ` is `Pic(X) ⊗ ℚ` modulo numerical equivalence**: the class map induces an
isomorphism from `Pic(X) ⊗ ℚ` modulo the kernel of the `ℚ`-linear degree pairing with curves onto
`N¹(X/k)_ℚ = Num(X/k) ⊗ ℚ`. -/
def picQuotientRatNumericallyTrivialEquiv :
    ((ℚ ⊗[ℤ] Additive (LineBundleClass X)) ⧸ ratNumericallyTrivialClasses k x) ≃ₗ[ℚ]
      RatNumericalClasses k x :=
  (Submodule.quotEquivOfEq _ _ (ker_picToRatNumericalClasses k x).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (picToRatNumericalClasses_surjective k x))

/-- The isomorphism `(Pic(X) ⊗ ℚ)/≡ ≃ N¹(X/k)_ℚ` sends the class of `v` to its image under the
class map. -/
@[simp]
theorem picQuotientRatNumericallyTrivialEquiv_mk (v : ℚ ⊗[ℤ] Additive (LineBundleClass X)) :
    picQuotientRatNumericallyTrivialEquiv k x (Submodule.Quotient.mk v) =
      picToRatNumericalClasses k x v := by
  simp [picQuotientRatNumericallyTrivialEquiv, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

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

/-- The base-changed relative intersection number is compatible with a change of coefficients
`A ⟶ B`. -/
@[simp]
theorem relNumericalIntersectionNumberBaseChange_rTensor {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (v : A ⊗[ℤ] Additive (LineBundleClass X ⧸ relNumericallyTrivialClasses f)) :
    relNumericalIntersectionNumberBaseChange hi hC B
        (((Algebra.linearMap A B).restrictScalars ℤ).rTensor _ v) =
      algebraMap A B (relNumericalIntersectionNumberBaseChange hi hC A v) :=
  Module.Dual.baseChange_rTensor _ v

/-- The real relative intersection number of the image of a rational relative numerical class is
its rational relative intersection number. -/
@[simp]
theorem relNumericalIntersectionNumberBaseChange_ratToRealRelNumericalClasses
    (v : RelRatNumericalClasses f) :
    relNumericalIntersectionNumberBaseChange hi hC ℝ (ratToRealRelNumericalClasses f v) =
      relNumericalIntersectionNumberBaseChange hi hC ℚ v := by
  rw [ratToRealRelNumericalClasses, AlgebraTensorModule.coe_rTensor,
    relNumericalIntersectionNumberBaseChange_rTensor, eq_ratCast]

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
  refine TauCeti.Module.Dual.eq_zero_of_forall_baseChange_eq_zero
    (Φ := {φ | ∃ (s : S) (C : Scheme.{u}) (_ : IsIntegral C)
      (_ : C.Over (Spec (.of (S.residueField s)))) (i : C ⟶ f.fiber s) (_ : IsClosedImmersion i)
      (hi : C ↘ Spec (.of (S.residueField s)) = i ≫ f.fiberToSpecResidueField s)
      (hC : topologicalKrullDim C = 1),
        φ = (relNumericalIntersectionNumberHom hi hC).toIntLinearMap})
    (fun α hα ↦ Additive.toMul.injective ?_) ?_
  · refine numericalFiberRestriction_injective f (funext fun s ↦ ?_)
    refine eq_of_forall_numericalIntersectionNumber_eq _ _ fun C _ _ i _ hi hC ↦ ?_
    simpa using hα _ ⟨s, C, _, _, i, _, hi, hC, rfl⟩
  · rintro φ ⟨s, C, _, _, i, _, hi, hC, rfl⟩
    exact h s C i hi hC

variable (f) in
/-- The map `Pic(X) ⊗ ℚ ⟶ N¹(X/S)_ℚ` induced by the class map `Pic(X) ⟶ Num(X/S)`. -/
def picToRelRatNumericalClasses :
    ℚ ⊗[ℤ] Additive (LineBundleClass X) →ₗ[ℚ] RelRatNumericalClasses f :=
  LinearMap.baseChange ℚ
    (QuotientGroup.mk' (relNumericallyTrivialClasses f)).toAdditive.toIntLinearMap

/-- The map `Pic(X) ⊗ ℚ ⟶ N¹(X/S)_ℚ` sends `q ⊗ a` to `q ⊗ [a]`. -/
@[simp]
theorem picToRelRatNumericalClasses_tmul (q : ℚ) (a : Additive (LineBundleClass X)) :
    picToRelRatNumericalClasses f (q ⊗ₜ a) =
      q ⊗ₜ Additive.ofMul (a.toMul : LineBundleClass X ⧸ relNumericallyTrivialClasses f) :=
  (rfl)

variable (f) in
/-- The map `Pic(X) ⊗ ℚ ⟶ N¹(X/S)_ℚ` is surjective. -/
theorem picToRelRatNumericalClasses_surjective :
    Function.Surjective (picToRelRatNumericalClasses f) :=
  LinearMap.baseChange_surjective ℚ <|
    MonoidHom.toAdditive_surjective_iff.2 (QuotientGroup.mk'_surjective _)

/-- The relative intersection number `Pic(X) ⊗ ℚ ⟶ ℚ` with an integral curve `C` in a fibre of
`f`: the `ℚ`-linear degree pairing of `Pic(X) ⊗ ℚ` with `C`. -/
def picRatRelIntersectionNumber : ℚ ⊗[ℤ] Additive (LineBundleClass X) →ₗ[ℚ] ℚ :=
  relNumericalIntersectionNumberBaseChange hi hC ℚ ∘ₗ picToRelRatNumericalClasses f

/-- The rational relative intersection number of a class of `Pic(X) ⊗ ℚ` with `C` is the
relative intersection number of its image in `N¹(X/S)_ℚ`. -/
theorem picRatRelIntersectionNumber_apply (v : ℚ ⊗[ℤ] Additive (LineBundleClass X)) :
    picRatRelIntersectionNumber hi hC v =
      relNumericalIntersectionNumberBaseChange hi hC ℚ (picToRelRatNumericalClasses f v) :=
  (rfl)

/-- The rational relative intersection number of `q ⊗ a` with `C` is `q` times the degree on `C`
of the pullback of `a` to the fibre. -/
@[simp]
theorem picRatRelIntersectionNumber_tmul (q : ℚ) (a : Additive (LineBundleClass X)) :
    picRatRelIntersectionNumber hi hC (q ⊗ₜ a) =
      q * intersectionNumber (S.residueField s) i (pullback (f.fiberι s) a.toMul) := by
  simp [picRatRelIntersectionNumber]

variable (f) in
/-- The subspace of `Pic(X) ⊗ ℚ` of classes that are `ℚ`-numerically trivial relative to `f`,
those with zero degree on every integral curve in every fibre: the kernel of the `ℚ`-linear degree
pairing with curves in fibres. -/
def relRatNumericallyTrivialClasses : Submodule ℚ (ℚ ⊗[ℤ] Additive (LineBundleClass X)) where
  carrier := {v | ∀ (s : S) (C : Scheme.{u}) [IsIntegral C]
      [C.Over (Spec (.of (S.residueField s)))] (i : C ⟶ f.fiber s) [IsClosedImmersion i]
      (hi : C ↘ Spec (.of (S.residueField s)) = i ≫ f.fiberToSpecResidueField s)
      (hC : topologicalKrullDim C = 1), picRatRelIntersectionNumber hi hC v = 0}
  add_mem' ha hb s C _ _ i _ hi hC := by simp [ha s C i hi hC, hb s C i hi hC]
  zero_mem' _ _ _ _ _ _ _ _ := map_zero _
  smul_mem' c v hv s C _ _ i _ hi hC := by simp [hv s C i hi hC]

/-- A class of `Pic(X) ⊗ ℚ` is `ℚ`-numerically trivial relative to `f` iff it has zero degree on
every integral curve in every fibre of `f`. -/
@[simp]
theorem mem_relRatNumericallyTrivialClasses {v : ℚ ⊗[ℤ] Additive (LineBundleClass X)} :
    v ∈ relRatNumericallyTrivialClasses f ↔
      ∀ (s : S) (C : Scheme.{u}) [IsIntegral C]
        [C.Over (Spec (.of (S.residueField s)))] (i : C ⟶ f.fiber s) [IsClosedImmersion i]
        (hi : C ↘ Spec (.of (S.residueField s)) = i ≫ f.fiberToSpecResidueField s)
        (hC : topologicalKrullDim C = 1), picRatRelIntersectionNumber hi hC v = 0 :=
  Iff.rfl

variable (f) in
/-- **The kernel of `Pic(X) ⊗ ℚ ⟶ N¹(X/S)_ℚ` is the kernel of the degree pairing**: a class of
`Pic(X) ⊗ ℚ` vanishes in `N¹(X/S)_ℚ` iff it has zero degree on every integral curve in every
fibre of `f`. -/
theorem ker_picToRelRatNumericalClasses :
    LinearMap.ker (picToRelRatNumericalClasses f) = relRatNumericallyTrivialClasses f := by
  ext v
  rw [mem_relRatNumericallyTrivialClasses]
  refine ⟨fun hv s C _ _ i _ hi hC ↦ ?_, fun hv ↦
    eq_zero_of_forall_relNumericalIntersectionNumberBaseChange_eq_zero f _ hv⟩
  rw [LinearMap.mem_ker] at hv
  rw [picRatRelIntersectionNumber_apply, hv, map_zero]

variable (f) in
/-- **`N¹(X/S)_ℚ` is `Pic(X) ⊗ ℚ` modulo numerical equivalence**: the class map induces an
isomorphism from `Pic(X) ⊗ ℚ` modulo the kernel of the `ℚ`-linear degree pairing with curves in
fibres onto `N¹(X/S)_ℚ = Num(X/S) ⊗ ℚ`. -/
def picQuotientRelRatNumericallyTrivialEquiv :
    ((ℚ ⊗[ℤ] Additive (LineBundleClass X)) ⧸ relRatNumericallyTrivialClasses f) ≃ₗ[ℚ]
      RelRatNumericalClasses f :=
  (Submodule.quotEquivOfEq _ _ (ker_picToRelRatNumericalClasses f).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (picToRelRatNumericalClasses_surjective f))

/-- The isomorphism `(Pic(X) ⊗ ℚ)/≡_f ≃ N¹(X/S)_ℚ` sends the class of `v` to its image under the
class map. -/
@[simp]
theorem picQuotientRelRatNumericallyTrivialEquiv_mk (v : ℚ ⊗[ℤ] Additive (LineBundleClass X)) :
    picQuotientRelRatNumericallyTrivialEquiv f (Submodule.Quotient.mk v) =
      picToRelRatNumericalClasses f v := by
  simp [picQuotientRelRatNumericallyTrivialEquiv, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end Relative

end TauCeti.AlgebraicGeometry.LineBundleClass
