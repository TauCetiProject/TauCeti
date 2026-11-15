/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral.Positive

/-!
# Algebraic Haar functionals on Hopf star algebras

For a complex star bialgebra `A`, `TauCeti.AlgebraicHaar A` bundles a normalized two-sided
invariant integral that is algebraically positive on squares, `0 ≤ h (star a * a)`. Over a complex
Hopf star algebra it is unique (`Subsingleton`), can be constructed from a normalized positive
one-sided invariant integral (`ofIsRightInvariantIntegral`, `ofIsLeftInvariantIntegral`), preserves
the star and antipode, and is strictly positive on nonzero squares `star a * a` and `a * star a`.

## Main declarations

* `TauCeti.AlgebraicHaar`: a positive normalized two-sided invariant integral on a complex star
  bialgebra, with `Subsingleton`, `map_star`, `map_antipode`, and strict positivity on nonzero
  squares.
* `TauCeti.AlgebraicHaar.ofIsRightInvariantIntegral` and
  `TauCeti.AlgebraicHaar.ofIsLeftInvariantIntegral`: constructors from a normalized positive
  one-sided invariant integral on a complex Hopf algebra.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.6.6.
-/

public section

open Coalgebra HopfAlgebra TensorProduct
open scoped ComplexOrder

namespace TauCeti

/-- An algebraic Haar functional on a complex star bialgebra `A`: a normalized two-sided invariant
linear functional `h : A →ₗ[ℂ] ℂ` that is nonnegative on every square `star a * a`. -/
structure AlgebraicHaar (A : Type*) [Ring A] [StarRing A] [Bialgebra ℂ A] extends A →ₗ[ℂ] ℂ where
  /-- Normalization on the multiplicative unit. -/
  map_one' : toLinearMap 1 = 1
  /-- Left invariance `(id ⊗ h) Δ(a) = h(a) 1`. -/
  left_invariant' : toLinearMap.IsLeftInvariantIntegral
  /-- Right invariance `(h ⊗ id) Δ(a) = h(a) 1`. -/
  right_invariant' : toLinearMap.IsRightInvariantIntegral
  /-- Algebraic positivity on squares `star a * a`. -/
  map_star_mul_self_nonneg : ∀ a, 0 ≤ toLinearMap (star a * a)

namespace AlgebraicHaar

section Bialgebra

variable {A : Type*} [Ring A] [StarRing A] [Bialgebra ℂ A]

instance : FunLike (AlgebraicHaar A) A ℂ where
  coe h := h.toLinearMap
  coe_injective := fun ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ H ↦ by
    congr
    exact DFunLike.coe_injective H

instance : LinearMapClass (AlgebraicHaar A) ℂ A ℂ where
  map_add h := h.toLinearMap.map_add
  map_smulₛₗ h := h.toLinearMap.map_smul

/-- Algebraic Haar functionals are determined by their values on elements. -/
@[ext]
theorem ext {h₁ h₂ : AlgebraicHaar A} (H : ∀ a, h₁ a = h₂ a) : h₁ = h₂ := DFunLike.ext h₁ h₂ H

/-- Applying `toLinearMap` to an `AlgebraicHaar` functional agrees with function coercion. -/
@[simp]
theorem toLinearMap_apply (h : AlgebraicHaar A) (a : A) : h.toLinearMap a = h a := (rfl)

/-- Applying a newly constructed `AlgebraicHaar` functional evaluates the underlying linear map. -/
@[simp]
theorem mk_apply (f : A →ₗ[ℂ] ℂ) (h1 hl hr hp) (a : A) : (mk f h1 hl hr hp) a = f a := (rfl)

/-- An algebraic Haar functional is unique whenever it exists. -/
instance : Subsingleton (AlgebraicHaar A) where
  allEq h₁ h₂ := ext <| LinearMap.congr_fun <|
    h₁.left_invariant'.eq_of_isRightInvariantIntegral h₂.right_invariant' h₁.map_one' h₂.map_one'

/-- Forget invariance and normalization to obtain a `StarPositiveFunctional`. -/
def toStarPositiveFunctional (h : AlgebraicHaar A) : StarPositiveFunctional A :=
  ⟨h.toLinearMap, h.map_star_mul_self_nonneg⟩

/-- Coercing `toStarPositiveFunctional` to a function agrees with coercing `h`. -/
@[simp]
theorem toStarPositiveFunctional_apply (h : AlgebraicHaar A) (a : A) :
    h.toStarPositiveFunctional a = h a := (rfl)

/-- The underlying linear map of `toStarPositiveFunctional` is `h.toLinearMap`. -/
@[simp]
theorem toLinearMap_toStarPositiveFunctional (h : AlgebraicHaar A) :
    h.toStarPositiveFunctional.toLinearMap = h.toLinearMap := (rfl)

/-- An algebraic Haar functional takes the value `1` at `1`. -/
@[simp]
theorem map_one (h : AlgebraicHaar A) : h 1 = 1 := h.map_one'

/-- Left invariance of an algebraic Haar functional. -/
theorem isLeftInvariantIntegral (h : AlgebraicHaar A) : h.toLinearMap.IsLeftInvariantIntegral :=
  h.left_invariant'

/-- Right invariance of an algebraic Haar functional. -/
theorem isRightInvariantIntegral (h : AlgebraicHaar A) : h.toLinearMap.IsRightInvariantIntegral :=
  h.right_invariant'

/-- Left-slice identity `(id ⊗ h) Δ(a) = h(a) 1`. -/
theorem rid_lTensor_comul (h : AlgebraicHaar A) (a : A) :
    TensorProduct.rid ℂ A (h.toLinearMap.lTensor A (Coalgebra.comul a)) = h a • (1 : A) :=
  LinearMap.isLeftInvariantIntegral_iff.mp h.left_invariant' a

/-- Right-slice identity `(h ⊗ id) Δ(a) = h(a) 1`. -/
theorem lid_rTensor_comul (h : AlgebraicHaar A) (a : A) :
    TensorProduct.lid ℂ A (h.toLinearMap.rTensor A (Coalgebra.comul a)) = h a • (1 : A) :=
  LinearMap.isRightInvariantIntegral_iff.mp h.right_invariant' a

/-- The underlying linear map of an algebraic Haar functional is nonzero. -/
theorem toLinearMap_ne_zero (h : AlgebraicHaar A) : h.toLinearMap ≠ 0 :=
  fun h0 ↦ one_ne_zero (h.map_one'.symm.trans (by simp [h0]))

/-- Any algebra admitting an algebraic Haar functional is nontrivial. -/
theorem nontrivial (h : AlgebraicHaar A) : Nontrivial A :=
  nontrivial_of_ne 1 0 fun h10 ↦ one_ne_zero (by rw [← h.map_one, h10, map_zero])

/-- Nonnegativity on right-handed squares `a * star a`. -/
theorem map_mul_star_self_nonneg (h : AlgebraicHaar A) (a : A) : 0 ≤ h (a * star a) := by
  simpa using h.map_star_mul_self_nonneg (star a)

/-- An algebraic Haar functional preserves the involution. -/
@[simp]
theorem map_star [StarModule ℂ A] (h : AlgebraicHaar A) (a : A) : h (star a) = star (h a) :=
  h.toStarPositiveFunctional.map_star a

end Bialgebra

section HopfAlgebra

variable {A : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]

/-- Construct an `AlgebraicHaar` functional on a complex Hopf algebra from a normalized positive
right invariant integral, deducing left invariance automatically via the antipode. -/
def ofIsRightInvariantIntegral (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1) (hr : f.IsRightInvariantIntegral)
    (hpos : ∀ a, 0 ≤ f (star a * a)) : AlgebraicHaar A :=
  ⟨f, h1, hr.isLeftInvariantIntegral h1, hr, hpos⟩

/-- Applying `ofIsRightInvariantIntegral` evaluates the underlying linear functional. -/
@[simp]
theorem ofIsRightInvariantIntegral_apply (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hr : f.IsRightInvariantIntegral) (hpos : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    ofIsRightInvariantIntegral f h1 hr hpos a = f a := (rfl)

/-- Construct an `AlgebraicHaar` functional on a complex Hopf algebra from a normalized positive
left invariant integral, deducing right invariance automatically via the antipode. -/
def ofIsLeftInvariantIntegral (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1) (hl : f.IsLeftInvariantIntegral)
    (hpos : ∀ a, 0 ≤ f (star a * a)) : AlgebraicHaar A :=
  ⟨f, h1, hl, hl.isRightInvariantIntegral h1, hpos⟩

/-- Applying `ofIsLeftInvariantIntegral` evaluates the underlying linear functional. -/
@[simp]
theorem ofIsLeftInvariantIntegral_apply (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hl : f.IsLeftInvariantIntegral) (hpos : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    ofIsLeftInvariantIntegral f h1 hl hpos a = f a := (rfl)

/-- An algebraic Haar functional on a Hopf algebra is invariant under the antipode. -/
@[simp]
theorem map_antipode (h : AlgebraicHaar A) (a : A) : h (HopfAlgebra.antipode ℂ a) = h a :=
  h.isRightInvariantIntegral.map_antipode h.map_one a

variable [StarModule ℂ A]

/-- An algebraic Haar functional on a Hopf star algebra vanishes on `star a * a` only at `0`. -/
@[simp]
theorem map_star_mul_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (star a * a) = 0 ↔ a = 0 :=
  h.isRightInvariantIntegral.map_star_mul_self_eq_zero_iff h.toLinearMap_ne_zero
    h.map_star_mul_self_nonneg

/-- An algebraic Haar functional on a Hopf star algebra vanishes on `a * star a` only at `0`. -/
@[simp]
theorem map_mul_star_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (a * star a) = 0 ↔ a = 0 := by
  simpa [star_eq_zero] using h.map_star_mul_self_eq_zero_iff (a := star a)

/-- Strict positivity of an algebraic Haar functional on `star a * a` for `a ≠ 0`. -/
theorem map_star_mul_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) : 0 < h (star a * a) :=
  h.isRightInvariantIntegral.map_star_mul_self_pos h.toLinearMap_ne_zero
    h.map_star_mul_self_nonneg ha

/-- Strict positivity of an algebraic Haar functional on `a * star a` for `a ≠ 0`. -/
theorem map_mul_star_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) : 0 < h (a * star a) := by
  simpa using h.map_star_mul_self_pos (a := star a) (star_ne_zero.mpr ha)

end HopfAlgebra

end AlgebraicHaar

end TauCeti
