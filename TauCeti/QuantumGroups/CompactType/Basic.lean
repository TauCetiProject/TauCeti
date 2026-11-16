/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Decomposition
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.PositiveIntegral

/-!
# Algebraic Haar integrals on complex bialgebras and Hopf star algebras

An *algebraic Haar integral* on a complex bialgebra with a star operation is a complex-linear
functional `h : A → ℂ` that is normalized (`h 1 = 1`), both left and right invariant under the
coproduct, and positive on algebraic squares (`0 ≤ h (star a * a)`).

Because a normalized left invariant integral and a normalized right invariant integral on the same
bialgebra automatically coincide, an algebraic Haar integral is unique whenever it exists
(`Subsingleton (AlgebraicHaar A)`). Over a complex Hopf star algebra, it is automatically strictly
positive, algebraically faithful on both sides, and forces the coalgebra to be linearly reductive,
yielding the internal direct sum decomposition of `A` into its distinct simple coefficient spaces.

## Main declarations

* `TauCeti.AlgebraicHaar`: a positive normalized two-sided invariant integral.
* `TauCeti.AlgebraicHaar.instSubsingleton`: uniqueness of the algebraic Haar integral.
* `TauCeti.AlgebraicHaar.complex`: the identity functional on `ℂ` as an algebraic Haar integral.
* `TauCeti.AlgebraicHaar.apply_star_mul_self_pos`: strict positivity on nonzero squares.
* `TauCeti.AlgebraicHaar.isLinearlyReductive` and
  `TauCeti.AlgebraicHaar.isInternal_simpleCoefficientSubmodules`: algebraic Peter–Weyl
  decomposition induced by an algebraic Haar integral.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Section 1.6.
-/

public section

open scoped ComplexOrder

namespace TauCeti

universe u v

/-- A positive normalized two-sided invariant integral (algebraic Haar functional) on a complex
bialgebra with a star operation. -/
structure AlgebraicHaar (A : Type u) [Semiring A] [Bialgebra ℂ A] [Star A] extends A →ₗ[ℂ] ℂ where
  /-- Normalization at the unit element. -/
  map_one' : toLinearMap 1 = 1
  /-- Left invariance `(id ⊗ h) Δ(a) = h(a) • 1`. -/
  isLeftInvariantIntegral : toLinearMap.IsLeftInvariantIntegral
  /-- Right invariance `(h ⊗ id) Δ(a) = h(a) • 1`. -/
  isRightInvariantIntegral : toLinearMap.IsRightInvariantIntegral
  /-- Positivity on algebraic squares `star a * a`. -/
  square_nonneg : ∀ a : A, 0 ≤ toLinearMap (star a * a)

namespace AlgebraicHaar

section Bialgebra

variable {A : Type u} [Semiring A] [Bialgebra ℂ A] [Star A]

instance : FunLike (AlgebraicHaar A) A ℂ where
  coe h := h.toLinearMap
  coe_injective h₁ h₂ h := by
    cases h₁
    cases h₂
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (AlgebraicHaar A) ℂ A ℂ where
  map_add h := h.toLinearMap.map_add
  map_smulₛₗ h := h.toLinearMap.map_smul

/-- Algebraic Haar integrals are determined by their values. -/
@[ext]
theorem ext {h₁ h₂ : AlgebraicHaar A} (h : ∀ a, h₁ a = h₂ a) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ h

/-- Coercion of an algebraic Haar integral agrees with its underlying linear map. -/
@[simp]
theorem toLinearMap_apply (h : AlgebraicHaar A) (a : A) : h.toLinearMap a = h a := (rfl)

/-- An algebraic Haar integral is normalized at `1`. -/
@[simp]
theorem map_one (h : AlgebraicHaar A) : h 1 = 1 := h.map_one'

/-- An algebraic Haar integral is nonnegative on algebraic squares `star a * a`. -/
theorem apply_star_mul_self_nonneg (h : AlgebraicHaar A) (a : A) : 0 ≤ h (star a * a) :=
  h.square_nonneg a

/-- An algebraic Haar integral is nonzero. -/
theorem toLinearMap_ne_zero (h : AlgebraicHaar A) : h.toLinearMap ≠ 0 := by
  intro h0
  have h1 := congrArg (fun f : A →ₗ[ℂ] ℂ ↦ f 1) h0
  simp [h.map_one'] at h1

/-- An algebraic Haar integral is unique whenever it exists. -/
instance instSubsingleton : Subsingleton (AlgebraicHaar A) where
  allEq h₁ h₂ := by
    have hlin := h₁.isLeftInvariantIntegral.eq_of_isRightInvariantIntegral
      h₂.isRightInvariantIntegral h₁.map_one' h₂.map_one'
    exact ext fun a ↦ congrArg (fun f : A →ₗ[ℂ] ℂ ↦ f a) hlin

/-- The identity functional on `ℂ` is an algebraic Haar integral. -/
def complex : AlgebraicHaar ℂ where
  toLinearMap := LinearMap.id
  map_one' := rfl
  isLeftInvariantIntegral := LinearMap.isLeftInvariantIntegral_iff.mpr fun a ↦ by
    simp [LinearMap.lTensor]
  isRightInvariantIntegral := LinearMap.isRightInvariantIntegral_iff.mpr fun a ↦ by
    simp [LinearMap.rTensor]
  square_nonneg a := by
    simpa only [LinearMap.id_coe, id_eq] using star_mul_self_nonneg a

/-- Evaluation of the canonical algebraic Haar integral on `ℂ`. -/
@[simp]
theorem complex_apply (z : ℂ) : complex z = z := (rfl)

end Bialgebra

section StarRing

variable {A : Type u} [Ring A] [Bialgebra ℂ A] [StarRing A]

/-- View an algebraic Haar integral as a `StarPositiveFunctional`. -/
def toStarPositiveFunctional (h : AlgebraicHaar A) : StarPositiveFunctional A where
  toLinearMap := h.toLinearMap
  square_nonneg := h.square_nonneg

/-- Evaluation of the underlying `StarPositiveFunctional`. -/
@[simp]
theorem toStarPositiveFunctional_apply (h : AlgebraicHaar A) (a : A) :
    h.toStarPositiveFunctional a = h a := (rfl)

variable [StarModule ℂ A]

/-- An algebraic Haar integral preserves `star`. -/
@[simp]
theorem map_star (h : AlgebraicHaar A) (a : A) : h (star a) = star (h a) :=
  h.toStarPositiveFunctional.map_star a

/-- Conjugate symmetry of the Haar sesquilinear pairing. -/
theorem star_apply_star_mul (h : AlgebraicHaar A) (a b : A) :
    star (h (star a * b)) = h (star b * a) :=
  h.toStarPositiveFunctional.star_apply_star_mul a b

end StarRing

section HopfAlgebra

variable {A : Type u} [Ring A] [HopfAlgebra ℂ A]

/-- Algebraic faithfulness on the right: if `h (a * b) = 0` for all `b`, then `a = 0`. -/
theorem eq_zero_of_forall_mul_right_eq_zero [Star A] (h : AlgebraicHaar A) {a : A}
    (ha : ∀ b, h (a * b) = 0) : a = 0 :=
  h.isRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero h.toLinearMap_ne_zero ha

/-- Algebraic faithfulness on the left: if `h (b * a) = 0` for all `b`, then `a = 0`. -/
theorem eq_zero_of_forall_mul_left_eq_zero [Star A] (h : AlgebraicHaar A) {a : A}
    (ha : ∀ b, h (b * a) = 0) : a = 0 :=
  h.isLeftInvariantIntegral.eq_zero_of_forall_mul_eq_zero h.toLinearMap_ne_zero ha

variable [StarRing A] [StarModule ℂ A]

/-- An algebraic Haar integral on a complex Hopf algebra vanishes on `star a * a` only for
`a = 0`. -/
@[simp]
theorem apply_star_mul_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (star a * a) = 0 ↔ a = 0 :=
  h.isRightInvariantIntegral.map_star_mul_self_eq_zero_iff h.toLinearMap_ne_zero h.square_nonneg

/-- An algebraic Haar integral on a complex Hopf algebra is strictly positive on nonzero
squares. -/
theorem apply_star_mul_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) :
    0 < h (star a * a) :=
  h.isRightInvariantIntegral.map_star_mul_self_pos h.toLinearMap_ne_zero h.square_nonneg ha

variable [StarCoalgebra ℂ A]

/-- A complex Hopf star algebra admitting an algebraic Haar integral is linearly reductive. -/
theorem isLinearlyReductive (h : AlgebraicHaar A) :
    Coalgebra.IsLinearlyReductive.{0, u, v} ℂ A :=
  h.isRightInvariantIntegral.isLinearlyReductive h.toLinearMap_ne_zero h.square_nonneg

/-- The simple coefficient spaces span a complex Hopf star algebra admitting an algebraic Haar
integral. -/
theorem sSup_simpleCoefficientSubmodules_eq_top (h : AlgebraicHaar A) :
    sSup (Comodule.simpleCoefficientSubmodules ℂ A) = ⊤ :=
  h.isLinearlyReductive.sSup_simpleCoefficientSubmodules_eq_top

/-- A complex Hopf star algebra admitting an algebraic Haar integral is the internal direct sum of
its distinct simple coefficient spaces. -/
theorem isInternal_simpleCoefficientSubmodules (h : AlgebraicHaar A) :
    DirectSum.IsInternal
      (fun P : Comodule.simpleCoefficientSubmodules ℂ A ↦ (P.1 : Submodule ℂ A)) :=
  h.isLinearlyReductive.isInternal_simpleCoefficientSubmodules

/-- Over a complex Hopf star algebra with an algebraic Haar integral, every comodule with a finite
basis admits a basis indexed by the same type whose coefficient matrix is unitary. -/
theorem exists_basis_coefficientMatrix_mem_unitary (h : AlgebraicHaar A)
    {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) :
    ∃ c : Module.Basis ι ℂ M,
      Comodule.coefficientMatrix (C := A) c ∈ unitary (Matrix ι ι A) :=
  Comodule.exists_basis_coefficientMatrix_mem_unitary
    h.isRightInvariantIntegral h.toLinearMap_ne_zero h.square_nonneg b

end HopfAlgebra

end AlgebraicHaar

end TauCeti
