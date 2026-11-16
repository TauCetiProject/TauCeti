/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.PositiveIntegral
public import TauCeti.Algebra.HopfAlgebra.Integral.Positive
public import TauCeti.Algebra.HopfAlgebra.Star

/-!
# Algebraic Haar states on complex bialgebras and Hopf star algebras

An *algebraic Haar state* on a complex star bialgebra `A` is a normalized, positive,
two-sided invariant linear functional `h : A →ₗ[ℂ] ℂ`:

* `h 1 = 1`;
* `(id ⊗ h) Δ(a) = h(a) 1` (`LinearMap.IsLeftInvariantIntegral`);
* `(h ⊗ id) Δ(a) = h(a) 1` (`LinearMap.IsRightInvariantIntegral`);
* `0 ≤ h (star a * a)` for every `a : A`.

Because any normalized right invariant integral agrees with any normalized left invariant
integral, an algebraic Haar state is unique when it exists (`Subsingleton (AlgebraicHaar A)`).
On a complex Hopf star algebra, it is automatically strictly positive, algebraically faithful on
both sides, antipode-invariant (`h (S a) = h a`), and forces `A` to be linearly reductive.

No norm, C*-completion, or topology on `A` is assumed.

## Main declarations

* `TauCeti.AlgebraicHaar`: a normalized positive two-sided invariant integral on `A`.
* `TauCeti.AlgebraicHaar.complex`: the identity Haar state on `ℂ`.
* `TauCeti.AlgebraicHaar.map_star_mul_self_pos`: strict positivity on a complex Hopf star algebra.
* `TauCeti.AlgebraicHaar.map_antipode`: antipode invariance `h (S a) = h a`.
* `TauCeti.AlgebraicHaar.isLinearlyReductive`: linear reductivity of a complex Hopf star algebra
  admitting an algebraic Haar state.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Section 1.2 and Section 1.4.
-/

public section

open scoped ComplexOrder

namespace TauCeti

universe u w

/-- A normalized, positive, two-sided invariant linear functional on a complex star bialgebra. -/
structure AlgebraicHaar (A : Type u) [Semiring A] [Star A] [Bialgebra ℂ A] where
  /-- The underlying `ℂ`-linear functional. -/
  functional : A →ₗ[ℂ] ℂ
  /-- Normalization at the unit. -/
  normalized : functional 1 = 1
  /-- Left invariance `(id ⊗ h) Δ(a) = h(a) 1`. -/
  left_invariant : functional.IsLeftInvariantIntegral
  /-- Right invariance `(h ⊗ id) Δ(a) = h(a) 1`. -/
  right_invariant : functional.IsRightInvariantIntegral
  /-- Algebraic positivity on squares `star a * a`. -/
  positive : ∀ a : A, 0 ≤ functional (star a * a)

namespace AlgebraicHaar

section Bialgebra

variable {A : Type u} [Semiring A] [Star A] [Bialgebra ℂ A]

instance : FunLike (AlgebraicHaar A) A ℂ where
  coe h := h.functional
  coe_injective h₁ h₂ H := by
    cases h₁
    cases h₂
    congr
    exact DFunLike.coe_injective H

instance : LinearMapClass (AlgebraicHaar A) ℂ A ℂ where
  map_add h := h.functional.map_add
  map_smulₛₗ h := h.functional.map_smul

/-- Algebraic Haar states are determined by their values. -/
@[ext]
theorem ext {h₁ h₂ : AlgebraicHaar A} (H : ∀ a, h₁ a = h₂ a) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ H

@[simp]
theorem functional_apply (h : AlgebraicHaar A) (a : A) : h.functional a = h a :=
  (rfl)

/-- An algebraic Haar state sends `1` to `1`. -/
@[simp]
theorem map_one (h : AlgebraicHaar A) : h 1 = 1 :=
  h.normalized

/-- An algebraic Haar state is nonzero. -/
theorem functional_ne_zero (h : AlgebraicHaar A) : h.functional ≠ 0 := by
  intro h0
  have : (1 : ℂ) = 0 := by
    rw [← h.normalized, h0, LinearMap.zero_apply]
  exact one_ne_zero this

/-- An algebraic Haar state on a complex star bialgebra is unique when it exists. -/
instance : Subsingleton (AlgebraicHaar A) where
  allEq h₁ h₂ := by
    ext a
    exact LinearMap.congr_fun
      (h₁.right_invariant.eq_of_isLeftInvariantIntegral h₂.left_invariant
        h₁.normalized h₂.normalized) a

/-- The canonical algebraic Haar state on `ℂ`, given by the identity map. -/
def complex : AlgebraicHaar ℂ where
  functional := LinearMap.id
  normalized := rfl
  left_invariant := LinearMap.isLeftInvariantIntegral_iff.mpr fun a ↦ by simp
  right_invariant := LinearMap.isRightInvariantIntegral_iff.mpr fun a ↦ by simp
  positive a := star_mul_self_nonneg a

@[simp]
theorem complex_apply (z : ℂ) : complex z = z :=
  (rfl)

end Bialgebra

section StarRing

variable {A : Type u} [Ring A] [StarRing A] [Bialgebra ℂ A]

/-- View an algebraic Haar state as an algebraic positive functional. -/
def toStarPositiveFunctional (h : AlgebraicHaar A) : StarPositiveFunctional A where
  toLinearMap := h.functional
  square_nonneg := h.positive

@[simp]
theorem toStarPositiveFunctional_apply (h : AlgebraicHaar A) (a : A) :
    h.toStarPositiveFunctional a = h a :=
  (rfl)

variable [StarModule ℂ A]

/-- An algebraic Haar state commutes with `star`. -/
@[simp]
theorem map_star (h : AlgebraicHaar A) (a : A) : h (star a) = star (h a) :=
  h.toStarPositiveFunctional.map_star a

/-- Conjugate symmetry of the Haar sesquilinear form. -/
theorem star_apply_star_mul (h : AlgebraicHaar A) (a b : A) :
    star (h (star a * b)) = h (star b * a) :=
  h.toStarPositiveFunctional.star_apply_star_mul a b

end StarRing

section HopfAlgebra

variable {A : Type u} [Ring A]

/-- Left algebraic faithfulness of an algebraic Haar state. -/
theorem eq_zero_of_forall_mul_eq_zero_left [Star A] [HopfAlgebra ℂ A]
    (h : AlgebraicHaar A) {a : A} (ha : ∀ b, h (a * b) = 0) : a = 0 :=
  h.right_invariant.eq_zero_of_forall_mul_eq_zero h.functional_ne_zero ha

/-- Right algebraic faithfulness of an algebraic Haar state. -/
theorem eq_zero_of_forall_mul_eq_zero_right [Star A] [HopfAlgebra ℂ A]
    (h : AlgebraicHaar A) {a : A} (ha : ∀ b, h (b * a) = 0) : a = 0 :=
  h.left_invariant.eq_zero_of_forall_mul_eq_zero h.functional_ne_zero ha

variable [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]

/-- An algebraic Haar state vanishes on `star a * a` only when `a = 0`. -/
theorem map_star_mul_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (star a * a) = 0 ↔ a = 0 :=
  h.right_invariant.map_star_mul_self_eq_zero_iff h.functional_ne_zero h.positive

/-- An algebraic Haar state on a complex Hopf star algebra is strictly positive. -/
theorem map_star_mul_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) :
    0 < h (star a * a) :=
  h.right_invariant.map_star_mul_self_pos h.functional_ne_zero h.positive ha

variable [StarCoalgebra ℂ A]

/-- An algebraic Haar state on a complex Hopf star algebra is antipode-invariant. -/
@[simp]
theorem map_antipode (h : AlgebraicHaar A) (a : A) :
    h (HopfAlgebra.antipode ℂ a) = h a :=
  h.left_invariant.apply_antipode h.normalized
    (TauCeti.HopfAlgebra.antipode_bijective (R := ℂ) (A := A)).injective a

/-- A complex Hopf star algebra admitting an algebraic Haar state is linearly reductive. -/
theorem isLinearlyReductive (h : AlgebraicHaar A) :
    Coalgebra.IsLinearlyReductive.{0, u, w} ℂ A :=
  h.right_invariant.isLinearlyReductive h.functional_ne_zero h.positive

end HopfAlgebra

end AlgebraicHaar

end TauCeti
