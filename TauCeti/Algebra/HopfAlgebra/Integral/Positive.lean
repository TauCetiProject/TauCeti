/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# Strict positivity of positive invariant integrals and algebraic Haar functionals

Let `A` be a complex Hopf algebra with a star structure and let `h : A → ℂ` be a nonzero
one-sided invariant integral which is positive in the algebraic sense,
`0 ≤ h (star a * a)` for every `a`. Then `h` is strictly positive: `0 < h (star a * a)` for every
`a ≠ 0`.

The Cauchy–Schwarz inequality, in the form
`TauCeti.StarPositiveFunctional.apply_star_mul_self_eq_zero_iff`, turns `h (star a * a) = 0` into
the vanishing of `h (star b * a)` and of `h (star a * b)` for all `b`. The algebraic faithfulness
of nonzero invariant integrals, `LinearMap.IsRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero`
and its left counterpart, then forces `a = 0`. No norm, order or completeness on `A` is involved,
and the comultiplication need not be a star map. Strict positivity is what makes the
Haar-averaged inner products of finite-dimensional comodules definite, and the Haar GNS
construction faithful.

This file also bundles normalized positive two-sided invariant integrals on a complex bialgebra
with a star structure as `TauCeti.AlgebraicHaar`. Normalized two-sided invariant integrals are
unique (`Subsingleton (AlgebraicHaar A)`), and normalization forces the underlying linear
functional to be nonzero, so on a complex Hopf algebra with a compatible star structure every
`AlgebraicHaar` functional is strictly positive on nonzero squares and has nondegenerate
multiplication pairings on both sides.

## Main declarations

* `LinearMap.IsRightInvariantIntegral.map_star_mul_self_eq_zero_iff` and
  `LinearMap.IsLeftInvariantIntegral.map_star_mul_self_eq_zero_iff`: `h (star a * a) = 0` only
  for `a = 0`.
* `LinearMap.IsRightInvariantIntegral.map_star_mul_self_pos` and
  `LinearMap.IsLeftInvariantIntegral.map_star_mul_self_pos`: `0 < h (star a * a)` for `a ≠ 0`.
* `TauCeti.AlgebraicHaar`: a positive normalized two-sided invariant integral on a complex
  bialgebra with a star structure, with `FunLike`, `LinearMapClass`, `OneHomClass`, extensionality,
  uniqueness (`Subsingleton`), and strict positivity over a Hopf algebra.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 2.2.4,
  Remark 2.2.2, and Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.6.6, Step 1, p. 18.
-/

public section

open scoped ComplexOrder

namespace LinearMap

variable {A : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  {h : A →ₗ[ℂ] ℂ}

/-- A nonzero positive right invariant integral vanishes on `star a * a` only for `a = 0`. -/
theorem IsRightInvariantIntegral.map_star_mul_self_eq_zero_iff
    (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A} :
    h (star a * a) = 0 ↔ a = 0 := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ by simp [ha]⟩
  let φ : TauCeti.StarPositiveFunctional A := ⟨h, hpos⟩
  have hnull := (φ.apply_star_mul_self_eq_zero_iff a).mp ha
  rw [← star_eq_zero]
  refine hh.eq_zero_of_forall_mul_eq_zero h0 fun b ↦ ?_
  have hab := φ.star_apply_star_mul a b
  rw [hnull b, star_eq_zero] at hab
  simpa [φ] using hab

/-- A nonzero positive left invariant integral vanishes on `star a * a` only for `a = 0`. -/
theorem IsLeftInvariantIntegral.map_star_mul_self_eq_zero_iff
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A} :
    h (star a * a) = 0 ↔ a = 0 := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ by simp [ha]⟩
  let φ : TauCeti.StarPositiveFunctional A := ⟨h, hpos⟩
  have hnull := (φ.apply_star_mul_self_eq_zero_iff a).mp ha
  exact hh.eq_zero_of_forall_mul_eq_zero h0 fun b ↦ by simpa [φ] using hnull (star b)

/-- A nonzero positive right invariant integral is strictly positive. -/
theorem IsRightInvariantIntegral.map_star_mul_self_pos
    (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A}
    (ha : a ≠ 0) : 0 < h (star a * a) :=
  (hpos a).lt_of_ne' ((hh.map_star_mul_self_eq_zero_iff h0 hpos).not.mpr ha)

/-- A nonzero positive left invariant integral is strictly positive. -/
theorem IsLeftInvariantIntegral.map_star_mul_self_pos
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A}
    (ha : a ≠ 0) : 0 < h (star a * a) :=
  (hpos a).lt_of_ne' ((hh.map_star_mul_self_eq_zero_iff h0 hpos).not.mpr ha)

end LinearMap

namespace TauCeti

/-- A positive normalized two-sided invariant integral on a complex bialgebra with a star structure
`A`: a `ℂ`-linear functional `h : A → ℂ` with `h 1 = 1`, left invariance `(id ⊗ h) Δ(a) = h(a) 1`,
right invariance `(h ⊗ id) Δ(a) = h(a) 1`, and algebraic positivity `0 ≤ h (star a * a)` for
every `a : A`. -/
structure AlgebraicHaar (A : Type*) [Semiring A] [StarRing A] [Bialgebra ℂ A]
    extends A →ₗ[ℂ] ℂ where
  /-- Normalization on the unit element. -/
  map_one' : toLinearMap 1 = 1
  /-- Left Haar slice invariance `(id ⊗ h) Δ(a) = h(a) 1`. -/
  left_invariant' : toLinearMap.IsLeftInvariantIntegral
  /-- Right Haar slice invariance `(h ⊗ id) Δ(a) = h(a) 1`. -/
  right_invariant' : toLinearMap.IsRightInvariantIntegral
  /-- Nonnegativity on every algebraic square `star a * a`. -/
  square_nonneg' : ∀ a, 0 ≤ toLinearMap (star a * a)

namespace AlgebraicHaar

section Bialgebra

variable {A : Type*} [Semiring A] [StarRing A] [Bialgebra ℂ A]

instance : FunLike (AlgebraicHaar A) A ℂ where
  coe h := h.toLinearMap
  coe_injective h₁ h₂ H := by
    cases h₁
    cases h₂
    congr
    exact DFunLike.coe_injective H

instance : LinearMapClass (AlgebraicHaar A) ℂ A ℂ where
  map_add h := h.toLinearMap.map_add
  map_smulₛₗ h := h.toLinearMap.map_smul

instance : OneHomClass (AlgebraicHaar A) A ℂ where
  map_one h := h.map_one'

/-- Two `AlgebraicHaar` functionals are equal as soon as they agree pointwise. -/
@[ext]
theorem ext {h₁ h₂ : AlgebraicHaar A} (H : ∀ a, h₁ a = h₂ a) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ H

@[simp]
theorem coe_toLinearMap (h : AlgebraicHaar A) : ⇑h.toLinearMap = h :=
  (rfl)

theorem toLinearMap_apply (h : AlgebraicHaar A) (a : A) : h.toLinearMap a = h a :=
  (rfl)

@[simp]
theorem ofClass_eq_toLinearMap (h : AlgebraicHaar A) : (h : A →ₗ[ℂ] ℂ) = h.toLinearMap :=
  (rfl)

@[simp]
theorem mk_apply (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1) (hl : f.IsLeftInvariantIntegral)
    (hr : f.IsRightInvariantIntegral) (hp : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    (AlgebraicHaar.mk f h1 hl hr hp) a = f a :=
  (rfl)

/-- The underlying linear functional of an `AlgebraicHaar` integral is left invariant. -/
theorem isLeftInvariantIntegral (h : AlgebraicHaar A) :
    h.toLinearMap.IsLeftInvariantIntegral :=
  h.left_invariant'

/-- The underlying linear functional of an `AlgebraicHaar` integral is right invariant. -/
theorem isRightInvariantIntegral (h : AlgebraicHaar A) :
    h.toLinearMap.IsRightInvariantIntegral :=
  h.right_invariant'

/-- An `AlgebraicHaar` integral is nonnegative on every square `star a * a`. -/
theorem map_star_mul_self_nonneg (h : AlgebraicHaar A) (a : A) :
    0 ≤ h (star a * a) :=
  h.square_nonneg' a

/-- Normalization `h 1 = 1` prevents the underlying linear functional from vanishing. -/
theorem toLinearMap_ne_zero (h : AlgebraicHaar A) : h.toLinearMap ≠ 0 := fun h0 ↦
  one_ne_zero (h.map_one'.symm.trans (by simp [h0]))

/-- Normalized two-sided invariant integrals on a complex bialgebra are unique. -/
instance : Subsingleton (AlgebraicHaar A) :=
  ⟨fun h₁ h₂ ↦ ext fun a ↦ by
    let r := Coalgebra.Repr.arbitrary ℂ a
    have hright := congr_arg h₂ (h₁.isRightInvariantIntegral.sum_smul r)
    have hleft := congr_arg h₁ (h₂.isLeftInvariantIntegral.sum_smul r)
    simp only [coe_toLinearMap, map_sum, map_smul, smul_eq_mul, map_one, mul_one] at hright hleft
    calc
      h₁ a = ∑ i ∈ r.index, h₁ (r.left i) * h₂ (r.right i) := hright.symm
      _ = ∑ i ∈ r.index, h₂ (r.right i) * h₁ (r.left i) :=
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
      _ = h₂ a := hleft⟩

end Bialgebra

section Ring

variable {A : Type*} [Ring A] [StarRing A] [Bialgebra ℂ A]

/-- Forget invariance and normalization to view an `AlgebraicHaar` integral as a
`StarPositiveFunctional`. -/
def toStarPositiveFunctional (h : AlgebraicHaar A) : StarPositiveFunctional A where
  toLinearMap := h.toLinearMap
  square_nonneg := h.square_nonneg'

@[simp]
theorem coe_toStarPositiveFunctional (h : AlgebraicHaar A) :
    ⇑h.toStarPositiveFunctional = h :=
  (rfl)

@[simp]
theorem toStarPositiveFunctional_toLinearMap (h : AlgebraicHaar A) :
    h.toStarPositiveFunctional.toLinearMap = h.toLinearMap :=
  (rfl)

/-- An `AlgebraicHaar` integral on a complex star algebra commutes with `star`. -/
@[simp]
theorem map_star [StarModule ℂ A] (h : AlgebraicHaar A) (a : A) :
    h (star a) = star (h a) :=
  h.toStarPositiveFunctional.map_star a

end Ring

section HopfAlgebra

variable {A : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]

/-- Right Haar faithfulness: an element `a` satisfying `h (a * b) = 0` for all `b` is zero. -/
theorem eq_zero_of_forall_mul_right_eq_zero (h : AlgebraicHaar A) {a : A}
    (ha : ∀ b, h (a * b) = 0) : a = 0 :=
  h.isRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero h.toLinearMap_ne_zero ha

/-- Left Haar faithfulness: an element `a` satisfying `h (b * a) = 0` for all `b` is zero. -/
theorem eq_zero_of_forall_mul_left_eq_zero (h : AlgebraicHaar A) {a : A}
    (ha : ∀ b, h (b * a) = 0) : a = 0 :=
  h.isLeftInvariantIntegral.eq_zero_of_forall_mul_eq_zero h.toLinearMap_ne_zero ha

variable [StarModule ℂ A]

/-- An `AlgebraicHaar` integral on a complex Hopf algebra with a compatible star structure
vanishes on `star a * a` only at `a = 0`. -/
@[simp]
theorem map_star_mul_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (star a * a) = 0 ↔ a = 0 :=
  h.isRightInvariantIntegral.map_star_mul_self_eq_zero_iff
    h.toLinearMap_ne_zero h.map_star_mul_self_nonneg

/-- Strict positivity: `0 < h (star a * a)` for every nonzero element `a`. -/
theorem map_star_mul_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) :
    0 < h (star a * a) :=
  h.isRightInvariantIntegral.map_star_mul_self_pos
    h.toLinearMap_ne_zero h.map_star_mul_self_nonneg ha

end HopfAlgebra

end AlgebraicHaar

end TauCeti
