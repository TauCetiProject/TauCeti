/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.Star.Projection.Commute
import Mathlib.Tactic.LinearCombination

/-!
# Balanced projections at the endpoint `τ = 0`

For `τ = 0` the balanced relation between adjacent generators of
`TauCeti.BalancedProjectionAlgebra R 0` reads `e i * e (i + 1) * e i = e (i + 1) * e i * e (i + 1)`.
It holds for any two commuting idempotents, so every sequence of idempotents in a commutative
algebra defines a representation (`TauCeti.BalancedProjectionAlgebra.liftComm`). In particular each
subset `s ⊆ ℕ`, that is each point of `{0, 1} ^ ℕ`, gives a character sending `e i` to `1` for
`i ∈ s` and to `0` otherwise (`TauCeti.BalancedProjectionAlgebra.indicatorCharacter`); at `s = ∅`
and `s = Set.univ` these are the two scalar characters.

Conversely, for two star projections in a ring with a proper star this forces them to commute
(`IsStarProjection.commute_of_mul_mul_eq`), and distant generators commute by definition. Hence
every representation of the balanced projection algebra by projections in such a ring (for
instance a C⋆-algebra) has commutative image.

## Main definitions

* `TauCeti.BalancedProjectionAlgebra.liftComm`: the representation defined by a sequence of
  idempotents in a commutative algebra.
* `TauCeti.BalancedProjectionAlgebra.indicatorCharacter`: the character at a subset of `ℕ`.

## Main results

* `TauCeti.BalancedProjectionAlgebra.commute_map_e_of_zero`: the images of any two generators
  commute.
* `TauCeti.BalancedProjectionAlgebra.commute_map_of_zero`: the image is commutative.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, for
  the projection generators of the Hecke algebra.
-/

public section

namespace TauCeti

namespace BalancedProjectionAlgebra

variable {R : Type*} [CommRing R]

/-! ### Representations in commutative algebras -/

section LiftComm

variable {A : Type*} [CommRing A] [Algebra R A]

variable (R) in
/-- At `τ = 0`, a sequence of idempotents in a commutative algebra defines a representation of the
balanced projection algebra: for commuting idempotents both sides of the balanced relation are
`e i * e (i + 1)`. -/
def liftComm (f : ℕ → A) (hf : ∀ i, IsIdempotentElem (f i)) :
    BalancedProjectionAlgebra R (0 : R) →ₐ[R] A :=
  lift f hf (fun i ↦ by
    simp only [zero_smul, sub_zero]
    linear_combination f (i + 1) * (hf i).eq - f i * (hf (i + 1)).eq) fun _ ↦ mul_comm _ _

/-- The representation `TauCeti.BalancedProjectionAlgebra.liftComm R f` sends `e i` to `f i`. -/
@[simp]
theorem liftComm_e (f : ℕ → A) (hf : ∀ i, IsIdempotentElem (f i)) (i : ℕ) :
    liftComm R f hf (e 0 i) = f i :=
  lift_e (τ := (0 : R)) _ _ _ _ i

end LiftComm

/-! ### Indicator characters -/

section IndicatorCharacter

variable (R) in
/-- The character of `TauCeti.BalancedProjectionAlgebra R 0` at a subset `s ⊆ ℕ`, that is at a
point of `{0, 1} ^ ℕ`: it sends `e i` to `1` for `i ∈ s` and to `0` otherwise. -/
noncomputable def indicatorCharacter (s : Set ℕ) : BalancedProjectionAlgebra R (0 : R) →ₐ[R] R :=
  liftComm R (s.indicator 1) fun i ↦ by
    by_cases hi : i ∈ s <;> simp [IsIdempotentElem, hi]

/-- The indicator character at `s` sends `e i` to `1` for `i ∈ s` and to `0` otherwise. -/
@[simp]
theorem indicatorCharacter_e (s : Set ℕ) (i : ℕ) :
    indicatorCharacter R s (e 0 i) = s.indicator 1 i :=
  liftComm_e _ _ i

/-- The indicator character at `∅` is the scalar character sending every generator to `0`. -/
@[simp]
theorem indicatorCharacter_empty : indicatorCharacter R ∅ = character 0 .zero :=
  hom_ext fun i ↦ by simp

/-- The indicator character at `Set.univ` is the scalar character sending every generator to
`1`. -/
@[simp]
theorem indicatorCharacter_univ : indicatorCharacter R Set.univ = character 1 .one :=
  hom_ext fun i ↦ by simp

end IndicatorCharacter

/-! ### Representations by projections -/

section StarProjection

variable {A F : Type*} [Ring A] [StarRing A] [IsProperStar A] [Algebra R A]
  [FunLike F (BalancedProjectionAlgebra R (0 : R)) A]
  [AlgHomClass F R (BalancedProjectionAlgebra R (0 : R)) A] (φ : F)

/-- For `τ = 0`, the images of any two generators under a representation by projections in a ring
with a proper star commute. -/
theorem commute_map_e_of_zero (hφ : ∀ i, IsStarProjection (φ (e 0 i))) (i j : ℕ) :
    Commute (φ (e 0 i)) (φ (e 0 j)) := by
  refine commute_map_e_of_commute_map_e_succ φ (fun i ↦ ?_) i j
  refine (hφ i).commute_of_mul_mul_eq (hφ (i + 1)) ?_
  simpa only [map_sub, map_mul, map_smul, zero_smul, sub_zero] using
    congr_arg φ (e_balanced (τ := (0 : R)) i)

/-- For `τ = 0`, a representation by projections in a ring with a proper star has commutative
image. -/
theorem commute_map_of_zero (hφ : ∀ i, IsStarProjection (φ (e 0 i)))
    (x y : BalancedProjectionAlgebra R (0 : R)) : Commute (φ x) (φ y) :=
  commute_map_of_commute_map_e_succ φ (fun i ↦ commute_map_e_of_zero φ hφ i (i + 1)) x y

end StarProjection

end BalancedProjectionAlgebra

end TauCeti
