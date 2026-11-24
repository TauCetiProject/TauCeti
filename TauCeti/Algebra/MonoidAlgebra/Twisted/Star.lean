/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# The star structure on a twisted group algebra with unitary factor set

Let `k` be a commutative star semiring, `G` a group and `α` a factor set on `G` whose values are
unitary elements of `k` (`TauCeti.IsUnitaryFactorSet`); over `ℂ` this means that `α` takes values
on the unit circle. Then the twisted group algebra `k_α[G]` carries the conjugate-linear,
product-reversing involution for which every basis element `e g` is unitary:
`star (e g) = (e g)⁻¹ = star (α g g⁻¹) • e g⁻¹`, and
`star (Σ c_g e g) = Σ star c_g • star (e g)`. For the trivial factor set and `k = ℂ` this is the
usual adjoint `f ↦ (g ↦ conj (f g⁻¹))` of the complex group algebra.

The coefficient at the identity is a positive trace for this star structure:
`(star x * x)_1 = Σ_g star x_g * x_g`. So over an ordered star ring without zero divisors, such as
`ℂ` with its `ComplexOrder`, it is faithful.

## Main definitions

* `TauCeti.IsUnitaryFactorSet`: a factor set with unitary values.
* `TauCeti.TwistedMonoidAlgebra.instStarRing` and `TauCeti.TwistedMonoidAlgebra.instStarModule`:
  the conjugate-linear star structure on `k_α[G]` for a unitary factor set.
* `TauCeti.TwistedMonoidAlgebra.identityCoefficient`: over `ℂ`, the coefficient at the identity
  as a positive functional.

## Main results

* `TauCeti.TwistedMonoidAlgebra.star_of` and `TauCeti.TwistedMonoidAlgebra.of_mem_unitary`: the
  adjoint of a basis element, which is unitary.
* `TauCeti.TwistedMonoidAlgebra.repr_star_apply`: the coefficients of the adjoint.
* `TauCeti.TwistedMonoidAlgebra.map_star_iff`: an algebra map into a star algebra preserves the
  star structure exactly when it sends the basis elements to unitaries.
* `TauCeti.TwistedMonoidAlgebra.repr_star_mul_self_apply_one`,
  `TauCeti.TwistedMonoidAlgebra.repr_star_mul_self_apply_one_nonneg` and
  `TauCeti.TwistedMonoidAlgebra.repr_star_mul_self_apply_one_eq_zero_iff`: the coefficient at
  the identity is a faithful positive trace.
* `TauCeti.TwistedMonoidAlgebra.nullSubmodule_identityCoefficient`: over `ℂ`, the coefficient at
  the identity has trivial GNS null space.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti

open Module

/-- A factor set is **unitary** when all of its values are unitary elements of the star semiring
`k`; for `k = ℂ`, when they lie on the unit circle. Its twisted group algebra then carries a star
structure making every basis element unitary (`TauCeti.TwistedMonoidAlgebra.instStarRing`). -/
class IsUnitaryFactorSet {k G : Type*} [CommSemiring k] [StarRing k] (α : G → G → kˣ) :
    Prop where
  /-- Every value of the factor set is unitary. -/
  mem_unitary (g h : G) : (α g h : k) ∈ unitary k

namespace TwistedMonoidAlgebra

variable {k G : Type*} [CommSemiring k] [StarRing k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- The adjoint `Σ c_g e g ↦ Σ star c_g • star (α g g⁻¹) • e g⁻¹`, a conjugate-linear map. -/
private noncomputable def adjoint :
    twistedMonoidAlgebra k G α →ₗ⋆[k] twistedMonoidAlgebra k G α where
  toFun x := ((basis k G α).repr x).sum fun g c ↦ star c • star (α g g⁻¹ : k) • of g⁻¹
  map_add' x y := by
    rw [map_add]
    exact Finsupp.sum_add_index' (by simp) (by simp [add_smul])
  map_smul' r x := by
    rw [map_smul, Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
    simp [star_mul', mul_smul, starRingEnd_apply]

private theorem adjoint_of (g : G) :
    adjoint (of g : twistedMonoidAlgebra k G α) = star (α g g⁻¹ : k) • of g⁻¹ := by
  simp [adjoint]

variable [IsUnitaryFactorSet α]

private theorem of_mul_adjoint_of (g : G) :
    (of g : twistedMonoidAlgebra k G α) * adjoint (of g) = 1 := by
  simp [adjoint_of, smul_smul, Unitary.star_mul_self_of_mem (IsUnitaryFactorSet.mem_unitary _ _)]

private theorem adjoint_of_mul_of (g : G) :
    adjoint (of g : twistedMonoidAlgebra k G α) * of g = 1 := by
  simp [adjoint_of, smul_smul, ← IsFactorSet.apply_inv_eq_inv_apply α g,
    Unitary.star_mul_self_of_mem (IsUnitaryFactorSet.mem_unitary _ _)]

private theorem adjoint_of_mul_of_eq (g h : G) :
    adjoint (of g * of h : twistedMonoidAlgebra k G α) = adjoint (of h) * adjoint (of g) := by
  -- Both sides are inverses of `of g * of h`: the left side on the left, the right side on the
  -- right.
  refine left_inv_eq_right_inv (a := of g * of h) ?_ ?_
  · simp [adjoint_of_mul_of, smul_smul, starRingEnd_apply,
      Unitary.mul_star_self_of_mem (IsUnitaryFactorSet.mem_unitary _ _)]
  · rw [mul_assoc, ← mul_assoc (of h), of_mul_adjoint_of, one_mul, of_mul_adjoint_of]

private theorem adjoint_mul (x y : twistedMonoidAlgebra k G α) :
    adjoint (x * y) = adjoint y * adjoint x := by
  -- The two sides are conjugate-linear in each variable, so it suffices to compare them on basis
  -- elements.
  have hof (g : G) (y : twistedMonoidAlgebra k G α) :
      adjoint (of g * y) = adjoint y * adjoint (of g) := by
    have h : adjoint ∘ₛₗ LinearMap.mulLeft k (of g : twistedMonoidAlgebra k G α) =
        LinearMap.mulRight k (adjoint (of g)) ∘ₛₗ adjoint :=
      (basis k G α).ext fun h ↦ by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
          basis_apply, adjoint_of_mul_of_eq]
    exact LinearMap.congr_fun h y
  have h : adjoint ∘ₛₗ LinearMap.mulRight k y = LinearMap.mulLeft k (adjoint y) ∘ₛₗ adjoint :=
    (basis k G α).ext fun g ↦ by simp [hof]
  exact LinearMap.congr_fun h x

private theorem adjoint_adjoint (x : twistedMonoidAlgebra k G α) : adjoint (adjoint x) = x := by
  have h : adjoint ∘ₛₗ adjoint = (LinearMap.id : twistedMonoidAlgebra k G α →ₗ[k] _) :=
    (basis k G α).ext fun g ↦ by
      simp [adjoint_of, smul_smul, starRingEnd_apply, ← IsFactorSet.apply_inv_eq_inv_apply α g,
        Unitary.mul_star_self_of_mem (IsUnitaryFactorSet.mem_unitary _ _)]
  exact LinearMap.congr_fun h x

/-- **The star structure on a twisted group algebra** with unitary factor set: the
conjugate-linear, product-reversing involution `Σ c_g e g ↦ Σ star c_g • (e g)⁻¹`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (twistedMonoidAlgebra k G α) where
  star := adjoint
  star_involutive := adjoint_adjoint
  star_mul := adjoint_mul
  star_add := map_add adjoint

/-- The star structure on a twisted group algebra is conjugate-linear. -/
instance instStarModule : StarModule k (twistedMonoidAlgebra k G α) where
  star_smul r x := LinearMap.map_smulₛₗ adjoint r x

private theorem star_def (x : twistedMonoidAlgebra k G α) :
    star x = ((basis k G α).repr x).sum fun g c ↦ star c • star (α g g⁻¹ : k) • of g⁻¹ :=
  (rfl)

/-- The adjoint of a basis element is its inverse, `star (e g) = star (α g g⁻¹) • e g⁻¹`. -/
@[simp]
theorem star_of (g : G) :
    star (of g : twistedMonoidAlgebra k G α) = star (α g g⁻¹ : k) • of g⁻¹ :=
  adjoint_of g

/-- The basis elements of a twisted group algebra with unitary factor set are unitary. -/
theorem of_mem_unitary (g : G) : (of g : twistedMonoidAlgebra k G α) ∈ unitary _ :=
  Unitary.mem_iff.2 ⟨adjoint_of_mul_of g, of_mul_adjoint_of g⟩

/-- The coefficients of the adjoint: `(star x)_g = star (α g⁻¹ g * x_(g⁻¹))`. -/
theorem repr_star_apply (x : twistedMonoidAlgebra k G α) (g : G) :
    (basis k G α).repr (star x) g = star ((α g⁻¹ g : k) * (basis k G α).repr x g⁻¹) := by
  classical
  rw [star_def, map_finsuppSum, Finsupp.sum_apply]
  simp only [map_smul, repr_of, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply,
    inv_eq_iff_eq_inv]
  rw [Finsupp.sum_ite_eq']
  split_ifs with h
  · rw [inv_inv, star_mul', mul_comm]
  · rw [Finsupp.notMem_support_iff.1 h, mul_zero, star_zero]

/-- An algebra map from a twisted group algebra with unitary factor set into a star algebra
preserves the star structure exactly when it sends every basis element to a unitary. -/
theorem map_star_iff {A : Type*} [Semiring A] [StarRing A] [Algebra k A] [StarModule k A]
    {φ : twistedMonoidAlgebra k G α →ₐ[k] A} :
    (∀ x, φ (star x) = star (φ x)) ↔ ∀ g, φ (of g) ∈ unitary A := by
  constructor
  · intro h g
    have hg := of_mem_unitary (α := α) g
    simp [Unitary.mem_iff, ← h, ← map_mul, -star_of, Unitary.star_mul_self_of_mem hg,
      Unitary.mul_star_self_of_mem hg]
  · intro h
    -- On a basis element both sides are inverses of `φ (of g)`.
    have hof (g : G) : φ (star (of g)) = star (φ (of g)) :=
      left_inv_eq_right_inv (a := φ (of g))
        (by rw [← map_mul, Unitary.star_mul_self_of_mem (of_mem_unitary (α := α) g), map_one])
        (Unitary.mul_star_self_of_mem (h g))
    have key : φ.toLinearMap ∘ₛₗ (starLinearEquiv k).toLinearMap =
        (starLinearEquiv k).toLinearMap ∘ₛₗ φ.toLinearMap :=
      (basis k G α).ext fun g ↦ by simpa using hof g
    exact fun x ↦ LinearMap.congr_fun key x

/-- The coefficient at the identity of `star (e g) * e h` is `1` when `g = h` and `0` otherwise. -/
private theorem repr_star_of_mul_of_apply_one [DecidableEq G] (g h : G) :
    (basis k G α).repr (star (of g) * of h : twistedMonoidAlgebra k G α) 1 =
      if g = h then 1 else 0 := by
  split_ifs with hgh
  · rw [hgh, Unitary.star_mul_self_of_mem (of_mem_unitary (α := α) h), repr_one,
      Finsupp.single_eq_same]
  · simp [inv_mul_eq_one, hgh]

/-- **The coefficient at the identity of `star x * x`** is `Σ_g star x_g * x_g`. -/
theorem repr_star_mul_self_apply_one (x : twistedMonoidAlgebra k G α) :
    (basis k G α).repr (star x * x) 1 = ((basis k G α).repr x).sum fun _ c ↦ star c * c := by
  classical
  conv_lhs => rw [← (basis k G α).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, star_sum, star_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, basis_apply, smul_eq_mul, repr_star_of_mul_of_apply_one, mul_ite,
    mul_one, mul_zero]
  exact Finset.sum_congr rfl fun g hg ↦ by rw [Finset.sum_ite_eq', ite_eq_left hg]

section Order

variable {k : Type*} [CommSemiring k] [PartialOrder k] [StarRing k] [StarOrderedRing k]
  {α : G → G → kˣ} [IsFactorSet α] [IsUnitaryFactorSet α]

/-- The coefficient at the identity is a positive functional. -/
theorem repr_star_mul_self_apply_one_nonneg (x : twistedMonoidAlgebra k G α) :
    0 ≤ (basis k G α).repr (star x * x) 1 := by
  rw [repr_star_mul_self_apply_one]
  exact Finset.sum_nonneg fun g _ ↦ star_mul_self_nonneg _

/-- Over an ordered star ring without zero divisors, the coefficient at the identity is a
faithful positive functional. -/
@[simp]
theorem repr_star_mul_self_apply_one_eq_zero_iff [NoZeroDivisors k]
    {x : twistedMonoidAlgebra k G α} :
    (basis k G α).repr (star x * x) 1 = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [repr_star_mul_self_apply_one, Finsupp.sum,
    Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦ star_mul_self_nonneg _] at h
  rw [← (basis k G α).repr.map_eq_zero_iff, ← Finsupp.support_eq_empty,
    Finset.eq_empty_iff_forall_notMem]
  intro g hg
  rcases mul_eq_zero.1 (h g hg) with h' | h'
  · exact Finsupp.mem_support_iff.1 hg (star_eq_zero.1 h')
  · exact Finsupp.mem_support_iff.1 hg h'

end Order

section Complex

open scoped ComplexOrder

variable {α : G → G → ℂˣ} [IsFactorSet α] [IsUnitaryFactorSet α]

/-- Over `ℂ`, **the coefficient at the identity** as a positive functional on `ℂ_α[G]`. -/
noncomputable def identityCoefficient : StarPositiveFunctional (twistedMonoidAlgebra ℂ G α) where
  toLinearMap := (basis ℂ G α).coord 1
  square_nonneg := repr_star_mul_self_apply_one_nonneg

/-- `identityCoefficient` evaluates as the coefficient at the identity. -/
@[simp]
theorem identityCoefficient_apply (x : twistedMonoidAlgebra ℂ G α) :
    identityCoefficient x = (basis ℂ G α).repr x 1 :=
  (rfl)

/-- The coefficient at the identity is faithful: its GNS null space is trivial. -/
theorem nullSubmodule_identityCoefficient :
    (identityCoefficient : StarPositiveFunctional (twistedMonoidAlgebra ℂ G α)).nullSubmodule =
      ⊥ := by
  ext x
  simp

end Complex

end TwistedMonoidAlgebra

end TauCeti
