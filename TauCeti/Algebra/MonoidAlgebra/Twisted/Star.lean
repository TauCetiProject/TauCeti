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

/-!
# The adjoint on a twisted group algebra

Let `G` be a group, `k` a commutative semiring with an involution `star`, and `α` a factor set on
`G` with `star (α g h) = α h⁻¹ g⁻¹`, a **star factor set** (`TauCeti.IsStarFactorSet`). Then the
twisted group algebra `k_α[G]` carries the conjugate-linear *adjoint*
`(Σ z_g e g)⋆ = Σ star (z_g) e g⁻¹`. It reverses products because conjugating the multiplication
table `e g * e h = α g h • e (g * h)` gives `e h⁻¹ * e g⁻¹ = α h⁻¹ g⁻¹ • e (h⁻¹ * g⁻¹)`. So
`k_α[G]` is a star algebra in which `e g⋆ = e g⁻¹`.

If moreover `α g⁻¹ g = 1` for every `g`, the basis elements are unitary and the coefficient at the
identity satisfies the **Parseval identity** `(x⋆ x)_1 = Σ_g star (x_g) x_g`. Over a star-ordered
ring without zero divisors, for instance `ℂ`, the coefficient at the identity is therefore a
faithful positive functional; over `ℂ` it is packaged as one in
`TauCeti.Algebra.MonoidAlgebra.Twisted.Positive`.

## Main definitions

* `TauCeti.IsStarFactorSet`: a factor set compatible with the involution on the scalars.
* `TauCeti.TwistedMonoidAlgebra.instStarRing` and `TauCeti.TwistedMonoidAlgebra.instStarModule`:
  the conjugate-linear adjoint on `k_α[G]`.

## Main results

* `TauCeti.TwistedMonoidAlgebra.star_of` and `TauCeti.TwistedMonoidAlgebra.repr_star`: the adjoint
  on the basis and on coefficients.
* `TauCeti.TwistedMonoidAlgebra.map_star_of_map_of_inv`: a linear map out of `k_α[G]` commutes
  with the adjoints once it does so on the basis.
* `TauCeti.TwistedMonoidAlgebra.of_mem_unitary`: the basis elements are unitary.
* `TauCeti.TwistedMonoidAlgebra.map_star_iff`: when the basis elements are unitary, an algebra
  map into a star algebra preserves the adjoint exactly when it sends them to unitaries.
* `TauCeti.TwistedMonoidAlgebra.repr_star_mul_self_apply_one` and
  `TauCeti.TwistedMonoidAlgebra.repr_star_mul_self_apply_one_eq_zero_iff`: the Parseval identity
  and faithfulness of the coefficient at the identity.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti

/-- A factor set `α` on a group with values in a star ring is a **star factor set** if
conjugating it reverses and inverts its arguments: `star (α g h) = α h⁻¹ g⁻¹`. This is what makes
`e g ↦ e g⁻¹` extend to a conjugate-linear anti-multiplicative involution of the twisted group
algebra. -/
class IsStarFactorSet {k G : Type*} [CommSemiring k] [StarRing k] [Group G] (α : G → G → kˣ) :
    Prop where
  /-- Conjugating the factor set reverses and inverts its arguments. -/
  star_apply (g h : G) : star (α g h : k) = α h⁻¹ g⁻¹

namespace TwistedMonoidAlgebra

variable {k G : Type*} [CommSemiring k] [StarRing k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-! ### The adjoint -/

section Adjoint

variable (k G α) in
/-- The conjugate-linear map `Σ z_g e g ↦ Σ star (z_g) e g⁻¹` underlying the adjoint. -/
private noncomputable def starₗ : twistedMonoidAlgebra k G α →ₗ⋆[k] twistedMonoidAlgebra k G α where
  toFun x := ((basis k G α).repr x).sum fun g c ↦ star c • of g⁻¹
  map_add' x y := by
    rw [map_add]
    exact Finsupp.sum_add_index' (by simp) (by simp [add_smul])
  map_smul' c x := by
    rw [map_smul, Finsupp.sum_smul_index' (by simp)]
    simp [Finsupp.smul_sum, star_mul', mul_smul, starRingEnd_apply]

private theorem starₗ_of (g : G) : starₗ k G α (of g) = of g⁻¹ := by
  simp [starₗ]

private theorem starₗ_starₗ (x : twistedMonoidAlgebra k G α) :
    starₗ k G α (starₗ k G α x) = x := by
  have key : (starₗ k G α).comp (starₗ k G α) = LinearMap.id :=
    (basis k G α).ext fun g ↦ by simp [starₗ_of]
  exact LinearMap.congr_fun key x

variable [IsStarFactorSet α]

private theorem starₗ_mul (x y : twistedMonoidAlgebra k G α) :
    starₗ k G α (x * y) = starₗ k G α y * starₗ k G α x := by
  -- Both sides are conjugate-linear in each argument, so compare them on basis elements.
  have hof (g : G) :
      (starₗ k G α).comp (LinearMap.mulLeft k (of g)) =
        (LinearMap.mulRight k (of g⁻¹)).comp (starₗ k G α) :=
    (basis k G α).ext fun h ↦ by
      simp [starₗ_of, starRingEnd_apply, IsStarFactorSet.star_apply]
  have key : (starₗ k G α).comp (LinearMap.mulRight k y) =
      (LinearMap.mulLeft k (starₗ k G α y)).comp (starₗ k G α) :=
    (basis k G α).ext fun g ↦ by
      simpa [starₗ_of] using LinearMap.congr_fun (hof g) y
  simpa using LinearMap.congr_fun key x

/-- The **adjoint** on a twisted group algebra of a star factor set: the conjugate-linear,
product-reversing involution `(Σ z_g e g)⋆ = Σ star (z_g) e g⁻¹`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (twistedMonoidAlgebra k G α) where
  star := starₗ k G α
  star_involutive := starₗ_starₗ
  star_mul := starₗ_mul
  star_add := map_add (starₗ k G α)

/-- A shortcut to the `Star` of `instStarRing`. Instance search tries it before the `StarMemClass`
star of the ambient `Module.End k (G →₀ k)`, whose search through the inner-product adjoint
instances can exhaust the instance-synthesis budget, for instance at `CubicTorus (m - 1)` in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`. -/
noncomputable instance instStar : Star (twistedMonoidAlgebra k G α) :=
  inferInstance

private theorem star_eq_starₗ (x : twistedMonoidAlgebra k G α) : star x = starₗ k G α x :=
  (rfl)

/-- The adjoint on a twisted group algebra is conjugate-linear. -/
instance instStarModule : StarModule k (twistedMonoidAlgebra k G α) where
  star_smul c x := by
    simpa only [star_eq_starₗ, starRingEnd_apply] using map_smulₛₗ (starₗ k G α) c x

/-- The adjoint on the basis: `e g⋆ = e g⁻¹`. -/
@[simp]
theorem star_of (g : G) : star (of g : twistedMonoidAlgebra k G α) = of g⁻¹ :=
  starₗ_of g

/-- A linear map out of a twisted group algebra commutes with the adjoints once it does so on the
basis. -/
theorem map_star_of_map_of_inv {A : Type*} [AddCommMonoid A] [Module k A] [StarAddMonoid A]
    [StarModule k A] (f : twistedMonoidAlgebra k G α →ₗ[k] A)
    (hf : ∀ g, f (of g⁻¹) = star (f (of g))) (x : twistedMonoidAlgebra k G α) :
    f (star x) = star (f x) := by
  have key : f.comp (starLinearEquiv k (A := twistedMonoidAlgebra k G α)).toLinearMap =
      (starLinearEquiv k (A := A)).toLinearMap.comp f :=
    (basis k G α).ext fun g ↦ by simp [hf]
  simpa using LinearMap.congr_fun key x

/-- The coefficients of the adjoint: the coefficient of `x⋆` at `g` is the conjugate of the
coefficient of `x` at `g⁻¹`. -/
@[simp]
theorem repr_star (x : twistedMonoidAlgebra k G α) (g : G) :
    (basis k G α).repr (star x) g = star ((basis k G α).repr x g⁻¹) := by
  classical
  have key : ((Finsupp.lapply g).comp (basis k G α).repr.toLinearMap).comp
      (starLinearEquiv k (A := twistedMonoidAlgebra k G α)).toLinearMap =
        (starLinearEquiv k (A := k)).toLinearMap.comp
          ((Finsupp.lapply g⁻¹).comp (basis k G α).repr.toLinearMap) :=
    (basis k G α).ext fun h ↦ by
      simp [Finsupp.single_apply, inv_eq_iff_eq_inv]
      split_ifs <;> simp
  simpa using LinearMap.congr_fun key x

/-- A basis element `e g` is unitary when `α g⁻¹ g = 1`. -/
theorem of_mem_unitary {g : G} (hg : (α g⁻¹ g : k) = 1) :
    (of g : twistedMonoidAlgebra k G α) ∈ unitary (twistedMonoidAlgebra k G α) := by
  have hg' : (α g g⁻¹ : k) = 1 := by rw [IsFactorSet.apply_inv_eq_inv_apply α g, hg]
  rw [Unitary.mem_iff, star_of]
  constructor <;> simp [hg, hg']

/-- **The universal property as a star algebra**: when `α g⁻¹ g = 1` for every `g`, an algebra
map from a twisted group algebra into a star algebra preserves the adjoint exactly when it sends
every basis element to a unitary. -/
theorem map_star_iff {A : Type*} [Semiring A] [StarRing A] [Algebra k A] [StarModule k A]
    (hα : ∀ g, (α g⁻¹ g : k) = 1) {φ : twistedMonoidAlgebra k G α →ₐ[k] A} :
    (∀ x, φ (star x) = star (φ x)) ↔ ∀ g, φ (of g) ∈ unitary A := by
  constructor
  · intro h g
    have hg := of_mem_unitary (α := α) (hα g)
    simp [Unitary.mem_iff, ← h, ← map_mul, -star_of, Unitary.star_mul_self_of_mem hg,
      Unitary.mul_star_self_of_mem hg]
  · intro h
    refine map_star_of_map_of_inv φ.toLinearMap fun g ↦ ?_
    -- Both sides are inverses of `φ (of g)`.
    have hg := of_mem_unitary (α := α) (hα g)
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← star_of]
    exact left_inv_eq_right_inv (a := φ (of g))
      (by rw [← map_mul, Unitary.star_mul_self_of_mem hg, map_one])
      (Unitary.mul_star_self_of_mem (h g))

end Adjoint

/-! ### The coefficient at the identity -/

section CoeffOne

variable [IsStarFactorSet α]

/-- **The Parseval identity**: when `α g⁻¹ g = 1` for every `g`, the coefficient of `x⋆ x` at the
identity is the sum of the products `star (x_g) x_g` of the coefficients of `x`. -/
theorem repr_star_mul_self_apply_one (hα : ∀ g, (α g⁻¹ g : k) = 1)
    (x : twistedMonoidAlgebra k G α) :
    (basis k G α).repr (star x * x) 1 =
      ((basis k G α).repr x).sum fun _ c ↦ star c * c := by
  classical
  conv_lhs => rw [← (basis k G α).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, star_sum, star_smul, basis_apply,
    star_of, Finset.sum_mul_sum, smul_mul_smul_comm, of_mul_of, smul_smul, map_sum, map_smul,
    repr_of, Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply,
    inv_mul_eq_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_congr rfl fun g hg ↦ by simp [hg, hα]

/-- Over a star-ordered ring, the coefficient of `x⋆ x` at the identity is nonnegative. -/
theorem repr_star_mul_self_apply_one_nonneg [PartialOrder k] [StarOrderedRing k]
    (hα : ∀ g, (α g⁻¹ g : k) = 1) (x : twistedMonoidAlgebra k G α) :
    0 ≤ (basis k G α).repr (star x * x) 1 := by
  rw [repr_star_mul_self_apply_one hα]
  exact Finset.sum_nonneg fun g _ ↦ star_mul_self_nonneg _

/-- **The coefficient at the identity is faithful**: over a star-ordered ring without zero
divisors, the coefficient of `x⋆ x` at the identity vanishes only for `x = 0`. -/
theorem repr_star_mul_self_apply_one_eq_zero_iff [PartialOrder k] [StarOrderedRing k]
    [NoZeroDivisors k] (hα : ∀ g, (α g⁻¹ g : k) = 1) (x : twistedMonoidAlgebra k G α) :
    (basis k G α).repr (star x * x) 1 = 0 ↔ x = 0 := by
  rw [repr_star_mul_self_apply_one hα, Finsupp.sum,
    Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦ star_mul_self_nonneg _]
  simpa [mul_eq_zero] using (basis k G α).forall_coord_eq_zero_iff

end CoeffOne

end TwistedMonoidAlgebra

end TauCeti
