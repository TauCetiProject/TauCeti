/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected

/-!
# The monoid of path components of a topological monoid

For a topological monoid `M`, the path components `ZerothHomotopy M` form a monoid: if `γ` joins
`a` to `a'` and `δ` joins `b` to `b'`, then `t ↦ γ t * δ t` joins `a * b` to `a' * b'` (Mathlib's
`Joined.mul`), so multiplication descends to path components. For a group with continuous
multiplication the path components form a group: if `γ` joins `a` to `b`, then
`t ↦ a⁻¹ * γ t * b⁻¹` joins `b⁻¹` to `a⁻¹`, so no continuity of inversion is needed. The quotient
map `ZerothHomotopy.mk` is then a monoid homomorphism `ZerothHomotopy.mkMonoidHom`.

The monoid structure is needed for topological monoids which are not groups, such as the
Fredholm operators on a Banach space under composition, whose path components form a group only
a posteriori. For a topological group `G` the same group is Mathlib's quotient
`G ⧸ Subgroup.pathComponentOne G`, by `QuotientGroup.mk_eq_mk_iff_joined_pathComponentOne`.

## Main definitions

* `ZerothHomotopy.instMonoid`, `ZerothHomotopy.instCommMonoid`, `ZerothHomotopy.instGroup`,
  `ZerothHomotopy.instCommGroup`: the monoid and group structures on path components, with additive
  versions.
* `ZerothHomotopy.mkMonoidHom`: the quotient map as a monoid homomorphism.
-/

public section

namespace ZerothHomotopy

variable {M : Type*} [TopologicalSpace M]

section Mul

variable [Mul M] [ContinuousMul M]

/-- Multiplication of path components of a topological magma, pointwise multiplication of paths
joining the representatives. -/
@[to_additive /-- Addition of path components of a topological additive magma, pointwise addition
of paths joining the representatives. -/]
instance instMul : Mul (ZerothHomotopy M) where
  mul := Quotient.map₂ (· * ·) fun _ _ ha _ _ hb => Joined.mul ha hb

@[to_additive (attr := simp)]
theorem mk_mul (a b : M) : mk (a * b) = mk a * mk b :=
  (rfl)

end Mul

/-- The path component of `1`. -/
@[to_additive /-- The path component of `0`. -/]
instance instOne [One M] : One (ZerothHomotopy M) where
  one := mk 1

@[to_additive (attr := simp)]
theorem mk_one [One M] : mk (1 : M) = 1 :=
  (rfl)

/-- The path components of a topological monoid form a monoid. -/
@[to_additive /-- The path components of a topological additive monoid form an additive
monoid. -/]
instance instMonoid [Monoid M] [ContinuousMul M] : Monoid (ZerothHomotopy M) where
  mul_assoc x y z := by
    induction x; induction y; induction z
    simp only [← mk_mul, mul_assoc]
  one_mul x := by
    induction x
    rw [← mk_one, ← mk_mul, one_mul]
  mul_one x := by
    induction x
    rw [← mk_one, ← mk_mul, mul_one]

@[to_additive (attr := simp)]
theorem mk_pow [Monoid M] [ContinuousMul M] (a : M) (n : ℕ) : mk (a ^ n) = mk a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mk_mul, ih, pow_succ]

/-- The path components of a commutative topological monoid form a commutative monoid. -/
@[to_additive /-- The path components of a commutative topological additive monoid form a
commutative additive monoid. -/]
instance instCommMonoid [CommMonoid M] [ContinuousMul M] : CommMonoid (ZerothHomotopy M) where
  mul_comm x y := by
    induction x; induction y
    rw [← mk_mul, ← mk_mul, mul_comm]

variable (M) in
/-- The quotient map from a topological monoid to its path components, as a monoid
homomorphism. -/
@[to_additive /-- The quotient map from a topological additive monoid to its path components, as
an additive monoid homomorphism. -/]
def mkMonoidHom [Monoid M] [ContinuousMul M] : M →* ZerothHomotopy M where
  toFun := mk
  map_one' := mk_one
  map_mul' := mk_mul

@[to_additive (attr := simp)]
theorem mkMonoidHom_apply [Monoid M] [ContinuousMul M] (a : M) : mkMonoidHom M a = mk a :=
  (rfl)

section Group

variable [Group M] [ContinuousMul M]

/-- Inversion of path components of a topological group, pointwise inversion of the
representatives. Continuity of multiplication suffices: if `γ` joins `a` to `b`, then
`t ↦ a⁻¹ * γ t * b⁻¹` joins `b⁻¹` to `a⁻¹`. -/
@[to_additive /-- Negation of path components of a topological additive group, pointwise negation
of the representatives. Continuity of addition suffices: if `γ` joins `a` to `b`, then
`t ↦ -a + γ t + -b` joins `-b` to `-a`. -/]
instance instInv : Inv (ZerothHomotopy M) where
  inv := Quotient.map (·⁻¹) fun a b (h : Joined a b) => by
    have h' : Joined (a⁻¹ * a * b⁻¹) (a⁻¹ * b * b⁻¹) :=
      ((Joined.refl a⁻¹).mul h).mul (Joined.refl b⁻¹)
    rw [inv_mul_cancel, one_mul, mul_inv_cancel_right] at h'
    exact h'.symm

@[to_additive (attr := simp)]
theorem mk_inv (a : M) : mk a⁻¹ = (mk a)⁻¹ :=
  (rfl)

/-- The path components of a topological group form a group. -/
@[to_additive /-- The path components of a topological additive group form an additive group. -/]
instance instGroup : Group (ZerothHomotopy M) where
  inv_mul_cancel x := by
    induction x
    rw [← mk_inv, ← mk_mul, inv_mul_cancel, mk_one]

@[to_additive (attr := simp)]
theorem mk_div (a b : M) : mk (a / b) = mk a / mk b :=
  map_div (mkMonoidHom M) a b

@[to_additive (attr := simp)]
theorem mk_zpow (a : M) (n : ℤ) : mk (a ^ n) = mk a ^ n :=
  map_zpow (mkMonoidHom M) a n

end Group

/-- The path components of a commutative topological group form a commutative group. -/
@[to_additive /-- The path components of a commutative topological additive group form a
commutative additive group. -/]
instance instCommGroup [CommGroup M] [ContinuousMul M] : CommGroup (ZerothHomotopy M) where
  __ := instGroup
  __ := instCommMonoid

end ZerothHomotopy
