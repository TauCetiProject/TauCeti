/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Equivalences of positive linear maps

An order-preserving linear equivalence `e : U ≃ₗ[R] V` induces a bijection between positive linear
maps out of `U` and positive linear maps out of `V`, by precomposition with `e.symm` and `e`. When
`e` is an algebra equivalence `U ≃ₐ[R] V`, this bijection preserves the value at `1`, so it
restricts to a bijection between normalized positive linear maps `{m : U →ₚ[R] W // m 1 = w}`
and `{m : V →ₚ[R] W // m 1 = w}`.

## Main definitions

* `PositiveLinearMap.equivOfLinearEquiv`: transport of positive linear maps along an
  order-preserving linear equivalence.
* `PositiveLinearMap.normalizedEquivOfAlgEquiv`: transport of positive linear maps taking a fixed
  value `w` at `1` along an order-preserving algebra equivalence.
-/

public section

namespace PositiveLinearMap

section LinearEquiv

variable {R U V W : Type*} [Semiring R]
  [AddCommMonoid U] [PartialOrder U] [Module R U]
  [AddCommMonoid V] [PartialOrder V] [Module R V]
  [AddCommMonoid W] [PartialOrder W] [Module R W]

/-- Transport of positive linear maps along an order-preserving linear equivalence. -/
def equivOfLinearEquiv (e : U ≃ₗ[R] V) (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) :
    (U →ₚ[R] W) ≃ (V →ₚ[R] W) where
  toFun m :=
    { toLinearMap := m.toLinearMap ∘ₗ e.symm.toLinearMap
      monotone' := fun _ _ h => OrderHomClass.mono m (hle.2 h) }
  invFun m :=
    { toLinearMap := m.toLinearMap ∘ₗ e.toLinearMap
      monotone' := fun _ _ h => OrderHomClass.mono m <| hle.1 <| by
        simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h }
  left_inv m := toLinearMap_injective <| LinearMap.ext fun f =>
    congrArg m (e.symm_apply_apply f)
  right_inv m := toLinearMap_injective <| LinearMap.ext fun f =>
    congrArg m (e.apply_symm_apply f)

@[simp]
theorem equivOfLinearEquiv_apply (e : U ≃ₗ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) (m : U →ₚ[R] W) (f : V) :
    equivOfLinearEquiv e hle m f = m (e.symm f) :=
  (rfl)

@[simp]
theorem equivOfLinearEquiv_symm_apply (e : U ≃ₗ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) (m : V →ₚ[R] W) (f : U) :
    (equivOfLinearEquiv e hle).symm m f = m (e f) :=
  (rfl)

end LinearEquiv

section AlgEquiv

variable {R U V W : Type*} [CommSemiring R]
  [Semiring U] [PartialOrder U] [Algebra R U]
  [Semiring V] [PartialOrder V] [Algebra R V]
  [AddCommMonoid W] [PartialOrder W] [Module R W]

/-- Transport of positive linear maps taking a prescribed value `w` at `1` along an
order-preserving algebra equivalence. -/
def normalizedEquivOfAlgEquiv (e : U ≃ₐ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) {w : W} :
    {m : U →ₚ[R] W // m 1 = w} ≃ {m : V →ₚ[R] W // m 1 = w} where
  toFun m := ⟨equivOfLinearEquiv e.toLinearEquiv hle m.val,
    (congrArg m.val e.symm.map_one).trans m.property⟩
  invFun m := ⟨(equivOfLinearEquiv e.toLinearEquiv hle).symm m.val,
    (congrArg m.val e.map_one).trans m.property⟩
  left_inv m := Subtype.ext ((equivOfLinearEquiv e.toLinearEquiv hle).left_inv m.val)
  right_inv m := Subtype.ext ((equivOfLinearEquiv e.toLinearEquiv hle).right_inv m.val)

@[simp]
theorem normalizedEquivOfAlgEquiv_apply (e : U ≃ₐ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) {w : W}
    (m : {m : U →ₚ[R] W // m 1 = w}) (f : V) :
    (normalizedEquivOfAlgEquiv e hle m).val f = m.val (e.symm f) :=
  (rfl)

@[simp]
theorem normalizedEquivOfAlgEquiv_symm_apply (e : U ≃ₐ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) {w : W}
    (m : {m : V →ₚ[R] W // m 1 = w}) (f : U) :
    ((normalizedEquivOfAlgEquiv e hle).symm m).val f = m.val (e f) :=
  (rfl)

end AlgEquiv

end PositiveLinearMap
