/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Coercion, equivalences, and faithfulness kernels of positive linear maps

Mathlib's `PositiveLinearMap.ofClass` reinterprets an element of a type of positive linear maps as
a bundled positive linear map, but has no lemma computing its coercion to a function. This file
supplies the simp lemma `PositiveLinearMap.coe_ofClass`, matching `LinearMap.coe_ofClass` and
`PositiveContinuousLinearMap.coe_ofClass`.

An order-preserving linear equivalence `e : U ≃ₗ[R] V` induces a bijection between positive linear
maps out of `U` and positive linear maps out of `V`, by precomposition with `e.symm` and `e`. When
`e` is an algebra equivalence `U ≃ₐ[R] V`, this bijection preserves the value at `1`, so it
restricts to a bijection between normalized positive linear maps `{m : U →ₚ[R] W // m 1 = w}`
and `{m : V →ₚ[R] W // m 1 = w}`.

A faithful positive linear map on a proper star-ordered ring vanishes on `star a * a` only when
`a = 0` (`PositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self`).

## Main declarations

* `PositiveLinearMap.coe_ofClass`: coercion of `PositiveLinearMap.ofClass f` as a function.
* `LinearEquiv.positiveLinearMapCongrLeft`: transport of positive linear maps along an
  order-preserving linear equivalence.
* `AlgEquiv.normalizedPositiveLinearMapCongrLeft`: transport of positive linear maps taking a
  fixed value `w` at `1` along an order-preserving algebra equivalence.
* `PositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self`: a faithful positive linear map on
  a proper star-ordered ring has trivial quadratic kernel on `star a * a`.
-/

public section

namespace PositiveLinearMap

section OfClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/-- The positive linear map `PositiveLinearMap.ofClass f` has the same underlying function as
`f`. -/
@[simp]
theorem coe_ofClass (f : F) : ⇑(ofClass f : E₁ →ₚ[R] E₂) = f :=
  rfl

end OfClass

/-- A faithful positive linear map on a proper star-ordered ring vanishes on `star a * a` only
when `a = 0`. -/
theorem eq_zero_of_faithful_apply_star_mul_self {A 𝕜 E : Type*} [NonUnitalSemiring A]
    [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    [Semiring 𝕜] [AddCommMonoid E] [PartialOrder E] [Module 𝕜 A] [Module 𝕜 E]
    (f : A →ₚ[𝕜] E) (hf : ∀ a : A, 0 ≤ a → a ≠ 0 → 0 < f a) {a : A}
    (ha : f (star a * a) = 0) : a = 0 := by
  by_contra ha0
  exact (hf _ (star_mul_self_nonneg a) (star_mul_self_eq_zero.not.2 ha0)).ne' ha

end PositiveLinearMap

namespace LinearEquiv

variable {R U V W : Type*} [Semiring R]
  [AddCommMonoid U] [PartialOrder U] [Module R U]
  [AddCommMonoid V] [PartialOrder V] [Module R V]
  [AddCommMonoid W] [PartialOrder W] [Module R W]

/-- Transport of positive linear maps along an order-preserving linear equivalence. -/
def positiveLinearMapCongrLeft (e : U ≃ₗ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) :
    (U →ₚ[R] W) ≃ (V →ₚ[R] W) where
  toFun m :=
    { toLinearMap := m.toLinearMap ∘ₗ e.symm.toLinearMap
      monotone' := fun _ _ h => OrderHomClass.mono m (hle.2 h) }
  invFun m :=
    { toLinearMap := m.toLinearMap ∘ₗ e.toLinearMap
      monotone' := fun _ _ h => OrderHomClass.mono m <| hle.1 <| by
        simpa only [coe_coe, symm_apply_apply] using h }
  left_inv m := PositiveLinearMap.toLinearMap_injective <| LinearMap.ext fun f =>
    congrArg m (e.symm_apply_apply f)
  right_inv m := PositiveLinearMap.toLinearMap_injective <| LinearMap.ext fun f =>
    congrArg m (e.apply_symm_apply f)

@[simp]
theorem positiveLinearMapCongrLeft_apply (e : U ≃ₗ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) (m : U →ₚ[R] W) (f : V) :
    e.positiveLinearMapCongrLeft hle m f = m (e.symm f) :=
  (rfl)

@[simp]
theorem positiveLinearMapCongrLeft_symm_apply (e : U ≃ₗ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) (m : V →ₚ[R] W) (f : U) :
    (e.positiveLinearMapCongrLeft hle).symm m f = m (e f) :=
  (rfl)

end LinearEquiv

namespace AlgEquiv

variable {R U V W : Type*} [CommSemiring R]
  [Semiring U] [PartialOrder U] [Algebra R U]
  [Semiring V] [PartialOrder V] [Algebra R V]
  [AddCommMonoid W] [PartialOrder W] [Module R W]

/-- Transport of positive linear maps taking a prescribed value `w` at `1` along an
order-preserving algebra equivalence. -/
def normalizedPositiveLinearMapCongrLeft (e : U ≃ₐ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) {w : W} :
    {m : U →ₚ[R] W // m 1 = w} ≃ {m : V →ₚ[R] W // m 1 = w} :=
  let hle' : ∀ {f g : V}, e.toLinearEquiv.symm f ≤ e.toLinearEquiv.symm g ↔ f ≤ g :=
    fun {f g} => by
      simpa only [← AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply] using hle
  (e.toLinearEquiv.positiveLinearMapCongrLeft hle').subtypeEquiv fun m => by
    simp

@[simp]
theorem normalizedPositiveLinearMapCongrLeft_apply (e : U ≃ₐ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) {w : W}
    (m : {m : U →ₚ[R] W // m 1 = w}) (f : V) :
    (e.normalizedPositiveLinearMapCongrLeft hle m).val f = m.val (e.symm f) :=
  (rfl)

@[simp]
theorem normalizedPositiveLinearMapCongrLeft_symm_apply (e : U ≃ₐ[R] V)
    (hle : ∀ {f g : V}, e.symm f ≤ e.symm g ↔ f ≤ g) {w : W}
    (m : {m : V →ₚ[R] W // m 1 = w}) (f : U) :
    ((e.normalizedPositiveLinearMapCongrLeft hle).symm m).val f = m.val (e f) :=
  (rfl)

end AlgEquiv
