/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuous homomorphisms out of a product

Mathlib defines `ContinuousMonoidHom.coprod`, `ContinuousMonoidHom.inl`, and
`ContinuousMonoidHom.inr`, mirroring the monoid-homomorphism API in `Mathlib.Algebra.Group.Prod`,
but does not state the restriction, uniqueness, and composition laws for `coprod` or package the
universal property as a multiplicative equivalence. This file supplies those lemmas and the
isomorphism `(A →ₜ* E) × (B →ₜ* E) ≃* ((A × B) →ₜ* E)` (with additive counterparts).

## Main definitions

* `ContinuousMonoidHom.coprodEquiv`, `ContinuousAddMonoidHom.coprodEquiv`: the universal
  property of `coprod` as a multiplicative (resp. additive) equivalence.

## Main results

* `ContinuousMonoidHom.coprod_comp_inl`, `ContinuousMonoidHom.coprod_comp_inr`: restricting
  `f.coprod g` to either factor recovers `f` and `g`.
* `ContinuousMonoidHom.coprod_unique`: a continuous homomorphism out of `A × B` is uniquely
  reconstructed from its restrictions along `inl` and `inr`.
* `ContinuousMonoidHom.comp_coprod`: postcomposition distributes over `coprod`.
-/

public section

namespace ContinuousMonoidHom

section CommMonoid

variable {A B E F : Type*} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
  [CommMonoid E] [TopologicalSpace E] [ContinuousMul E]
  [CommMonoid F] [TopologicalSpace F] [ContinuousMul F]

/-- Restricting `f.coprod g` to the first factor recovers `f`. -/
@[to_additive (attr := simp) /-- Restricting `f.coprod g` to the first factor recovers `f`. -/]
theorem coprod_comp_inl (f : A →ₜ* E) (g : B →ₜ* E) : (f.coprod g).comp (inl A B) = f :=
  ext fun x ↦ by simp

/-- Restricting `f.coprod g` to the second factor recovers `g`. -/
@[to_additive (attr := simp) /-- Restricting `f.coprod g` to the second factor recovers `g`. -/]
theorem coprod_comp_inr (f : A →ₜ* E) (g : B →ₜ* E) : (f.coprod g).comp (inr A B) = g :=
  ext fun y ↦ by simp

/-- A continuous homomorphism out of a product `A × B` is recovered from its restrictions to the
two factors. -/
@[to_additive (attr := simp) /-- A continuous additive homomorphism out of a product `A × B` is
recovered from its restrictions to the two factors. -/]
theorem coprod_unique (h : (A × B) →ₜ* E) : (h.comp (inl A B)).coprod (h.comp (inr A B)) = h :=
  ext fun x ↦ by simp [← map_mul]

/-- The coproduct of the two canonical inclusions is the identity on `A × B`. -/
@[to_additive (attr := simp) /-- The coproduct of the two canonical inclusions is the identity on
`A × B`. -/]
theorem coprod_inl_inr {C D : Type*} [CommMonoid C] [CommMonoid D] [TopologicalSpace C]
    [TopologicalSpace D] [ContinuousMul C] [ContinuousMul D] :
    (inl C D).coprod (inr C D) = id (C × D) :=
  coprod_unique (id (C × D))

/-- Postcomposing a coproduct with a continuous homomorphism distributes over the factors. -/
@[to_additive /-- Postcomposing an additive coproduct with a continuous additive homomorphism
distributes over the factors. -/]
theorem comp_coprod (k : E →ₜ* F) (f : A →ₜ* E) (g : B →ₜ* E) :
    k.comp (f.coprod g) = (k.comp f).coprod (k.comp g) :=
  ext fun x ↦ by simp

/-- **Universal property of the product for continuous homomorphisms.** A continuous homomorphism
out of `A × B` into a commutative topological monoid `E` is equivalent to a pair of continuous
homomorphisms out of `A` and `B`. -/
@[to_additive /-- **Universal property of the product for continuous additive homomorphisms.** A
continuous additive homomorphism out of `A × B` into a commutative topological additive monoid `E`
is equivalent to a pair of continuous additive homomorphisms out of `A` and `B`. -/]
def coprodEquiv : (A →ₜ* E) × (B →ₜ* E) ≃* ((A × B) →ₜ* E) where
  toFun fg := fg.1.coprod fg.2
  invFun h := (h.comp (inl A B), h.comp (inr A B))
  left_inv fg := Prod.ext (coprod_comp_inl fg.1 fg.2) (coprod_comp_inr fg.1 fg.2)
  right_inv h := coprod_unique h
  map_mul' fg₁ fg₂ := ext fun x ↦ by simp [mul_mul_mul_comm]

@[to_additive (attr := simp)]
theorem coprodEquiv_apply (fg : (A →ₜ* E) × (B →ₜ* E)) :
    coprodEquiv fg = fg.1.coprod fg.2 :=
  (rfl)

@[to_additive (attr := simp)]
theorem coprodEquiv_symm_apply (h : (A × B) →ₜ* E) :
    coprodEquiv.symm h = (h.comp (inl A B), h.comp (inr A B)) :=
  (rfl)

end CommMonoid

end ContinuousMonoidHom
