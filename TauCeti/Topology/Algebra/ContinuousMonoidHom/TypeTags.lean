/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions

/-!
# Transport of continuous additive homomorphisms and subgroups to `Multiplicative`

Mathlib's `AddMonoidHom.toMultiplicative` identifies homomorphisms between additive monoids with
homomorphisms between their `Multiplicative` type tags. Since `Multiplicative` inherits the
topology of its underlying type, continuity is preserved in both directions. This file packages the
resulting equivalence for `ContinuousAddMonoidHom`, records its compatibility with identity,
composition, surjectivity, and dense range, and upgrades Mathlib's subgroup correspondence
`AddSubgroup.toSubgroup` to a topological isomorphism on the carrier subtypes carrying the subspace
topology.

## Main definitions

* `ContinuousAddMonoidHom.toMultiplicative`: the equivalence
  `(M →ₜ+ N) ≃ (Multiplicative M →ₜ* Multiplicative N)` upgrading `AddMonoidHom.toMultiplicative`.
* `AddSubgroup.toSubgroupContinuousMulEquiv`: the topological isomorphism
  `Multiplicative H ≃ₜ* H.toSubgroup` for `H : AddSubgroup A`.
-/

public section

open Multiplicative (ofAdd toAdd)

namespace ContinuousAddMonoidHom

variable {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- Reinterpret continuous additive homomorphisms `M →ₜ+ N` as continuous multiplicative
homomorphisms `Multiplicative M →ₜ* Multiplicative N`. This is `AddMonoidHom.toMultiplicative`
upgraded to `ContinuousAddMonoidHom`. -/
def toMultiplicative : (M →ₜ+ N) ≃ (Multiplicative M →ₜ* Multiplicative N) where
  toFun f :=
    { toMonoidHom := f.toAddMonoidHom.toMultiplicative
      continuous_toFun := continuous_ofAdd.comp (f.continuous.comp continuous_toAdd) }
  invFun f :=
    { toAddMonoidHom := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
      continuous_toFun := continuous_toAdd.comp (f.continuous.comp continuous_ofAdd) }
  left_inv _ := ext fun _ => rfl
  right_inv _ := ContinuousMonoidHom.ext fun _ => rfl

/-- Evaluating `f.toMultiplicative` conjugates `f` by `toAdd` and `ofAdd`. -/
@[simp]
theorem toMultiplicative_apply_apply (f : M →ₜ+ N) (x : Multiplicative M) :
    f.toMultiplicative x = ofAdd (f x.toAdd) :=
  (rfl)

/-- Evaluating `toMultiplicative.symm` conjugates by `ofAdd` and `toAdd`. -/
@[simp]
theorem toMultiplicative_symm_apply_apply (f : Multiplicative M →ₜ* Multiplicative N) (x : M) :
    toMultiplicative.symm f x = (f (ofAdd x)).toAdd :=
  (rfl)

/-- Forgetting continuity commutes with `toMultiplicative`. -/
@[simp]
theorem toMonoidHom_toMultiplicative (f : M →ₜ+ N) :
    (f.toMultiplicative : Multiplicative M →* Multiplicative N) =
      f.toAddMonoidHom.toMultiplicative :=
  (rfl)

/-- `toMultiplicative` maps the identity continuous additive homomorphism to the identity. -/
@[simp]
theorem toMultiplicative_id :
    (ContinuousAddMonoidHom.id M).toMultiplicative = ContinuousMonoidHom.id (Multiplicative M) :=
  (rfl)

/-- `toMultiplicative` commutes with composition of continuous additive homomorphisms. -/
@[simp]
theorem toMultiplicative_comp (g : N →ₜ+ P) (f : M →ₜ+ N) :
    (g.comp f).toMultiplicative = g.toMultiplicative.comp f.toMultiplicative :=
  (rfl)

/-- `f.toMultiplicative` is surjective if and only if `f` is surjective. -/
@[simp]
theorem surjective_toMultiplicative_iff (f : M →ₜ+ N) :
    Function.Surjective f.toMultiplicative ↔ Function.Surjective f := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · obtain ⟨x, hx⟩ := h (ofAdd y)
    exact ⟨x.toAdd, ofAdd.injective hx⟩
  · obtain ⟨x, rfl⟩ := h y.toAdd
    exact ⟨ofAdd x, rfl⟩

/-- `f.toMultiplicative` has dense range if and only if `f` has dense range. -/
@[simp]
theorem denseRange_toMultiplicative_iff (f : M →ₜ+ N) :
    DenseRange f.toMultiplicative ↔ DenseRange f :=
  ⟨fun h =>
      (toAdd.surjective.denseRange.comp
        (h.comp ofAdd.surjective.denseRange f.toMultiplicative.continuous) continuous_toAdd),
    fun h =>
      (ofAdd.surjective.denseRange.comp
        (h.comp toAdd.surjective.denseRange f.continuous) continuous_ofAdd)⟩

end ContinuousAddMonoidHom

namespace AddSubgroup

/-- The multiplicative type tag of an additive subgroup `H : AddSubgroup A`, carrying the subspace
topology, is topologically isomorphic to the corresponding subgroup `H.toSubgroup` of
`Multiplicative A`. -/
def toSubgroupContinuousMulEquiv {A : Type*} [AddGroup A] [TopologicalSpace A]
    (H : AddSubgroup A) : Multiplicative H ≃ₜ* H.toSubgroup where
  toFun x := ⟨ofAdd (x.toAdd : A), x.toAdd.2⟩
  invFun y := ofAdd ⟨y.1.toAdd, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_ofAdd.comp (continuous_subtype_val.comp continuous_toAdd)).subtype_mk _
  continuous_invFun :=
    continuous_ofAdd.comp ((continuous_toAdd.comp continuous_subtype_val).subtype_mk _)

/-- Forward evaluation of `AddSubgroup.toSubgroupContinuousMulEquiv` in the ambient group. -/
@[simp]
theorem coe_toSubgroupContinuousMulEquiv_apply {A : Type*} [AddGroup A] [TopologicalSpace A]
    (H : AddSubgroup A) (x : Multiplicative H) :
    (H.toSubgroupContinuousMulEquiv x : Multiplicative A) = ofAdd (x.toAdd : A) :=
  (rfl)

/-- Inverse evaluation of `AddSubgroup.toSubgroupContinuousMulEquiv` in the ambient group. -/
@[simp]
theorem toAdd_toSubgroupContinuousMulEquiv_symm_apply {A : Type*} [AddGroup A]
    [TopologicalSpace A] (H : AddSubgroup A) (y : H.toSubgroup) :
    ((H.toSubgroupContinuousMulEquiv.symm y).toAdd : A) = (y : Multiplicative A).toAdd :=
  (rfl)

end AddSubgroup
