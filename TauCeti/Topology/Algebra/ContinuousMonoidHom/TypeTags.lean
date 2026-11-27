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
public import TauCeti.Algebra.GroupAction.TypeTags

/-!
# Transport of continuous homomorphisms and subgroups between additive and multiplicative type tags

Mathlib's `AddMonoidHom.toMultiplicative` and `MonoidHom.toAdditive` identify homomorphisms
between additive and multiplicative monoids with homomorphisms between their `Multiplicative` and
`Additive` type tags. Since `Multiplicative` and `Additive` inherit the topology of the underlying
type, continuity is preserved in both directions. This file packages the resulting equivalences
for `ContinuousAddMonoidHom` and `ContinuousMonoidHom`, records their compatibility with identity,
composition, surjectivity, and dense range, and upgrades Mathlib's subgroup correspondence
`AddSubgroup.toSubgroup` to a topological isomorphism on the carrier subtypes carrying the subspace
topology.

## Main definitions

* `ContinuousAddMonoidHom.toMultiplicative`: the equivalence
  `(M →ₜ+ N) ≃ (Multiplicative M →ₜ* Multiplicative N)` upgrading `AddMonoidHom.toMultiplicative`.
* `ContinuousMonoidHom.toAdditive`: the equivalence
  `(M →ₜ* N) ≃ (Additive M →ₜ+ Additive N)` upgrading `MonoidHom.toAdditive`.
* `AddSubgroup.toSubgroupContinuousMulEquiv`: the topological isomorphism
  `Multiplicative H ≃ₜ* H.toSubgroup` for `H : AddSubgroup A`.
-/

public section

open Additive (ofMul toMul)
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

/-- A continuous additive homomorphism compatible with a map of acting monoids `ψ` stays
compatible with `ψ` on the multiplicative type tags. This is
`AddMonoidHom.toMultiplicative_map_smul` for `f.toMultiplicative`. -/
theorem toMultiplicative_map_smul {G H : Type*} [Monoid G] [Monoid H] [DistribMulAction G M]
    [DistribMulAction H N] (f : M →ₜ+ N) (ψ : H → G) (h : ∀ (g : H) (m : M), f (ψ g • m) = g • f m)
    (g : H) (x : Multiplicative M) : f.toMultiplicative (ψ g • x) = g • f.toMultiplicative x :=
  f.toAddMonoidHom.toMultiplicative_map_smul ψ h g x

end ContinuousAddMonoidHom

namespace ContinuousMonoidHom

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- Reinterpret continuous multiplicative homomorphisms `M →ₜ* N` as continuous additive
homomorphisms `Additive M →ₜ+ Additive N`. This is `MonoidHom.toAdditive` upgraded to
`ContinuousMonoidHom`. -/
def toAdditive : (M →ₜ* N) ≃ (Additive M →ₜ+ Additive N) where
  toFun f :=
    { toAddMonoidHom := f.toMonoidHom.toAdditive
      continuous_toFun := continuous_ofMul.comp (f.continuous.comp continuous_toMul) }
  invFun f :=
    { toMonoidHom := MonoidHom.toAdditive.symm f.toAddMonoidHom
      continuous_toFun := continuous_toMul.comp (f.continuous.comp continuous_ofMul) }
  left_inv _ := ext fun _ => rfl
  right_inv _ := ContinuousAddMonoidHom.ext fun _ => rfl

/-- Evaluating `f.toAdditive` conjugates `f` by `toMul` and `ofMul`. -/
@[simp]
theorem toAdditive_apply_apply (f : M →ₜ* N) (x : Additive M) :
    f.toAdditive x = ofMul (f x.toMul) :=
  (rfl)

/-- Evaluating `toAdditive.symm` conjugates by `ofMul` and `toMul`. -/
@[simp]
theorem toAdditive_symm_apply_apply (f : Additive M →ₜ+ Additive N) (x : M) :
    toAdditive.symm f x = (f (ofMul x)).toMul :=
  (rfl)

/-- Forgetting continuity commutes with `toAdditive`. -/
@[simp]
theorem toAddMonoidHom_toAdditive (f : M →ₜ* N) :
    (f.toAdditive : Additive M →+ Additive N) = f.toMonoidHom.toAdditive :=
  (rfl)

/-- `toAdditive` maps the identity continuous multiplicative homomorphism to the identity. -/
@[simp]
theorem toAdditive_id :
    (ContinuousMonoidHom.id M).toAdditive = ContinuousAddMonoidHom.id (Additive M) :=
  ContinuousAddMonoidHom.ext fun x => by simp

/-- `toAdditive` commutes with composition of continuous multiplicative homomorphisms. -/
@[simp]
theorem toAdditive_comp (g : N →ₜ* P) (f : M →ₜ* N) :
    (g.comp f).toAdditive = g.toAdditive.comp f.toAdditive :=
  ContinuousAddMonoidHom.ext fun x => by simp

/-- `f.toAdditive` is surjective if and only if `f` is surjective. -/
@[simp]
theorem surjective_toAdditive_iff (f : M →ₜ* N) :
    Function.Surjective f.toAdditive ↔ Function.Surjective f := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · obtain ⟨x, hx⟩ := h (ofMul y)
    exact ⟨x.toMul, ofMul.injective hx⟩
  · obtain ⟨x, rfl⟩ := h y.toMul
    exact ⟨ofMul x, rfl⟩

/-- `f.toAdditive` has dense range if and only if `f` has dense range. -/
@[simp]
theorem denseRange_toAdditive_iff (f : M →ₜ* N) :
    DenseRange f.toAdditive ↔ DenseRange f :=
  ⟨fun h =>
      (toMul.surjective.denseRange.comp
        (h.comp ofMul.surjective.denseRange f.toAdditive.continuous) continuous_toMul),
    fun h =>
      (ofMul.surjective.denseRange.comp
        (h.comp toMul.surjective.denseRange f.continuous) continuous_ofMul)⟩

end ContinuousMonoidHom

namespace AddSubgroup

/-- The multiplicative type tag of an additive subgroup `H : AddSubgroup A`, carrying the subspace
topology, is topologically isomorphic to the corresponding subgroup `H.toSubgroup` of
`Multiplicative A`. -/
def toSubgroupContinuousMulEquiv {A : Type*} [AddGroup A] [TopologicalSpace A]
    (H : AddSubgroup A) : Multiplicative H ≃ₜ* H.toSubgroup where
  toFun x := ⟨ofAdd (x.toAdd : A), x.toAdd.property⟩
  invFun y := ofAdd ⟨y.val.toAdd, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_ofAdd.comp (continuous_subtypeVal.comp continuous_toAdd)).subtype_mk _
  continuous_invFun :=
    continuous_ofAdd.comp ((continuous_toAdd.comp continuous_subtypeVal).subtype_mk _)

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
