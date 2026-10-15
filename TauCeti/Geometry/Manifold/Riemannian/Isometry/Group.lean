/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic

/-!
# The isometry group of a Riemannian manifold

The smooth Riemannian self-isometries of `M` form a group `Isom(M)` under composition. This file
defines `TauCeti.Isom I M` as `RiemannianIsometry I I M M` and equips it with that group structure,
using the convention of `Equiv.Perm` and of the self-diffeomorphism group: `Φ * Ψ = Ψ.trans Φ` acts
as `Φ ∘ Ψ`. Forgetting the metric condition is an injective group homomorphism to the
diffeomorphism group. The action of `Isom(M)` on `M` is in
`TauCeti.Geometry.Manifold.Riemannian.Isometry.Action`.

## Main definitions

* `TauCeti.Isom I M`: the isometry group of the Riemannian manifold `M`.
* `TauCeti.RiemannianIsometry.instGroup`: the group of Riemannian self-isometries.
* `TauCeti.RiemannianIsometry.toDiff`: the injective homomorphism to the diffeomorphism group.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2
  (isometries and homogeneous Riemannian manifolds).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487
  (model geometries as homogeneous spaces of their isometry groups).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- `Isom I M` is the isometry group `Isom(M)` of the Riemannian manifold `M` modelled on `I`: its
smooth Riemannian self-isometries under composition. -/
abbrev Isom (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] : Type _ :=
  RiemannianIsometry I I M M

namespace RiemannianIsometry

variable {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The identity isometry is the unit of the isometry group. -/
instance instOne : One (Isom I M) where one := RiemannianIsometry.refl I M

/-- Multiplication of isometries is composition: `Φ * Ψ` follows `Ψ` then `Φ`, so that it acts as
`Φ ∘ Ψ`, matching the `Equiv.Perm` convention. -/
instance instMul : Mul (Isom I M) where mul Φ Ψ := Ψ.trans Φ

/-- The inverse in the isometry group is the inverse isometry. -/
instance instInv : Inv (Isom I M) where inv Φ := Φ.symm

/-- The smooth Riemannian self-isometries of `M` form a group under composition, with
multiplication acting as function composition. -/
instance instGroup : Group (Isom I M) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

/-- The unit of the isometry group is the identity isometry. -/
theorem one_def : (1 : Isom I M) = RiemannianIsometry.refl I M := rfl

/-- Multiplication in the isometry group is `RiemannianIsometry.trans` in composition order. -/
theorem mul_def (Φ Ψ : Isom I M) : Φ * Ψ = Ψ.trans Φ := rfl

/-- Inversion in the isometry group is the inverse isometry. -/
theorem inv_def (Φ : Isom I M) : Φ⁻¹ = Φ.symm := rfl

/-- The unit isometry coerces to the identity function. -/
@[simp]
theorem coe_one : ⇑(1 : Isom I M) = id := funext (refl_apply I M)

/-- Multiplication of isometries coerces to function composition. -/
@[simp]
theorem coe_mul (Φ Ψ : Isom I M) : ⇑(Φ * Ψ) = Φ ∘ Ψ := funext (trans_apply Ψ Φ)

/-- The inverse in the isometry group coerces to the inverse isometry. -/
@[simp]
theorem coe_inv (Φ : Isom I M) : ⇑Φ⁻¹ = Φ.symm := rfl

/-- Multiplication of isometries applies the right factor, then the left. -/
@[simp]
theorem mul_apply (Φ Ψ : Isom I M) (x : M) : (Φ * Ψ) x = Φ (Ψ x) :=
  trans_apply Ψ Φ x

/-- The unit isometry fixes every point. -/
@[simp]
theorem one_apply (x : M) : (1 : Isom I M) x = x := refl_apply I M x

/-- The inverse in the isometry group acts as the inverse isometry. -/
@[simp]
theorem inv_apply (Φ : Isom I M) (x : M) : Φ⁻¹ x = Φ.symm x := rfl

/-- The underlying diffeomorphism of the unit isometry is the unit diffeomorphism. -/
@[simp]
theorem toDiffeomorph_one : (1 : Isom I M).toDiffeomorph = (1 : Diff I M ∞) :=
  Diffeomorph.ext one_apply

/-- The underlying diffeomorphism preserves multiplication of isometries. -/
@[simp]
theorem toDiffeomorph_mul (Φ Ψ : Isom I M) :
    (Φ * Ψ).toDiffeomorph = (Φ.toDiffeomorph * Ψ.toDiffeomorph : Diff I M ∞) :=
  Diffeomorph.ext (mul_apply Φ Ψ)

/-- The underlying diffeomorphism preserves inversion of isometries. -/
@[simp]
theorem toDiffeomorph_inv (Φ : Isom I M) :
    Φ⁻¹.toDiffeomorph = (Φ.toDiffeomorph⁻¹ : Diff I M ∞) :=
  symm_toDiffeomorph Φ

/-- The forgetful group homomorphism from the isometry group to the diffeomorphism group,
sending an isometry to its underlying smooth diffeomorphism. -/
def toDiff : Isom I M →* Diff I M ∞ where
  toFun Φ := Φ.toDiffeomorph
  map_one' := toDiffeomorph_one
  map_mul' := toDiffeomorph_mul

/-- The forgetful homomorphism to the diffeomorphism group forgets the metric condition. -/
@[simp]
theorem toDiff_apply (Φ : Isom I M) : toDiff Φ = Φ.toDiffeomorph := (rfl)

/-- The forgetful homomorphism to the diffeomorphism group is injective, so the isometry group is
a subgroup of the diffeomorphism group. -/
theorem toDiff_injective : Function.Injective (toDiff : Isom I M → Diff I M ∞) :=
  fun _ _ h ↦ RiemannianIsometry.ext fun x ↦ DFunLike.congr_fun h x

end RiemannianIsometry

end TauCeti

end
