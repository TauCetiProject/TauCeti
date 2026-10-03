/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic

/-!
# The isometry group of a Riemannian manifold

The smooth Riemannian self-isometries of `M` form a group `Isom(M)` under composition. This file
equips `RiemannianIsometry I I M M` with that group structure, using the convention of
`Equiv.Perm` and of the self-diffeomorphism group: `Φ * Ψ = Ψ.trans Φ` acts as `Φ ∘ Ψ`. The group
acts faithfully on `M` by evaluation, and forgetting the metric condition is an injective group
homomorphism to the diffeomorphism group.

A Riemannian manifold is *homogeneous* when its isometry group acts transitively, which is
`MulAction.IsPretransitive (RiemannianIsometry I I M M) M` for the action recorded here. The model
spaces of Thurston's eight three-dimensional geometries are homogeneous in this sense, and the
model geometry is the pair `(X, Isom(X))`.

## Main definitions

* `TauCeti.RiemannianIsometry.instGroup`: the group of Riemannian self-isometries.
* `TauCeti.RiemannianIsometry.applyMulAction`: its action on `M` by evaluation, which is faithful.
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

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The identity isometry is the unit of the isometry group. -/
instance instOne : One (RiemannianIsometry I I M M) where one := RiemannianIsometry.refl I M

/-- Multiplication of isometries is composition: `Φ * Ψ` follows `Ψ` then `Φ`, so that it acts as
`Φ ∘ Ψ`, matching the `Equiv.Perm` convention. -/
instance instMul : Mul (RiemannianIsometry I I M M) where mul Φ Ψ := Ψ.trans Φ

/-- The inverse in the isometry group is the inverse isometry. -/
instance instInv : Inv (RiemannianIsometry I I M M) where inv Φ := Φ.symm

/-- The smooth Riemannian self-isometries of `M` form a group under composition, with
multiplication acting as function composition. -/
instance instGroup : Group (RiemannianIsometry I I M M) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

/-- The unit of the isometry group is the identity isometry. -/
theorem one_def : (1 : RiemannianIsometry I I M M) = RiemannianIsometry.refl I M := rfl

/-- Multiplication in the isometry group is `RiemannianIsometry.trans` in composition order. -/
theorem mul_def (Φ Ψ : RiemannianIsometry I I M M) : Φ * Ψ = Ψ.trans Φ := rfl

/-- Inversion in the isometry group is the inverse isometry. -/
theorem inv_def (Φ : RiemannianIsometry I I M M) : Φ⁻¹ = Φ.symm := rfl

/-- The unit isometry coerces to the identity function. -/
@[simp]
theorem coe_one : ⇑(1 : RiemannianIsometry I I M M) = id := funext (refl_apply I M)

/-- Multiplication of isometries coerces to function composition. -/
@[simp]
theorem coe_mul (Φ Ψ : RiemannianIsometry I I M M) : ⇑(Φ * Ψ) = Φ ∘ Ψ := funext (trans_apply Ψ Φ)

/-- The inverse in the isometry group coerces to the inverse isometry. -/
@[simp]
theorem coe_inv (Φ : RiemannianIsometry I I M M) : ⇑Φ⁻¹ = Φ.symm := rfl

/-- Multiplication of isometries applies the right factor, then the left. -/
@[simp]
theorem mul_apply (Φ Ψ : RiemannianIsometry I I M M) (x : M) : (Φ * Ψ) x = Φ (Ψ x) :=
  trans_apply Ψ Φ x

/-- The unit isometry fixes every point. -/
@[simp]
theorem one_apply (x : M) : (1 : RiemannianIsometry I I M M) x = x := refl_apply I M x

/-- The inverse in the isometry group acts as the inverse isometry. -/
@[simp]
theorem inv_apply (Φ : RiemannianIsometry I I M M) (x : M) : Φ⁻¹ x = Φ.symm x := rfl

/-- The isometry group acts on `M` by evaluation. -/
instance applyMulAction : MulAction (RiemannianIsometry I I M M) M where
  smul Φ x := Φ x
  one_smul := one_apply
  mul_smul := mul_apply

/-- The action of the isometry group on `M` is evaluation. -/
@[simp]
theorem smul_def (Φ : RiemannianIsometry I I M M) (x : M) : Φ • x = Φ x := rfl

/-- The isometry group acts faithfully on `M`. -/
instance applyFaithfulSMul : FaithfulSMul (RiemannianIsometry I I M M) M :=
  ⟨fun h ↦ RiemannianIsometry.ext h⟩

/-- The forgetful group homomorphism from the isometry group to the diffeomorphism group,
sending an isometry to its underlying smooth diffeomorphism. -/
def toDiff : RiemannianIsometry I I M M →* Diff I M ∞ where
  toFun Φ := Φ.toDiffeomorph
  map_one' := Diffeomorph.ext one_apply
  map_mul' Φ Ψ := Diffeomorph.ext (mul_apply Φ Ψ)

/-- The forgetful homomorphism to the diffeomorphism group forgets the metric condition. -/
@[simp]
theorem toDiff_apply (Φ : RiemannianIsometry I I M M) : toDiff Φ = Φ.toDiffeomorph := (rfl)

/-- The forgetful homomorphism to the diffeomorphism group is injective, so the isometry group is
a subgroup of the diffeomorphism group. -/
theorem toDiff_injective : Function.Injective (toDiff : RiemannianIsometry I I M M → Diff I M ∞) :=
  fun _ _ h ↦ RiemannianIsometry.ext fun x ↦ DFunLike.congr_fun h x

end TauCeti.RiemannianIsometry

end
