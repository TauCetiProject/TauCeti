/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Scalar towers and precomposition for locally constant functions

Mathlib equips `LocallyConstant X Y` with the pointwise actions of a monoid acting on `Y`. This file
records that the pointwise actions inherit scalar towers and commuting actions from `Y`, which
is what makes `LocallyConstant X N` a target for linear maps out of tensor products such as
`N ⊗[R] M` with its `S`-module structure.

It also packages precomposition with a locally constant map `π : X → Y` as a linear map
`IsLocallyConstant.funLeft` from all functions on `Y` to locally constant functions on `X`, the
analogue of `LinearMap.funLeft`. Typical choices of `π` are the projection of `X` to a discrete
quotient and the identity of a discrete space; in the second case `funLeft` identifies
`LocallyConstant X M` with `X → M`.
-/

public section

namespace LocallyConstant

variable {X Y A B : Type*} [TopologicalSpace X]

instance [Monoid A] [Monoid B] [SMul A B] [MulAction A Y] [MulAction B Y] [IsScalarTower A B Y] :
    IsScalarTower A B (LocallyConstant X Y) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_assoc _ _ _⟩

instance [Monoid A] [Monoid B] [MulAction A Y] [MulAction B Y] [SMulCommClass A B Y] :
    SMulCommClass A B (LocallyConstant X Y) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_comm _ _ _⟩

end LocallyConstant

section FunLeft

variable {X Y : Type*} [TopologicalSpace X] {π : X → Y}

/-- Precomposition with a locally constant map `π : X → Y`, as a linear map from all functions on
`Y` to locally constant functions on `X`. -/
def IsLocallyConstant.funLeft (hπ : IsLocallyConstant π) (A M : Type*) [Semiring A]
    [AddCommMonoid M] [Module A M] : (Y → M) →ₗ[A] LocallyConstant X M where
  toFun g := ⟨g ∘ π, hπ.comp g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem IsLocallyConstant.coe_funLeft (hπ : IsLocallyConstant π) (A M : Type*) [Semiring A]
    [AddCommMonoid M] [Module A M] (g : Y → M) : ⇑(hπ.funLeft A M g) = g ∘ π :=
  (rfl)

/-- Precomposition with a surjective locally constant map is injective. -/
theorem IsLocallyConstant.funLeft_injective (hπ : IsLocallyConstant π)
    (hsurj : Function.Surjective π) (A M : Type*) [Semiring A] [AddCommMonoid M] [Module A M] :
    Function.Injective (hπ.funLeft A M) := fun _ _ h ↦
  hsurj.injective_comp_right (congrArg DFunLike.coe h :)

/-- Precomposition with an injective locally constant map is surjective: a locally constant
function on `X` extends by zero off the image of `π`. -/
theorem IsLocallyConstant.funLeft_surjective (hπ : IsLocallyConstant π)
    (hinj : Function.Injective π) (A M : Type*) [Semiring A] [AddCommMonoid M] [Module A M] :
    Function.Surjective (hπ.funLeft A M) := fun f ↦
  ⟨Function.extend π f 0, LocallyConstant.ext fun x ↦ hinj.extend_apply _ _ x⟩

end FunLeft
