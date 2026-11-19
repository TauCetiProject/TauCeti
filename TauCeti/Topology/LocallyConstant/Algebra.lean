/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Scalar towers and precomposition for locally constant functions

Mathlib equips `LocallyConstant X Y` with the pointwise actions on `Y`. This file
records that the pointwise actions inherit scalar towers and commuting actions from `Y`, which
is what makes `LocallyConstant X N` a target for linear maps out of tensor products such as
`N ⊗[R] M` with its `S`-module structure.

It also packages precomposition with a locally constant map `π : X → Y` as a linear map
`IsLocallyConstant.funLeft` from all functions on `Y` to locally constant functions on `X`, the
analogue of `LinearMap.funLeft`. The typical choice of `π` is the projection of `X` to a discrete
quotient: every locally constant function is pulled back from the discrete quotient by its fibres
(`LocallyConstant.funLeft_lift`). On a discrete space, `LocallyConstant.linearEquivFnOfDiscrete`
identifies `LocallyConstant X M` with `X → M`.
-/

public section

namespace LocallyConstant

variable {X Y A B : Type*} [TopologicalSpace X]

instance [SMul A B] [SMul A Y] [SMul B Y] [IsScalarTower A B Y] :
    IsScalarTower A B (LocallyConstant X Y) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_assoc _ _ _⟩

instance [SMul A Y] [SMul B Y] [SMulCommClass A B Y] :
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
  hsurj.injective_comp_right (by simpa using congrArg DFunLike.coe h)

/-- Precomposition with an injective locally constant map is surjective: a locally constant
function on `X` extends by zero off the image of `π`. -/
theorem IsLocallyConstant.funLeft_surjective (hπ : IsLocallyConstant π)
    (hinj : Function.Injective π) (A M : Type*) [Semiring A] [AddCommMonoid M] [Module A M] :
    Function.Surjective (hπ.funLeft A M) := fun f ↦
  ⟨Function.extend π f 0, LocallyConstant.ext fun x ↦ by simp [hinj.extend_apply]⟩

/-- Precomposing with `π` after precomposing with `g` is precomposing with `g ∘ π`. -/
theorem IsLocallyConstant.funLeft_comp {Z : Type*} (hπ : IsLocallyConstant π) (g : Y → Z)
    (A M : Type*) [Semiring A] [AddCommMonoid M] [Module A M] :
    (hπ.comp g).funLeft A M = hπ.funLeft A M ∘ₗ LinearMap.funLeft A M g :=
  (rfl)

/-- A locally constant function is pulled back from the discrete quotient by its fibres. -/
theorem LocallyConstant.funLeft_lift {M : Type*} (A : Type*) [Semiring A] [AddCommMonoid M]
    [Module A M] (f : LocallyConstant X M) :
    f.discreteQuotient.proj_isLocallyConstant.funLeft A M f.lift = f :=
  LocallyConstant.ext fun x ↦ by
    rw [IsLocallyConstant.coe_funLeft]
    exact congrFun f.lift_comp_proj x

end FunLeft

namespace LocallyConstant

variable {X M : Type*} [TopologicalSpace X] [DiscreteTopology X]

/-- On a discrete space every function is locally constant, so `DFunLike.coe` is a linear
equivalence `LocallyConstant X M ≃ₗ[A] (X → M)`. -/
def linearEquivFnOfDiscrete (A : Type*) [Semiring A] [AddCommMonoid M] [Module A M] :
    LocallyConstant X M ≃ₗ[A] (X → M) where
  __ := coeFnₗ A
  invFun f := ⟨f, .of_discrete f⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_linearEquivFnOfDiscrete (A : Type*) [Semiring A] [AddCommMonoid M] [Module A M] :
    ⇑(linearEquivFnOfDiscrete A : LocallyConstant X M ≃ₗ[A] (X → M)) = DFunLike.coe :=
  (rfl)

@[simp]
theorem coe_linearEquivFnOfDiscrete_symm_apply (A : Type*) [Semiring A] [AddCommMonoid M]
    [Module A M] (f : X → M) :
    ⇑((linearEquivFnOfDiscrete A : LocallyConstant X M ≃ₗ[A] (X → M)).symm f) = f :=
  (rfl)

end LocallyConstant
