/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The transpose of a morphism of Lie modules and the double dual

The dual `M* = Module.Dual R M` of a Lie module carries the contragredient action
`⁅x, φ⁆ m = - φ ⁅x, m⁆` (Mathlib's `Module.Dual.instLieRingModule`). This file shows that the two
linear-algebra constructions which make `Module.Dual` a contravariant functor are compatible with
it:

* the transpose `f.dualMap : N* → M*` of a morphism of Lie modules `f : M → N` is again a morphism
  of Lie modules;
* the evaluation map `M → M**` is a morphism of Lie modules, hence an equivalence of Lie modules
  when `M` is reflexive (for instance finite-dimensional over a field).

Together they identify the morphism spaces `M →ₗ⁅R,L⁆ N` and `N* →ₗ⁅R,L⁆ M*` whenever `N` is
reflexive (`TauCeti.LieModule.dualMapEquiv`). This is how statements about morphisms *into* a module
are traded for statements about morphisms *out of* its dual, for instance when comparing the
multiplicity of an irreducible module in `M*` with a morphism space out of `M`.

## Main definitions

* `LieModuleHom.dualMap`: the transpose of a morphism of Lie modules.
* `TauCeti.LieModule.dualEval`: the evaluation morphism `M → M**`.
* `TauCeti.LieModule.evalEquiv`: the evaluation equivalence `M ≃ M**` of a reflexive Lie module.
* `TauCeti.LieModule.dualMapEquiv`: transposition, as a linear equivalence between
  `M →ₗ⁅R,L⁆ N` and `N* →ₗ⁅R,L⁆ M*` for reflexive `N`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre I, §3.3.
-/

public section

open Module (Dual)

universe u v w w₁ w₂

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

/-- **The transpose of a morphism of Lie modules.** For `f : M → N` commuting with the action of
`L`, the transpose `φ ↦ φ ∘ f` commutes with the contragredient actions on the duals. -/
def dualMap (f : M →ₗ⁅R,L⁆ N) : Dual R N →ₗ⁅R,L⁆ Dual R M where
  __ := f.toLinearMap.dualMap
  map_lie' {x φ} := by
    ext m
    simp

@[simp]
theorem dualMap_apply (f : M →ₗ⁅R,L⁆ N) (φ : Dual R N) (m : M) : f.dualMap φ m = φ (f m) :=
  (rfl)

@[simp]
theorem toLinearMap_dualMap (f : M →ₗ⁅R,L⁆ N) :
    (f.dualMap : Dual R N →ₗ[R] Dual R M) = (f : M →ₗ[R] N).dualMap :=
  (rfl)

@[simp]
theorem dualMap_id : (LieModuleHom.id : M →ₗ⁅R,L⁆ M).dualMap = LieModuleHom.id :=
  (rfl)

theorem dualMap_comp (g : N →ₗ⁅R,L⁆ P) (f : M →ₗ⁅R,L⁆ N) :
    (g.comp f).dualMap = f.dualMap.comp g.dualMap :=
  (rfl)

end LieModuleHom

namespace TauCeti.LieModule

variable (R : Type u) (L : Type v) (M : Type w) {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [_root_.LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [_root_.LieModule R L N]

/-- **Evaluation into the double dual is a morphism of Lie modules.** The two signs of the
contragredient action cancel: `⁅x, ev m⁆ φ = - ev m ⁅x, φ⁆ = φ ⁅x, m⁆`. -/
def dualEval : M →ₗ⁅R,L⁆ Dual R (Dual R M) where
  __ := Module.Dual.eval R M
  map_lie' {x m} := by
    ext φ
    simp

@[simp]
theorem dualEval_apply (m : M) (φ : Dual R M) : dualEval R L M m φ = φ m :=
  (rfl)

@[simp]
theorem toLinearMap_dualEval :
    (dualEval R L M : M →ₗ[R] Dual R (Dual R M)) = Module.Dual.eval R M :=
  (rfl)

/-- **A reflexive Lie module is equivalent to its double dual**, by evaluation. -/
noncomputable def evalEquiv [Module.IsReflexive R M] : M ≃ₗ⁅R,L⁆ Dual R (Dual R M) where
  __ := dualEval R L M
  __ := Module.evalEquiv R M

@[simp]
theorem evalEquiv_apply [Module.IsReflexive R M] (m : M) (φ : Dual R M) :
    evalEquiv R L M m φ = φ m :=
  (rfl)

@[simp]
theorem toLinearEquiv_evalEquiv [Module.IsReflexive R M] :
    (evalEquiv R L M).toLinearEquiv = Module.evalEquiv R M :=
  (rfl)

/-- A functional applied to the inverse of evaluation is evaluation at that functional. -/
@[simp]
theorem apply_evalEquiv_symm_apply [Module.IsReflexive R M] (Φ : Dual R (Dual R M))
    (φ : Dual R M) : φ ((evalEquiv R L M).symm Φ) = Φ φ := by
  conv_rhs => rw [← (evalEquiv R L M).apply_symm_apply Φ]
  rfl

variable (N) in
/-- **Transposition identifies the morphisms `M → N` with the morphisms `N* → M*`** when `N` is
reflexive. The inverse sends `g : N* → M*` to the morphism `M → N` corresponding to
`m ↦ (φ ↦ g φ m)` under `N ≃ N**`. -/
noncomputable def dualMapEquiv [Module.IsReflexive R N] :
    (M →ₗ⁅R,L⁆ N) ≃ₗ[R] (Dual R N →ₗ⁅R,L⁆ Dual R M) where
  toFun f := f.dualMap
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun g := ((evalEquiv R L N).symm : Dual R (Dual R N) →ₗ⁅R,L⁆ N).comp
    (g.dualMap.comp (dualEval R L M))
  left_inv f := by
    ext m
    refine (evalEquiv R L N).injective (LinearMap.ext fun φ ↦ ?_)
    simp
  right_inv g := by
    ext φ m
    simp

@[simp]
theorem dualMapEquiv_apply [Module.IsReflexive R N] (f : M →ₗ⁅R,L⁆ N) :
    dualMapEquiv R L M N f = f.dualMap :=
  (rfl)

/-- The morphism corresponding to `g : N* → M*` pairs with a functional `φ` on `N` through `g`. -/
@[simp]
theorem apply_dualMapEquiv_symm_apply [Module.IsReflexive R N] (g : Dual R N →ₗ⁅R,L⁆ Dual R M)
    (m : M) (φ : Dual R N) : φ ((dualMapEquiv R L M N).symm g m) = g φ m := by
  simp [dualMapEquiv]

end TauCeti.LieModule
