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
`⁅x, φ⁆ m = - φ ⁅x, m⁆` (Mathlib's `Module.Dual.instLieRingModule`). This file lifts two
linear-algebra constructions to morphisms of Lie modules: transposition, which makes `Module.Dual`
a contravariant functor, and evaluation into the double dual:

* the transpose `f.dualMap : N* → M*` of a morphism of Lie modules `f : M → N` is again a morphism
  of Lie modules, and the transpose of an equivalence is an equivalence;
* the evaluation map `M → M**` is a morphism of Lie modules, hence an equivalence of Lie modules
  when `M` is reflexive (for instance finite-dimensional over a field).

Together they identify the morphism spaces `M →ₗ⁅R,L⁆ N` and `N* →ₗ⁅R,L⁆ M*` whenever `N` is
reflexive (`TauCeti.LieModule.dualMapEquiv`). This is how statements about morphisms *into* a module
are traded for statements about morphisms *out of* its dual, for instance when comparing the
multiplicity of an irreducible module in `M*` with a morphism space out of `M`.

## Main definitions

* `LieModuleHom.dualMap`: the transpose of a morphism of Lie modules.
* `LieModuleEquiv.dualMap`: the transpose of an equivalence of Lie modules.
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

/-- **The transpose of a morphism of Lie modules.** For a morphism `f : M → N`, this is the
morphism `φ ↦ φ ∘ f` between the duals with their contragredient actions, lifting
`LinearMap.dualMap`. -/
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

@[simp]
theorem dualMap_zero : (0 : M →ₗ⁅R,L⁆ N).dualMap = 0 := by
  ext
  simp

@[simp]
theorem dualMap_add (f g : M →ₗ⁅R,L⁆ N) : (f + g).dualMap = f.dualMap + g.dualMap := by
  ext
  simp

@[simp]
theorem dualMap_neg (f : M →ₗ⁅R,L⁆ N) : (-f).dualMap = -f.dualMap := by
  ext
  simp

@[simp]
theorem dualMap_sub (f g : M →ₗ⁅R,L⁆ N) : (f - g).dualMap = f.dualMap - g.dualMap := by
  ext
  simp

@[simp]
theorem dualMap_smul (r : R) (f : M →ₗ⁅R,L⁆ N) : (r • f).dualMap = r • f.dualMap := by
  ext
  simp

end LieModuleHom

namespace LieModuleEquiv

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

/-- **The transpose of an equivalence of Lie modules.** For an equivalence `e : M ≃ N`, this is the
equivalence `φ ↦ φ ∘ e` between the duals with their contragredient actions, lifting
`LinearEquiv.dualMap`. -/
def dualMap (e : M ≃ₗ⁅R,L⁆ N) : Dual R N ≃ₗ⁅R,L⁆ Dual R M where
  __ := (e : M →ₗ⁅R,L⁆ N).dualMap
  __ := e.toLinearEquiv.dualMap

@[simp]
theorem dualMap_apply (e : M ≃ₗ⁅R,L⁆ N) (φ : Dual R N) (m : M) : e.dualMap φ m = φ (e m) :=
  (rfl)

@[simp]
theorem toLinearEquiv_dualMap (e : M ≃ₗ⁅R,L⁆ N) :
    e.dualMap.toLinearEquiv = e.toLinearEquiv.dualMap :=
  (rfl)

@[simp]
theorem toLieModuleHom_dualMap (e : M ≃ₗ⁅R,L⁆ N) :
    (e.dualMap : Dual R N →ₗ⁅R,L⁆ Dual R M) = (e : M →ₗ⁅R,L⁆ N).dualMap :=
  (rfl)

@[simp]
theorem dualMap_refl : (refl : M ≃ₗ⁅R,L⁆ M).dualMap = refl :=
  (rfl)

@[simp]
theorem dualMap_symm (e : M ≃ₗ⁅R,L⁆ N) : e.dualMap.symm = e.symm.dualMap :=
  (rfl)

theorem dualMap_trans (e : M ≃ₗ⁅R,L⁆ N) (e' : N ≃ₗ⁅R,L⁆ P) :
    (e.trans e').dualMap = e'.dualMap.trans e.dualMap :=
  (rfl)

end LieModuleEquiv

namespace TauCeti.LieModule

variable (R : Type u) (L : Type v) (M : Type w) {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [_root_.LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [_root_.LieModule R L N]

/-- **Evaluation into the double dual as a morphism of Lie modules**: the morphism
`m ↦ (φ ↦ φ m)` from `M` to `M**`, lifting `Module.Dual.eval R M`. -/
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

@[simp]
theorem toLieModuleHom_evalEquiv [Module.IsReflexive R M] :
    (evalEquiv R L M : M →ₗ⁅R,L⁆ Dual R (Dual R M)) = dualEval R L M :=
  (rfl)

/-- A functional applied to the inverse of evaluation is evaluation at that functional. -/
@[simp]
theorem apply_evalEquiv_symm_apply [Module.IsReflexive R M] (Φ : Dual R (Dual R M))
    (φ : Dual R M) : φ ((evalEquiv R L M).symm Φ) = Φ φ := by
  rw [← evalEquiv_apply R L M, (evalEquiv R L M).apply_symm_apply]

section DualMapEquiv

variable (N)

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

@[simp]
theorem dualMapEquiv_symm_dualMap [Module.IsReflexive R N] (f : M →ₗ⁅R,L⁆ N) :
    (dualMapEquiv R L M N).symm f.dualMap = f :=
  (dualMapEquiv R L M N).symm_apply_apply f

@[simp]
theorem dualMap_dualMapEquiv_symm [Module.IsReflexive R N] (g : Dual R N →ₗ⁅R,L⁆ Dual R M) :
    ((dualMapEquiv R L M N).symm g).dualMap = g :=
  (dualMapEquiv R L M N).apply_symm_apply g

end DualMapEquiv

end TauCeti.LieModule
