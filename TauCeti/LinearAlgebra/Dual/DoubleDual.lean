/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The universal property of the double dual

If the dual of `M` is reflexive, every map from `M` to a reflexive module extends uniquely
across evaluation `M → M**`. The extension is the double dual of the map followed by inverse
evaluation in the target. Thus, whenever double duals are reflexive, double dualization is a
reflection into reflexive modules. The statement does not require evaluation on `M` to be
injective; torsion may be killed by it.

## Main declarations

* `TauCeti.Module.Dual.evalHomEquiv`: precomposition with evaluation is a linear equivalence on maps
to a reflexive target, provided the dual of the source is reflexive.
-/

public section

open Module Module.Dual

namespace TauCeti.Module.Dual

universe u v w

variable (R : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M]
  (N : Type w) [AddCommMonoid N] [Module R N]
  [Module.IsReflexive R (Dual R M)] [Module.IsReflexive R N]

/-- Precomposition with evaluation identifies maps from the double dual to a reflexive
module with maps from the original module, when its dual is reflexive. -/
noncomputable def evalHomEquiv :
    (Dual R (Dual R M) →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) where
  toFun g := g.comp (eval R M)
  invFun f := (Module.evalEquiv R N).symm.toLinearMap.comp f.dualMap.dualMap
  left_inv g := by
    ext x
    apply (Module.bijective_dual_eval R N).injective
    ext φ
    obtain ⟨ψ, hψ⟩ := (Module.bijective_dual_eval R (Dual R M)).surjective (φ.comp g)
    have h : φ.comp (g.comp (eval R M)) = ψ := by
      ext m
      exact (LinearMap.congr_fun hψ (eval R M m)).symm
    simpa [LinearMap.dualMap_apply', h] using LinearMap.congr_fun hψ x
  right_inv f := by
    ext m
    apply (Module.bijective_dual_eval R N).injective
    ext φ
    simp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The forward map is restriction along evaluation. -/
@[simp]
theorem evalHomEquiv_apply (g : Dual R (Dual R M) →ₗ[R] N) :
    evalHomEquiv R M N g = g.comp (eval R M) := (rfl)

/-- The extension to the double dual is obtained by double dualizing and identifying the
reflexive target with its double dual. -/
theorem evalHomEquiv_symm_apply (f : M →ₗ[R] N) :
    (evalHomEquiv R M N).symm f =
      (Module.evalEquiv R N).symm.toLinearMap.comp f.dualMap.dualMap := (rfl)

/-- The extension restricts to the original map along evaluation. -/
@[simp]
theorem evalHomEquiv_symm_comp_eval (f : M →ₗ[R] N) :
    ((evalHomEquiv R M N).symm f).comp (eval R M) = f :=
  (evalHomEquiv R M N).apply_symm_apply f

/-- The extension agrees pointwise with the original map on evaluation vectors. -/
@[simp]
theorem evalHomEquiv_symm_apply_eval (f : M →ₗ[R] N) (m : M) :
    (evalHomEquiv R M N).symm f (eval R M m) = f m :=
  LinearMap.congr_fun (evalHomEquiv_symm_comp_eval R M N f) m

/-- A map from a module to a reflexive module extends uniquely across evaluation when the
dual of the source is reflexive. -/
theorem existsUnique_comp_eval_eq (f : M →ₗ[R] N) :
    ∃! g : Dual R (Dual R M) →ₗ[R] N, g.comp (eval R M) = f :=
  (evalHomEquiv R M N).toEquiv.bijective.existsUnique f

end TauCeti.Module.Dual
