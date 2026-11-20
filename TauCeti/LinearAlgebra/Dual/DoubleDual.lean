/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# The universal property of the double dual

If the dual of `M` is reflexive, every map from `M` to a reflexive module extends uniquely
across evaluation `M → M**`. The extension is the double dual of the map followed by inverse
evaluation in the target. Thus, whenever duals are reflexive, double dualization is a
reflection into reflexive modules. The statement does not require evaluation on `M` to be
injective; torsion may be killed by it.

On the other hand, evaluation `M → M**` is injective if and only if `Module.Dual R M` separates
nonzero points of `M` (`TauCeti.Module.Dual.injective_eval_iff`), and over any integral domain `R`
this holds for every finitely generated torsion-free `R`-module
(`TauCeti.Module.Dual.injective_eval_of_finite`), obtained by clearing denominators of a
`FractionRing R`-linear functional on the localized module across a finite generating set.

## Main declarations

* `TauCeti.Module.Dual.injective_eval_iff`: `Module.Dual.eval R M` is injective if and only if every
  nonzero element of `M` is not killed by some `R`-linear functional.
* `TauCeti.Module.Dual.injective_eval_of_finite`: over any integral domain `R`, a finitely
  generated torsion-free `R`-module has injective double-dual evaluation.
* `TauCeti.Module.Dual.evalHomEquiv`: precomposition with evaluation is a linear equivalence on maps
  to a reflexive target, provided the dual of the source is reflexive.
-/

public section

open Module Module.Dual

namespace TauCeti.Module.Dual

/-- The canonical evaluation map `Module.Dual.eval R M` into the double dual is injective if and
only if `Module.Dual R M` separates nonzero points of `M`. -/
theorem injective_eval_iff {R : Type*} {M : Type*} [CommSemiring R] [AddCommGroup M]
    [Module R M] :
    Function.Injective (Module.Dual.eval R M) ↔
      ∀ x : M, x ≠ 0 → ∃ φ : Module.Dual R M, φ x ≠ 0 := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · by_contra! hall
    exact hx (h x (LinearMap.ext hall))
  · by_contra hx0
    obtain ⟨φ, hφ⟩ := h x hx0
    exact hφ (by simpa using LinearMap.congr_fun hx φ)

/-- Over an integral domain `R`, `Module.Dual.eval R M` is injective for any finitely generated
torsion-free `R`-module `M` (without requiring `IsNoetherianRing R`). -/
theorem injective_eval_of_finite {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M] :
    Function.Injective (Module.Dual.eval R M) := by
  classical
  let K := FractionRing R
  let V := LocalizedModule (nonZeroDivisors R) M
  let f : M →ₗ[R] V := LocalizedModule.mkLinearMap (nonZeroDivisors R) M
  have hf : Function.Injective f :=
    (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R) f).mpr fun c ↦
      (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero c.property)).isSMulRegular
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine injective_eval_iff.mpr fun x hx ↦ ?_
  obtain ⟨ψ, hψx⟩ := Module.Projective.exists_dual_ne_zero K ((map_ne_zero_iff f hf).mpr hx)
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun y : s ↦ ψ (f y.val))
  have hmem : ∀ m : M, (d : R) • ψ (f m) ∈ LinearMap.range (Algebra.linearMap R K) := by
    suffices ⊤ ≤ (LinearMap.range (Algebra.linearMap R K)).comap
        ((d : R) • (ψ.restrictScalars R).comp f) from fun m ↦ this trivial
    rw [← hs, Submodule.span_le]
    exact fun m hm ↦ hd ⟨m, hm⟩
  let φ : Module.Dual R M :=
    ((d : R) • (ψ.restrictScalars R).comp f).codRestrictOfInjective
      (Algebra.linearMap R K) (IsFractionRing.injective R K) hmem
  refine ⟨φ, fun hφ0 ↦ ?_⟩
  have hmap : algebraMap R K (φ x) = algebraMap R K (d : R) * ψ (f x) := by
    simpa [φ, Algebra.smul_def] using
      LinearMap.codRestrictOfInjective_comp_apply ((d : R) • (ψ.restrictScalars R).comp f)
        (Algebra.linearMap R K) (IsFractionRing.injective R K) hmem x
  exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property) hψx
    (by rwa [hφ0, map_zero, eq_comm] at hmap)

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
