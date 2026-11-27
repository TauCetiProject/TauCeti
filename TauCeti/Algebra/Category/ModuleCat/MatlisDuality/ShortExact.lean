/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.LinearAlgebra.Exact

/-!
# Dual short exact sequences of right modules

Matlis duality with injective coefficients sends a short exact sequence of right modules to a
short exact sequence of left modules, reversing its two maps.
-/

public section

open CategoryTheory TauCeti

namespace CategoryTheory.ShortComplex

universe u v w t

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  {A : Type w} [Ring A] [Algebra R A] {S : ShortComplex (ModuleCat.{max v t} Aᵐᵒᵖ)}

/-- The Matlis dual of a short complex of right modules, with terms and maps written as the
corresponding bundled dual modules and dual maps. -/
noncomputable abbrev matlisDualOp (S : ShortComplex (ModuleCat.{max v t} Aᵐᵒᵖ)) :
    ShortComplex (ModuleCat.{max v t} A) :=
  ShortComplex.mk (ModuleCat.matlisDualOpMap R E S.g) (ModuleCat.matlisDualOpMap R E S.f)
    (by exact (S.op.map (ModuleCat.matlisDualOp R E)).zero)

/-- Matlis duality with injective coefficients takes short exact sequences of right modules to
short exact sequences of left modules. -/
theorem ShortExact.matlisDualOp [Small.{v} R] [Module.Injective R E] (hS : S.ShortExact) :
    (S.matlisDualOp R E).ShortExact := by
  let e (N : ModuleCat.{max v t} Aᵐᵒᵖ) :
      ModuleCat.matlisDualOpObj R E N ≃ (N →ₗ[R] E) :=
    (ModuleCat.matlisDualOpObjEquiv R E N).toEquiv.trans
      (MatlisDual.equivLinearMap R E N).toEquiv
  have hmap {N N' : ModuleCat.{max v t} Aᵐᵒᵖ} (f : N ⟶ N')
      (φ : ModuleCat.matlisDualOpObj R E N') :
      e N (ModuleCat.matlisDualOpMap R E f φ) = (e N' φ).comp (f.hom.restrictScalars R) :=
    LinearMap.ext fun x ↦ ModuleCat.matlisDualOpObjEquiv_map_apply R E f φ x
  have hex : Function.Exact S.f.hom S.g.hom :=
    (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  refine ModuleCat.shortComplex_shortExact _ (fun φ ↦ ?_) ?_ (fun ψ ↦ ?_)
  · have hex' : Function.Exact (S.f.hom.restrictScalars R) (S.g.hom.restrictScalars R) := hex
    have hd := hex'.lcomp_of_surjective (T := R) E hS.moduleCat_surjective_g
    constructor
    · intro hφ
      have hzero : (e S.X₂ φ).comp (S.f.hom.restrictScalars R) = 0 := by
        rw [← hmap, hφ]
        simp [e]
      obtain ⟨χ, hχ⟩ := (hd (e S.X₂ φ)).mp hzero
      refine ⟨(e S.X₃).symm χ, (e S.X₂).injective ?_⟩
      rw [hmap, Equiv.apply_symm_apply]
      exact hχ
    · rintro ⟨χ, rfl⟩
      exact (S.matlisDualOp R E).moduleCat_zero_apply χ
  · exact ModuleCat.mono_iff_injective _ |>.mp
      (ModuleCat.mono_matlisDualOp_map_of_surjective R E S.g hS.moduleCat_surjective_g)
  · have : Module.Injective R (ULift.{t} E) := Module.ulift_injective_of_injective R inferInstance
    obtain ⟨χ, hχ⟩ := Module.Injective.out (S.f.hom.restrictScalars R)
      hS.moduleCat_injective_f (ULift.moduleEquiv.symm.toLinearMap ∘ₗ e S.X₁ ψ)
    refine ⟨(e S.X₂).symm (ULift.moduleEquiv.toLinearMap ∘ₗ χ), (e S.X₁).injective ?_⟩
    rw [hmap, Equiv.apply_symm_apply]
    ext x
    simpa using congrArg ULift.down (hχ x)

end CategoryTheory.ShortComplex
