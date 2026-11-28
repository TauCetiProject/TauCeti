/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Module

/-!
# Strict continuous linear maps

This file extends Mathlib's strict linear map API (`Mathlib/Topology/Maps/Strict/Module.lean`)
with `ContinuousLinearMap.equivRangeOfIsStrictMap`, which upgrades an injective strict continuous
linear map to a continuous linear equivalence onto its range.
-/

public section

namespace ContinuousLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [TopologicalSpace E] [Module R E]
  [AddCommMonoid F] [TopologicalSpace F] [Module R F]

/-- An injective strict continuous linear map induces a continuous linear equivalence onto its
range. -/
noncomputable def equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    E ≃L[R] f.range :=
  .ofIsHomeomorph (LinearEquiv.ofInjective f.toLinearMap hinj) <|
    isHomeomorph_iff_isQuotientMap_injective.mpr
      ⟨by
        have hcoe : ⇑(LinearEquiv.ofInjective f.toLinearMap hinj) = f.rangeRestrict := by
          ext x
          rw [LinearEquiv.ofInjective_apply, coe_codRestrict_apply, coe_coe]
        rw [hcoe, coe_rangeRestrict]
        exact Topology.isStrictMap_iff_isQuotientMap_rangeFactorization.mp hstrict,
      (LinearEquiv.ofInjective f.toLinearMap hinj).injective⟩

@[simp]
theorem toLinearEquiv_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    (f.equivRangeOfIsStrictMap hinj hstrict).toLinearEquiv =
      LinearEquiv.ofInjective f.toLinearMap hinj :=
  (rfl)

@[simp]
theorem coeFn_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    ⇑(f.equivRangeOfIsStrictMap hinj hstrict) = f.rangeRestrict := by
  rw [equivRangeOfIsStrictMap, ContinuousLinearEquiv.coe_ofIsHomeomorph, coe_rangeRestrict]
  ext x
  exact LinearEquiv.ofInjective_apply f.toLinearMap x

@[simp]
theorem equivRangeOfIsStrictMap_apply (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (x : E) :
    f.equivRangeOfIsStrictMap hinj hstrict x = f.rangeRestrict x :=
  congrFun (coeFn_equivRangeOfIsStrictMap f hinj hstrict) x

@[simp]
theorem coe_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    (f.equivRangeOfIsStrictMap hinj hstrict : E →L[R] f.range) = f.rangeRestrict :=
  ContinuousLinearMap.ext (equivRangeOfIsStrictMap_apply f hinj hstrict)

@[simp]
theorem equivRangeOfIsStrictMap_symm_apply_apply (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (x : E) :
    (f.equivRangeOfIsStrictMap hinj hstrict).symm ⟨f x, f.mem_range_self x⟩ = x := by
  have h : (⟨f x, f.mem_range_self x⟩ : f.range) = f.equivRangeOfIsStrictMap hinj hstrict x :=
    (equivRangeOfIsStrictMap_apply f hinj hstrict x).symm
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

@[simp]
theorem apply_equivRangeOfIsStrictMap_symm (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (y : f.range) :
    f ((f.equivRangeOfIsStrictMap hinj hstrict).symm y) = y := by
  have h := congrArg Subtype.val ((f.equivRangeOfIsStrictMap hinj hstrict).apply_symm_apply y)
  simpa only [equivRangeOfIsStrictMap_apply, coe_codRestrict_apply, coe_coe] using h

end ContinuousLinearMap

end
