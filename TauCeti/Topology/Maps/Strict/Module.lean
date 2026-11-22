/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Module
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Range

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
    E ≃L[R] f.range where
  toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hinj
  continuous_toFun := f.rangeRestrict.continuous.congr fun x ↦
    (congrFun (coe_ofInjective_eq_rangeRestrict f hinj) x).symm
  continuous_invFun :=
    (Topology.isEmbedding_iff_isStrictMap_injective.mpr ⟨hstrict, hinj⟩).continuous_iff.mpr <|
      continuous_subtypeVal.congr fun y ↦
        (LinearEquiv.ofInjective_symm_apply f.toLinearMap (h := hinj) y).symm

@[simp]
theorem toLinearEquiv_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    (f.equivRangeOfIsStrictMap hinj hstrict).toLinearEquiv =
      LinearEquiv.ofInjective f.toLinearMap hinj :=
  (rfl)

@[simp]
theorem coeFn_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    ⇑(f.equivRangeOfIsStrictMap hinj hstrict) = f.rangeRestrict :=
  coe_ofInjective_eq_rangeRestrict f hinj

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
theorem equivRangeOfIsStrictMap_symm_apply_rangeFactorization (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (x : E) :
    (f.equivRangeOfIsStrictMap hinj hstrict).symm (Set.rangeFactorization f x) = x := by
  rw [← coe_rangeRestrict, ← equivRangeOfIsStrictMap_apply f hinj hstrict x,
    ContinuousLinearEquiv.symm_apply_apply]

theorem equivRangeOfIsStrictMap_symm_apply_rangeRestrict (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (x : E) :
    (f.equivRangeOfIsStrictMap hinj hstrict).symm (f.rangeRestrict x) = x :=
  equivRangeOfIsStrictMap_symm_apply_rangeFactorization f hinj hstrict x

@[simp]
theorem rangeFactorization_equivRangeOfIsStrictMap_symm_apply (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (y : f.range) :
    Set.rangeFactorization f ((f.equivRangeOfIsStrictMap hinj hstrict).symm y) = y := by
  rw [← coe_rangeRestrict, ← equivRangeOfIsStrictMap_apply f hinj hstrict,
    ContinuousLinearEquiv.apply_symm_apply]

theorem rangeRestrict_equivRangeOfIsStrictMap_symm_apply (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (y : f.range) :
    f.rangeRestrict ((f.equivRangeOfIsStrictMap hinj hstrict).symm y) = y :=
  rangeFactorization_equivRangeOfIsStrictMap_symm_apply f hinj hstrict y

end ContinuousLinearMap

end
