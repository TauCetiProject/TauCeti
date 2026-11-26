/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Domain restriction of positive continuous linear maps

This file supplements `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive` with domain
restriction to additive `R`-subobjects `s` (`Submodule`, `StarSubalgebra`,
`NonUnitalStarSubalgebra`).

## Main definitions and results

* `PositiveContinuousLinearMap.domRestrict`: restrict the domain of `f : E₁ →P[R] E₂` to an
  additive `R`-subobject `s` (`PositiveContinuousLinearMap.domRestrict_apply`).
* `PositiveContinuousLinearMap.comp_ofClass_eq_domRestrict`: composing `f` with a bundled inclusion
  `i : s → E₁` (`i x = x`) agrees with `f.domRestrict s`.
-/

public section

namespace PositiveContinuousLinearMap

variable {R E₁ E₂ M : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid E₂] [PartialOrder E₂] [Module R E₂] [TopologicalSpace E₂]
  [SetLike M E₁] [AddSubmonoidClass M E₁] [SMulMemClass M R E₁]

/-- Restrict the domain of a positive continuous linear map `f : E₁ →P[R] E₂` to an additive
`R`-subobject `s` (for instance a `Submodule`, `StarSubalgebra`, or `NonUnitalStarSubalgebra`). -/
def domRestrict (f : E₁ →P[R] E₂) (s : M) : s →P[R] E₂ where
  toFun x := f x
  map_add' x y := map_add f (x : E₁) (y : E₁)
  map_smul' c x := by
    simp only [RingHom.id_apply, SetLike.val_smul, map_smul]
  cont := (map_continuous f).comp continuous_subtypeVal
  monotone' _ _ h := f.mono h

/-- `f.domRestrict s` evaluates on `x : s` as `f x`. -/
@[simp]
theorem domRestrict_apply (f : E₁ →P[R] E₂) (s : M) (x : s) : f.domRestrict s x = f x :=
  (rfl)

/-- Composing `f` with a positive continuous linear inclusion `i : s → E₁` (`i x = x`) produces
`f.domRestrict s`. -/
theorem comp_ofClass_eq_domRestrict {s : M} {F : Type*} [FunLike F s E₁]
    [ContinuousLinearMapClass F R s E₁] [OrderHomClass F s E₁] (f : E₁ →P[R] E₂) (i : F)
    (hi : ∀ x : s, i x = x) : f.comp (.ofClass i) = f.domRestrict s := by
  ext x
  simp [hi]

end PositiveContinuousLinearMap
