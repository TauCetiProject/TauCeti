/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Hom spaces and direct sums of isotypic components

Mathlib shows that the isotypic components of a module are independent
(`sSupIndep_isotypicComponents`) and, for a semisimple module, span it
(`sSup_isotypicComponents`); it reads off the consequence for endomorphisms
(`IsSemisimpleModule.endAlgEquiv`). This file records the consequence for the module itself: a
semisimple module is the internal direct sum of its isotypic components. When there are finitely
many components, for instance when the module is Noetherian, composing with
`DFinsupp.linearEquivFunOnFintype` presents it as their product.

Maps from a simple module `S` into `M` land in its `S`-isotypic component. Restricting the
codomain therefore gives an equivalence of hom spaces, without any semisimplicity or
finiteness assumption on `M`. A map from a simple module into an isotypic module of a different
type is zero (`IsIsotypicOfType.linearMap_eq_zero`).

## Main definitions

* `TauCeti.linearMapIsotypicComponentEquiv`: the hom space from `S` into its isotypic component
  is linearly equivalent to the hom space from `S` into the ambient module.

* `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents`: a semisimple module is linearly
  equivalent to the direct sum of its isotypic components.

## Main statements

* `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents_apply_coe` and
  `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents_symm_single`: the equivalence and its
  inverse on a single isotypic component.
-/

public section

namespace TauCeti

section Hom

variable {R M S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup S] [Module R S]

/-- A module is its own isotypic component: the top submodule is isomorphic to the module. -/
@[simp]
theorem isotypicComponent_self_eq_top : isotypicComponent R S S = ⊤ :=
  eq_top_iff.mpr <| (Submodule.le_isotypicComponent ⊤).trans_eq
    Submodule.topEquiv.isotypicComponent_eq

variable [IsSimpleModule R S]

/-- A map out of a simple module takes its values in the isotypic component of that type. -/
theorem _root_.LinearMap.apply_mem_isotypicComponent (f : S →ₗ[R] M) (s : S) :
    f s ∈ isotypicComponent R M S := by
  have h := LinearMap.le_comap_isotypicComponent (M := S) (N := M) S f
  rw [isotypicComponent_self_eq_top] at h
  exact h Submodule.mem_top

variable (k : Type*) [CommSemiring k] [Algebra k R] [Module k M] [IsScalarTower k R M]

/-- Composition with the inclusion of the `S`-isotypic component is an equivalence of hom
spaces out of the simple module `S`. Its inverse corestricts a map to that component.
The equivalence is linear over the scalar semiring acting on the target. -/
def linearMapIsotypicComponentEquiv :
    (S →ₗ[R] isotypicComponent R M S) ≃ₗ[k] (S →ₗ[R] M) where
  toFun g := (isotypicComponent R M S).subtype ∘ₗ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.codRestrict _ f.apply_mem_isotypicComponent
  left_inv _ := by ext s; rfl
  right_inv _ := by ext s; rfl

/-- The forward equivalence composes a map into the isotypic component with its inclusion
into the ambient module. -/
@[simp]
theorem linearMapIsotypicComponentEquiv_apply
    (f : S →ₗ[R] isotypicComponent R M S) (s : S) :
    linearMapIsotypicComponentEquiv k f s = f s := (rfl)

/-- The inverse equivalence corestricts a map into the ambient module to its isotypic
component, preserving its values. -/
@[simp]
theorem linearMapIsotypicComponentEquiv_symm_apply (f : S →ₗ[R] M) (s : S) :
    (linearMapIsotypicComponentEquiv k).symm f s =
      ⟨f s, f.apply_mem_isotypicComponent s⟩ := (rfl)

end Hom

end TauCeti

namespace IsIsotypicOfType

variable {R M N S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup S] [Module R S]
  [IsSimpleModule R S]

/-- A map from a simple module into an isotypic module of a different type is zero. -/
theorem linearMap_eq_zero (h : IsIsotypicOfType R M N)
    (hne : ¬ Nonempty (S ≃ₗ[R] N)) (f : S →ₗ[R] M) : f = 0 := by
  obtain hinj | hzero := f.injective_or_eq_zero
  · let e := LinearEquiv.ofInjective f hinj
    have : IsSimpleModule R (LinearMap.range f) := .congr e.symm
    exact False.elim (hne ⟨e.trans (h (LinearMap.range f)).some⟩)
  · exact hzero

end IsIsotypicOfType

namespace TauCeti.IsSemisimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  [DecidableEq (isotypicComponents R M)]

/-- **A semisimple module is the direct sum of its isotypic components.** The equivalence sends
an element to its family of components, and its inverse adds the components up. This is the
module-level counterpart of `IsSemisimpleModule.endAlgEquiv`. -/
noncomputable def linearEquivIsotypicComponents : M ≃ₗ[R] Π₀ c : isotypicComponents R M, c.1 :=
  .symm <| ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).linearEquiv <|
    (sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M

variable {R M}

/-- The inverse of `linearEquivIsotypicComponents` sends the family that is `x` at the isotypic
component `c` and zero elsewhere to `x`, viewed as an element of `M`. -/
@[simp]
theorem linearEquivIsotypicComponents_symm_single (c : isotypicComponents R M) (x : c.1) :
    (linearEquivIsotypicComponents R M).symm (DFinsupp.single c x) = x := by
  simp [linearEquivIsotypicComponents]

/-- `linearEquivIsotypicComponents` sends an element `x` of an isotypic component `c`, viewed as an
element of `M`, to the family that is `x` at `c` and zero elsewhere. -/
@[simp]
theorem linearEquivIsotypicComponents_apply_coe {c : isotypicComponents R M} (x : c.1) :
    linearEquivIsotypicComponents R M x = DFinsupp.single c x := by
  rw [← linearEquivIsotypicComponents_symm_single, LinearEquiv.apply_symm_apply]

-- Not `@[simp]`: the component `c` does not occur in the left-hand side, so `simp` could only
-- find it by solving `x ∈ c.1` for `c`. The simp form is
-- `linearEquivIsotypicComponents_apply_coe`, as with `DirectSum.decompose_coe` and
-- `DirectSum.decompose_of_mem`.
/-- An element `x` of `M` lying in an isotypic component `c` is sent by
`linearEquivIsotypicComponents` to the family that is `x` at `c` and zero elsewhere. -/
theorem linearEquivIsotypicComponents_apply_of_mem {c : isotypicComponents R M} {x : M}
    (hx : x ∈ c.1) : linearEquivIsotypicComponents R M x = DFinsupp.single c ⟨x, hx⟩ :=
  linearEquivIsotypicComponents_apply_coe ⟨x, hx⟩

end TauCeti.IsSemisimpleModule
