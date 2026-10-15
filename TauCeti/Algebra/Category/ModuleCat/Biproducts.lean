/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.DirectSum.Module

/-!
# The carrier of a finite biproduct in `ModuleCat`

Mathlib's `ModuleCat.biproductIsoPi` identifies a finite biproduct in `ModuleCat A` with the
dependent function type `∀ i, P i`. Over a finite index type the external direct sum `⨁ i, P i` is
the same module (`DirectSum.linearEquivFunOnFintype`), so a finite biproduct is also the external
direct sum of the carriers of its summands. This file records that identification, together with
the two lemmas that characterise it: its components are the biproduct projections, and it sends a
biproduct inclusion to the corresponding direct-sum inclusion.

This is the transport along which results about `DirectSum` decompositions of a module — the
Krull-Schmidt theorem among them — can be read as results about biproducts in `ModuleCat A`.

## Main definitions

* `TauCeti.biproductDirectSumEquiv`: the carrier of a finite biproduct in `ModuleCat A` is the
  external direct sum of the carriers of the summands.

## Main results

* `TauCeti.component_biproductDirectSumEquiv`: its `i`-th component is the `i`-th biproduct
  projection.
* `TauCeti.biproductDirectSumEquiv_ι`: it carries the `i`-th biproduct inclusion to the `i`-th
  direct-sum inclusion.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits DirectSum

universe u v

variable {A : Type u} [Ring A] {ι : Type} [Fintype ι] (P : ι → ModuleCat.{v} A)

/-- **The carrier of a finite biproduct in `ModuleCat A` is the external direct sum of the carriers
of the summands.** -/
noncomputable def biproductDirectSumEquiv :
    (biproduct P : ModuleCat.{v} A) ≃ₗ[A] ⨁ i, (P i : Type v) :=
  (ModuleCat.biproductIsoPi P).toLinearEquiv.trans
    (DirectSum.linearEquivFunOnFintype A ι fun i ↦ (P i : Type v)).symm

/-- The `i`-th component of `TauCeti.biproductDirectSumEquiv` is the `i`-th biproduct projection. -/
@[simp]
theorem component_biproductDirectSumEquiv (x : (biproduct P : ModuleCat.{v} A)) (i : ι) :
    DirectSum.component A ι (fun i ↦ (P i : Type v)) i (biproductDirectSumEquiv P x) =
      (biproduct.π P i).hom x := by
  -- Read through `ModuleCat.biproductIsoPi`, the `i`-th projection out of the dependent function
  -- type is the `i`-th biproduct projection.
  have key : (ModuleCat.biproductIsoPi P).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, (P j : Type v)) →ₗ[A] (P i : Type v)) =
      biproduct.π P i := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π P i, Iso.hom_inv_id_assoc]
  -- The underlying function of `biproductDirectSumEquiv P x` is `(ModuleCat.biproductIsoPi P).hom`
  -- applied to `x`, because the second factor of the composite is the inverse of
  -- `DirectSum.linearEquivFunOnFintype`.
  have hfun : (DirectSum.linearEquivFunOnFintype A ι fun j ↦ (P j : Type v))
      (biproductDirectSumEquiv P x) = (ModuleCat.biproductIsoPi P).hom.hom x := by
    unfold biproductDirectSumEquiv
    rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Iso.toLinearEquiv_apply]
  rw [← key, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearMap.proj_apply,
    ← hfun, DirectSum.linearEquivFunOnFintype_apply, ← DirectSum.apply_eq_component]

/-- `TauCeti.biproductDirectSumEquiv` carries the `i`-th biproduct inclusion to the `i`-th
direct-sum inclusion. -/
@[simp]
theorem biproductDirectSumEquiv_ι [DecidableEq ι] (i : ι) (y : (P i : Type v)) :
    biproductDirectSumEquiv P ((biproduct.ι P i).hom y) =
      DirectSum.lof A ι (fun i ↦ (P i : Type v)) i y := by
  -- Both sides are determined by their components, which `biproduct.ι_π` computes.
  refine DirectSum.ext_component A fun j ↦ ?_
  rw [component_biproductDirectSumEquiv, DirectSum.component.of, ← ModuleCat.comp_apply,
    biproduct.ι_π]
  rcases eq_or_ne i j with h | h
  · subst h
    simp
  · simp [h]

end TauCeti
