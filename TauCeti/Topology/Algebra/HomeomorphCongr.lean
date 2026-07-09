/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Transporting the self-homeomorphism group along a homeomorphism

A homeomorphism `e : M ≃ₜ N` conjugates self-homeomorphisms of `M` into self-homeomorphisms of `N`
by `φ ↦ e ∘ φ ∘ e⁻¹`. Because this preserves composition, it is a group isomorphism
`(M ≃ₜ M) ≃* (N ≃ₜ N)` between the self-homeomorphism groups. This file records that isomorphism,
`Homeomorph.homeoCongr`, its pointwise action, and its functoriality: it is the identity on
`Homeomorph.refl`, respects `Homeomorph.trans` and `Homeomorph.symm`, and sends inverses to
inverses.

This is the topological analogue of `Equiv.permCongr` (`Mathlib/Logic/Equiv/Defs.lean`), the
conjugation isomorphism of permutation groups, and is the target of the forgetful naturality of the
diffeomorphism-level `TauCeti.Diffeomorph.diffCongr` in
`TauCeti.Geometry.Diffeomorphism.Congr`.

## Main definitions

* `TauCeti.Homeomorph.homeoCongr e`: the group isomorphism `(M ≃ₜ M) ≃* (N ≃ₜ N)` conjugating
  self-homeomorphisms by a homeomorphism `e : M ≃ₜ N`.

## Main results

* `TauCeti.Homeomorph.homeoCongr_apply_apply`: the pointwise action
  `homeoCongr e φ x = e (φ (e.symm x))`.
* `TauCeti.Homeomorph.homeoCongr_refl`, `TauCeti.Homeomorph.homeoCongr_trans`, and
  `TauCeti.Homeomorph.homeoCongr_symm`: the functoriality of `homeoCongr` on the groupoid of
  homeomorphisms.
* `TauCeti.Homeomorph.eventuallyEq_comp_iff`: precomposition by a homeomorphism transports
  eventual equality at the corresponding neighbourhoods.
-/

public section

namespace TauCeti

open Topology

variable {M : Type*} [TopologicalSpace M]
  {N : Type*} [TopologicalSpace N]
  {P : Type*} [TopologicalSpace P]
  {Z : Type*}

namespace Homeomorph

/-- Precomposition by a homeomorphism transports eventual equality at neighbourhood filters:
`f ∘ e` and `g ∘ e` are eventually equal near `x` iff `f` and `g` are eventually equal near
`e x`. -/
theorem eventuallyEq_comp_iff (e : M ≃ₜ N) (f g : N → Z) (x : M) :
    (f ∘ e =ᶠ[𝓝 x] g ∘ e) ↔ (f =ᶠ[𝓝 (e x)] g) := by
  rw [← e.map_nhds_eq x]
  constructor
  · intro hyp
    refine Filter.eventually_map.mpr ?_
    filter_upwards [hyp] with y hy
    simpa using hy
  · intro hyp
    have hyp' := Filter.eventually_map.mp hyp
    filter_upwards [hyp'] with y hy
    simpa using hy

/-- Precomposition by a homeomorphism transports eventual equality to a constant at
neighbourhood filters. -/
theorem eventuallyEq_comp_const_iff (e : M ≃ₜ N) (f : N → Z) (z : Z) (x : M) :
    (f ∘ e =ᶠ[𝓝 x] fun _ ↦ z) ↔ (f =ᶠ[𝓝 (e x)] fun _ ↦ z) := by
  simpa [Function.comp_def] using eventuallyEq_comp_iff e f (fun _ ↦ z) x

/-- Precomposition by a homeomorphism transports eventual vanishing at neighbourhood filters. -/
theorem eventuallyEq_comp_zero_iff [Zero Z] (e : M ≃ₜ N) (f : N → Z) (x : M) :
    (f ∘ e =ᶠ[𝓝 x] 0) ↔ (f =ᶠ[𝓝 (e x)] 0) := by
  simpa using eventuallyEq_comp_iff e f (0 : N → Z) x

/-- Conjugation by a homeomorphism `e : M ≃ₜ N` as a group isomorphism between the
self-homeomorphism groups: `homeoCongr e φ = e ∘ φ ∘ e⁻¹`. This is the homeomorphism analogue of
`Equiv.permCongrHom` and the target of the forgetful naturality of `Diffeomorph.diffCongr`. -/
@[expose, simps apply]
def homeoCongr (e : M ≃ₜ N) : (M ≃ₜ M) ≃* (N ≃ₜ N) where
  toFun φ := (e.symm.trans φ).trans e
  invFun ψ := (e.trans ψ).trans e.symm
  left_inv φ := by ext x; simp
  right_inv ψ := by ext x; simp
  map_mul' φ ψ := by ext x; simp

/-- The conjugating isomorphism acts pointwise by `homeoCongr e φ x = e (φ (e.symm x))`. -/
@[simp, grind =]
theorem homeoCongr_apply_apply (e : M ≃ₜ N) (φ : M ≃ₜ M) (x : N) :
    homeoCongr e φ x = e (φ (e.symm x)) := rfl

/-- The inverse of `homeoCongr e φ` is `homeoCongr e φ⁻¹`, since conjugation is a homomorphism. -/
theorem homeoCongr_inv (e : M ≃ₜ N) (φ : M ≃ₜ M) :
    (homeoCongr e φ)⁻¹ = homeoCongr e φ⁻¹ := (map_inv (homeoCongr e) φ).symm

/-- Conjugating by the identity homeomorphism is the identity isomorphism. -/
@[simp]
theorem homeoCongr_refl : homeoCongr (_root_.Homeomorph.refl M) = MulEquiv.refl (M ≃ₜ M) := by
  ext φ x
  simp

/-- Conjugation is functorial: conjugating by a composite homeomorphism is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem homeoCongr_trans (e : M ≃ₜ N) (e' : N ≃ₜ P) :
    homeoCongr (e.trans e') = (homeoCongr e).trans (homeoCongr e') := by
  ext φ x
  simp

/-- The isomorphism conjugating by `e.symm` is the inverse of the one conjugating by `e`. -/
@[simp, grind =]
theorem homeoCongr_symm (e : M ≃ₜ N) : (homeoCongr e).symm = homeoCongr e.symm := by
  ext ψ x
  rfl

end Homeomorph

end TauCeti
