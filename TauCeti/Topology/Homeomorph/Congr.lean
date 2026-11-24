/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Transporting the self-homeomorphism group along a homeomorphism

A homeomorphism `e : M ≃ₜ N` conjugates self-homeomorphisms of `M` into self-homeomorphisms of `N`
by `φ ↦ e ∘ φ ∘ e⁻¹`. Because this preserves composition, it is a group isomorphism
`(M ≃ₜ M) ≃* (N ≃ₜ N)` between the self-homeomorphism groups. This file records that isomorphism,
`Homeomorph.homeoCongr`, its pointwise action, and its functoriality: it is the identity on
`Homeomorph.refl` and respects `Homeomorph.trans` and `Homeomorph.symm`. Being a `MulEquiv`, it
sends inverses to inverses by the generic `map_inv`.

This is the topological analogue of `Equiv.permCongr` (`Mathlib/Logic/Equiv/Defs.lean`), the
conjugation isomorphism of permutation groups, and is the target of the forgetful naturality of the
diffeomorphism-level `Diffeomorph.diffCongr` in
`TauCeti.Geometry.Diffeomorphism.Congr`.

The unit, products, inverses and conjugates of self-homeomorphisms are also expressed through
composition of the underlying continuous maps, extending Mathlib's `Homeomorph.coe_trans` to the
group structure.

## Main definitions

* `Homeomorph.homeoCongr e`: the group isomorphism `(M ≃ₜ M) ≃* (N ≃ₜ N)` conjugating
  self-homeomorphisms by a homeomorphism `e : M ≃ₜ N`.

## Main results

* `Homeomorph.homeoCongr_apply_apply`: the pointwise action
  `homeoCongr e φ x = e (φ (e.symm x))`.
* `Homeomorph.homeoCongr_refl`, `Homeomorph.homeoCongr_trans`, and
  `Homeomorph.homeoCongr_symm`: the functoriality of `homeoCongr` on the groupoid of
  homeomorphisms.
* `Homeomorph.ofClass_one`, `Homeomorph.ofClass_mul`, `Homeomorph.ofClass_inv`, and
  `Homeomorph.ofClass_homeoCongr`: the continuous maps underlying `1`, `f * g`, `f⁻¹` and
  `homeoCongr e f`.
-/

public section

variable {M : Type*} [TopologicalSpace M]
  {N : Type*} [TopologicalSpace N]
  {P : Type*} [TopologicalSpace P]

namespace Homeomorph

/-- Conjugation by a homeomorphism `e : M ≃ₜ N` as a group isomorphism between the
self-homeomorphism groups: `homeoCongr e φ = e ∘ φ ∘ e⁻¹`. This is the homeomorphism analogue of
`Equiv.permCongrHom` and the target of the forgetful naturality of `Diffeomorph.diffCongr`. -/
def homeoCongr (e : M ≃ₜ N) : (M ≃ₜ M) ≃* (N ≃ₜ N) where
  toFun φ := (e.symm.trans φ).trans e
  invFun ψ := (e.trans ψ).trans e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' _ _ := by ext; simp

/-- The conjugating isomorphism acts pointwise by `homeoCongr e φ x = e (φ (e.symm x))`. -/
@[simp, grind =]
theorem homeoCongr_apply_apply (e : M ≃ₜ N) (φ : M ≃ₜ M) (x : N) :
    homeoCongr e φ x = e (φ (e.symm x)) := (rfl)

/-- Conjugating by the identity homeomorphism is the identity isomorphism. -/
@[simp]
theorem homeoCongr_refl : homeoCongr (Homeomorph.refl M) = MulEquiv.refl (M ≃ₜ M) := by
  ext
  simp

/-- Conjugation is functorial: conjugating by a composite homeomorphism is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem homeoCongr_trans (e : M ≃ₜ N) (e' : N ≃ₜ P) :
    homeoCongr (e.trans e') = (homeoCongr e).trans (homeoCongr e') := by
  ext
  simp

/-- The isomorphism conjugating by `e.symm` is the inverse of the one conjugating by `e`. -/
@[simp, grind =]
theorem homeoCongr_symm (e : M ≃ₜ N) : (homeoCongr e).symm = homeoCongr e.symm := by
  ext
  rfl

/-- The continuous map underlying the unit self-homeomorphism is the identity. -/
@[simp]
theorem ofClass_one : ((1 : M ≃ₜ M) : C(M, M)) = ContinuousMap.id M :=
  (rfl)

/-- The continuous map underlying a product of self-homeomorphisms is the composite. -/
@[simp]
theorem ofClass_mul (f g : M ≃ₜ M) : ((f * g : M ≃ₜ M) : C(M, M)) = (f : C(M, M)).comp g :=
  (rfl)

/-- The continuous map underlying the inverse of a self-homeomorphism is its inverse map. -/
@[simp]
theorem ofClass_inv (f : M ≃ₜ M) : ((f⁻¹ : M ≃ₜ M) : C(M, M)) = (f.symm : C(M, M)) :=
  (rfl)

/-- The continuous map underlying a conjugate is `e ∘ φ ∘ e⁻¹`. -/
@[simp]
theorem ofClass_homeoCongr (e : M ≃ₜ N) (φ : M ≃ₜ M) :
    (homeoCongr e φ : C(N, N)) = (e : C(M, N)).comp ((φ : C(M, M)).comp e.symm) :=
  (rfl)

end Homeomorph
