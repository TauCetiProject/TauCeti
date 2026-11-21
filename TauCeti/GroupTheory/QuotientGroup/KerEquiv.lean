/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Evaluating the first isomorphism theorem and descending along surjections

Mathlib packages the first isomorphism theorem for a surjective homomorphism `φ : G →* M` as
`QuotientGroup.quotientKerEquivOfSurjective φ hφ : G ⧸ φ.ker ≃* M`. It is defined through
`QuotientGroup.quotientKerEquivOfRightInverse` applied to a right inverse extracted from `hφ`
by choice, so evaluating it on a class otherwise means unfolding that noncomputable
implementation. Likewise, `QuotientGroup.quotientKerEquivRange φ : G ⧸ φ.ker ≃* φ.range` is
built with `MulEquiv.ofBijective` from `QuotientGroup.rangeKerLift`, and Mathlib states no
evaluation rule for it.

This file records these computation rules on classes, so that users never have to unfold the
definitions. The first two are the group-theoretic counterparts of Mathlib's
`RingHom.quotientKerEquivOfSurjective_apply_mk` and
`RingHom.quotientKerEquivOfSurjective_symm_apply`; all three belong beside their definitions in
Mathlib.

It also provides `TauCeti.QuotientGroup.descOfSurjective`: descending a monoid-valued
homomorphism `φ : P →* M` along any surjective group homomorphism `p : P →* Q` whose kernel is
contained in `φ.ker` (whereas `MonoidHom.liftOfSurjective` requires a group target).

## Main statements

* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* M` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply`: the inverse sends
  `φ g` back to the class of `g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply`.
* `TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* φ.range` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivRange_symm_apply`: the inverse sends `φ g` back to the
  class of `g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivRange_symm_apply`.
* `TauCeti.QuotientGroup.descOfSurjective`: descend a monoid-valued homomorphism along a
  surjective group homomorphism, with `_apply`, `_comp`, `_unique`, kernel, and injectivity laws
  (and additive counterparts under `TauCeti.QuotientAddGroup`).

The first isomorphism theorem for the composite `H → G → G ⧸ N` of the inclusion of a subgroup
and a quotient map identifies `H ⧸ N.subgroupOf H` with the image of `H` in `G ⧸ N`; this is
`Subgroup.quotientSubgroupOfMulEquivMap`, with evaluation rule
`Subgroup.coe_quotientSubgroupOfMulEquivMap_mk`.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G M : Type*} [Group G] [Group M] (φ : G →* M) (hφ : Function.Surjective φ)

/-- The first isomorphism theorem for a surjective homomorphism sends the class of `g` to
`φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk
  /-- The first isomorphism theorem for a surjective additive homomorphism sends the class of
  `g` to `φ g`. -/]
theorem quotientKerEquivOfSurjective_apply_mk (g : G) :
    QuotientGroup.quotientKerEquivOfSurjective φ hφ g = φ g :=
  rfl

/-- The inverse of the first isomorphism theorem sends `φ g` to the class of `g`. -/
@[to_additive (attr := simp)
  TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply
  /-- The inverse of the additive first isomorphism theorem sends `φ g` to the class of `g`. -/]
theorem quotientKerEquivOfSurjective_symm_apply (g : G) :
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ g) = (g : G ⧸ φ.ker) :=
  (MulEquiv.symm_apply_eq _).2 (quotientKerEquivOfSurjective_apply_mk φ hφ g).symm

/-- The first isomorphism theorem onto the range sends the class of `g` to `φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk
  /-- The first isomorphism theorem onto the range of an additive homomorphism sends the class
  of `g` to `φ g`. -/]
theorem quotientKerEquivRange_apply_mk (g : G) :
    QuotientGroup.quotientKerEquivRange φ g = ⟨φ g, g, rfl⟩ :=
  rfl

/-- The inverse of the first isomorphism theorem onto the range sends `φ g` to the class of
`g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivRange_symm_apply
  /-- The inverse of the first isomorphism theorem onto the range of an additive homomorphism
  sends `φ g` to the class of `g`. -/]
theorem quotientKerEquivRange_symm_apply (g : G) :
    (QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict g) = (g : G ⧸ φ.ker) :=
  (MulEquiv.symm_apply_eq _).2 (quotientKerEquivRange_apply_mk φ g).symm

section DescOfSurjective

variable {P Q M' : Type*} [Group P] [Group Q] [Monoid M']
  (p : P →* Q) (hp : Function.Surjective p) (ψ : P →* M') (hψ : p.ker ≤ ψ.ker)

/-- Descend a monoid-valued homomorphism along a surjective group homomorphism whose kernel is
contained in `ψ.ker`. Unlike `MonoidHom.liftOfSurjective`, the target `M'` need only be a
monoid. -/
@[to_additive TauCeti.QuotientAddGroup.descOfSurjective
  /-- Descend an additive-monoid-valued homomorphism along a surjective additive group
  homomorphism whose kernel is contained in `ψ.ker`. -/]
noncomputable def descOfSurjective : Q →* M' :=
  (QuotientGroup.lift p.ker ψ hψ).comp (QuotientGroup.liftEquiv p.ker hp rfl).symm.toMonoidHom

/-- The descended homomorphism agrees with `ψ` after precomposing with `p`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.descOfSurjective_apply
  /-- The descended additive homomorphism agrees with `ψ` after precomposing with `p`. -/]
theorem descOfSurjective_apply (g : P) :
    descOfSurjective p hp ψ hψ (p g) = ψ g := by
  have hmk : (QuotientGroup.liftEquiv p.ker hp rfl).symm (p g) = (g : P ⧸ p.ker) :=
    (QuotientGroup.liftEquiv p.ker hp rfl).symm_apply_eq.mpr
      (QuotientGroup.liftEquiv_coe p.ker hp rfl g).symm
  dsimp only [descOfSurjective]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hmk, QuotientGroup.lift_mk]

/-- Precomposing the descended homomorphism with `p` recovers `ψ`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.descOfSurjective_comp
  /-- Precomposing the descended additive homomorphism with `p` recovers `ψ`. -/]
theorem descOfSurjective_comp :
    (descOfSurjective p hp ψ hψ).comp p = ψ :=
  MonoidHom.ext (descOfSurjective_apply p hp ψ hψ)

/-- A homomorphism out of the target of a surjection is uniquely determined by its precomposition
with `p`. -/
@[to_additive TauCeti.QuotientAddGroup.descOfSurjective_unique
  /-- An additive homomorphism out of the target of a surjection is uniquely determined by its
  precomposition with `p`. -/]
theorem descOfSurjective_unique (χ : Q →* M') (hχ : ∀ g, χ (p g) = ψ g) :
    χ = descOfSurjective p hp ψ hψ := by
  ext q
  obtain ⟨g, rfl⟩ := hp q
  rw [hχ, descOfSurjective_apply]

/-- The kernel of the descended homomorphism is the image of `ψ.ker` under `p`. -/
@[to_additive TauCeti.QuotientAddGroup.ker_descOfSurjective
  /-- The kernel of the descended additive homomorphism is the image of `ψ.ker` under `p`. -/]
theorem ker_descOfSurjective :
    (descOfSurjective p hp ψ hψ).ker = ψ.ker.map p :=
  MonoidHom.ker_eq_map_of_comp_eq hp (descOfSurjective_comp p hp ψ hψ)

/-- The descended homomorphism is injective if and only if `ψ.ker = p.ker`. -/
@[to_additive TauCeti.QuotientAddGroup.injective_descOfSurjective_iff
  /-- The descended additive homomorphism is injective if and only if `ψ.ker = p.ker`. -/]
theorem injective_descOfSurjective_iff :
    Function.Injective (descOfSurjective p hp ψ hψ) ↔ ψ.ker = p.ker := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_descOfSurjective, Subgroup.map_eq_bot_iff]
  exact ⟨fun h ↦ le_antisymm h hψ, fun h ↦ h.le⟩

end DescOfSurjective

end QuotientGroup

end TauCeti

namespace Subgroup

/-- For a normal subgroup `N` and any subgroup `H` of `G`, the quotient `H ⧸ N.subgroupOf H` is
isomorphic to the image `H.map (mk' N)` of `H` in `G ⧸ N`: this is the first isomorphism theorem
for the composite `H → G → G ⧸ N`, whose kernel is `N.subgroupOf H`. -/
noncomputable def quotientSubgroupOfMulEquivMap {G : Type*} [Group G] (N H : Subgroup G)
    [N.Normal] : H ⧸ N.subgroupOf H ≃* H.map (QuotientGroup.mk' N) :=
  QuotientGroup.liftEquiv (N.subgroupOf H) ((QuotientGroup.mk' N).subgroupMap_surjective H)
    (by rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- `quotientSubgroupOfMulEquivMap` sends the class of `h : H` to the class of `h` in `G ⧸ N`. -/
@[simp]
theorem coe_quotientSubgroupOfMulEquivMap_mk {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
    (h : H) :
    (quotientSubgroupOfMulEquivMap N H (h : H ⧸ N.subgroupOf H) : G ⧸ N) = (h : G) :=
  (rfl)

end Subgroup
