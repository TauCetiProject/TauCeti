/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient

/-!
# Quotients by subgroups of the deck group

For a map `p : E → B`, every subgroup `H ≤ Deck p` acts on `E` by deck transformations, so
the projection `p` is constant on `H`-orbits. This file packages the resulting quotient
`E / H` and the induced map `E / H → B`.

This is the abstract deck-action bookkeeping behind the universal-covers roadmap Stage 2
construction `UniversalCover x₀ / H → X`: before proving that this is a connected pointed
cover with recovered subgroup `H`, one needs the quotient by an arbitrary subgroup of the deck
group and the projection it inherits from the original covering projection.

## Main declarations

* `TauCeti.Deck.SubgroupOrbitQuotient`: the quotient of `E` by a subgroup `H ≤ Deck p`.
* `TauCeti.Deck.subgroupOrbitQuotientToDeckOrbitQuotient`: the natural map
  `E / H → E / Deck p`.
* `TauCeti.Deck.subgroupOrbitQuotientToBase`: the projection `E / H → B` induced by `p`.

## References

This supplies a prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 7:
the cover associated to `H ≤ π₁(X, x₀)` is the quotient of the universal cover by `H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

/-- The quotient of the total space `E` by the action of a subgroup `H ≤ Deck p`. -/
abbrev SubgroupOrbitQuotient (p : E → B) (H : Subgroup (Deck p)) : Type _ :=
  MulAction.orbitRel.Quotient H E

/-- The orbit class of a point in the quotient by a subgroup of the deck group. -/
@[expose] def subgroupOrbitClass (H : Subgroup (Deck p)) (e : E) :
    SubgroupOrbitQuotient p H :=
  Quotient.mk'' e

/-- The subgroup-orbit quotient map sends a point to its own class. -/
@[simp]
lemma subgroupOrbitClass_eq_mk (H : Subgroup (Deck p)) (e : E) :
    subgroupOrbitClass H e = (Quotient.mk'' e : SubgroupOrbitQuotient p H) :=
  rfl

/-- Two points have the same subgroup-orbit class exactly when they lie in the same
`H`-orbit. -/
lemma subgroupOrbitClass_eq_iff (H : Subgroup (Deck p)) (e e' : E) :
    subgroupOrbitClass H e = subgroupOrbitClass H e' ↔ e ∈ MulAction.orbit H e' := by
  rw [subgroupOrbitClass_eq_mk, subgroupOrbitClass_eq_mk, Quotient.eq'',
    MulAction.orbitRel_apply]

/-- Points related by the action of a subgroup of the deck group have the same projection. -/
lemma eq_proj_of_subgroupOrbitRel (H : Subgroup (Deck p)) {e e' : E}
    (h : MulAction.orbitRel H E e e') : p e = p e' := by
  rw [MulAction.orbitRel_apply] at h
  rcases h with ⟨φ, hφ⟩
  rw [← hφ]
  -- Normalize the subgroup action to the ambient deck action so `map_proj` applies.
  change p ((φ : Deck p) • e') = p e'
  simpa only [smul_eq_apply] using map_proj (φ : Deck p) e'

/-- Inclusion of subgroups induces a map between the corresponding orbit quotients. -/
@[expose] def subgroupOrbitQuotientMap {H K : Subgroup (Deck p)} (hHK : H ≤ K) :
    SubgroupOrbitQuotient p H → SubgroupOrbitQuotient p K :=
  Quotient.map' id fun e e' h => by
    rw [MulAction.orbitRel_apply] at h ⊢
    rcases h with ⟨φ, hφ⟩
    refine ⟨⟨φ, hHK φ.2⟩, ?_⟩
    -- The same ambient deck transformation is being viewed in two subgroup actions.
    change ((φ : Deck p) • e') = e
    change ((φ : Deck p) • e') = e at hφ
    exact hφ

/-- The map induced by subgroup inclusion evaluates on representatives by the identity. -/
@[simp]
lemma subgroupOrbitQuotientMap_mk {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : E) :
    subgroupOrbitQuotientMap hHK (Quotient.mk'' e : SubgroupOrbitQuotient p H) =
      (Quotient.mk'' e : SubgroupOrbitQuotient p K) :=
  rfl

/-- The identity inclusion induces the identity on the subgroup-orbit quotient. -/
@[simp]
lemma subgroupOrbitQuotientMap_refl (H : Subgroup (Deck p)) :
    subgroupOrbitQuotientMap (le_refl H) = id := by
  ext x
  induction x using Quotient.inductionOn' with
  | h e => rfl

/-- The maps induced by subgroup inclusions compose as expected. -/
@[simp]
lemma subgroupOrbitQuotientMap_comp {H K L : Subgroup (Deck p)} (hHK : H ≤ K)
    (hKL : K ≤ L) :
    subgroupOrbitQuotientMap (hHK.trans hKL) =
      subgroupOrbitQuotientMap hKL ∘ subgroupOrbitQuotientMap hHK := by
  ext x
  induction x using Quotient.inductionOn' with
  | h e => rfl

/-- The natural map from the quotient by a subgroup of the deck group to the quotient by the
full deck group. -/
@[expose] def subgroupOrbitQuotientToDeckOrbitQuotient (H : Subgroup (Deck p)) :
    SubgroupOrbitQuotient p H → MulAction.orbitRel.Quotient (Deck p) E :=
  Quotient.map' id (MulAction.orbitRel_subgroup_le H)

/-- The map from the subgroup quotient to the full deck quotient evaluates on representatives
by the identity. -/
@[simp]
lemma subgroupOrbitQuotientToDeckOrbitQuotient_mk (H : Subgroup (Deck p)) (e : E) :
    subgroupOrbitQuotientToDeckOrbitQuotient H
      (Quotient.mk'' e : SubgroupOrbitQuotient p H) =
        (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) :=
  rfl

/-- The projection map factors through the quotient by any subgroup of the deck group. -/
@[expose] def subgroupOrbitQuotientToBase (H : Subgroup (Deck p)) :
    SubgroupOrbitQuotient p H → B :=
  Quotient.lift p fun _ _ h => eq_proj_of_subgroupOrbitRel H h

/-- The induced map from the subgroup-orbit quotient to the base evaluates on representatives
by the original projection. -/
@[simp]
lemma subgroupOrbitQuotientToBase_mk (H : Subgroup (Deck p)) (e : E) :
    subgroupOrbitQuotientToBase H (Quotient.mk'' e : SubgroupOrbitQuotient p H) = p e :=
  rfl

/-- The projection from `E / H` to the base factors through the full deck-orbit quotient. -/
lemma orbitQuotientToBase_subgroupOrbitQuotientToDeckOrbitQuotient
    (H : Subgroup (Deck p)) (x : SubgroupOrbitQuotient p H) :
    orbitQuotientToBase p (subgroupOrbitQuotientToDeckOrbitQuotient H x) =
      subgroupOrbitQuotientToBase H x := by
  induction x using Quotient.inductionOn' with
  | h e => rfl

section Topology

variable [TopologicalSpace B]

/-- A continuous projection induces a continuous map from any subgroup-orbit quotient of the
total space to the base. -/
lemma continuous_subgroupOrbitQuotientToBase (H : Subgroup (Deck p)) (hp : Continuous p) :
    Continuous (subgroupOrbitQuotientToBase H) :=
  hp.quotient_lift fun _ _ h => eq_proj_of_subgroupOrbitRel H h

/-- An open projection induces an open map from any subgroup-orbit quotient of the total space
to the base. -/
lemma isOpenMap_subgroupOrbitQuotientToBase (H : Subgroup (Deck p)) (hp : IsOpenMap p) :
    IsOpenMap (subgroupOrbitQuotientToBase H) := by
  intro V hV
  have hsurj : Function.Surjective (Quotient.mk'' : E → SubgroupOrbitQuotient p H) :=
    Quotient.mk''_surjective
  have hpre : IsOpen ((Quotient.mk'' : E → SubgroupOrbitQuotient p H) ⁻¹' V) :=
    hV.preimage continuous_quotient_mk'
  have himg : subgroupOrbitQuotientToBase H '' V =
      p '' ((Quotient.mk'' : E → SubgroupOrbitQuotient p H) ⁻¹' V) := by
    ext b
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hxV, rfl⟩
      obtain ⟨e, rfl⟩ := hsurj x
      exact ⟨e, hxV, rfl⟩
    · rintro ⟨e, heV, rfl⟩
      exact ⟨Quotient.mk'' e, heV, rfl⟩
  rw [himg]
  exact hp _ hpre

end Topology

end Deck

end TauCeti
