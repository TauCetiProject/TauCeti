/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice

/-!
# Comma simplicial sets and their cones

For `i : A ⟶ B` and a vertex `b` of `B`, `SSet.comma i b` is the pullback
`A ×_B B_{b/}`. It parametrizes vertices of `A` together with arrows from `b` to
their images, including their higher simplices. The universal property of the coslice
gives a cone `Δ[0] ⋆ comma i b ⟶ B` on its diagram in `B`, with apex `b`.

`SSet.comma.lift` and `SSet.comma.hom_ext` express the universal property using
maps to `A` and cones in `B`. Reindexing the map to `B` induces maps of comma
simplicial sets, compatible with these cones.

## References

* J. Lurie, *Higher Topos Theory*, §§1.2.9, 4.3.2–4.3.3.
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

variable {A B : SSet.{u}}

/-- The comma simplicial set `A ×_B B_{b/}` of a map `i : A ⟶ B` under a vertex `b`.
Its projection to `A` indexes the pointwise right Kan extension formula at `b`. -/
noncomputable def comma (i : A ⟶ B) (b : B _⦋0⦌) : SSet.{u} :=
  pullback i (coslice.π (const b : Δ[0] ⟶ B))

namespace comma

variable (i : A ⟶ B) (b : B _⦋0⦌)

/-- The projection from the comma simplicial set to the source of `i`. -/
noncomputable def π : comma i b ⟶ A :=
  pullback.fst _ _

/-- The projection remembering the arrow in `B` with source `b`. -/
noncomputable def toCoslice : comma i b ⟶ coslice (const b : Δ[0] ⟶ B) :=
  pullback.snd _ _

/-- The defining square of the comma simplicial set is a pullback. -/
theorem isPullback : IsPullback (π i b) (toCoslice i b) i
    (coslice.π (const b : Δ[0] ⟶ B)) :=
  IsPullback.of_hasPullback _ _

/-- The tautological cone in `B` with apex `b` over the comma diagram. -/
noncomputable def coneMap : join Δ[0] (comma i b) ⟶ B :=
  (coslice.homEquiv (toCoslice i b)).val

@[reassoc (attr := simp)]
lemma inl_coneMap : join.inl _ _ ≫ coneMap i b = const b :=
  (coslice.homEquiv (toCoslice i b)).property

@[reassoc (attr := simp)]
lemma inr_coneMap : join.inr _ _ ≫ coneMap i b = π i b ≫ i := by
  rw [coneMap, ← coslice.comp_π]
  exact (isPullback i b).w.symm

variable {i b} {X : SSet.{u}}

/-- A map to `A` together with a cone from `b` to its image in `B` determines a
map to the comma simplicial set. -/
noncomputable def lift (a : X ⟶ A) (c : join Δ[0] X ⟶ B)
    (hc₀ : join.inl _ _ ≫ c = const b) (hc₁ : join.inr _ _ ≫ c = a ≫ i) : X ⟶ comma i b :=
  pullback.lift a (coslice.homEquiv.symm ⟨c, hc₀⟩) (by
    rw [coslice.comp_π, Equiv.apply_symm_apply, hc₁])

@[reassoc (attr := simp)]
lemma lift_π (a : X ⟶ A) (c : join Δ[0] X ⟶ B) (hc₀ hc₁) :
    lift a c hc₀ hc₁ ≫ π i b = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_toCoslice (a : X ⟶ A) (c : join Δ[0] X ⟶ B) (hc₀ hc₁) :
    lift a c hc₀ hc₁ ≫ toCoslice i b = coslice.homEquiv.symm ⟨c, hc₀⟩ :=
  pullback.lift_snd _ _ _

/-- The cone induced by a lift is the supplied cone. -/
@[reassoc (attr := simp)]
lemma map_lift_coneMap (a : X ⟶ A) (c : join Δ[0] X ⟶ B) (hc₀ hc₁) :
    join.map (𝟙 _) (lift a c hc₀ hc₁) ≫ coneMap i b = c := by
  rw [coneMap, ← coslice.homEquiv_comp_coe]
  rw [lift_toCoslice, Equiv.apply_symm_apply]

/-- Maps to the comma simplicial set are determined by their projections to `A`
and their associated cones in `B`. -/
@[ext]
lemma hom_ext {f g : X ⟶ comma i b} (hπ : f ≫ π i b = g ≫ π i b)
    (hc : join.map (𝟙 _) f ≫ coneMap i b = join.map (𝟙 _) g ≫ coneMap i b) : f = g := by
  apply (isPullback i b).hom_ext hπ
  apply coslice.hom_ext
  simpa only [coslice.homEquiv_comp_coe, coneMap] using hc

variable {A' A'' : SSet.{u}} {i' : A' ⟶ B} {i'' : A'' ⟶ B}

/-- Reindexing a map to `B` induces a map of its comma simplicial sets under `b`. -/
noncomputable def map (a : A' ⟶ A) (h : a ≫ i = i') : comma i' b ⟶ comma i b :=
  lift (π i' b ≫ a) (coneMap i' b) (inl_coneMap i' b) (by simp [h])

@[reassoc (attr := simp)]
lemma map_π (a : A' ⟶ A) (h : a ≫ i = i') : map a h ≫ π i b = π i' b ≫ a :=
  lift_π _ _ _ _

@[reassoc (attr := simp)]
lemma map_coneMap (a : A' ⟶ A) (h : a ≫ i = i') :
    join.map (𝟙 _) (map a h (b := b)) ≫ coneMap i b = coneMap i' b :=
  map_lift_coneMap _ _ _ _

@[simp]
lemma map_id : map (𝟙 A) (Category.id_comp i) (b := b) = 𝟙 (comma i b) := by
  apply hom_ext <;> simp

@[reassoc (attr := simp)]
lemma map_comp (a : A' ⟶ A) (h : a ≫ i = i') (a' : A'' ⟶ A') (h' : a' ≫ i' = i'') :
    map a' h' (b := b) ≫ map a h = map (a' ≫ a) (by simp [h, h']) := by
  apply hom_ext
  · simp
  · rw [← Category.id_comp (𝟙 Δ[0]), join.map_comp_assoc]
    simp

end comma

end SSet
