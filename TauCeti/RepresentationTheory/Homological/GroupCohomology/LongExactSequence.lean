/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Naturality of the connecting map in group cohomology under change of group

Mathlib's `groupCohomology.δ` is the connecting map `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`, `i + 1 = j`, of the
long exact sequence of a short exact sequence `X` of `G`-representations, and
`groupCohomology.δ_naturality` states its naturality for a morphism of short exact sequences of
`G`-representations — that is, along the identity of `G`. This file removes that restriction.
Given `f : G →* H`, a short exact sequence `Y` of `H`-representations, a short exact sequence `X`
of `G`-representations, and a morphism `Φ : Res_f Y ⟶ X` of short complexes, the square

`Hⁱ(H, Y₃) ⟶ Hʲ(H, Y₁)`
`    ↓              ↓`
`Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`

formed by the two connecting maps and the change-of-group maps `groupCohomology.map f Φ.τᵢ`
commutes. Restriction to a subgroup and inflation from a quotient are both change-of-group maps,
so this contains the compatibility of `δ` with each of them.

## Main definitions

* `TauCeti.groupCohomology.cochainsMapShortComplex`: the morphism of short complexes of cochain
  complexes induced by a morphism `Res_f Y ⟶ X` along `f : G →* H`; its components are
  `groupCohomology.cochainsMap f Φ.τᵢ` (`cochainsMapShortComplex_τ₁` and its siblings).

## Main results

* `TauCeti.groupCohomology.δ_naturality`: the connecting map of group cohomology commutes with
  change-of-group maps.

## References

* The restriction and inflation cases are `rest_δ_naturality`
  (`ClassFieldTheory/Cohomology/Functors/Restriction.lean`) and `infl_δ_naturality`
  (`ClassFieldTheory/Cohomology/Functors/Inflation.lean`) in `kbuzzard/ClassFieldTheory`, commit
  `ccc3323c6750abca25b49b35106f54eb3a398509` (Apache-2.0), proved by the same reduction to
  `HomologicalComplex.HomologySequence.δ_naturality`; this file generalises them to an arbitrary
  morphism `Φ : Res_f Y ⟶ X`.
-/

public section

universe u

open CategoryTheory Rep ShortComplex

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  (f : G →* H) {X : ShortComplex (Rep.{u} k G)} {Y : ShortComplex (Rep.{u} k H)}

/-- A morphism `Φ : Res_f Y ⟶ X` of short complexes of representations, along a group
homomorphism `f : G →* H`, induces a morphism between the short complexes of inhomogeneous
cochain complexes, given in each position by `groupCohomology.cochainsMap f`. -/
noncomputable def cochainsMapShortComplex (Φ : Y.map (resFunctor f) ⟶ X) :
    Y.map (cochainsFunctor k H) ⟶ X.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f Φ.τ₁
  τ₂ := cochainsMap f Φ.τ₂
  τ₃ := cochainsMap f Φ.τ₃
  -- The middle terms of the `Eq.trans` chains agree only up to definitional unfolding:
  -- `cochainsMap_comp` composes along `f.comp (MonoidHom.id G)` and `(MonoidHom.id H).comp f`,
  -- which unfold to `f`; `resFunctor (MonoidHom.id _)` acts as the identity on morphisms; and
  -- `(Y.map (resFunctor f)).f` unfolds to `(resFunctor f).map Y.f`. Mathlib's `cochainsFunctor`
  -- relies on the same unfolding (its `map_comp` is `cochainsMap_comp (MonoidHom.id G)
  -- (MonoidHom.id G)`), so no dependent rewrite through `groupCohomology.congr` is needed.
  comm₁₂ :=
    (cochainsMap_comp f (MonoidHom.id G) Φ.τ₁ X.f).symm.trans
      ((congrArg (cochainsMap f) Φ.comm₁₂).trans (cochainsMap_comp (MonoidHom.id H) f Y.f Φ.τ₂))
  comm₂₃ :=
    (cochainsMap_comp f (MonoidHom.id G) Φ.τ₂ X.g).symm.trans
      ((congrArg (cochainsMap f) Φ.comm₂₃).trans (cochainsMap_comp (MonoidHom.id H) f Y.g Φ.τ₃))

/-- The first component of `cochainsMapShortComplex f Φ` is the cochain map induced by the pair `(f,
Φ.τ₁)`. -/
@[simp]
theorem cochainsMapShortComplex_τ₁ (Φ : Y.map (resFunctor f) ⟶ X) :
    (cochainsMapShortComplex f Φ).τ₁ = cochainsMap f Φ.τ₁ := by
  rw [cochainsMapShortComplex.eq_def]

/-- The second component of `cochainsMapShortComplex f Φ` is the cochain map induced by the pair
`(f, Φ.τ₂)`. -/
@[simp]
theorem cochainsMapShortComplex_τ₂ (Φ : Y.map (resFunctor f) ⟶ X) :
    (cochainsMapShortComplex f Φ).τ₂ = cochainsMap f Φ.τ₂ := by
  rw [cochainsMapShortComplex.eq_def]

/-- The third component of `cochainsMapShortComplex f Φ` is the cochain map induced by the pair `(f,
Φ.τ₃)`. -/
@[simp]
theorem cochainsMapShortComplex_τ₃ (Φ : Y.map (resFunctor f) ⟶ X) :
    (cochainsMapShortComplex f Φ).τ₃ = cochainsMap f Φ.τ₃ := by
  rw [cochainsMapShortComplex.eq_def]

/-- **The connecting map of group cohomology is natural with respect to change of group.** For
short exact sequences `Y` of `H`-representations and `X` of `G`-representations, and a morphism
`Φ : Res_f Y ⟶ X` along `f : G →* H`, the connecting maps commute with the change-of-group maps
`groupCohomology.map f`. -/
@[reassoc]
theorem δ_naturality (hY : Y.ShortExact) (hX : X.ShortExact) (Φ : Y.map (resFunctor f) ⟶ X)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hY i j hij ≫ map f Φ.τ₁ j = map f Φ.τ₃ i ≫ δ hX i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f Φ)
    (map_cochainsFunctor_shortExact hY) (map_cochainsFunctor_shortExact hX) i j hij

end TauCeti.groupCohomology
