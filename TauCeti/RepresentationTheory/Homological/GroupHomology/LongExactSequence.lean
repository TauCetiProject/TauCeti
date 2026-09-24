/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Naturality of the connecting map in group homology

Mathlib's `groupHomology.δ` is the connecting map `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`, `j + 1 = i`, of the
long exact sequence of a short exact sequence `X` of `G`-representations. This file shows it is
natural with respect to change of group: given `f : G →* H`, a short exact sequence `Y` of
`H`-representations, and a morphism `Φ : X ⟶ Res_f Y` of short complexes, the square

`Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`
`    ↓              ↓`
`Hᵢ(H, Y₃) ⟶ Hⱼ(H, Y₁)`

formed by the two connecting maps and the change-of-group maps `groupHomology.map f Φ.τᵢ`
commutes.

Taking `f` to be the identity recovers naturality of `δ` for a morphism of short exact sequences
of `G`-representations. The general case is what compares connecting maps across a change of
group, for instance across Shapiro's isomorphism, whose inverse is the change-of-group map along a
subgroup inclusion (`TauCeti.groupHomology.indIso_inv`).

## Main definitions

* `TauCeti.groupHomology.chainsMapShortComplex`: the morphism of short complexes of chain
  complexes induced by a morphism `X ⟶ Res_f Y` along `f : G →* H`; its components are
  `groupHomology.chainsMap f Φ.τᵢ` (`chainsMapShortComplex_τ₁` and its siblings).

## Main results

* `TauCeti.groupHomology.δ_naturality`: the connecting map of group homology commutes with
  change-of-group maps.
-/

public section

universe u

open CategoryTheory Rep ShortComplex

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

section Naturality

variable (f : G →* H) {X : ShortComplex (Rep.{u} k G)} {Y : ShortComplex (Rep.{u} k H)}

/-- A morphism `Φ : X ⟶ Res_f Y` of short complexes of representations, along a group
homomorphism `f : G →* H`, induces a morphism between the short complexes of inhomogeneous chain
complexes, given in each position by `groupHomology.chainsMap f`. -/
noncomputable def chainsMapShortComplex (Φ : X ⟶ Y.map (resFunctor f)) :
    X.map (chainsFunctor k G) ⟶ Y.map (chainsFunctor k H) where
  τ₁ := chainsMap f Φ.τ₁
  τ₂ := chainsMap f Φ.τ₂
  τ₃ := chainsMap f Φ.τ₃
  -- The middle terms of the `Eq.trans` chains agree only up to definitional unfolding:
  -- `chainsMap_comp` composes along `(MonoidHom.id H).comp f` and `f.comp (MonoidHom.id G)`,
  -- which unfold to `f`; `resFunctor (MonoidHom.id _)` acts as the identity on morphisms; and
  -- `(Y.map (resFunctor f)).f` unfolds to `(resFunctor f).map Y.f`. Mathlib's `chainsFunctor`
  -- relies on the same unfolding (its `map_comp` is `chainsMap_comp (MonoidHom.id G)
  -- (MonoidHom.id G)`), so no dependent rewrite through `groupHomology.congr` is needed.
  comm₁₂ :=
    (chainsMap_comp f (MonoidHom.id H) Φ.τ₁ Y.f).symm.trans
      ((congrArg (chainsMap f) Φ.comm₁₂).trans (chainsMap_comp (MonoidHom.id G) f X.f Φ.τ₂))
  comm₂₃ :=
    (chainsMap_comp f (MonoidHom.id H) Φ.τ₂ Y.g).symm.trans
      ((congrArg (chainsMap f) Φ.comm₂₃).trans (chainsMap_comp (MonoidHom.id G) f X.g Φ.τ₃))

@[simp]
theorem chainsMapShortComplex_τ₁ (Φ : X ⟶ Y.map (resFunctor f)) :
    (chainsMapShortComplex f Φ).τ₁ = chainsMap f Φ.τ₁ := by
  rw [chainsMapShortComplex.eq_def]

@[simp]
theorem chainsMapShortComplex_τ₂ (Φ : X ⟶ Y.map (resFunctor f)) :
    (chainsMapShortComplex f Φ).τ₂ = chainsMap f Φ.τ₂ := by
  rw [chainsMapShortComplex.eq_def]

@[simp]
theorem chainsMapShortComplex_τ₃ (Φ : X ⟶ Y.map (resFunctor f)) :
    (chainsMapShortComplex f Φ).τ₃ = chainsMap f Φ.τ₃ := by
  rw [chainsMapShortComplex.eq_def]

/-- **The connecting map of group homology is natural with respect to change of group.** For short
exact sequences `X` of `G`-representations and `Y` of `H`-representations, and a morphism
`Φ : X ⟶ Res_f Y` along `f : G →* H`, the connecting maps commute with the change-of-group maps
`groupHomology.map f`. -/
@[reassoc]
theorem δ_naturality (hX : X.ShortExact) (hY : Y.ShortExact) (Φ : X ⟶ Y.map (resFunctor f))
    (i j : ℕ) (hij : j + 1 = i) :
    δ hX i j hij ≫ map f Φ.τ₁ j = map f Φ.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (chainsMapShortComplex f Φ)
    (map_chainsFunctor_shortExact hX) (map_chainsFunctor_shortExact hY) i j hij

end Naturality

end TauCeti.groupHomology
