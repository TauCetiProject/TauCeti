/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Topology.Category.TopCat.GlueData.Star

/-!
# Star gluings of manifolds

The star gluing `TauCeti.starGlueData ψ` attaches pieces `U i` to a centre `X` by homeomorphisms
`ψ i : W i ≃ₜ A i` between open subsets, and glues two pieces along the points they attach to the
same points of `X`. When `X` and the pieces are charted spaces, every piece carries its own atlas
and every overlap the atlas of an open subset of its piece. If every `ψ i` is a `C^n` local
diffeomorphism, hence a `C^n` diffeomorphism from `W i` onto `A i`, then the star gluing is a
compatible gluing (`TauCeti.isCompatible_starGlueData`): both maps out of an overlap are, after
following the attaching maps into `X`, inclusions of open subsets of `X`.

The general results on compatible gluings then apply to star gluings without further work. If the
pieces are `C^n` manifolds, `TopCat.GlueData.IsCompatible.isManifold` makes the glued space a
`C^n` manifold for the glued atlas `TopCat.GlueData.chartedSpace`, and
`TopCat.GlueData.IsCompatible.isLocalDiffeomorph_ι` makes every canonical map from a piece a
`C^n` local diffeomorphism. Taking a hub, the centre itself attached by the identity, together
with finitely many arms gives the finite star gluings, whose arms with disjoint images in the hub
meet only the hub (`TauCeti.nonempty_starGlueData_V_iff`). For `𝕜 = ℂ` these glue complex
manifolds along biholomorphisms.

## Main declarations

* `TauCeti.isLocalDiffeomorph_starTransition`: the transitions of a star gluing along local
  diffeomorphisms are local diffeomorphisms.
* `TauCeti.isCompatible_starGlueData`: a star gluing along local diffeomorphisms is compatible.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {J : Type u} {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {U : J → Type u}
  [∀ i, TopologicalSpace (U i)] [∀ i, ChartedSpace H (U i)] {W : ∀ i, Opens (U i)}
  {A : J → Opens X} (ψ : ∀ i, W i ≃ₜ A i)

-- The indices below have type `(starGlueData ψ).J`, which is `J` by `starGlueData_J`, so that
-- these instances apply to the families of instances in `TopCat.GlueData.IsCompatible`. The
-- instances of the family indexed by `J` are applied to them directly for the same reason.

/-- Each piece of a star gluing carries its own atlas. -/
noncomputable instance instChartedSpaceStarGlueDataU (i : (starGlueData ψ).J) :
    ChartedSpace H ((starGlueData ψ).U i) :=
  (inferInstance : ∀ i, ChartedSpace H (U i)) i

/-- The overlap of the pieces `i` and `j` of a star gluing carries the atlas of the open subset
`starOverlap ψ i j` of the piece `i`. -/
noncomputable instance instChartedSpaceStarGlueDataV
    (p : (starGlueData ψ).J × (starGlueData ψ).J) : ChartedSpace H ((starGlueData ψ).V p) :=
  (inferInstance : ∀ i j, ChartedSpace H (starOverlap ψ i j)) p.1 p.2

/-- Each piece of a star gluing of `C^n` manifolds is a `C^n` manifold. -/
instance instIsManifoldStarGlueDataU [∀ i, IsManifold I n (U i)] (i : (starGlueData ψ).J) :
    IsManifold I n ((starGlueData ψ).U i) :=
  (inferInstance : ∀ i, IsManifold I n (U i)) i

variable {ψ}

/-- On the overlap of distinct pieces `i` and `j`, the attaching map `ψ i` into the centre is a
`C^n` local diffeomorphism, if `ψ i` is one. -/
private theorem isLocalDiffeomorph_apply_inclusion_starOverlap {i j : J} (hij : i ≠ j)
    (hψ : IsLocalDiffeomorph I I n (ψ i)) :
    IsLocalDiffeomorph I I n fun y : starOverlap ψ i j ↦
      (ψ i (Opens.inclusion (starOverlap_le hij) y) : X) := fun y ↦ by
  -- The inclusion of the overlap into `W i` is a local diffeomorphism, since its composite with
  -- the inclusion of `W i` is the inclusion of the overlap.
  have hincl : IsLocalDiffeomorphAt I I n (Opens.inclusion (starOverlap_le (ψ := ψ) hij)) y :=
    IsLocalDiffeomorphAt.of_comp_left (f := (Subtype.val : W i → U i))
      (isLocalDiffeomorph_subtype_val y) (isLocalDiffeomorph_subtype_val _)
      (continuous_inclusion _).continuousAt
  exact (hincl.comp (hg := hψ _)).comp (hg := isLocalDiffeomorph_subtype_val _)

/-- **The transitions of a star gluing are local diffeomorphisms.** If every attaching map `ψ i` is
a `C^n` local diffeomorphism, then so is every transition `ψ j⁻¹ ∘ ψ i` between overlaps. -/
theorem isLocalDiffeomorph_starTransition (hψ : ∀ i, IsLocalDiffeomorph I I n (ψ i)) (i j : J) :
    IsLocalDiffeomorph I I n (starTransition ψ i j) := by
  by_cases hij : i = j
  · subst hij
    rw [starTransition_self, ContinuousMap.coe_id]
    exact (Diffeomorph.refl I _ n).isLocalDiffeomorph
  -- Followed by the attaching map `ψ j`, the transition is the attaching map `ψ i`.
  refine fun x ↦ IsLocalDiffeomorphAt.of_comp_left
    (f := fun y : starOverlap ψ j i ↦ (ψ j (Opens.inclusion (starOverlap_le (Ne.symm hij)) y) : X))
    ?_ (isLocalDiffeomorph_apply_inclusion_starOverlap (Ne.symm hij) (hψ j) _)
    (starTransition ψ i j).continuous.continuousAt
  have h : (fun y : starOverlap ψ j i ↦
      (ψ j (Opens.inclusion (starOverlap_le (Ne.symm hij)) y) : X)) ∘ starTransition ψ i j =
      fun y : starOverlap ψ i j ↦ (ψ i (Opens.inclusion (starOverlap_le hij) y) : X) :=
    funext fun y ↦ apply_starTransition y _ _
  rw [h]
  exact isLocalDiffeomorph_apply_inclusion_starOverlap hij (hψ i) x

/-- **Star gluings along local diffeomorphisms are compatible.** If every attaching map `ψ i` is a
`C^n` local diffeomorphism from the open subset `W i` of its piece onto the open subset `A i` of
the centre, then the pieces and overlaps of the star gluing are `C^n` compatible. -/
theorem isCompatible_starGlueData (hψ : ∀ i, IsLocalDiffeomorph I I n (ψ i)) :
    (starGlueData ψ).IsCompatible I n :=
  -- By `starGlueData_f` and `starGlueData_t`, each map `f i j` is the inclusion of the open
  -- subset `starOverlap ψ i j` and each transition `t i j` is `starTransition ψ i j`. The
  -- inclusions are stated for indices in `J` and then read at the indices of `starGlueData ψ`.
  have hf (i j : J) : IsLocalDiffeomorph I I n (Subtype.val : starOverlap ψ i j → U i) :=
    isLocalDiffeomorph_subtype_val
  .of_isLocalDiffeomorph_t hf fun i j : J ↦ isLocalDiffeomorph_starTransition hψ i j

end TauCeti
