/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.LocalInvariantProperties
public import TauCeti.Topology.Algebra.ConstMulAction
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# (G, X)-manifolds

Let a group `G` act on a topological space `X` by homeomorphisms. Thurston's pseudogroup generated
by `G` consists of the homeomorphisms between open subsets of `X` that agree, near each point of
their domain, with the action of some element of `G`. In Mathlib's language this is a structure
groupoid on `X`, `TauCeti.smulGroupoid G X`, built from the pregroupoid
`TauCeti.smulPregroupoid G X` exactly as `contDiffGroupoid` and `conformalGroupoid` are built from
theirs.

A *(G, X)-manifold* is then a charted space `M` over `X` whose transition maps lie in this groupoid,
that is `[ChartedSpace X M] [HasGroupoid M (smulGroupoid G X)]`; no new structure is introduced.
Specialising `(G, X)` gives the classical geometric structures: Euclidean manifolds for the
isometries of Euclidean space, spherical manifolds for the orthogonal group acting on the sphere,
and hyperbolic manifolds for the isometries of hyperbolic space.

Two results connect this notion to the rest of the manifold library.

* If `X` is a `C^n` manifold modelled on `I` and `G` acts by `C^n` maps, then a (G, X)-manifold is
  a `C^n` manifold for the charts obtained by composing its `X`-valued charts with the charts of
  `X` (`TauCeti.isManifold_of_hasGroupoid_smulGroupoid`). So geometric structures are in
  particular smooth structures.
* The orbit space `X / Γ` of a free, properly discontinuous action of a group `Γ`, with the charts
  of `MulAction.instChartedSpaceQuotient`, is a (Γ, X)-manifold
  (`TauCeti.hasGroupoid_smulGroupoid_quotient`), and a (G, X)-manifold when `Γ` is a subgroup of
  `G` (`TauCeti.hasGroupoid_smulGroupoid_quotient_subgroup`). This is the source of (G, X)-manifolds
  of the form `X / Γ`. More generally, the charts pushed forward along a surjective local
  homeomorphism `X → M` whose deck transformations are locally given by `G` form a (G, X)-atlas
  (`IsLocalHomeomorph.hasGroupoid_smulGroupoid_chartedSpaceOfRightInverse`).

The deck-transformation hypothesis has the shape of the one in
`IsLocalHomeomorph.isManifold_chartedSpaceOfRightInverse`
(`TauCeti/Geometry/Manifold/Instances/Quotient.lean`), where the deck transformations are only
required to be `C^n`. The developing map and completeness of a (G, X)-structure are not treated
here.

## Main definitions

* `TauCeti.smulPregroupoid G X`: maps of `X` that agree near each point of a set with the action of
  an element of `G`.
* `TauCeti.smulGroupoid G X`: the structure groupoid of open partial homeomorphisms of `X` that are
  locally given by the action of `G`.

## Main results

* `TauCeti.mem_smulGroupoid_iff`: an open partial homeomorphism lies in `smulGroupoid G X` as soon
  as it is locally given by the action of `G`; the inverse is then automatically of the same kind.
* `TauCeti.hasGroupoid_smulGroupoid_iff`: a charted space over `X` is a (G, X)-manifold exactly
  when its transition maps are locally given by the action of `G`.
* `TauCeti.smulGroupoid_le`: a group whose action is realised by another group's action gives a
  smaller groupoid.
* `TauCeti.contMDiffOn_of_mem_smulGroupoid`: for an action by `C^n` maps, every member of
  `smulGroupoid G X` is `C^n` on its source.
* `TauCeti.isManifold_of_hasGroupoid_smulGroupoid`: a (G, X)-manifold is a `C^n` manifold when `G`
  acts by `C^n` maps on the `C^n` manifold `X`.
* `TauCeti.hasGroupoid_smulGroupoid_quotient`: the orbit space of a free, properly discontinuous
  action of `Γ` on `X` is a (Γ, X)-manifold.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton University Press,
  1997, Definitions 3.1.1 and 3.1.2 (pseudogroups and `𝒢`-manifolds) and Section 3.3 ((G, X)-
  manifolds, Examples 3.3.2, 3.3.5 and 3.3.6).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

section Pregroupoid

variable (G X : Type*) [Monoid G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The pregroupoid of maps of `X` that are locally given by the action of `G`: a map `f` has the
property on `u` if near each point of `u` it agrees with `x ↦ g • x` for some `g : G`. -/
def smulPregroupoid : Pregroupoid X where
  property f u := ∀ x ∈ u, ∃ g : G, f =ᶠ[𝓝 x] (g • ·)
  comp {f f'} {_ _} hf hf' _ _ _ x hx := by
    obtain ⟨g, hg⟩ := hf x hx.1
    obtain ⟨g', hg'⟩ := hf' (f x) hx.2
    have hcont : ContinuousAt f x := (continuous_const_smul g).continuousAt.congr hg.symm
    refine ⟨g' * g, ?_⟩
    filter_upwards [hcont.eventually hg', hg] with y hy hy'
    rw [Function.comp_apply, hy, hy', mul_smul]
  id_mem x _ := ⟨1, Eventually.of_forall fun y ↦ (one_smul G y).symm⟩
  locality {_ _} _ h x hx := by
    obtain ⟨v, -, hxv, hv⟩ := h x hx
    exact hv x ⟨hx, hxv⟩
  congr {_ _ _} hu h hf x hx := by
    obtain ⟨g, hg⟩ := hf x hx
    refine ⟨g, ?_⟩
    filter_upwards [hu.mem_nhds hx, hg] with y hy hy'
    rw [h y hy, hy']

/-- The structure groupoid of open partial homeomorphisms of `X` that are locally given by the
action of `G`. When `G` is a group, this is Thurston's pseudogroup generated by `G`, and a charted
space over `X` with this groupoid is a (G, X)-manifold. -/
def smulGroupoid : StructureGroupoid X :=
  (smulPregroupoid G X).groupoid

variable {G X}

@[simp]
theorem smulPregroupoid_property {f : X → X} {u : Set X} :
    (smulPregroupoid G X).property f u ↔ ∀ x ∈ u, ∃ g : G, f =ᶠ[𝓝 x] (g • ·) :=
  Iff.rfl

/-- If the action of each element of `G` on `X` is the action of some element of `G'`, then every
map locally given by `G` is locally given by `G'`. This applies in particular to a subgroup of `G'`
and to a group acting through a homomorphism to `G'`. -/
theorem smulGroupoid_le {G' : Type*} [Monoid G'] [MulAction G' X] [ContinuousConstSMul G' X]
    (h : ∀ g : G, ∃ g' : G', ∀ x : X, g • x = g' • x) :
    smulGroupoid G X ≤ smulGroupoid G' X :=
  groupoid_of_pregroupoid_le _ _ fun _ _ hf x hx ↦ by
    obtain ⟨g, hg⟩ := hf x hx
    obtain ⟨g', hg'⟩ := h g
    exact ⟨g', hg.trans (Eventually.of_forall hg')⟩

end Pregroupoid

section Groupoid

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- An open partial homeomorphism of `X` lies in `smulGroupoid G X` exactly when it is locally
given by the action of `G` on its source. The same condition on the inverse then holds
automatically. -/
theorem mem_smulGroupoid_iff {e : OpenPartialHomeomorph X X} :
    e ∈ smulGroupoid G X ↔ ∀ x ∈ e.source, ∃ g : G, e =ᶠ[𝓝 x] (g • ·) := by
  refine ⟨fun h ↦ smulPregroupoid_property.1 h.1, fun h ↦ ⟨h, fun y hy ↦ ?_⟩⟩
  obtain ⟨g, hg⟩ := h (e.symm y) (e.map_target hy)
  refine ⟨g⁻¹, ?_⟩
  filter_upwards [(e.continuousAt_symm hy).eventually hg, e.eventually_right_inverse hy]
    with z hz hz'
  calc e.symm z = g⁻¹ • g • e.symm z := (inv_smul_smul g _).symm
    _ = g⁻¹ • z := by rw [← hz, hz']

/-- The action of an element of `G`, as a homeomorphism of `X`, lies in `smulGroupoid G X`. -/
theorem smul_mem_smulGroupoid (g : G) :
    (Homeomorph.smul g : X ≃ₜ X).toOpenPartialHomeomorph ∈ smulGroupoid G X :=
  mem_smulGroupoid_iff.2 fun _ _ ↦ ⟨g, EventuallyEq.rfl⟩

/-- A charted space over `X` is a (G, X)-manifold exactly when each transition map between two of
its charts agrees, near each point of its source, with the action of an element of `G`. -/
theorem hasGroupoid_smulGroupoid_iff {M : Type*} [TopologicalSpace M] [ChartedSpace X M] :
    HasGroupoid M (smulGroupoid G X) ↔ ∀ e ∈ atlas X M, ∀ e' ∈ atlas X M,
      ∀ x ∈ (e.symm ≫ₕ e').source, ∃ g : G, e.symm ≫ₕ e' =ᶠ[𝓝 x] (g • ·) :=
  ⟨fun h _ he _ he' ↦ mem_smulGroupoid_iff.1 (h.compatible he he'),
    fun h ↦ ⟨fun he he' ↦ mem_smulGroupoid_iff.2 (h _ he _ he')⟩⟩

/-- The groupoid `smulGroupoid G X` is closed under restriction, so open subsets of a
(G, X)-manifold inherit the same (G, X)-structure. -/
instance : ClosedUnderRestriction (smulGroupoid G X) where
  closedUnderRestriction {_} he _ _ :=
    mem_smulGroupoid_iff.2 fun x hx ↦ mem_smulGroupoid_iff.1 he x hx.1

end Groupoid

/-! ### (G, X)-manifolds are `C^n` manifolds -/

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {G X : Type*} [Monoid G] [TopologicalSpace X] [ChartedSpace H X] [MulAction G X]
  [ContinuousConstSMul G X] [ContMDiffConstSMul I n G X]

/-- When `G` acts on `X` by `C^n` maps, every member of `smulGroupoid G X` is `C^n` on its
source. -/
theorem contMDiffOn_of_mem_smulGroupoid {e : OpenPartialHomeomorph X X}
    (he : e ∈ smulGroupoid G X) : ContMDiffOn I I n e e.source := fun x hx ↦ by
  obtain ⟨g, hg⟩ := smulPregroupoid_property.1 he.1 x hx
  exact ((contMDiff_const_smul g).contMDiffAt.congr_of_eventuallyEq hg).contMDiffWithinAt

variable (I n G) in
/-- A (G, X)-manifold, for an action of `G` by `C^n` maps on a `C^n` manifold `X` modelled on `I`,
is a `C^n` manifold for the composite charts `ChartedSpace.comp H X M`. -/
theorem isManifold_of_hasGroupoid_smulGroupoid [IsManifold I n X] (M : Type*)
    [TopologicalSpace M] [ChartedSpace X M] [HasGroupoid M (smulGroupoid G X)] :
    letI := ChartedSpace.comp H X M
    IsManifold I n M := by
  let := ChartedSpace.comp H X M
  refine { StructureGroupoid.HasGroupoid.comp (smulGroupoid G X) fun e he ↦ ?_ with }
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  exact ⟨contMDiffOn_of_mem_smulGroupoid he,
    contMDiffOn_of_mem_smulGroupoid ((smulGroupoid G X).symm he)⟩

end Smooth

/-! ### Quotients and deck transformations -/

section Quotient

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  {M : Type*} [TopologicalSpace M] {f : X → M}

/-- Let `f : X → M` be a local homeomorphism with a right inverse, whose deck transformations are
locally given by the action of `G`: whenever `f z = f w`, some `g : G` sends `z` to `w` and
satisfies `f (g • y) = f y` for `y` near `z`. Then the charts that `f` pushes forward from `X`
make `M` a (G, X)-manifold. -/
theorem _root_.IsLocalHomeomorph.hasGroupoid_smulGroupoid_chartedSpaceOfRightInverse
    (hf : IsLocalHomeomorph f) {s : M → X} (hs : Function.RightInverse s f)
    (hdeck : ∀ z w, f z = f w → ∃ g : G, g • z = w ∧ f ∘ (g • ·) =ᶠ[𝓝 z] f) :
    letI := hf.chartedSpaceOfRightInverse (H := X) hs
    HasGroupoid M (smulGroupoid G X) := by
  let := hf.chartedSpaceOfRightInverse (H := X) hs
  refine hasGroupoid_smulGroupoid_iff.2 ?_
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ x hx
  -- The charts of `X` over itself are the identity, so the transition map is `L ∘ f`.
  set L := hf.localInverseAt (s q)
  have hxL : f x ∈ L.source := by simpa [hf.localInverseAt_symm] using hx.2.1
  obtain ⟨g, hgx, hfg⟩ := hdeck x (L (f x)) (hf.apply_localInverseAt_of_mem hxL).symm
  refine ⟨g, ?_⟩
  have key := hf.localInverseAt_comp_eventuallyEq (continuous_const_smul g).continuousAt
    (hgx ▸ L.map_source hxL) hfg
  simpa [hf.localInverseAt_symm] using key

variable [T2Space X] [LocallyCompactSpace X]

/-- The orbit space of a free, properly discontinuous action of a group `Γ` on `X`, with the charts
pushed forward along the orbit projection, is a (Γ, X)-manifold. -/
instance hasGroupoid_smulGroupoid_quotient (Γ : Type*) [Group Γ] [MulAction Γ X]
    [ContinuousConstSMul Γ X] [ProperlyDiscontinuousSMul Γ X] [IsCancelSMul Γ X] :
    HasGroupoid (MulAction.orbitRel.Quotient Γ X) (smulGroupoid Γ X) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ) (E := X)).isCoveringMap
    |>.isLocalHomeomorph |>.hasGroupoid_smulGroupoid_chartedSpaceOfRightInverse
      Quotient.mk_surjective.hasRightInverse.choose_spec fun z w h ↦ by
        obtain ⟨γ, hγ⟩ := Quotient.exact h.symm
        exact ⟨γ, hγ, Eventually.of_forall fun y ↦ Quotient.sound ⟨γ, rfl⟩⟩

/-- The orbit space `X / Γ` of a free, properly discontinuous action of a subgroup `Γ` of `G` is a
(G, X)-manifold. -/
instance hasGroupoid_smulGroupoid_quotient_subgroup (Γ : Subgroup G)
    [ProperlyDiscontinuousSMul Γ X] [IsCancelSMul Γ X] :
    HasGroupoid (MulAction.orbitRel.Quotient Γ X) (smulGroupoid G X) :=
  hasGroupoid_of_le (hasGroupoid_smulGroupoid_quotient Γ)
    (smulGroupoid_le fun γ ↦ ⟨γ, fun _ ↦ rfl⟩)

end Quotient

end TauCeti
