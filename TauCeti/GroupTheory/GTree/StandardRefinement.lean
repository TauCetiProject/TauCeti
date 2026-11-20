/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.FixedPoint
public import TauCeti.GroupTheory.GTree.JSJ
public import TauCeti.GroupTheory.GTree.Refinement

/-!
# Standard refinements of group actions on trees

Let `T₁` and `T₂` be `G`-trees. Equivariant maps between trees are given on vertices.

A `G`-tree `T` is a *standard refinement of `T₁` dominating `T₂`* when there are a collapse map
`p : T → T₁` and an equivariant map `f : T → T₂` whose restriction to every fibre `p⁻¹(v)` is an
embedding of trees: it is injective on the vertices of the fibre and sends each dart joining two
of them to a dart of `T₂`. A tree is a standard refinement of itself dominating every tree it
dominates, and of every tree it refines dominating itself; in particular a tree is a standard
refinement of each of its collapses dominating itself.

Guirardel and Levitt construct, when `T₁` is elliptic with respect to `T₂` (the stabilizer of every
dart of `T₁` fixes a vertex of `T₂`, their Definition 2.1), a standard refinement by blowing up
each vertex `v` of `T₁` into a `G_v`-invariant subtree of `T₂` (Proposition 2.2); the construction
is not in this file. This file proves Assertions (i), (ii) and (iv) of their Proposition 2.2 and
their consequences:

* a standard refinement refines `T₁` and dominates `T₂`;
* the stabilizer of each of its darts fixes a dart of `T₁` or a dart of `T₂`: it fixes the images
  of the two ends of the dart under `p` or, when these coincide, under `f`
  (`TauCeti.GTree.exists_stabilizer_le_of_apply_ne`);
* a subgroup is elliptic in it exactly when it is elliptic in `T₁` and in `T₂`, so all standard
  refinements of `T₁` dominating `T₂` lie in one deformation space;
* it is relative to families `𝒜` and `ℋ` when `T₁` and `T₂` are and `𝒜` is closed under passing
  to subgroups;

and their Lemma 2.8 (2): a standard refinement of a universally elliptic tree dominating a
universally elliptic tree is universally elliptic.

## Main declarations

* `TauCeti.GTree.IsStandardRefinement`: standard refinements.
* `TauCeti.GTree.IsStandardRefinement.exists_stabilizer_le`: dart stabilizers of a standard
  refinement.
* `TauCeti.GTree.IsStandardRefinement.isEllipticSubgroup_iff`: the elliptic subgroups of a standard
  refinement.
* `TauCeti.GTree.IsUniversallyElliptic.of_isStandardRefinement`: standard refinements of
  universally elliptic trees are universally elliptic.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017),
  Definition 2.1, Proposition 2.2, Definition 2.5 and Lemma 2.8.
-/

public section

universe u v u' v' u'' v'' u₃ v₃ w

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] {T : GTree.{u, v} G} {T' : GTree.{u', v'} G}

/-! ### Stabilizers of darts under equivariant maps -/

/-- If an equivariant map separates the two ends of a dart, the stabilizer of the dart fixes a
dart of the target. -/
theorem exists_stabilizer_le_of_apply_ne (f : T.V →[G] T'.V) {e : T.E}
    (he : f (T.src e) ≠ f (T.tgt e)) : ∃ e' : T'.E, stabilizer G e ≤ stabilizer G e' :=
  -- The stabilizer of `e` fixes both ends of `e`, hence their images.
  let ⟨e', _, he'⟩ := exists_src_eq_and_stabilizer_inf_le he
  ⟨e', le_trans (le_inf
    (fun g hg => by rw [mem_stabilizer_iff, ← map_smul, ← src_smul, mem_stabilizer_iff.mp hg])
    (fun g hg => by rw [mem_stabilizer_iff, ← map_smul, ← tgt_smul, mem_stabilizer_iff.mp hg])) he'⟩

/-! ### Standard refinements -/

variable {T₁ : GTree.{u', v'} G} {T₂ : GTree.{u'', v''} G}

variable (T T₁ T₂) in
/-- `T` is a *standard refinement of `T₁` dominating `T₂`* when there are a collapse map
`p : T → T₁` and an equivariant map `f : T → T₂` whose restriction to every fibre of `p` is an
embedding of trees: it is injective on the vertices of the fibre and sends each dart joining two
vertices of the fibre to a dart of `T₂`.

Guirardel and Levitt ask only that the restriction of `f` to each fibre be injective, for maps
which send edges to edge paths; such a map may stretch an edge of a fibre over a segment of
several edges. Here a dart of a fibre goes to a single dart. The trees constructed in their proof,
whose fibres are subtrees of `T₂` mapped by inclusion, are standard refinements in this sense.
Unlike theirs, `T` is not required to be minimal. -/
def IsStandardRefinement : Prop :=
  ∃ (p : T.V →[G] T₁.V) (f : T.V →[G] T₂.V), IsCollapseMap p ∧
    (∀ x y, p x = p y → f x = f y → x = y) ∧
    ∀ e : T.E, p (T.src e) = p (T.tgt e) →
      ∃ e' : T₂.E, T₂.src e' = f (T.src e) ∧ T₂.tgt e' = f (T.tgt e)

/-- Unfold the definition of a standard refinement. -/
theorem isStandardRefinement_iff : T.IsStandardRefinement T₁ T₂ ↔
    ∃ (p : T.V →[G] T₁.V) (f : T.V →[G] T₂.V), IsCollapseMap p ∧
      (∀ x y, p x = p y → f x = f y → x = y) ∧
      ∀ e : T.E, p (T.src e) = p (T.tgt e) →
        ∃ e' : T₂.E, T₂.src e' = f (T.src e) ∧ T₂.tgt e' = f (T.tgt e) := Iff.rfl

/-- A tree is a standard refinement of itself dominating every tree it dominates. -/
theorem Dominates.isStandardRefinement (h : T.Dominates T₂) : T.IsStandardRefinement T T₂ :=
  ⟨MulActionHom.id G, (dominates_iff_nonempty.mp h).some, isCollapseMap_id T, fun _ _ hxy _ => hxy,
    fun e he => (T.isAcyclic.src_ne_tgt e he).elim⟩

/-- A tree is a standard refinement of every tree it refines, dominating itself. -/
theorem Refines.isStandardRefinement (h : T.Refines T₁) : T.IsStandardRefinement T₁ T :=
  let ⟨p, hp⟩ := refines_iff.mp h
  ⟨p, MulActionHom.id G, hp, fun _ _ _ hxy => hxy, fun e _ => ⟨e, rfl, rfl⟩⟩

/-- A standard refinement of `T₁` refines `T₁`. -/
theorem IsStandardRefinement.refines (h : T.IsStandardRefinement T₁ T₂) : T.Refines T₁ :=
  let ⟨p, _, hp, _⟩ := h
  refines_iff.mpr ⟨p, hp⟩

/-- A standard refinement of `T₁` dominating `T₂` dominates `T₂`. -/
theorem IsStandardRefinement.dominates (h : T.IsStandardRefinement T₁ T₂) : T.Dominates T₂ :=
  let ⟨_, f, _⟩ := h
  dominates_iff_nonempty.mpr ⟨f⟩

/-- The stabilizer of a dart of a standard refinement of `T₁` dominating `T₂` fixes a dart of
`T₁` or a dart of `T₂`. -/
theorem IsStandardRefinement.exists_stabilizer_le (h : T.IsStandardRefinement T₁ T₂) (e : T.E) :
    (∃ e₁ : T₁.E, stabilizer G e ≤ stabilizer G e₁) ∨
      ∃ e₂ : T₂.E, stabilizer G e ≤ stabilizer G e₂ := by
  obtain ⟨p, f, -, hinj, -⟩ := h
  -- If `p` identifies the ends of `e`, they lie in one fibre, on which `f` is injective.
  by_cases hp : p (T.src e) = p (T.tgt e)
  · exact .inr (exists_stabilizer_le_of_apply_ne f fun hf =>
      T.isAcyclic.src_ne_tgt e (hinj _ _ hp hf))
  · exact .inl (exists_stabilizer_le_of_apply_ne p hp)

/-- A subgroup is elliptic in a standard refinement of `T₁` dominating `T₂` exactly when it is
elliptic in `T₁` and in `T₂`. -/
theorem IsStandardRefinement.isEllipticSubgroup_iff (h : T.IsStandardRefinement T₁ T₂)
    {H : Subgroup G} :
    T.IsEllipticSubgroup H ↔ T₁.IsEllipticSubgroup H ∧ T₂.IsEllipticSubgroup H := by
  refine ⟨fun hH => ⟨h.refines.dominates.isEllipticSubgroup hH, h.dominates.isEllipticSubgroup hH⟩,
    fun ⟨h₁, h₂⟩ => ?_⟩
  obtain ⟨p, f, hp, hinj, hdart⟩ := h
  obtain ⟨v, hv⟩ := GTree.isEllipticSubgroup_iff.mp h₁
  -- `H` preserves the fibre `Y` of `p` over a vertex `v` it fixes.
  have hY (g : G) (hg : g ∈ H) (y : T.V) (hy : p y = v) : p (g • y) = v := by
    rw [map_smul, hy, mem_stabilizer_iff.mp (hv hg)]
  -- The image `f(Y)` is a nonempty convex set preserved by `H`, so `H` fixes a vertex `f y` of it.
  have hC : T₂.IsConvex (f '' (p ⁻¹' {v})) :=
    T₂.isAcyclic.isConvex_image (hp.isConvex_preimage (T₁.isAcyclic.isConvex_singleton v))
      (fun _ _ _ _ => T.nonempty_path _ _) fun e hs ht =>
        .inr (hdart e ((Set.mem_singleton_iff.mp hs).trans (Set.mem_singleton_iff.mp ht).symm))
  obtain ⟨y₀, hy₀⟩ := hp.surjective v
  obtain ⟨_, ⟨y, hy, rfl⟩, hfy⟩ := h₂.exists_mem_le_stabilizer hC ⟨f y₀, y₀, hy₀, rfl⟩
    fun g hg _ ⟨y, hy, hfy⟩ => ⟨g • y, hY g hg y hy, by rw [map_smul, hfy]⟩
  -- Since `f` is injective on `Y`, `H` fixes `y`.
  refine GTree.isEllipticSubgroup_iff.mpr ⟨y, fun g hg => mem_stabilizer_iff.mpr ?_⟩
  exact hinj _ _ ((hY g hg y hy).trans (Set.mem_singleton_iff.mp hy).symm)
    (by rw [map_smul, mem_stabilizer_iff.mp (hfy hg)])

/-- Any two standard refinements of `T₁` dominating `T₂` lie in the same deformation space. -/
theorem IsStandardRefinement.sameDeformationSpace {T' : GTree.{u₃, v₃} G}
    (h : T.IsStandardRefinement T₁ T₂) (h' : T'.IsStandardRefinement T₁ T₂) :
    T.SameDeformationSpace T' :=
  sameDeformationSpace_iff_forall_isEllipticSubgroup.mpr fun _ =>
    h.isEllipticSubgroup_iff.trans h'.isEllipticSubgroup_iff.symm

/-- A standard refinement of a tree relative to `𝒜` and `ℋ`, dominating a tree relative to `𝒜`
and `ℋ`, is relative to `𝒜` and `ℋ` when `𝒜` is closed under passing to subgroups. -/
theorem IsStandardRefinement.isRelative {𝒜 ℋ : Set (Subgroup G)} (h : T.IsStandardRefinement T₁ T₂)
    (h𝒜 : ∀ A ∈ 𝒜, ∀ B ≤ A, B ∈ 𝒜) (h₁ : T₁.IsRelative 𝒜 ℋ) (h₂ : T₂.IsRelative 𝒜 ℋ) :
    T.IsRelative 𝒜 ℋ := by
  refine isRelative_iff.mpr ⟨fun e => ?_, fun H hH => h.isEllipticSubgroup_iff.mpr
    ⟨h₁.isEllipticSubgroup hH, h₂.isEllipticSubgroup hH⟩⟩
  rcases h.exists_stabilizer_le e with ⟨e₁, he⟩ | ⟨e₂, he⟩
  · exact h𝒜 _ (h₁.stabilizer_mem e₁) _ he
  · exact h𝒜 _ (h₂.stabilizer_mem e₂) _ he

/-- A standard refinement of a universally elliptic tree dominating a universally elliptic tree
is universally elliptic. -/
theorem IsUniversallyElliptic.of_isStandardRefinement {𝒜 ℋ : Set (Subgroup G)}
    {T T₁ T₂ : GTree.{u, v} G} (h : T.IsStandardRefinement T₁ T₂)
    (h₁ : T₁.IsUniversallyElliptic 𝒜 ℋ) (h₂ : T₂.IsUniversallyElliptic 𝒜 ℋ) :
    T.IsUniversallyElliptic 𝒜 ℋ := by
  refine isUniversallyElliptic_iff.mpr fun e => ?_
  rcases h.exists_stabilizer_le e with ⟨e₁, he⟩ | ⟨e₂, he⟩
  · exact (h₁.isUniversallyEllipticSubgroup_stabilizer e₁).mono he
  · exact (h₂.isUniversallyEllipticSubgroup_stabilizer e₂).mono he

end GTree

end TauCeti
