/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.QuotientGraphOfGroups
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree

/-!
# The structure theorem for groups acting on trees

Let a group `G` act on a tree `T` without inversions, let `D` be a lifting of the quotient graph
`B = T / G` with lifted vertices `x_v`, lifted darts `d_y` and elements `t_y`, and let
`𝔹 = D.graphOfGroups` be the quotient graph of groups. The structure theorem of Bass–Serre theory
says that `T` is the Bass–Serre tree of `𝔹` and `G` is its fundamental group.

Reading a `𝔹`-path `p` from `v₀` to `b` letter by letter, with vertex group elements read as
elements of `G` and darts `y` as `t_y`, gives an element `φ(p)` of `G`; on closed paths this is the
isomorphism `φ : π₁(𝔹, v₀) ≃* G` (`GTree.Lifting.π₁Equiv`). The map sending the vertex `p B_b` of
the Bass–Serre tree `X(𝔹, v₀)` to `φ(p) • x_b` and the dart `p α_y(B_y)` to `φ(p) • d_y` is a
morphism of graphs `X(𝔹, v₀) → T` (`GTree.Lifting.bassSerreHom`), equivariant along `φ`. It is
injective on the darts issuing from each vertex: two darts at `p B_b` over the same dart `y` of
`B` differ by an element of `B_b` fixing `d_y`, which lies in the image of `α_y`
(`GTree.Lifting.mem_range_α_iff`). Every dart of `T` issuing from an image vertex `φ(p) • x_b` is
the image of a dart there, since every dart issuing from `x_b` is a translate of a lifted dart by
an element of the stabilizer `B_b`. As `X(𝔹, v₀)` and `T` are trees, the morphism is an
isomorphism (`GTree.Lifting.bassSerreIso`, `SerreGraph.Iso.ofLocallyBijective`).

## Main definitions

* `TauCeti.GTree.Lifting.bassSerreHom`: the equivariant morphism `X(𝔹, v₀) → T`.
* `TauCeti.GTree.Lifting.bassSerreIso`: the same morphism, as an isomorphism of graphs.

## Main results

* `TauCeti.GTree.Lifting.bassSerreHom_mapV_smul`, `TauCeti.GTree.Lifting.bassSerreHom_mapE_smul`:
  the morphism `X(𝔹, v₀) → T` is equivariant along `π₁(𝔹, v₀) ≃* G`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.4, Theorem 13.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.6 and Remark 2.7.
-/

public section

universe u v w

namespace TauCeti

open SerreGraph GraphOfGroups _root_.MulAction

namespace GTree.Lifting

variable {G : Type w} [Group G] {T : GTree.{u, v} G} (D : T.Lifting)

/-! ### Reading `𝔹`-paths in `G` -/

/-- The element of `G` read off a `𝔹`-path: the product of its letters, with vertex group elements
read as elements of `G` and darts `y` as `t_y`. -/
private noncomputable def pathElem {x y : D.graphOfGroups.LetterVertex}
    (p : D.graphOfGroups.Path x y) : G :=
  D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts)

variable {D}

private theorem pathElem_def {x y : D.graphOfGroups.LetterVertex} (p : D.graphOfGroups.Path x y) :
    D.pathElem p = D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) :=
  (rfl)

private theorem pathElem_comp {x y z : D.graphOfGroups.LetterVertex}
    (p : D.graphOfGroups.Path x y) (q : D.graphOfGroups.Path y z) :
    D.pathElem (p.comp q) = D.pathElem p * D.pathElem q := by
  simp [pathElem]

private theorem pathElem_cons_vertex {x : D.graphOfGroups.LetterVertex} {b : T.quotient.V}
    (p : D.graphOfGroups.Path x ⟨b⟩) (g : D.graphOfGroups.vertexGroup b) :
    D.pathElem (p.cons (.vertex g)) = D.pathElem p * (g : G) := by
  simp only [pathElem, Path.toπ₁Tree_cons, Letter.toπ₁Tree_vertex, map_mul]
  exact congrArg _ (π₁TreeToGroup_of D b g)

private theorem pathElem_cons_dart {x : D.graphOfGroups.LetterVertex} {b c : T.quotient.V}
    (p : D.graphOfGroups.Path x ⟨b⟩) (e : b ⟶ c) :
    D.pathElem (p.cons (.dart e)) = D.pathElem p * D.twist e.val := by
  simp [pathElem]

private theorem pathElem_congr {x y : D.graphOfGroups.LetterVertex}
    {p q : D.graphOfGroups.Path x y} (h : p.Homotopic q) : D.pathElem p = D.pathElem q := by
  rw [pathElem, pathElem, Path.Homotopic.toπ₁Tree_eq _ h]

/-! ### The morphism from the Bass–Serre tree -/

/-- Two paths giving the same vertex `p B_b` of the Bass–Serre tree give the same vertex
`φ(p) • x_b` of `T`. -/
private theorem pathElem_smul_vertex_eq_of_bassSerreVertex_eq {b₀ b b' : T.quotient.V}
    {p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩} {p' : D.graphOfGroups.Path ⟨b₀⟩ ⟨b'⟩}
    (h : bassSerreVertex p = bassSerreVertex p') :
    D.pathElem p • D.vertex b = D.pathElem p' • D.vertex b' := by
  obtain rfl : b = b' := by
    simpa using congrArg (bassSerreProjection D.graphOfGroups b₀).mapV h
  obtain ⟨g, hg⟩ := bassSerreVertex_eq_bassSerreVertex_iff.1 h
  rw [pathElem_congr hg, pathElem_cons_vertex, mul_smul,
    mem_stabilizer_iff.1 (D.vertexGroupSubtype_mem b g)]

/-- Two pairs of a path and a dart giving the same dart `p α_y(B_y)` of the Bass–Serre tree give
the same dart `φ(p) • d_y` of `T`. -/
private theorem pathElem_smul_dart_eq_of_bassSerreDart_eq {b₀ b c b' c' : T.quotient.V}
    {p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩} {e : b ⟶ c} {p' : D.graphOfGroups.Path ⟨b₀⟩ ⟨b'⟩}
    {e' : b' ⟶ c'} (h : bassSerreDart p e = bassSerreDart p' e') :
    D.pathElem p • D.dart e.val = D.pathElem p' • D.dart e'.val := by
  obtain ⟨y, rfl, rfl⟩ := e
  obtain ⟨y', rfl, rfl⟩ := e'
  obtain rfl : y = y' := by
    simpa using congrArg (bassSerreProjection D.graphOfGroups b₀).mapE h
  obtain ⟨c₀, hc₀⟩ := bassSerreDart_eq_bassSerreDart_iff.1 h
  rw [pathElem_congr hc₀, pathElem_cons_vertex, mul_smul, αArrow_mk,
    mem_stabilizer_iff.1 (D.mem_range_α_iff.1 ⟨c₀, rfl⟩)]

variable (D)

/-- The vertex map of `bassSerreHom`, through chosen representatives. -/
private noncomputable def bassSerreMapV (b₀ : T.quotient.V)
    (x : (bassSerreTree D.graphOfGroups b₀).V) : T.V :=
  D.pathElem (bassSerreVertex_surjective x).choose_spec.choose •
    D.vertex (bassSerreVertex_surjective x).choose

/-- The dart map of `bassSerreHom`, through chosen representatives. -/
private noncomputable def bassSerreMapE (b₀ : T.quotient.V)
    (d : (bassSerreTree D.graphOfGroups b₀).E) : T.E :=
  D.pathElem (bassSerreDart_surjective d).choose_spec.choose_spec.choose •
    D.dart (bassSerreDart_surjective d).choose_spec.choose_spec.choose_spec.choose.val

variable {D}

private theorem bassSerreMapV_bassSerreVertex {b₀ b : T.quotient.V}
    (p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩) :
    D.bassSerreMapV b₀ (bassSerreVertex p) = D.pathElem p • D.vertex b :=
  pathElem_smul_vertex_eq_of_bassSerreVertex_eq
    (bassSerreVertex_surjective (bassSerreVertex p)).choose_spec.choose_spec

private theorem bassSerreMapE_bassSerreDart {b₀ b c : T.quotient.V}
    (p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩) (e : b ⟶ c) :
    D.bassSerreMapE b₀ (bassSerreDart p e) = D.pathElem p • D.dart e.val :=
  pathElem_smul_dart_eq_of_bassSerreDart_eq
    (bassSerreDart_surjective (bassSerreDart p e)).choose_spec.choose_spec.choose_spec.choose_spec

variable (D)

/-- The morphism from the Bass–Serre tree `X(𝔹, v₀)` of the quotient graph of groups to `T`: the
vertex `p B_b` goes to `φ(p) • x_b` and the dart `p α_y(B_y)` to `φ(p) • d_y`, where `φ(p)` is the
element of `G` read off the `𝔹`-path `p`. -/
noncomputable def bassSerreHom (b₀ : T.quotient.V) :
    (bassSerreTree D.graphOfGroups b₀).Hom T.toSerreGraph where
  mapV := D.bassSerreMapV b₀
  mapE := D.bassSerreMapE b₀
  map_src d := by
    obtain ⟨b, c, p, ⟨y, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d
    rw [bassSerreMapE_bassSerreDart, src_bassSerreDart, bassSerreMapV_bassSerreVertex, ← src_dart]
    exact src_smul ..
  map_rev d := by
    obtain ⟨b, c, p, ⟨y, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d
    rw [rev_bassSerreDart, bassSerreMapE_bassSerreDart, bassSerreMapE_bassSerreDart]
    simp [pathElem_cons_dart, dart_rev, mul_smul]

variable {D}

@[simp] theorem bassSerreHom_mapV_bassSerreVertex {b₀ b : T.quotient.V}
    (p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩) :
    (D.bassSerreHom b₀).mapV (bassSerreVertex p) =
      D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) • D.vertex b :=
  bassSerreMapV_bassSerreVertex p

@[simp] theorem bassSerreHom_mapE_bassSerreDart {b₀ b c : T.quotient.V}
    (p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩) (e : b ⟶ c) :
    (D.bassSerreHom b₀).mapE (bassSerreDart p e) =
      D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) • D.dart e.val :=
  bassSerreMapE_bassSerreDart p e

/-- The morphism `X(𝔹, v₀) → T` is equivariant on vertices along `π₁(𝔹, v₀) →* G`. -/
theorem bassSerreHom_mapV_smul {b₀ : T.quotient.V} (g : π₁ D.graphOfGroups b₀)
    (x : (bassSerreTree D.graphOfGroups b₀).V) :
    (D.bassSerreHom b₀).mapV (g • x) = D.π₁Equiv b₀ g • (D.bassSerreHom b₀).mapV x := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective x
  induction g using π₁.induction_on with | h γ => ?_
  rw [smul_bassSerreVertex, bassSerreHom_mapV_bassSerreVertex, bassSerreHom_mapV_bassSerreVertex,
    π₁Equiv_mk, ← pathElem_def, ← pathElem_def, ← pathElem_def, pathElem_comp, mul_smul]

/-- The morphism `X(𝔹, v₀) → T` is equivariant on darts along `π₁(𝔹, v₀) →* G`. -/
theorem bassSerreHom_mapE_smul {b₀ : T.quotient.V} (g : π₁ D.graphOfGroups b₀)
    (d : (bassSerreTree D.graphOfGroups b₀).E) :
    (D.bassSerreHom b₀).mapE (g • d) = D.π₁Equiv b₀ g • (D.bassSerreHom b₀).mapE d := by
  obtain ⟨b, c, p, e, rfl⟩ := bassSerreDart_surjective d
  induction g using π₁.induction_on with | h γ => ?_
  rw [smul_bassSerreDart, bassSerreHom_mapE_bassSerreDart, bassSerreHom_mapE_bassSerreDart,
    π₁Equiv_mk, ← pathElem_def, ← pathElem_def, ← pathElem_def, pathElem_comp, mul_smul]

/-- The morphism `X(𝔹, v₀) → T` is injective on the darts issuing from each vertex: two darts at
`p B_b` over the same dart `y` of `B` differ by an element of `B_b` fixing `d_y`, which lies in the
image of `α_y`. -/
private theorem bassSerreHom_locallyInjective (b₀ : T.quotient.V)
    (d d' : (bassSerreTree D.graphOfGroups b₀).E)
    (hsrc : (bassSerreTree D.graphOfGroups b₀).src d = (bassSerreTree D.graphOfGroups b₀).src d')
    (h : (D.bassSerreHom b₀).mapE d = (D.bassSerreHom b₀).mapE d') : d = d' := by
  obtain ⟨b, c, p, ⟨y, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d
  obtain ⟨b', c', p', ⟨y', rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d'
  simp only [bassSerreHom_mapE_bassSerreDart, ← pathElem_def] at h
  obtain rfl : y = y' := by simpa using congrArg T.quotientMap.mapE h
  rw [src_bassSerreDart, src_bassSerreDart, bassSerreVertex_eq_bassSerreVertex_iff] at hsrc
  obtain ⟨g, hg⟩ := hsrc
  -- `g` fixes `d_y`, so it lies in the image of `α_y`.
  have hgy : (g : G) ∈ stabilizer G (D.dart y) := by
    rw [pathElem_congr hg, pathElem_cons_vertex, mul_smul, smul_left_cancel_iff] at h
    exact mem_stabilizer_iff.2 h.symm
  obtain ⟨c₀, rfl⟩ := D.mem_range_α_iff.2 hgy
  rw [bassSerreDart_congr hg, ← αArrow_mk, bassSerreDart_cons_vertex_αArrow]

/-- Every dart of `T` issuing from the image `φ(p) • x_b` of a vertex `p B_b` is the image of a dart
issuing from `p B_b`. -/
private theorem bassSerreHom_locallySurjective (b₀ : T.quotient.V) (d : T.E)
    (hd : T.src d ∈ Set.range (D.bassSerreHom b₀).mapV) :
    d ∈ Set.range (D.bassSerreHom b₀).mapE := by
  obtain ⟨x, hx⟩ := hd
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective x
  rw [bassSerreHom_mapV_bassSerreVertex, ← pathElem_def] at hx
  -- Translated back by `φ(p)`, the dart issues from `x_b`, so it is `s • d_y` with `s ∈ B_b`.
  obtain ⟨s, hs, hse⟩ := D.exists_smul_dart_eq (b := b) (e := (D.pathElem p)⁻¹ • d) (by
    rw [src_smul, ← hx, inv_smul_smul])
  set y := T.quotientMap.mapE ((D.pathElem p)⁻¹ • d)
  have hy : T.quotient.src y = b := by
    simp [y, Hom.map_src, ← hx]
  obtain ⟨s, rfl⟩ : ∃ s' : D.graphOfGroups.vertexGroup b, (s' : G) = s :=
    ⟨⟨s, hs⟩, D.vertexGroupSubtype_mk b s hs⟩
  refine ⟨bassSerreDart (p.cons (.vertex s)) (⟨y, hy, rfl⟩ : b ⟶ T.quotient.tgt y), ?_⟩
  rw [bassSerreHom_mapE_bassSerreDart, ← pathElem_def, pathElem_cons_vertex, mul_smul, hse,
    smul_inv_smul]

variable (D)

/-- **The structure theorem for groups acting on trees, for the tree.** The morphism from the
Bass–Serre tree `X(𝔹, v₀)` of the quotient graph of groups to `T` is an isomorphism of graphs; it
is equivariant along the isomorphism `π₁(𝔹, v₀) ≃* G` (`bassSerreHom_mapV_smul`,
`bassSerreHom_mapE_smul`). -/
noncomputable def bassSerreIso (b₀ : T.quotient.V) :
    (bassSerreTree D.graphOfGroups b₀).Iso T.toSerreGraph :=
  Iso.ofLocallyBijective (D.bassSerreHom b₀)
    ((connected_iff _).1 (bassSerreTree D.graphOfGroups b₀).isTree.connected).2
    ((connected_iff _).1 T.isTree.connected).2 T.isAcyclic (bassSerreHom_locallyInjective b₀)
    (bassSerreHom_locallySurjective b₀)

@[simp] theorem bassSerreIso_toHom (b₀ : T.quotient.V) :
    (D.bassSerreIso b₀).toHom = D.bassSerreHom b₀ :=
  Iso.ofLocallyBijective_toHom ..

@[simp] theorem bassSerreIso_equivV_apply (b₀ : T.quotient.V)
    (x : (bassSerreTree D.graphOfGroups b₀).V) :
    (D.bassSerreIso b₀).equivV x = (D.bassSerreHom b₀).mapV x :=
  Iso.ofLocallyBijective_equivV_apply ..

@[simp] theorem bassSerreIso_equivE_apply (b₀ : T.quotient.V)
    (d : (bassSerreTree D.graphOfGroups b₀).E) :
    (D.bassSerreIso b₀).equivE d = (D.bassSerreHom b₀).mapE d :=
  Iso.ofLocallyBijective_equivE_apply ..

end GTree.Lifting

end TauCeti
