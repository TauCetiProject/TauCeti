/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree
public import TauCeti.GroupTheory.GTree.FixedPoint

/-!
# Elliptic and hyperbolic elements of Bass–Serre trees

Let `𝔸` be a graph of groups over `Γ` and `X(𝔸, a)` its Bass–Serre tree, a tree for the
fundamental group `π₁(𝔸, a)`. The stabilizer of the vertex `p A_b` is the conjugate
`p A_b p⁻¹` of the vertex group, the image of `π₁.vertexHom p`. Hence:

* a subgroup or an element of `π₁(𝔸, a)` is elliptic in `X(𝔸, a)` exactly when it lies in a
  conjugate of a vertex group; in particular the conjugates of the vertex groups are elliptic;
* `X(𝔸, a)` dominates a tree `T` of `π₁(𝔸, a)` exactly when the vertex groups are elliptic in
  `T`. Since ellipticity is invariant under conjugation, one embedding of each vertex group
  suffices: for the amalgamated product `A ∗_C B` (the segment graph of groups) the Bass–Serre tree
  dominates `T` exactly when `A` and `B` are elliptic in `T`;
* over a graph without edges (a trivial splitting) the Bass–Serre tree is a point, so it dominates
  exactly the trees in which `π₁(𝔸, a)` is elliptic (`GTree.dominates_iff_of_subsingleton`) and is
  dominated by every tree (`GTree.dominates_of_subsingleton`).

For a dart `e : b ⟶ c` and an `𝔸`-path `p` from `a` to `b`, the elements `p g p⁻¹` with
`g ∈ A_b` fix the vertex `p A_b`, and they fix the dart `p α_e(A_e)` from `p A_b` to `p e A_c`
exactly when `g ∈ α_e(A_e)`; similarly the elements `(p e) h (p e)⁻¹` with `h ∈ A_c` fix
`p e A_c`, and fix the dart exactly when `h ∈ ω_e(A_e)`. By Serre's criterion for products of
elliptic elements (`GTree.isHyperbolic_mul_of_isReduced`), the product `(p g p⁻¹) ((p e) h (p e)⁻¹)`
is hyperbolic exactly when `g ∉ α_e(A_e)` and `h ∉ ω_e(A_e)`. For `A ∗_C B` this says that `a b` is
hyperbolic for `a ∈ A ∖ C` and `b ∈ B ∖ C`; so if `C` is a proper subgroup of both `A` and `B`, then
`A ∗_C B` fixes no vertex of its Bass–Serre tree: the action is not trivial, and the one-vertex
tree does not dominate the Bass–Serre tree (`GTree.point_dominates_iff`).

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isEllipticSubgroup_iff`,
  `TauCeti.GraphOfGroups.bassSerreTree_isElliptic_iff`: the elliptic subgroups and elements are
  those contained in conjugates of vertex groups.
* `TauCeti.GraphOfGroups.bassSerreTree_dominates_iff`,
  `TauCeti.GraphOfGroups.bassSerreTree_dominates_iff_of_paths`: domination by the Bass–Serre tree.
* `TauCeti.GraphOfGroups.instUniqueVBassSerreTreeOfIsEmptyE`: over a graph without edges, the
  Bass–Serre tree has exactly one vertex.
* `TauCeti.GraphOfGroups.bassSerreTree_isHyperbolic_vertexHom_mul_vertexHom_iff`: hyperbolic
  products of elements of adjacent vertex groups.
* `TauCeti.GraphOfGroups.bassSerreTree_segment_dominates_iff`,
  `TauCeti.GraphOfGroups.bassSerreTree_segment_isHyperbolic_mul_iff`,
  `TauCeti.GraphOfGroups.not_bassSerreTree_segment_isEllipticSubgroup_top`: amalgamated products.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.2 (elliptic
  subgroups are the subgroups of conjugates of vertex groups) and §1.4.2 (domination).
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and the paragraph after it (vertex and
  edge stabilizers of the Bass–Serre tree).
* J.-P. Serre, *Trees*, Chapter I, §6.5, Proposition 26.
-/

public section

universe u v w x u' v'

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

/-! ### Elliptic subgroups -/

/-- A subgroup of `π₁(𝔸, a)` is elliptic in the Bass–Serre tree exactly when it lies in a
conjugate `p A_b p⁻¹` of a vertex group. -/
theorem bassSerreTree_isEllipticSubgroup_iff {H : Subgroup (π₁ 𝔸 a)} :
    (bassSerreTree 𝔸 a).IsEllipticSubgroup H ↔
      ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), H ≤ (π₁.vertexHom p).range := by
  rw [GTree.isEllipticSubgroup_iff]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨b, p, hp⟩ ↦
    ⟨bassSerreVertex p, by rwa [stabilizer_bassSerreVertex]⟩⟩
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
  exact ⟨b, p, by rwa [← stabilizer_bassSerreVertex]⟩

/-- An element of `π₁(𝔸, a)` is elliptic in the Bass–Serre tree exactly when it lies in a
conjugate `p A_b p⁻¹` of a vertex group. -/
theorem bassSerreTree_isElliptic_iff {g : π₁ 𝔸 a} : (bassSerreTree 𝔸 a).IsElliptic g ↔
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), g ∈ (π₁.vertexHom p).range := by
  simp only [← GTree.isEllipticSubgroup_zpowers_iff, bassSerreTree_isEllipticSubgroup_iff,
    Subgroup.zpowers_le]

/-- The conjugates `p A_b p⁻¹` of the vertex groups are elliptic in the Bass–Serre tree. -/
@[simp] theorem bassSerreTree_isEllipticSubgroup_range_vertexHom {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (bassSerreTree 𝔸 a).IsEllipticSubgroup (π₁.vertexHom p).range :=
  bassSerreTree_isEllipticSubgroup_iff.2 ⟨b, p, le_rfl⟩

/-- Whether the image of a subgroup `H` of a vertex group `A_b` in `π₁(𝔸, a)` is elliptic in a
tree does not depend on the path from `a` to `b` along which it is conjugated. -/
theorem isEllipticSubgroup_map_vertexHom_iff {T : GTree.{u', v'} (π₁ 𝔸 a)} {b : Γ.V}
    (H : Subgroup (𝔸.vertexGroup b)) (p q : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    T.IsEllipticSubgroup (H.map (π₁.vertexHom p)) ↔
      T.IsEllipticSubgroup (H.map (π₁.vertexHom q)) := by
  rw [π₁.map_vertexHom_eq_map_conj q p, GTree.isEllipticSubgroup_map_conj_iff]

/-! ### Domination -/

/-- The Bass–Serre tree dominates a tree `T` exactly when the conjugates `p A_b p⁻¹` of the vertex
groups are elliptic in `T`. -/
theorem bassSerreTree_dominates_iff {T : GTree.{u', v'} (π₁ 𝔸 a)} :
    (bassSerreTree 𝔸 a).Dominates T ↔
      ∀ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), T.IsEllipticSubgroup (π₁.vertexHom p).range := by
  rw [GTree.dominates_iff]
  refine ⟨fun h b p ↦ ?_, fun h y ↦ ?_⟩
  · simpa only [stabilizer_bassSerreVertex] using h (bassSerreVertex p)
  · obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
    simpa only [stabilizer_bassSerreVertex] using h b p

/-- Given an `𝔸`-path `q b` from `a` to every vertex `b`, the Bass–Serre tree dominates a tree `T`
exactly when the images `q b A_b (q b)⁻¹` of the vertex groups are elliptic in `T`. -/
theorem bassSerreTree_dominates_iff_of_paths (q : ∀ b : Γ.V, 𝔸.Path ⟨a⟩ ⟨b⟩)
    {T : GTree.{u', v'} (π₁ 𝔸 a)} : (bassSerreTree 𝔸 a).Dominates T ↔
      ∀ b : Γ.V, T.IsEllipticSubgroup (π₁.vertexHom (q b)).range := by
  rw [bassSerreTree_dominates_iff]
  refine forall_congr' fun b ↦ ⟨fun h ↦ h (q b), fun h p ↦ ?_⟩
  rw [MonoidHom.range_eq_map] at h ⊢
  exact (isEllipticSubgroup_map_vertexHom_iff ⊤ (q b) p).1 h

/-! ### Graphs without edges -/

/-- Over a graph without edges, for instance for the trivial splitting of a group as a single
vertex group, the Bass–Serre tree is a point: every `𝔸`-path from `a` stays at `a` and is homotopic
to a single element of `A_a`. -/
noncomputable instance [IsEmpty Γ.E] : Unique (bassSerreTree 𝔸 a).V where
  default := bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩)
  uniq y := by
    obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
    obtain rfl : a = b := Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim (Path.edgePath p)
    obtain ⟨g, hg⟩ := π₁.exists_homotopic_ofVertex_of_isEmpty p
    rw [bassSerreVertex_congr hg, Path.ofVertex_eq_nil_cons, bassSerreVertex_cons_vertex]

/-! ### Hyperbolic elements -/

/-- The element `p g p⁻¹` fixes the dart `p α_e(A_e)` exactly when `g ∈ α_e(A_e)`. -/
private theorem vertexHom_mem_stabilizer_bassSerreDart_iff {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) (g : 𝔸.vertexGroup b) : π₁.vertexHom p g ∈ stabilizer (π₁ 𝔸 a) (bassSerreDart p e) ↔
      g ∈ (𝔸.αArrow e).range := by
  rw [stabilizer_bassSerreDart, Subgroup.mem_map_iff_mem (π₁.vertexHom_injective p)]

/-- The element `(p e) h (p e)⁻¹` fixes the dart `p α_e(A_e)` exactly when `h ∈ ω_e(A_e)`: it
fixes the reverse dart `(p e) α_{rev e}(A_e)`, and `α_{rev e}(A_e) = ω_e(A_e)`. -/
private theorem vertexHom_cons_mem_stabilizer_bassSerreDart_iff {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) (h : 𝔸.vertexGroup c) :
    π₁.vertexHom (p.cons (.dart e)) h ∈ stabilizer (π₁ 𝔸 a) (bassSerreDart p e) ↔
      h ∈ (𝔸.ωArrow e).range := by
  rw [← GTree.stabilizer_rev, rev_bassSerreDart, stabilizer_bassSerreDart, range_αArrow_reverse,
    Subgroup.mem_map_iff_mem (π₁.vertexHom_injective _)]

/-- Let `e : b ⟶ c` be a dart and `p` an `𝔸`-path from `a` to `b`, and let `g ∈ A_b` and
`h ∈ A_c`. In the Bass–Serre tree, the product `(p g p⁻¹) ((p e) h (p e)⁻¹)` is hyperbolic exactly
when `g ∉ α_e(A_e)` and `h ∉ ω_e(A_e)`. -/
theorem bassSerreTree_isHyperbolic_vertexHom_mul_vertexHom_iff {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) (g : 𝔸.vertexGroup b) (h : 𝔸.vertexGroup c) :
    (bassSerreTree 𝔸 a).IsHyperbolic (π₁.vertexHom p g * π₁.vertexHom (p.cons (.dart e)) h) ↔
      g ∉ (𝔸.αArrow e).range ∧ h ∉ (𝔸.ωArrow e).range := by
  set X := bassSerreTree 𝔸 a
  set d := bassSerreDart p e
  have hs : π₁.vertexHom p g ∈ stabilizer (π₁ 𝔸 a) (X.src d) := by
    rw [src_bassSerreDart, stabilizer_bassSerreVertex]
    exact ⟨g, rfl⟩
  have ht : π₁.vertexHom (p.cons (.dart e)) h ∈ stabilizer (π₁ 𝔸 a) (X.tgt d) := by
    rw [tgt_bassSerreDart, stabilizer_bassSerreVertex]
    exact ⟨h, rfl⟩
  refine ⟨fun hX ↦ ⟨fun hg ↦ GTree.not_isHyperbolic_iff.2 ?_ hX,
    fun hh ↦ GTree.not_isHyperbolic_iff.2 ?_ hX⟩, fun ⟨hg, hh⟩ ↦ ?_⟩
  · -- If `g ∈ α_e(A_e)`, both factors fix the target of the dart.
    refine (X.isEllipticSubgroup_stabilizer _).isElliptic (mul_mem ?_ ht)
    exact X.stabilizer_dart_le_stabilizer_tgt d
      ((vertexHom_mem_stabilizer_bassSerreDart_iff p e g).2 hg)
  · -- If `h ∈ ω_e(A_e)`, both factors fix the source of the dart.
    refine (X.isEllipticSubgroup_stabilizer _).isElliptic (mul_mem hs ?_)
    exact X.stabilizer_dart_le_stabilizer_src d
      ((vertexHom_cons_mem_stabilizer_bassSerreDart_iff p e h).2 hh)
  · -- Otherwise neither factor fixes the dart, and Serre's criterion applies to the path `d`.
    refine GTree.isHyperbolic_mul_of_isReduced (p := (X.dart d).toPath)
      (SerreGraph.Path.isReduced_toPath _ _) (X.isAcyclic.src_ne_tgt d) (mem_stabilizer_iff.1 hs)
      (fun f hf hfix ↦ ?_) (mem_stabilizer_iff.1 ht) fun f hf hfix ↦ ?_
    · obtain rfl : d = f := by simpa using hf
      exact hg ((vertexHom_mem_stabilizer_bassSerreDart_iff p e g).1 (mem_stabilizer_iff.2 hfix))
    · obtain rfl : d = f := by simpa using hf
      exact hh ((vertexHom_cons_mem_stabilizer_bassSerreDart_iff p e h).1
        (mem_stabilizer_iff.2 hfix))

/-! ### Amalgamated products -/

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}

/-- The Bass–Serre tree of the amalgamated product `A ∗_C B`, based at the vertex of `A`,
dominates a tree `T` exactly when `A` and `B` are elliptic in `T`. Here `A` is embedded along the
empty path and `B` along the dart of the segment. -/
theorem bassSerreTree_segment_dominates_iff {hf : Function.Injective f} {hg : Function.Injective g}
    {T : GTree.{u', v'} (π₁ (segment f g hf hg) (SerreGraph.segment.src false))} :
    (bassSerreTree (segment f g hf hg) (SerreGraph.segment.src false)).Dominates T ↔
      T.IsEllipticSubgroup (π₁.vertexHom .nil).range ∧
        T.IsEllipticSubgroup
          (π₁.vertexHom (Path.ofDart (SerreGraph.segment.dart false))).range := by
  rw [bassSerreTree_dominates_iff_of_paths (Bool.rec (motive :=
    fun b ↦ (segment f g hf hg).Path ⟨SerreGraph.segment.src false⟩ ⟨b⟩) .nil
    (Path.ofDart (SerreGraph.segment.dart false)))]
  refine ⟨fun h ↦ ⟨h false, h true⟩, fun ⟨h₀, h₁⟩ b ↦ ?_⟩
  cases b
  exacts [h₀, h₁]

variable (hf : Function.Injective f) (hg : Function.Injective g)

/-- In the Bass–Serre tree of the amalgamated product `A ∗_C B`, the product `x y` of `x ∈ A` and
`y ∈ B` is hyperbolic exactly when `x ∉ C` and `y ∉ C`. Here `A` is embedded along the empty path
and `B` along the dart of the segment. -/
theorem bassSerreTree_segment_isHyperbolic_mul_iff (x : A) (y : B) :
    (bassSerreTree (segment f g hf hg) (SerreGraph.segment.src false)).IsHyperbolic
      (π₁.vertexHom (𝔸 := segment f g hf hg) (a := SerreGraph.segment.src false) .nil x *
        π₁.vertexHom (Path.ofDart (SerreGraph.segment.dart false)) y) ↔
      x ∉ f.range ∧ y ∉ g.range := by
  have h := bassSerreTree_isHyperbolic_vertexHom_mul_vertexHom_iff (𝔸 := segment f g hf hg)
    .nil (SerreGraph.segment.dart false) x y
  -- The dart `false` of the segment has `α = f` and `ω = g`. The literal `false : Bool` is a dart
  -- of the segment only up to unfolding, so `range_αArrow_dart` is instantiated explicitly.
  rw [(range_αArrow_dart _ _).trans (congrArg MonoidHom.range (segment_α_false f g hf hg)),
    (range_ωArrow_dart _ _).trans (congrArg MonoidHom.range (segment_ω_false f g hf hg))] at h
  rwa [Path.ofDart_eq_nil_cons]

/-- If `C` is a proper subgroup of both `A` and `B`, then the amalgamated product `A ∗_C B` fixes
no vertex of its Bass–Serre tree. -/
theorem not_bassSerreTree_segment_isEllipticSubgroup_top (hA : f.range ≠ ⊤) (hB : g.range ≠ ⊤) :
    ¬(bassSerreTree (segment f g hf hg) (SerreGraph.segment.src false)).IsEllipticSubgroup ⊤ := by
  obtain ⟨x, hx⟩ := not_forall.1 (mt (Subgroup.eq_top_iff' f.range).2 hA)
  obtain ⟨y, hy⟩ := not_forall.1 (mt (Subgroup.eq_top_iff' g.range).2 hB)
  exact fun htop ↦ GTree.not_isHyperbolic_iff.2 (htop.isElliptic (Subgroup.mem_top _))
    ((bassSerreTree_segment_isHyperbolic_mul_iff hf hg x y).2 ⟨hx, hy⟩)

end segment

end GraphOfGroups

end TauCeti
