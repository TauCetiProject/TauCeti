/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.AGraph
public import Mathlib.Tactic.Group

/-!
# Comparing the subgroups represented by two `𝔸`-graphs

Let `B` and `B'` be two `𝔸`-graphs with base vertices of type `v₀`. A type-preserving graph
morphism `φ : B → B'` respecting the base vertices induces an inclusion `L(B, u₀) ≤ L(B', u₀')` of
the represented subgroups as soon as the labels of `B` are those of `B'` up to the vertex groups of
`B'` and up to a conjugation at the vertices other than the base vertex: there are elements
`g_z ∈ A_[z]` with `g_{u₀} = 1` such that

* `g_z B_z g_z⁻¹ ≤ B'_{φ(z)}` for every vertex `z` of `B`, and
* `f_α = g_{o(f)}⁻¹ b' φ(f)_α` with `b' ∈ B'_{φ(o(f))}` for every dart `f` of `B`.

Indeed a `𝔹`-path `p` from `u₀` to `z` is then sent to a `𝔹'`-path from `u₀'` to `φ(z)` reading
`μ(p) g_z⁻¹` up to homotopy. This generalises the map `γ` of Kapovich, Weidmann and Myasnikov,
Proposition 4.15, given there for a folding map with equal labels and `g = 1`; the generalisation
applies to the auxiliary moves A0 and A2 as well, through the identity of the underlying graph.

## Main statements

* `TauCeti.GraphOfGroups.AGraph.subgroup_le_of_hom`: the inclusion `L(B, u₀) ≤ L(B', u₀')`.

## Implementation notes

The two `𝔸`-paths compared have the endpoints `[φ(z)]` and `[z]`, which are only propositionally
equal. The proof therefore first replaces the vertex groups and labels of `B` by those of `B'`,
read through the types of `B` (the paths of `B` are then lifted up to homotopy, with no transport),
and identifies the result with the pullback of `B'` along `φ`, whose type map is `[φ(·)]` by
definition and whose paths are read letter by letter as paths of `B'`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §4, Proposition 4.15.
-/

public section

universe u v w x u' v' u'' v''

namespace TauCeti

namespace GraphOfGroups

namespace AGraph

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-! ### Changing the vertex groups and the labels -/

section relabel

variable (B : AGraph.{u, v, w, x, u', v'} 𝔸 v₀)
  (grp : ∀ z : B.graph.V, Subgroup (𝔸.vertexGroup (B.typ.mapV z)))
  (lab : ∀ f : B.graph.E, 𝔸.vertexGroup (Γ.src (B.typ.mapE f)))

/-- The `𝔸`-graph with the underlying graph, the type map and the base vertex of `B`, and with the
vertex groups `grp` and the labels `lab`. -/
private abbrev relabel : AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := B.graph
  typ := B.typ
  base := B.base
  typ_base := B.typ_base
  grp := grp
  labelα := lab

variable {B grp lab} (g : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z))
  (hgrp : ∀ z, (B.grp z).map (MulAut.conj (g z)).toMonoidHom ≤ grp z)
  (hlab : ∀ f, ∃ b ∈ (grp (B.graph.src f)).comap
      (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f)).toMonoidHom,
    B.labelα f = (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm
      (g (B.graph.src f)))⁻¹ * (b * lab f))

include hgrp in
/-- The vertex step of `exists_relabel_path`. -/
private theorem homotopic_relabel_vertex {y : 𝔸.LetterVertex} {a : B.graph.V}
    {P : 𝔸.Path y ⟨B.typ.mapV a⟩} {P₁ : 𝔸.Path y ⟨B.typ.mapV a⟩}
    (h : Path.Homotopic P₁ (P.comp (Path.ofVertex (g a)⁻¹))) (b : B.grp a) :
    ∃ c : grp a, Path.Homotopic (P₁.comp (Path.ofVertex (c : 𝔸.vertexGroup _)))
      ((P.comp (Path.ofVertex (b : 𝔸.vertexGroup _))).comp (Path.ofVertex (g a)⁻¹)) := by
  refine ⟨⟨_, hgrp a (Subgroup.mem_map_of_mem _ b.2)⟩, ?_⟩
  simp only [Path.comp_ofVertex] at h ⊢
  have e : (g a)⁻¹ * (MulAut.conj (g a)).toMonoidHom b = b * (g a)⁻¹ := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ((h.cons _).trans (.mul _ _ _)).trans ?_
  rw [e]
  exact (Path.Homotopic.mul _ _ _).symm

include hlab in
/-- The dart step of `exists_relabel_path`. -/
private theorem homotopic_relabel_dart {y : 𝔸.LetterVertex} (e : B.graph.E)
    {P P₁ : 𝔸.Path y ⟨B.typ.mapV (B.graph.src e)⟩}
    (h : Path.Homotopic P₁ (P.comp (Path.ofVertex (g (B.graph.src e))⁻¹))) :
    ∃ (c₁ : grp (B.graph.src e)) (c₂ : grp (B.graph.tgt e)), Path.Homotopic
      (((P₁.comp (Path.ofVertex (c₁ : 𝔸.vertexGroup _))).comp ((B.relabel grp lab).letterPath
        (Letter.dart (𝔸 := (B.relabel grp lab).toGraphOfGroups) (B.graph.dart e)))).comp
          (Path.ofVertex (c₂ : 𝔸.vertexGroup _)))
      ((P.comp (B.letterPath (Letter.dart (𝔸 := B.toGraphOfGroups) (B.graph.dart e)))).comp
        (Path.ofVertex (g (B.graph.tgt e))⁻¹)) := by
  obtain ⟨b₁, hb₁, h₁⟩ := hlab e
  obtain ⟨b₂, hb₂, h₂⟩ := hlab (B.graph.rev e)
  let c₂ : grp (B.graph.tgt e) := (⟨_, hb₂⟩ : grp (B.graph.src (B.graph.rev e)))⁻¹
  refine ⟨⟨_, hb₁⟩, c₂, ?_⟩
  have hα : (g (B.graph.src e))⁻¹ * MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e) b₁ *
      MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e) (lab e) =
        MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e) (B.labelα e) := by
    rw [h₁, map_mul, map_mul, map_inv, mul_assoc]
    simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
  have hω : MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ e) ((B.relabel grp lab).labelω e) *
      (c₂ : 𝔸.vertexGroup _) = MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ e) (B.labelω e) *
          (g (B.graph.tgt e))⁻¹ := by
    -- `g` at `o(e⁻¹)` and at `t(e)`, which are the same vertex by definition.
    have hg : ∀ h : 𝔸.vertexGroup (B.typ.mapV (B.graph.src (B.graph.rev e))) =
        𝔸.vertexGroup (B.typ.mapV (B.graph.tgt e)), cast h (g _) = g (B.graph.tgt e) :=
      fun _ => rfl
    rw [labelω_def, labelω_def, h₂]
    simp only [c₂, map_mul, map_inv, inv_inv, mul_inv_rev, MulEquiv.cast_apply, cast_cast, hg,
      mul_inv_cancel_right]
    rfl
  rw [letterPath_dart, letterPath_dart]
  simp only [Path.comp_ofVertex, Quiver.Path.comp_cons, ← Quiver.Path.comp_assoc] at h ⊢
  have h' := (((h.cons (Letter.vertex (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e)
    b₁))).trans (.mul _ _ _)).cons (Letter.vertex (MulEquiv.cast (M := 𝔸.vertexGroup)
      (B.typ.map_src e) (lab e)))).trans (.mul _ _ _)
  rw [hα] at h'
  refine (((h'.comp_right _).cons _).cons _).trans ((Path.Homotopic.mul _ _ _).trans ?_)
  rw [hω]
  exact (Path.Homotopic.mul _ _ _).symm

include hgrp hlab in
/-- A `𝔹`-path `p` from the base vertex to `y` lifts to a path of the relabelled graph that reads
`μ(p) g_y⁻¹` up to homotopy. -/
private theorem exists_relabel_path (hg : g B.base = 1) {y : B.toGraphOfGroups.LetterVertex}
    (p : B.toGraphOfGroups.Path ⟨B.base⟩ y) :
    ∃ p₁ : (B.relabel grp lab).toGraphOfGroups.Path ⟨B.base⟩ ⟨y.as⟩,
      Path.Homotopic ((B.relabel grp lab).pathMap p₁)
        ((B.pathMap p).comp (Path.ofVertex (g y.as)⁻¹)) := by
  induction p with
  | nil =>
    refine ⟨.nil, ?_⟩
    simp only [pathMap_nil, Quiver.Path.nil_comp, hg, inv_one]
    exact Path.Homotopic.ofVertex_one.symm
  | cons p l ih =>
    obtain ⟨p₁, h⟩ := ih
    cases l with
    | vertex b =>
      obtain ⟨c, hc⟩ := homotopic_relabel_vertex g hgrp h b
      exact ⟨p₁.cons (Letter.vertex c), by simpa only [pathMap_cons, letterPath_vertex] using hc⟩
    | dart f =>
      obtain ⟨e, rfl, rfl⟩ := f
      obtain ⟨c₁, c₂, hc⟩ := homotopic_relabel_dart g hlab e h
      refine ⟨((p₁.cons (Letter.vertex c₁)).cons (Letter.dart (B.graph.dart e))).cons
        (Letter.vertex c₂), ?_⟩
      rw [(B.graph.dart_def e).symm]
      simpa only [pathMap_cons, letterPath_vertex] using hc

include hgrp hlab in
/-- Relabelling within the vertex groups of the target and up to a conjugation trivial at the base
vertex does not shrink the represented subgroup. -/
private theorem subgroup_le_relabel (hg : g B.base = 1) :
    B.subgroup ≤ (B.relabel grp lab).subgroup := by
  intro _ hx
  obtain ⟨p, rfl⟩ := (mem_subgroup_iff B).1 hx
  obtain ⟨p₁, h⟩ := exists_relabel_path g hgrp hlab hg p
  refine (mem_subgroup_iff _).2 ⟨p₁, ?_⟩
  rw [π₁.mk_eq_mk_iff.2 (h.trans ?_)]
  simp only [hg, inv_one, Path.comp_ofVertex]
  exact .one _

end relabel

/-! ### Pulling an `𝔸`-graph back along a graph morphism -/

section pullback

variable (B' : AGraph.{u, v, w, x, u'', v''} 𝔸 v₀) {G : SerreGraph.{u', v'}} (φ : G.Hom B'.graph)
  (base : G.V) (hbase : φ.mapV base = B'.base)

/-- The type map `[φ(·)]` of the pullback of `B'` along `φ`. -/
private abbrev pullbackTyp : G.Hom Γ where
  mapV z := B'.typ.mapV (φ.mapV z)
  mapE f := B'.typ.mapE (φ.mapE f)
  map_src f := by rw [B'.typ.map_src, φ.map_src]
  map_rev f := by rw [φ.map_rev, B'.typ.map_rev]

/-- The pullback of `B'` along `φ`: the graph `G` with the vertex groups and labels of the images
under `φ`. -/
private abbrev pullback : AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := G
  typ := pullbackTyp B' φ
  base := base
  typ_base := (congrArg B'.typ.mapV hbase).trans B'.typ_base
  grp z := B'.grp (φ.mapV z)
  labelα f := B'.labelα (φ.mapE f)

/-- The letters of the pullback, read as letters of `B'`. -/
private def pullbackLetter : ∀ {y z : (pullback B' φ base hbase).toGraphOfGroups.LetterVertex},
    (pullback B' φ base hbase).toGraphOfGroups.Letter y z →
      B'.toGraphOfGroups.Letter ⟨φ.mapV y.as⟩ ⟨φ.mapV z.as⟩
  | _, _, .vertex b => .vertex b
  | _, _, .dart f => .dart (φ.toPrefunctor.map f)

/-- The paths of the pullback, read as paths of `B'`. -/
private def pullbackHom : (pullback B' φ base hbase).toGraphOfGroups.LetterVertex ⥤q
    B'.toGraphOfGroups.LetterVertex where
  obj y := ⟨φ.mapV y.as⟩
  map := pullbackLetter B' φ base hbase

private theorem pullback_labelω (e : G.E) :
    (pullback B' φ base hbase).labelω e = B'.labelω (φ.mapE e) := by
  rw [labelω_def, labelω_def, MulEquiv.cast_apply, MulEquiv.cast_apply]
  -- Both sides are transports of the label of `φ(e⁻¹) = φ(e)⁻¹`.
  exact congrArg _ (eq_of_heq ((cast_heq _ _).trans ((congr_arg_heq B'.labelα (φ.map_rev e)).trans
    (cast_heq _ _).symm)))

private theorem pullback_letterPath {y z : (pullback B' φ base hbase).toGraphOfGroups.LetterVertex}
    (l : (pullback B' φ base hbase).toGraphOfGroups.Letter y z) :
    (pullback B' φ base hbase).letterPath l = B'.letterPath (pullbackLetter B' φ base hbase l) := by
  cases l with
  | vertex b => exact (letterPath_vertex _ b).trans (letterPath_vertex B' b).symm
  | dart f =>
    refine (letterPath_dart_arrow _ f).trans (Eq.trans ?_
      (letterPath_dart_arrow B' (φ.toPrefunctor.map f)).symm)
    rw [pullback_labelω]
    rfl

private theorem pullback_pathMap {y z : (pullback B' φ base hbase).toGraphOfGroups.LetterVertex}
    (p : (pullback B' φ base hbase).toGraphOfGroups.Path y z) :
    (pullback B' φ base hbase).pathMap p =
      B'.pathMap ((pullbackHom B' φ base hbase).mapPath p) := by
  induction p with
  | nil =>
    rw [pathMap_nil, Prefunctor.mapPath_nil, pathMap_nil]
    rfl
  | cons p l ih =>
    rw [pathMap_cons, Prefunctor.mapPath_cons, pathMap_cons, ih, pullback_letterPath]
    rfl

/-- The class of a closed `𝔹'`-path at a vertex equal to the base vertex lies in `L(B')`. -/
private theorem cast_mk_pathMap_mem {z : B'.graph.V} (hz : z = B'.base) (h : B'.typ.mapV z = v₀)
    (q : B'.toGraphOfGroups.Path ⟨z⟩ ⟨z⟩) :
    MulEquiv.cast (M := π₁ 𝔸) h (π₁.mk (B'.pathMap q)) ∈ B'.subgroup := by
  subst hz
  exact (mem_subgroup_iff _).2 ⟨q, rfl⟩

private theorem subgroup_pullback_le : (pullback B' φ base hbase).subgroup ≤ B'.subgroup := by
  intro _ hx
  obtain ⟨p, rfl⟩ := (mem_subgroup_iff _).1 hx
  rw [pullback_pathMap]
  exact cast_mk_pathMap_mem B' hbase _ _

end pullback

/-- Changing the type map of an `𝔸`-graph to an equal one, transporting the vertex groups and the
labels, does not change the represented subgroup. -/
private theorem subgroup_retype {G : SerreGraph.{u', v'}} {t₁ t₂ : G.Hom Γ}
    (hV : ∀ z, t₂.mapV z = t₁.mapV z) (hE : ∀ f, t₂.mapE f = t₁.mapE f) (base : G.V)
    (h₁ : t₁.mapV base = v₀) (h₂ : t₂.mapV base = v₀)
    (grp : ∀ z, Subgroup (𝔸.vertexGroup (t₂.mapV z)))
    (lab : ∀ f, 𝔸.vertexGroup (Γ.src (t₂.mapE f))) :
    (⟨G, t₁, base, h₁, fun z =>
      (grp z).comap (MulEquiv.cast (M := 𝔸.vertexGroup) (hV z).symm).toMonoidHom,
      fun f => MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) (lab f)⟩ :
        AGraph.{u, v, w, x, u', v'} 𝔸 v₀).subgroup =
      (⟨G, t₂, base, h₂, grp, lab⟩ : AGraph.{u, v, w, x, u', v'} 𝔸 v₀).subgroup := by
  obtain rfl : t₁ = t₂ := SerreGraph.Hom.ext _ (funext hV).symm (funext hE).symm
  congr

/-- Membership in a vertex group, read through equal vertices. -/
private theorem cast_mem_grp (B : AGraph.{u, v, w, x, u', v'} 𝔸 v₀) {z z' : B.graph.V}
    (h : z = z') {T : Type w} {c : T} {h₁ : T = 𝔸.vertexGroup (B.typ.mapV z)}
    {h₂ : T = 𝔸.vertexGroup (B.typ.mapV z')} (hc : cast h₁ c ∈ B.grp z) : cast h₂ c ∈ B.grp z' := by
  subst h
  exact hc

/-- A type-preserving graph morphism `φ : B → B'` of `𝔸`-graphs respecting the base vertices, under
which the labels of `B` are those of `B'` up to the vertex groups of `B'` and a conjugation by
elements `g_z ∈ A_[z]` trivial at the base vertex, gives an inclusion of the represented subgroups.
For a folding map, with equal labels and `g = 1`, this is the consequence `im ν ≤ im ν'` of the
factorisation `ν = ν' ∘ γ` of Kapovich, Weidmann and Myasnikov, Proposition 4.15. -/
theorem subgroup_le_of_hom {B : AGraph.{u, v, w, x, u', v'} 𝔸 v₀}
    {B' : AGraph.{u, v, w, x, u'', v''} 𝔸 v₀} (φ : B.graph.Hom B'.graph)
    (hV : ∀ z : B.graph.V, B'.typ.mapV (φ.mapV z) = B.typ.mapV z)
    (hE : ∀ f : B.graph.E, B'.typ.mapE (φ.mapE f) = B.typ.mapE f)
    (hbase : φ.mapV B.base = B'.base)
    (g : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z)) (hg : g B.base = 1)
    (hgrp : ∀ z : B.graph.V, (B.grp z).map (MulAut.conj (g z)).toMonoidHom ≤
      (B'.grp (φ.mapV z)).comap (MulEquiv.cast (M := 𝔸.vertexGroup) (hV z).symm).toMonoidHom)
    (hlab : ∀ f : B.graph.E, ∃ b' ∈ B'.grpSrc (φ.mapE f), B.labelα f =
      (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm (g (B.graph.src f)))⁻¹ *
        MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f)
          (b' * B'.labelα (φ.mapE f))) :
    B.subgroup ≤ B'.subgroup := by
  -- First relabel `B` by the vertex groups and labels of the images under `φ`, read through the
  -- types of `B`; this is the pullback of `B'` along `φ`, which maps to `B'` letter by letter.
  refine (subgroup_le_relabel (grp := fun z => (B'.grp (φ.mapV z)).comap
    (MulEquiv.cast (M := 𝔸.vertexGroup) (hV z).symm).toMonoidHom) (lab := fun f =>
      MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) (B'.labelα (φ.mapE f)))
        g hgrp (fun f => ?_) hg).trans ?_
  · obtain ⟨b, hb, h⟩ := hlab f
    refine ⟨MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) b, ?_, by rw [h, map_mul]⟩
    rw [mem_grpSrc] at hb
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.cast_apply, cast_cast] at hb ⊢
    exact cast_mem_grp B' (φ.map_src f) hb
  · exact (subgroup_retype (t₁ := B.typ) (t₂ := pullbackTyp B' φ) hV hE B.base B.typ_base _ _
      _).le.trans (subgroup_pullback_le B' φ B.base hbase)

end AGraph

end GraphOfGroups

end TauCeti
