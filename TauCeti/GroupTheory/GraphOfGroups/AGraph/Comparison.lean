/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.AGraph.Basic
public import Mathlib.Tactic.Group

/-!
# Comparing the subgroups represented by two `𝔸`-graphs

Let `B` and `B'` be two `𝔸`-graphs with base vertices of type `v₀`, and let `φ : B → B'` be a
type-preserving graph morphism respecting the base vertices. Suppose that the labels of `B` are
those of `B'` up to the vertex groups of `B'` and up to a conjugation: there are elements
`g_z ∈ A_[z]` such that

* `g_z B_z g_z⁻¹ ≤ B'_{φ(z)}` for every vertex `z` of `B`, and
* `f_α = g_{o(f)}⁻¹ b' φ(f)_α` with `b' ∈ B'_{φ(o(f))}` for every dart `f` of `B`.

Then every `𝔹`-path `p` from `u₀` to `z` lifts to a `𝔹'`-path from `u₀'` to `φ(z)` reading
`g_{u₀} μ(p) g_z⁻¹` up to homotopy, so that `g_{u₀} L(B, u₀) g_{u₀}⁻¹ ≤ L(B', u₀')`. When moreover
`g_{u₀} ∈ B'_{u₀'}`, for instance when `g_{u₀} = 1`, this is an inclusion `L(B, u₀) ≤ L(B', u₀')`.
This inclusion generalises the consequence `im ν ≤ im ν'` of the factorisation `ν = ν' ∘ γ` in
Kapovich, Weidmann and Myasnikov, Proposition 4.15, given there for a folding map with equal labels
and `g = 1`; the generalisation applies to the auxiliary moves A0 and A2 as well, which change only
the vertex groups and the labels.

## Main statements

* `TauCeti.GraphOfGroups.AGraph.subgroup_map_conj_le_mk`: the inclusion
  `g_{u₀} L(B, u₀) g_{u₀}⁻¹ ≤ L(B', u₀)` when `B'` is `B` with other vertex groups and labels, as
  after the auxiliary moves A0 and A2.
* `TauCeti.GraphOfGroups.AGraph.subgroup_map_conj_le_of_hom`: the inclusion
  `g_{u₀} L(B, u₀) g_{u₀}⁻¹ ≤ L(B', u₀')`.
* `TauCeti.GraphOfGroups.AGraph.subgroup_le_of_hom`: the inclusion `L(B, u₀) ≤ L(B', u₀')` when
  `g_{u₀} ∈ B'_{u₀'}`.

## Implementation notes

The two `𝔸`-paths compared have the endpoints `[φ(z)]` and `[z]`, which are only propositionally
equal. The proof therefore first replaces the vertex groups and labels of `B` by those of `B'`,
read through the types of `B` (the paths of `B` are then lifted up to homotopy, with no transport),
and identifies the result with the pullback of `B'` along `φ`, whose type map is `[φ(·)]` by
definition. The morphism of graphs of groups defined by the pullback is the composite of
`AGraph.toHom` for `B'` with the morphism given by `φ`, the identities of the vertex groups and
trivial twisting elements, so the pullback's `ν` factors through `π₁(𝔹', u₀')` (`π₁.map_map`).

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
  refine ⟨⟨_, hgrp a (Subgroup.mem_map_of_mem _ b.property)⟩, ?_⟩
  simp only [Path.comp_ofVertex] at h ⊢
  have e : (g a)⁻¹ * (MulAut.conj (g a)).toMonoidHom b = b * (g a)⁻¹ := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ((h.cons _).trans (.mul _ _ _)).trans ?_
  rw [e]
  exact (Path.Homotopic.mul _ _ _).symm

/-- The end-label step of `homotopic_relabel_dart`: if `(e⁻¹)_α = g_{t(e)}⁻¹ b (e⁻¹)'_α`, then
`e'_ω b⁻¹ = e_ω g_{t(e)}⁻¹`, where `e'_ω` is the end label of `e` after relabelling. -/
private theorem cast_labelω_relabel_mul_inv (e : B.graph.E)
    {b : 𝔸.vertexGroup (Γ.src (B.typ.mapE (B.graph.rev e)))}
    (h : B.labelα (B.graph.rev e) = (MulEquiv.cast (M := 𝔸.vertexGroup)
      (B.typ.map_src (B.graph.rev e)).symm (g (B.graph.src (B.graph.rev e))))⁻¹ *
        (b * lab (B.graph.rev e))) :
    MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ e) ((B.relabel grp lab).labelω e) *
      (MulEquiv.cast (M := 𝔸.vertexGroup) (j := B.typ.mapV (B.graph.tgt e))
        (B.typ.map_src (B.graph.rev e)) b)⁻¹ =
        MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ e) (B.labelω e) *
          (g (B.graph.tgt e))⁻¹ := by
  -- `g` at `o(e⁻¹)` and at `t(e)`, which are the same vertex by definition.
  have hg : ∀ h : 𝔸.vertexGroup (B.typ.mapV (B.graph.src (B.graph.rev e))) =
      𝔸.vertexGroup (B.typ.mapV (B.graph.tgt e)), cast h (g _) = g (B.graph.tgt e) :=
    fun _ => rfl
  rw [labelω_def, labelω_def, h]
  simp only [map_mul, map_inv, inv_inv, mul_inv_rev, MulEquiv.cast_apply, cast_cast, hg,
    mul_inv_cancel_right]
  -- What remains is `b` read at `o(e⁻¹)` and at `t(e)`, the same vertex by definition.
  rfl

include hlab in
/-- The dart step of `exists_relabel_path`. -/
private theorem homotopic_relabel_dart {y : 𝔸.LetterVertex} (e : B.graph.E)
    {P P₁ : 𝔸.Path y ⟨B.typ.mapV (B.graph.src e)⟩}
    (h : Path.Homotopic P₁ (P.comp (Path.ofVertex (g (B.graph.src e))⁻¹))) :
    ∃ (c₁ : grp (B.graph.src e)) (c₂ : grp (B.graph.tgt e)), Path.Homotopic
      (((P₁.comp (Path.ofVertex (c₁ : 𝔸.vertexGroup _))).comp ((B.relabel grp lab).toHom.mapLetter
        (Letter.dart (𝔸 := (B.relabel grp lab).toGraphOfGroups) (B.graph.dart e)))).comp
          (Path.ofVertex (c₂ : 𝔸.vertexGroup _)))
      ((P.comp (B.toHom.mapLetter (Letter.dart (𝔸 := B.toGraphOfGroups) (B.graph.dart e)))).comp
        (Path.ofVertex (g (B.graph.tgt e))⁻¹)) := by
  obtain ⟨b₁, hb₁, h₁⟩ := hlab e
  obtain ⟨b₂, hb₂, h₂⟩ := hlab (B.graph.rev e)
  -- `o(e⁻¹)` is `t(e)` by definition, so `b₂` is an element of the vertex group at `t(e)`.
  let c₂ : grp (B.graph.tgt e) := (⟨_, hb₂⟩ : grp (B.graph.tgt e))⁻¹
  refine ⟨⟨_, hb₁⟩, c₂, ?_⟩
  have hα : (g (B.graph.src e))⁻¹ * MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e) b₁ *
      MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e) (lab e) =
        MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src e) (B.labelα e) := by
    rw [h₁, map_mul, map_mul, map_inv, mul_assoc]
    simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
  -- `c₂` is `b₂⁻¹`, read in the vertex group at `t(e)`.
  have hω : MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ e) ((B.relabel grp lab).labelω e) *
      (c₂ : 𝔸.vertexGroup _) = MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ e) (B.labelω e) *
        (g (B.graph.tgt e))⁻¹ :=
    cast_labelω_relabel_mul_inv g e h₂
  rw [toHom_mapLetter_dart_eq (B.relabel grp lab) e rfl
    (d := ⟨B.typ.mapE e, B.typ.map_src e, B.typ.map_tgt _ e⟩) rfl rfl,
    toHom_mapLetter_dart_eq B e rfl (d := ⟨B.typ.mapE e, B.typ.map_src e, B.typ.map_tgt _ e⟩) rfl
      rfl]
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
`g_{u₀} μ(p) g_y⁻¹` up to homotopy. -/
private theorem exists_relabel_path {y : B.toGraphOfGroups.LetterVertex}
    (p : B.toGraphOfGroups.Path ⟨B.base⟩ y) :
    ∃ p₁ : (B.relabel grp lab).toGraphOfGroups.Path ⟨B.base⟩ ⟨y.as⟩,
      Path.Homotopic ((B.relabel grp lab).toHom.mapPath p₁)
        (((Path.ofVertex (g B.base)).comp (B.toHom.mapPath p)).comp
          (Path.ofVertex (g y.as)⁻¹)) := by
  induction p with
  | nil =>
    refine ⟨.nil, ?_⟩
    rw [Hom.mapPath_nil, Hom.mapPath_nil, Quiver.Path.comp_nil, Path.comp_ofVertex,
      Path.ofVertex_eq_nil_cons]
    refine ((Path.Homotopic.mul _ _ _).trans ?_).symm
    rw [mul_inv_cancel]
    exact .one _
  | cons p l ih =>
    obtain ⟨p₁, h⟩ := ih
    cases l with
    | vertex b =>
      obtain ⟨c, hc⟩ := homotopic_relabel_vertex g hgrp h b
      exact ⟨p₁.cons (Letter.vertex c), by
        simpa only [Hom.mapPath_cons, Hom.mapLetter_vertex, toHom_vertexHom,
          Subgroup.coe_subtype, Quiver.Path.comp_assoc] using hc⟩
    | dart f =>
      obtain ⟨e, rfl, rfl⟩ := f
      obtain ⟨c₁, c₂, hc⟩ := homotopic_relabel_dart g hlab e h
      refine ⟨((p₁.cons (Letter.vertex c₁)).cons (Letter.dart (B.graph.dart e))).cons
        (Letter.vertex c₂), ?_⟩
      rw [← B.graph.dart_def e]
      simpa only [Hom.mapPath_cons, Hom.mapLetter_vertex, toHom_vertexHom, Subgroup.coe_subtype,
        Quiver.Path.comp_assoc] using hc

include hgrp hlab in
/-- Let `B'` be the `𝔸`-graph `B` with the vertex groups `grp` and the labels `lab`, and let
`g_z ∈ A_[z]` be elements with `g_z B_z g_z⁻¹ ≤ B'_z` for every vertex `z` and
`f_α = g_{o(f)}⁻¹ b f'_α` with `b ∈ B'_{o(f)}` for every dart `f`, where `f'_α` is the label of `f`
in `B'`. Then the conjugate `g_{u₀} L(B, u₀) g_{u₀}⁻¹` of the represented subgroup lies in
`L(B', u₀)`, with `g_{u₀}` read in `π₁(𝔸, v₀)`. -/
theorem subgroup_map_conj_le_mk :
    B.subgroup.map (MulAut.conj (MulEquiv.cast (M := π₁ 𝔸) B.typ_base
      (π₁.vertexHom Quiver.Path.nil (g B.base)))).toMonoidHom ≤
        (⟨B.graph, B.typ, B.base, B.typ_base, grp, lab⟩ :
          AGraph.{u, v, w, x, u', v'} 𝔸 v₀).subgroup := by
  rintro _ ⟨_, hx, rfl⟩
  obtain ⟨p, rfl⟩ := (mem_subgroup_iff B).1 hx
  obtain ⟨p₁, h⟩ := exists_relabel_path g hgrp hlab p
  refine (mem_subgroup_iff _).2 ⟨p₁, ?_⟩
  rw [π₁.mk_eq_mk_iff.2 h]
  simp only [π₁.mk_comp, ← π₁.vertexHom_nil_apply, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

end relabel

/-! ### Pulling an `𝔸`-graph back along a graph morphism -/

section pullback

variable (B' : AGraph.{u, v, w, x, u'', v''} 𝔸 v₀) {G : SerreGraph.{u', v'}} (φ : G.Hom B'.graph)
  (base : G.V) (hbase : φ.mapV base = B'.base)

/-- The pullback of `B'` along `φ`: the graph `G` with the vertex groups and labels of the images
under `φ`. -/
private abbrev pullback : AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := G
  typ := B'.typ.comp φ
  base := base
  typ_base := (congrArg B'.typ.mapV hbase).trans B'.typ_base
  grp z := B'.grp (φ.mapV z)
  labelα f := B'.labelα (φ.mapE f)

/-- The morphism from the graph of groups of the pullback to that of `B'`: the graph morphism `φ`,
with the identities of the vertex groups `B'_{φ(z)}` and trivial twisting elements. -/
private abbrev pullbackHom : Hom (pullback B' φ base hbase).toGraphOfGroups B'.toGraphOfGroups where
  graph := φ
  vertexHom _ := MonoidHom.id _
  edgeHom _ := 1
  twist _ := 1
  edgeHom_rev _ _ := rfl
  vertexHom_α _ c := by
    obtain rfl : c = 1 := Subsingleton.elim _ _
    simp only [map_one, mul_one, inv_one]
    -- The identity of `B'_{φ(z)}`, read as a homomorphism of the vertex groups of the two graphs of
    -- groups, sends `1` to `1`.
    rfl

/-- The morphism of graphs of groups defined by the pullback factors through `B'`. -/
private theorem toHom_pullback :
    (pullback B' φ base hbase).toHom = B'.toHom.comp (pullbackHom B' φ base hbase) :=
  Hom.ext rfl (fun _ _ => .rfl) fun _ => heq_of_eq <| by
    simp only [toHom_twist, map_one, one_mul, MulEquiv.cast_apply, cast_cast]
    -- Both sides transport the label of `φ(f)` along proofs of the same equality of vertex groups,
    -- once `SerreGraph.Hom.comp` is unfolded.
    rfl

/-- An element of `π₁(𝔹', z)` at a vertex `z` equal to the base vertex, sent to `π₁(𝔸, v₀)`, lies
in `L(B')`. -/
private theorem cast_map_toHom_mem {z : B'.graph.V} (hz : z = B'.base) (h : B'.typ.mapV z = v₀)
    (x : π₁ B'.toGraphOfGroups z) :
    MulEquiv.cast (M := π₁ 𝔸) h (π₁.map B'.toHom z x) ∈ B'.subgroup := by
  subst hz
  rw [subgroup_def]
  exact ⟨x, B'.π₁Hom_apply x⟩

private theorem subgroup_pullback_le : (pullback B' φ base hbase).subgroup ≤ B'.subgroup := by
  intro _ hx
  rw [subgroup_def] at hx
  obtain ⟨x, rfl⟩ := hx
  rw [π₁Hom_apply, ← π₁.cast_map (toHom_pullback B' φ base hbase).symm base rfl, ← π₁.map_map]
  exact cast_map_toHom_mem B' hbase _ _

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
  have hgrp : (fun z => (grp z).comap (MulEquiv.cast (M := 𝔸.vertexGroup) (hV z).symm).toMonoidHom)
      = grp := by
    funext z
    ext c
    simp [MulEquiv.cast_apply]
  have hlab : (fun f => MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) (lab f)) =
      lab := by
    funext f
    simp [MulEquiv.cast_apply]
  rw [hgrp, hlab]

/-- An element of the vertex group at a vertex equal to the base vertex, read in `π₁(𝔸, v₀)`,
lies in `L(B')`. -/
private theorem cast_vertexHom_nil_mem (B' : AGraph.{u, v, w, x, u', v'} 𝔸 v₀) {a : Γ.V}
    {z : B'.graph.V} (hz : z = B'.base) (ha : B'.typ.mapV z = a) (h : a = v₀)
    {b : 𝔸.vertexGroup a}
    (hb : b ∈ (B'.grp z).comap (MulEquiv.cast (M := 𝔸.vertexGroup) ha.symm).toMonoidHom) :
    MulEquiv.cast (M := π₁ 𝔸) h (π₁.vertexHom Quiver.Path.nil b) ∈ B'.subgroup := by
  subst hz ha
  exact B'.cast_vertexHom_nil_mem_subgroup (by simpa [MulEquiv.cast_apply] using hb)

variable {B : AGraph.{u, v, w, x, u', v'} 𝔸 v₀} {B' : AGraph.{u, v, w, x, u'', v''} 𝔸 v₀}
  (φ : B.graph.Hom B'.graph) (hV : ∀ z : B.graph.V, B'.typ.mapV (φ.mapV z) = B.typ.mapV z)
  (hE : ∀ f : B.graph.E, B'.typ.mapE (φ.mapE f) = B.typ.mapE f) (hbase : φ.mapV B.base = B'.base)
  (g : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z))
  (hgrp : ∀ z : B.graph.V, (B.grp z).map (MulAut.conj (g z)).toMonoidHom ≤
    (B'.grp (φ.mapV z)).comap (MulEquiv.cast (M := 𝔸.vertexGroup) (hV z).symm).toMonoidHom)
  (hlab : ∀ f : B.graph.E, ∃ b' ∈ B'.grpSrc (φ.mapE f), B.labelα f =
    (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm (g (B.graph.src f)))⁻¹ *
      MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) (b' * B'.labelα (φ.mapE f)))

include hbase hgrp hlab in
/-- Let `φ : B → B'` be a type-preserving graph morphism of `𝔸`-graphs respecting the base
vertices, and let `g_z ∈ A_[z]` be elements with `g_z B_z g_z⁻¹ ≤ B'_{φ(z)}` for every vertex `z`
and `f_α = g_{o(f)}⁻¹ b' φ(f)_α` with `b' ∈ B'_{φ(o(f))}` for every dart `f`. Then the conjugate
`g_{u₀} L(B, u₀) g_{u₀}⁻¹` of the represented subgroup lies in `L(B', u₀')`, with `g_{u₀}` read in
`π₁(𝔸, v₀)`. -/
theorem subgroup_map_conj_le_of_hom :
    B.subgroup.map (MulAut.conj (MulEquiv.cast (M := π₁ 𝔸) B.typ_base
      (π₁.vertexHom Quiver.Path.nil (g B.base)))).toMonoidHom ≤ B'.subgroup := by
  -- First relabel `B` by the vertex groups and labels of the images under `φ`, read through the
  -- types of `B`; up to the type map, this is the pullback of `B'` along `φ`, whose morphism of
  -- graphs of groups to `𝔸` factors through `B'`.
  refine (subgroup_map_conj_le_mk (grp := fun z => (B'.grp (φ.mapV z)).comap
    (MulEquiv.cast (M := 𝔸.vertexGroup) (hV z).symm).toMonoidHom) (lab := fun f =>
      MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) (B'.labelα (φ.mapE f)))
        g hgrp (fun f => ?_)).trans ?_
  · obtain ⟨b, hb, h⟩ := hlab f
    refine ⟨MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) (hE f) b, ?_, by rw [h, map_mul]⟩
    rw [mem_grpSrc] at hb
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.cast_apply, cast_cast] at hb ⊢
    exact B'.cast_mem_grp (φ.map_src f) hb
  · exact (subgroup_retype (t₁ := B.typ) (t₂ := B'.typ.comp φ) hV hE B.base B.typ_base _ _
      _).le.trans (subgroup_pullback_le B' φ B.base hbase)

include hbase hgrp hlab in
/-- Let `φ : B → B'` be a type-preserving graph morphism of `𝔸`-graphs respecting the base
vertices, and let `g_z ∈ A_[z]` be elements with `g_z B_z g_z⁻¹ ≤ B'_{φ(z)}` for every vertex `z`
and `f_α = g_{o(f)}⁻¹ b' φ(f)_α` with `b' ∈ B'_{φ(o(f))}` for every dart `f`. If moreover `g_{u₀}`
lies in `B'_{u₀'}`, for instance if `g_{u₀} = 1`, then `L(B, u₀) ≤ L(B', u₀')`. For a folding map,
with equal labels and `g = 1`, this is the consequence `im ν ≤ im ν'` of the factorisation
`ν = ν' ∘ γ` of Kapovich, Weidmann and Myasnikov, Proposition 4.15. -/
theorem subgroup_le_of_hom
    (hg : g B.base ∈ (B'.grp (φ.mapV B.base)).comap
      (MulEquiv.cast (M := 𝔸.vertexGroup) (hV B.base).symm).toMonoidHom) :
    B.subgroup ≤ B'.subgroup := by
  have hx := cast_vertexHom_nil_mem B' hbase (hV B.base) B.typ_base hg
  intro y hy
  have h := subgroup_map_conj_le_of_hom φ hV hE hbase g hgrp hlab (Subgroup.mem_map_of_mem _ hy)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  simpa [mul_assoc] using mul_mem (mul_mem (inv_mem hx) h) hx

end AGraph

end GraphOfGroups

end TauCeti
