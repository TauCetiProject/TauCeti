/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.AGraph.Comparison
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# The auxiliary moves on `𝔸`-graphs

Kapovich, Weidmann and Myasnikov define three moves that change the labels of an `𝔸`-graph `B`
without changing its underlying graph. A conjugation move conjugates the represented subgroup by
its element at the base vertex, so it preserves the subgroup when that element lies in the vertex
group of `B` there, for instance when the move is admissible with respect to the base vertex. A
Bass–Serre move by a family taking the same value on a dart and on its reverse, and a simple
adjustment by elements of the vertex groups of `B`, preserve the represented subgroup.

* The conjugation move A0 at a vertex `u` by `g ∈ A_[u]` replaces `B_u` by `g B_u g⁻¹` and the
  label `f_α` of every dart `f` issuing from `u` by `g f_α`; the label `f_ω` of a dart ending at `u`
  thereby becomes `f_ω g⁻¹`. The move is admissible with respect to the base vertex when `u` is not
  the base vertex.
* The Bass–Serre move A1 at a dart `f` by `c ∈ A_[f]` replaces the label `(a, e, b)` of `f` by
  `(a α_e(c)⁻¹, e, ω_e(c) b)`.
* The simple adjustment A2 at a dart `f` by `a' ∈ B_{o(f)}` replaces `f_α` by `a' f_α`.

Each move is defined here for a whole family of elements at once: `AGraph.conj g` for a family
`g_z ∈ A_[z]` indexed by the vertices, `AGraph.bassSerre c` for a family `c_f ∈ A_[f]` indexed by
the darts, and `AGraph.adjust a` for a family `a_f ∈ A_{o([f])}` indexed by the darts. The moves
A0 at a single vertex and A2 at a single dart are the families `Pi.mulSingle`. A family of
Bass–Serre moves is a move on geometric edges when `c` takes the same value on a dart and on its
reverse; the move A1 at a single dart `f` is the family with value `c` at `f` and at its reverse,
and `1` elsewhere.

## Main definitions

* `TauCeti.GraphOfGroups.AGraph.conj`: the conjugation move A0.
* `TauCeti.GraphOfGroups.AGraph.bassSerre`: the Bass–Serre move A1.
* `TauCeti.GraphOfGroups.AGraph.adjust`: the simple adjustment A2.

## Main statements

* `TauCeti.GraphOfGroups.AGraph.subgroup_conj`: a conjugation move conjugates the represented
  subgroup by the element at the base vertex.
* `TauCeti.GraphOfGroups.AGraph.subgroup_conj_of_mem`: a conjugation move whose element at the
  base vertex lies in the vertex group there, for instance an admissible one, preserves the
  represented subgroup.
* `TauCeti.GraphOfGroups.AGraph.subgroup_bassSerre`: a Bass–Serre move by a family taking the same
  value on a dart and on its reverse preserves the represented subgroup.
* `TauCeti.GraphOfGroups.AGraph.subgroup_adjust`: a simple adjustment by elements of the vertex
  groups preserves the represented subgroup.
* `TauCeti.GraphOfGroups.AGraph.isFolded_conj_iff`,
  `TauCeti.GraphOfGroups.AGraph.isFolded_bassSerre_iff` and
  `TauCeti.GraphOfGroups.AGraph.isFolded_adjust_iff`: every conjugation move, a Bass–Serre move by
  a family taking the same value on a dart and on its reverse, and a simple adjustment by elements
  of the vertex groups preserve foldedness.
* `TauCeti.GraphOfGroups.AGraph.complexity_conj`: a conjugation move preserves the complexity.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §4.1, Definitions 4.5, 4.6 and 4.7, Proposition 4.15
  and Lemma 4.16.
-/

public section

universe u v w x u' v'

namespace TauCeti

namespace GraphOfGroups

namespace AGraph

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
  (B : AGraph.{u, v, w, x, u', v'} 𝔸 v₀)

/-! ### The conjugation move A0 -/

/-- The conjugation move A0 by a family `g_z ∈ A_[z]`: the vertex group `B_z` is replaced by
`g_z B_z g_z⁻¹` and the label `f_α` of a dart `f` by `g_{o(f)} f_α`. The underlying graph, the type
map and the base vertex are unchanged. The definition is exposed and unfolds at instance
transparency, so that vertices and darts of `B` are accepted as vertices and darts of the result by
rewriting, simplification and instance search, and moves can be chained. -/
@[expose, instance_reducible]
def conj (g : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z)) :
    AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := B.graph
  typ := B.typ
  base := B.base
  typ_base := B.typ_base
  grp z := (B.grp z).map (MulAut.conj (g z)).toMonoidHom
  labelα f :=
    MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm (g (B.graph.src f)) * B.labelα f

section conj

variable (g : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z))

@[simp] theorem conj_graph : (B.conj g).graph = B.graph :=
  rfl

@[simp] theorem conj_typ : (B.conj g).typ = B.typ :=
  rfl

@[simp] theorem conj_base : (B.conj g).base = B.base :=
  rfl

@[simp] theorem conj_grp (z : B.graph.V) :
    (B.conj g).grp z = (B.grp z).map (MulAut.conj (g z)).toMonoidHom :=
  rfl

@[simp] theorem conj_labelα (f : B.graph.E) : (B.conj g).labelα f =
    MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm (g (B.graph.src f)) * B.labelα f :=
  rfl

/-- After a conjugation move the label `f_ω` of a dart `f` is `f_ω g_{t(f)}⁻¹`. -/
@[simp] theorem labelω_conj (f : B.graph.E) : (B.conj g).labelω f = B.labelω f *
    (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ f).symm (g (B.graph.tgt f)))⁻¹ := by
  unfold conj
  rw [labelω_def, labelω_def, map_mul, mul_inv_rev]
  congr 2
  -- `g` at `o(f⁻¹)` and at `t(f)`, which are the same vertex by definition.
  simp only [MulEquiv.cast_apply, cast_cast]
  rfl

/-- After a conjugation move the vertex group at the start of a dart `f` is conjugated by
`g_{o(f)}`. -/
@[simp] theorem grpSrc_conj (f : B.graph.E) : (B.conj g).grpSrc f = (B.grpSrc f).map
    (MulAut.conj (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm
      (g (B.graph.src f)))).toMonoidHom := by
  ext c
  rw [mem_grpSrc, conj_grp, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, mem_grpSrc,
    MulAut.conj_symm_apply, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
  -- The start of `f` in `B.conj g` is its start in `B` by definition.
  rfl

/-- After a conjugation move the vertex group at the end of a dart `f` is conjugated by
`g_{t(f)}`. -/
@[simp] theorem grpTgt_conj (f : B.graph.E) : (B.conj g).grpTgt f = (B.grpTgt f).map
    (MulAut.conj (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ f).symm
      (g (B.graph.tgt f)))).toMonoidHom := by
  ext c
  rw [mem_grpTgt, conj_grp, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, mem_grpTgt,
    MulAut.conj_symm_apply, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
  -- The end of `f` in `B.conj g` is its end in `B` by definition.
  rfl

/-- A conjugation move preserves the ranks of the vertex groups. -/
@[simp] theorem rankGrp_conj (z : B.graph.V) : (B.conj g).rankGrp z = B.rankGrp z :=
  rankGrp_congr (Subgroup.equivMapOfInjective (B.grp z) _ (MulAut.conj (g z)).injective).symm

/-- The conjugation move by the trivial family is the identity. -/
@[simp] theorem conj_one : B.conj 1 = B := by
  cases B
  unfold conj
  congr 1
  · funext z
    simp [MulAut.one_def]
  · funext f
    rw [Pi.one_apply, map_one, one_mul]

/-- Two conjugation moves compose to the conjugation move by the product family. -/
@[simp] theorem conj_conj (g' : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z)) :
    (B.conj g).conj g' = B.conj (g' * g) := by
  unfold conj
  congr 1
  · funext z
    simp [Subgroup.map_map, MulAut.mul_def]
  · funext f
    rw [Pi.mul_apply, map_mul, mul_assoc]

/-- A conjugation move conjugates the represented subgroup by the element `g_{u₀}` at the base
vertex, read in `π₁(𝔸, v₀)` (Kapovich, Weidmann and Myasnikov, Proposition 4.15 for the move A0,
which they apply away from the base vertex). -/
theorem subgroup_conj : (B.conj g).subgroup = B.subgroup.map (MulAut.conj (MulEquiv.cast
    (M := π₁ 𝔸) B.typ_base (π₁.vertexHom Quiver.Path.nil (g B.base)))).toMonoidHom := by
  -- `B.conj g` is `B` with new vertex groups and labels, and `B` is `B.conj g` with the old ones,
  -- so both inclusions come from `subgroup_map_conj_le_mk`, with the families `g` and `g⁻¹`.
  have h₁ : B.subgroup.map _ ≤ (B.conj g).subgroup :=
    subgroup_map_conj_le_mk g (fun z => le_rfl) fun f => ⟨1, one_mem _, by
      simp only [one_mul, inv_mul_cancel_left]⟩
  have h₂ : (B.conj g).subgroup.map (MulAut.conj (MulEquiv.cast (M := π₁ 𝔸) B.typ_base
      (π₁.vertexHom Quiver.Path.nil (g B.base)⁻¹))).toMonoidHom ≤ B.subgroup :=
    subgroup_map_conj_le_mk (B := B.conj g) g⁻¹ (fun z => ?_) fun f => ⟨1, one_mem _, ?_⟩
  · refine le_antisymm (fun y hy => ⟨_, h₂ (Subgroup.mem_map_of_mem _ hy), ?_⟩) h₁
    simp only [map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply]
    group
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hc
  · simp [map_inv]

/-- A conjugation move whose element `g_{u₀}` at the base vertex lies in the vertex group `B_{u₀}`
preserves the represented subgroup; this covers the moves A0 admissible with respect to the base
vertex, with `g_{u₀} = 1` (Kapovich, Weidmann and Myasnikov, Proposition 4.15 for the move A0). -/
@[simp] theorem subgroup_conj_of_mem (hg : g B.base ∈ B.grp B.base) :
    (B.conj g).subgroup = B.subgroup := by
  rw [subgroup_conj]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer (B.cast_vertexHom_nil_mem_subgroup hg))

/-- A conjugation move preserves finiteness. -/
@[simp] theorem isFinite_conj_iff : (B.conj g).IsFinite ↔ B.IsFinite := by
  unfold conj
  refine ⟨fun h => ⟨h.finite_E, h.connected, fun z => ?_⟩,
    fun h => ⟨h.finite_E, h.connected, fun z => have := h.fg z; inferInstance⟩⟩
  exact (isMulFG_congr (Subgroup.equivMapOfInjective (B.grp z) _
    (MulAut.conj (g z)).injective)).2 (h.fg z)

/-- A conjugation move preserves the complexity. -/
@[simp] theorem complexity_conj : (B.conj g).complexity = B.complexity := by
  rw [complexity_def, complexity_def]
  exact congrArg _ (finsum_congr (B.rankGrp_conj g))

variable {B} in
/-- A conjugation move carries a folded `𝔸`-graph to a folded one (Kapovich, Weidmann and
Myasnikov, Lemma 4.16 (1)). -/
theorem IsFolded.conj (hB : B.IsFolded) : (B.conj g).IsFolded where
  eq_of_label f₁ f₂ hs he := by
    rintro ⟨a', ha', c, h⟩
    rw [grpSrc_conj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at ha'
    refine hB.eq_of_label f₁ f₂ hs he ⟨_, ha', c, ?_⟩
    -- `g` at `o(f₂)`, read in the vertex group of `o([f₁])`, is `g` at `o(f₁)`.
    have hg : MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) he
        (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f₂).symm (g (B.graph.src f₂))) =
          MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f₁).symm (g (B.graph.src f₁)) := by
      simp only [MulEquiv.cast_apply, cast_cast]
      exact eq_of_heq ((cast_heq _ _).trans ((congr_arg_heq g hs.symm).trans (cast_heq _ _).symm))
    rw [conj_labelα, conj_labelα, map_mul, hg] at h
    rw [eq_inv_mul_of_mul_eq h]
    simp only [mul_assoc, conj_typ]
  comap_eq f := by
    rw [grpSrc_conj, grpTgt_conj, conj_labelα, labelω_conj, Subgroup.map_conj_map_conj,
      Subgroup.map_conj_map_conj, mul_inv_rev, inv_mul_cancel_right, inv_mul_cancel_right]
    exact hB.comap_eq f

/-- A conjugation move preserves foldedness (Kapovich, Weidmann and Myasnikov, Lemma 4.16 (1)). -/
@[simp] theorem isFolded_conj_iff : (B.conj g).IsFolded ↔ B.IsFolded :=
  ⟨fun h => by simpa using IsFolded.conj (B := B.conj g) g⁻¹ h, fun h => h.conj g⟩

end conj

/-! ### The Bass–Serre move A1 -/

/-- The Bass–Serre move A1 by a family `c_f ∈ A_[f]`: the label `f_α` of a dart `f` is replaced by
`f_α α_[f](c_f)⁻¹`. When `c` takes the same value on a dart and on its reverse, the label
`(a, e, b)` of `f` becomes `(a α_e(c_f)⁻¹, e, ω_e(c_f) b)`. As for `AGraph.conj`, the definition
is exposed and unfolds at instance transparency. -/
@[expose, instance_reducible]
def bassSerre (c : ∀ f : B.graph.E, 𝔸.edgeGroup (Γ.toGeomEdge (B.typ.mapE f))) :
    AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := B.graph
  typ := B.typ
  base := B.base
  typ_base := B.typ_base
  grp := B.grp
  labelα f := B.labelα f * (𝔸.α (B.typ.mapE f) (c f))⁻¹

section bassSerre

variable (c : ∀ f : B.graph.E, 𝔸.edgeGroup (Γ.toGeomEdge (B.typ.mapE f)))

@[simp] theorem bassSerre_graph : (B.bassSerre c).graph = B.graph :=
  rfl

@[simp] theorem bassSerre_typ : (B.bassSerre c).typ = B.typ :=
  rfl

@[simp] theorem bassSerre_base : (B.bassSerre c).base = B.base :=
  rfl

@[simp] theorem bassSerre_grp (z : B.graph.V) : (B.bassSerre c).grp z = B.grp z :=
  rfl

@[simp] theorem bassSerre_labelα (f : B.graph.E) :
    (B.bassSerre c).labelα f = B.labelα f * (𝔸.α (B.typ.mapE f) (c f))⁻¹ :=
  rfl

/-- After a Bass–Serre move the label `f_ω` of a dart `f` is `ω_[f](c_{f⁻¹}) f_ω`, where the
element `c_{f⁻¹}` of `A_{[f⁻¹]}` is read in `A_{[f]}` through `[f⁻¹] = [f]⁻¹`, a dart with the same
edge group as `[f]`. -/
@[simp] theorem labelω_bassSerre (f : B.graph.E) : (B.bassSerre c).labelω f =
    𝔸.ω (B.typ.mapE f) (MulEquiv.cast (M := 𝔸.edgeGroup)
      ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)) (c (B.graph.rev f))) *
      B.labelω f := by
  unfold bassSerre
  rw [labelω_def, labelω_def, map_mul, mul_inv_rev, map_inv, inv_inv,
    ← 𝔸.cast_α_eq_ω (B.typ.map_rev f) ((congrArg Γ.src (B.typ.map_rev f)).trans (Γ.src_rev _))
      ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]

@[simp] theorem grpSrc_bassSerre (f : B.graph.E) : (B.bassSerre c).grpSrc f = B.grpSrc f := by
  ext
  rw [mem_grpSrc, mem_grpSrc]
  -- The vertex groups and the start of `f` are those of `B` by definition.
  rfl

@[simp] theorem grpTgt_bassSerre (f : B.graph.E) : (B.bassSerre c).grpTgt f = B.grpTgt f := by
  ext
  rw [mem_grpTgt, mem_grpTgt]
  -- The vertex groups and the end of `f` are those of `B` by definition.
  rfl

@[simp] theorem rankGrp_bassSerre (z : B.graph.V) : (B.bassSerre c).rankGrp z = B.rankGrp z :=
  rankGrp_congr (MulEquiv.refl _)

/-- The Bass–Serre move by the trivial family is the identity. -/
@[simp] theorem bassSerre_one : B.bassSerre 1 = B := by
  cases B
  simp [bassSerre]

/-- Two Bass–Serre moves compose to the Bass–Serre move by the product family. -/
@[simp] theorem bassSerre_bassSerre
    (c' : ∀ f : B.graph.E, 𝔸.edgeGroup (Γ.toGeomEdge (B.typ.mapE f))) :
    (B.bassSerre c).bassSerre c' = B.bassSerre (c' * c) := by
  unfold bassSerre
  simp [mul_assoc]

variable {B c} in
/-- After a Bass–Serre move by a family taking the same value on a dart `f` and on its reverse,
the label `f_ω` of `f` is `ω_[f](c_f) f_ω`. -/
theorem labelω_bassSerre_of_rev {f : B.graph.E} (hc : c (B.graph.rev f) = MulEquiv.cast
    (M := 𝔸.edgeGroup) ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm
      (c f)) :
    (B.bassSerre c).labelω f = 𝔸.ω (B.typ.mapE f) (c f) * B.labelω f := by
  rw [labelω_bassSerre, hc]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]

variable {B c} in
/-- The dart letter of `B.bassSerre c` is read as `a α(c)⁻¹, e, ω(c) b`, which is homotopic to the
reading `a, e, b` of the dart in `B`, when `c` takes the same value on the dart and on its
reverse. -/
private theorem homotopic_toHom_mapLetter_bassSerre {e : B.graph.E}
    (hc : c (B.graph.rev e) = MulEquiv.cast (M := 𝔸.edgeGroup)
      ((congrArg Γ.toGeomEdge (B.typ.map_rev e)).trans (Γ.toGeomEdge_rev _)).symm (c e)) :
    Path.Homotopic ((B.bassSerre c).toHom.mapLetter (Letter.dart ((B.bassSerre c).graph.dart e)))
      (B.toHom.mapLetter (Letter.dart (B.graph.dart e))) := by
  rw [toHom_mapLetter_dart_eq (B.bassSerre c) e rfl
    (d := ⟨B.typ.mapE e, B.typ.map_src e, B.typ.map_tgt _ e⟩) rfl rfl,
    toHom_mapLetter_dart_eq B e rfl (d := ⟨B.typ.mapE e, B.typ.map_src e, B.typ.map_tgt _ e⟩) rfl
      rfl, bassSerre_labelα, labelω_bassSerre_of_rev hc, map_mul, map_mul, map_inv]
  have h := Path.Homotopic.dart_αArrow_ωArrow (𝔸 := 𝔸)
    ⟨B.typ.mapE e, B.typ.map_src e, B.typ.map_tgt _ e⟩ (c e)
  rw [αArrow_apply, ωArrow_apply] at h
  exact h _ _

variable {B c} in
/-- Every `𝔹`-path is read as homotopic `𝔸`-paths in `B.bassSerre c` and in `B`, when `c` takes the
same value on a dart and on its reverse. -/
private theorem homotopic_toHom_mapPath_bassSerre (hc : ∀ f, c (B.graph.rev f) =
    MulEquiv.cast (M := 𝔸.edgeGroup)
      ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm (c f))
    {y z : B.toGraphOfGroups.LetterVertex} (p : B.toGraphOfGroups.Path y z) :
    Path.Homotopic ((B.bassSerre c).toHom.mapPath p) (B.toHom.mapPath p) := by
  induction p with
  | nil =>
    rw [Hom.mapPath_nil, Hom.mapPath_nil]
    exact .refl _
  | cons p l ih =>
    rw [Hom.mapPath_cons, Hom.mapPath_cons]
    refine ih.comp ?_
    cases l with
    | vertex b =>
      rw [Hom.mapLetter_vertex, Hom.mapLetter_vertex]
      exact .refl _
    | dart f =>
      obtain ⟨e, rfl, rfl⟩ := f
      rw [← B.graph.dart_def e]
      -- The dart `e` of `B` is a dart of `B.bassSerre c`, whose graph is that of `B`.
      exact homotopic_toHom_mapLetter_bassSerre (hc e)

/-- A Bass–Serre move by a family taking the same value on a dart and on its reverse preserves the
represented subgroup (Kapovich, Weidmann and Myasnikov, Proposition 4.15 for the move A1). -/
@[simp] theorem subgroup_bassSerre (hc : ∀ f, c (B.graph.rev f) = MulEquiv.cast (M := 𝔸.edgeGroup)
    ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm (c f)) :
    (B.bassSerre c).subgroup = B.subgroup := by
  -- Every `𝔹`-path reads homotopic `𝔸`-paths in `B` and in `B.bassSerre c`.
  ext x
  rw [mem_subgroup_iff, mem_subgroup_iff]
  constructor <;> rintro ⟨p, rfl⟩ <;> refine ⟨p, ?_⟩
  exacts [congrArg _ (π₁.mk_eq_mk_iff.2 (homotopic_toHom_mapPath_bassSerre hc p).symm),
    congrArg _ (π₁.mk_eq_mk_iff.2 (homotopic_toHom_mapPath_bassSerre hc p))]

/-- A Bass–Serre move preserves finiteness. -/
@[simp] theorem isFinite_bassSerre_iff : (B.bassSerre c).IsFinite ↔ B.IsFinite :=
  ⟨fun h => ⟨h.finite_E, h.connected, h.fg⟩, fun h => ⟨h.finite_E, h.connected, h.fg⟩⟩

/-- A Bass–Serre move preserves the complexity. -/
@[simp] theorem complexity_bassSerre : (B.bassSerre c).complexity = B.complexity := by
  rw [complexity_def, complexity_def]
  exact congrArg _ (finsum_congr (B.rankGrp_bassSerre c))

variable {B c} in
/-- A Bass–Serre move by a family taking the same value on a dart and on its reverse carries a
folded `𝔸`-graph to a folded one (Kapovich, Weidmann and Myasnikov, Lemma 4.16 (1)). -/
theorem IsFolded.bassSerre (hB : B.IsFolded) (hc : ∀ f, c (B.graph.rev f) = MulEquiv.cast
    (M := 𝔸.edgeGroup) ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm
      (c f)) : (B.bassSerre c).IsFolded where
  eq_of_label f₁ f₂ hs he := by
    rintro ⟨a', ha', c₀, h⟩
    rw [grpSrc_bassSerre] at ha'
    -- `α` of the type of `f₂`, read through the equal type of `f₁`.
    have hα : MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) he
        (𝔸.α (B.typ.mapE f₂) (c f₂)) = 𝔸.α (B.typ.mapE f₁)
          (MulEquiv.cast (M := 𝔸.edgeGroup) (congrArg Γ.toGeomEdge he) (c f₂)) := by
      have key : ∀ {e e' : Γ.E} (h : e = e') (d : 𝔸.edgeGroup (Γ.toGeomEdge e)),
          MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) h (𝔸.α e d) =
            𝔸.α e' (MulEquiv.cast (M := 𝔸.edgeGroup) (congrArg Γ.toGeomEdge h) d) := by
        rintro e _ rfl d
        simp only [MulEquiv.cast_apply, cast_eq]
      exact key he (c f₂)
    rw [bassSerre_labelα, bassSerre_labelα, map_mul, map_inv, hα] at h
    refine hB.eq_of_label f₁ f₂ hs he ⟨a', ha', (c f₁)⁻¹ * c₀ *
      MulEquiv.cast (M := 𝔸.edgeGroup) (congrArg Γ.toGeomEdge he) (c f₂), ?_⟩
    rw [mul_inv_eq_iff_eq_mul.1 h, map_mul, map_mul, map_inv]
    simp only [mul_assoc, bassSerre_typ]
  comap_eq f := by
    rw [grpSrc_bassSerre, grpTgt_bassSerre, bassSerre_labelα, labelω_bassSerre_of_rev (hc f),
      mul_inv_rev, inv_inv, ← Subgroup.map_conj_map_conj, ← Subgroup.map_conj_map_conj]
    simp only [bassSerre_typ]
    rw [Subgroup.comap_map_conj, Subgroup.comap_map_conj, hB.comap_eq f]

/-- A Bass–Serre move by a family taking the same value on a dart and on its reverse preserves
foldedness (Kapovich, Weidmann and Myasnikov, Lemma 4.16 (1)). -/
@[simp] theorem isFolded_bassSerre_iff (hc : ∀ f, c (B.graph.rev f) =
    MulEquiv.cast (M := 𝔸.edgeGroup)
      ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm (c f)) :
    (B.bassSerre c).IsFolded ↔ B.IsFolded := by
  refine ⟨fun h => ?_, fun h => h.bassSerre hc⟩
  -- The family `c⁻¹` takes the same value on a dart and on its reverse; the darts of
  -- `B.bassSerre c` are those of `B`.
  simpa using IsFolded.bassSerre (B := B.bassSerre c) (c := c⁻¹) h fun f => by
    rw [Pi.inv_apply, Pi.inv_apply, map_inv]
    exact congrArg Inv.inv (hc f)

end bassSerre

/-! ### The simple adjustment A2 -/

/-- The simple adjustment A2 by a family `a_f ∈ A_{o([f])}`: the label `f_α` of a dart `f` is
replaced by `a_f f_α`. The move of Kapovich, Weidmann and Myasnikov takes `a_f` in the vertex group
`B_{o(f)}`. As for `AGraph.conj`, the definition is exposed and unfolds at instance transparency. -/
@[expose, instance_reducible]
def adjust (a : ∀ f : B.graph.E, 𝔸.vertexGroup (Γ.src (B.typ.mapE f))) :
    AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := B.graph
  typ := B.typ
  base := B.base
  typ_base := B.typ_base
  grp := B.grp
  labelα f := a f * B.labelα f

section adjust

variable (a : ∀ f : B.graph.E, 𝔸.vertexGroup (Γ.src (B.typ.mapE f)))

@[simp] theorem adjust_graph : (B.adjust a).graph = B.graph :=
  rfl

@[simp] theorem adjust_typ : (B.adjust a).typ = B.typ :=
  rfl

@[simp] theorem adjust_base : (B.adjust a).base = B.base :=
  rfl

@[simp] theorem adjust_grp (z : B.graph.V) : (B.adjust a).grp z = B.grp z :=
  rfl

@[simp] theorem adjust_labelα (f : B.graph.E) : (B.adjust a).labelα f = a f * B.labelα f :=
  rfl

/-- After a simple adjustment the label `f_ω` of a dart `f` is `f_ω a_{f⁻¹}⁻¹`. -/
@[simp] theorem labelω_adjust (f : B.graph.E) : (B.adjust a).labelω f = B.labelω f *
    (MulEquiv.cast (M := 𝔸.vertexGroup) ((congrArg Γ.src (B.typ.map_rev f)).trans (Γ.src_rev _))
      (a (B.graph.rev f)))⁻¹ := by
  unfold adjust
  rw [labelω_def, labelω_def, map_mul, mul_inv_rev]

@[simp] theorem grpSrc_adjust (f : B.graph.E) : (B.adjust a).grpSrc f = B.grpSrc f := by
  ext
  rw [mem_grpSrc, mem_grpSrc]
  -- The vertex groups and the start of `f` are those of `B` by definition.
  rfl

@[simp] theorem grpTgt_adjust (f : B.graph.E) : (B.adjust a).grpTgt f = B.grpTgt f := by
  ext
  rw [mem_grpTgt, mem_grpTgt]
  -- The vertex groups and the end of `f` are those of `B` by definition.
  rfl

@[simp] theorem rankGrp_adjust (z : B.graph.V) : (B.adjust a).rankGrp z = B.rankGrp z :=
  rankGrp_congr (MulEquiv.refl _)

/-- The simple adjustment by the trivial family is the identity. -/
@[simp] theorem adjust_one : B.adjust 1 = B := by
  cases B
  simp [adjust]

/-- Two simple adjustments compose to the simple adjustment by the product family. -/
@[simp] theorem adjust_adjust (a' : ∀ f : B.graph.E, 𝔸.vertexGroup (Γ.src (B.typ.mapE f))) :
    (B.adjust a).adjust a' = B.adjust (a' * a) := by
  unfold adjust
  simp [mul_assoc]

/-- A simple adjustment by elements of the vertex groups preserves the represented subgroup
(Kapovich, Weidmann and Myasnikov, Proposition 4.15 for the move A2). -/
@[simp] theorem subgroup_adjust (ha : ∀ f, a f ∈ B.grpSrc f) :
    (B.adjust a).subgroup = B.subgroup := by
  -- `B.adjust a` is `B` with new labels, and `B` is `B.adjust a` with the old ones, so both
  -- inclusions come from `subgroup_map_conj_le_mk`, with `g = 1`, whose conjugation is trivial,
  -- and the elements `a_f` and `a_f⁻¹` of the vertex groups.
  have hgrp : ∀ z, (B.grp z).map
      (MulAut.conj ((1 : ∀ z, 𝔸.vertexGroup (B.typ.mapV z)) z)).toMonoidHom ≤ B.grp z := by
    simp [MulAut.one_def]
  refine le_antisymm ((le_of_eq ?_).trans (subgroup_map_conj_le_mk (B := B.adjust a)
    (lab := B.labelα) 1 hgrp fun f => ⟨a f, (mem_grpSrc B).1 (ha f), ?_⟩))
      ((le_of_eq ?_).trans (subgroup_map_conj_le_mk (lab := fun f => a f * B.labelα f) 1 hgrp
        fun f => ⟨(a f)⁻¹, inv_mem ((mem_grpSrc B).1 (ha f)), ?_⟩))
  · simp [MulAut.one_def, -MulEquiv.cast_apply]
  · simp only [adjust_labelα, Pi.one_apply, map_one, inv_one, one_mul]
  · simp [MulAut.one_def, -MulEquiv.cast_apply]
  · simp only [Pi.one_apply, map_one, inv_one, one_mul, inv_mul_cancel_left]

/-- A simple adjustment preserves finiteness. -/
@[simp] theorem isFinite_adjust_iff : (B.adjust a).IsFinite ↔ B.IsFinite :=
  ⟨fun h => ⟨h.finite_E, h.connected, h.fg⟩, fun h => ⟨h.finite_E, h.connected, h.fg⟩⟩

/-- A simple adjustment preserves the complexity. -/
@[simp] theorem complexity_adjust : (B.adjust a).complexity = B.complexity := by
  rw [complexity_def, complexity_def]
  exact congrArg _ (finsum_congr (B.rankGrp_adjust a))

variable {B a} in
/-- A simple adjustment by elements of the vertex groups carries a folded `𝔸`-graph to a folded
one (Kapovich, Weidmann and Myasnikov, Lemma 4.16 (1)). -/
theorem IsFolded.adjust (hB : B.IsFolded) (ha : ∀ f, a f ∈ B.grpSrc f) :
    (B.adjust a).IsFolded where
  eq_of_label f₁ f₂ hs he := by
    rintro ⟨a', ha', c, h⟩
    rw [grpSrc_adjust] at ha'
    -- `a_{f₂}`, read in the vertex group of `o([f₁])`, lies in the vertex group at `o(f₁)`.
    have h₂ : MulEquiv.cast (M := fun e => 𝔸.vertexGroup (Γ.src e)) he (a f₂) ∈ B.grpSrc f₁ := by
      have := ha f₂
      rw [mem_grpSrc] at this ⊢
      simp only [MulEquiv.cast_apply, cast_cast] at this ⊢
      exact B.cast_mem_grp hs.symm this
    refine hB.eq_of_label f₁ f₂ hs he ⟨_, mul_mem (mul_mem (inv_mem h₂) ha') (ha f₁), c, ?_⟩
    rw [adjust_labelα, adjust_labelα, map_mul] at h
    rw [eq_inv_mul_of_mul_eq h]
    simp only [mul_assoc, adjust_typ]
  comap_eq f := by
    -- `a_{f⁻¹}`, read in the vertex group of `t([f])`, lies in the vertex group at `t(f)`.
    have h₂ : MulEquiv.cast (M := 𝔸.vertexGroup) ((congrArg Γ.src (B.typ.map_rev f)).trans
        (Γ.src_rev _)) (a (B.graph.rev f)) ∈ B.grpTgt f := by
      have := ha (B.graph.rev f)
      rw [mem_grpSrc] at this
      rw [mem_grpTgt]
      simp only [MulEquiv.cast_apply, cast_cast] at this ⊢
      exact B.cast_mem_grp (B.graph.src_rev f) this
    rw [grpSrc_adjust, grpTgt_adjust, adjust_labelα, labelω_adjust, mul_inv_rev,
      ← Subgroup.map_conj_map_conj, ← Subgroup.map_conj_map_conj]
    simpa only [adjust_typ, MulEquiv.toMonoidHom_eq_coe,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (inv_mem (ha f))),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (inv_mem h₂))]
      using hB.comap_eq f

/-- A simple adjustment by elements of the vertex groups preserves foldedness (Kapovich, Weidmann
and Myasnikov, Lemma 4.16 (1)). -/
@[simp] theorem isFolded_adjust_iff (ha : ∀ f, a f ∈ B.grpSrc f) :
    (B.adjust a).IsFolded ↔ B.IsFolded := by
  refine ⟨fun h => ?_, fun h => h.adjust ha⟩
  simpa using IsFolded.adjust (B := B.adjust a) (a := a⁻¹) h fun f => by
    simpa using inv_mem (ha f)

end adjust

/-! ### The moves on a single edge -/

section segment

variable {P Q : Type w} {C : Type x} [Group P] [Group Q] [Group C] (f : C →* P) (g : C →* Q)
  (hf : Function.Injective f) (hg : Function.Injective g)
  (P₀ : Subgroup P) (Q₀ : Subgroup Q) (a : P) (b : Q)

/-- The conjugation move on a single edge `(a, e, b)` by `p` at its start and `q` at its end gives
the single edge `(p a, e, b q⁻¹)` with the groups `p P₀ p⁻¹` and `q Q₀ q⁻¹` (Kapovich, Weidmann and
Myasnikov, Figure 3). Every family indexed by the two vertices is of this form. -/
theorem segment_conj (p : P) (q : Q) :
    (segment f g hf hg P₀ Q₀ a b).conj (fun z => Bool.rec (motive := fun z => cond z Q P) p q z) =
      segment f g hf hg (P₀.map (MulAut.conj p).toMonoidHom) (Q₀.map (MulAut.conj q).toMonoidHom)
        (p * a) (b * q⁻¹) := by
  -- The vertices and darts of the single edge are the Booleans, and its vertex groups `P` and `Q`,
  -- only after unfolding; the components are then compared one Boolean at a time.
  unfold conj segment
  congr 1
  · funext z
    cases z <;> rfl
  · funext e
    cases e <;> dsimp only
    · exact congrArg (· * a) ((MulEquiv.cast_apply _ _).trans (cast_eq _ p))
    · rw [mul_inv_rev, inv_inv]
      exact congrArg (· * b⁻¹) ((MulEquiv.cast_apply _ _).trans (cast_eq _ q))

/-- The Bass–Serre move on a single edge `(a, e, b)` by a family `c` gives the single edge
`(a f(c_e)⁻¹, e, g(c_{e⁻¹}) b)`; for a constant family this is Figure 4 of Kapovich, Weidmann and
Myasnikov. -/
theorem segment_bassSerre (c : Bool → C) :
    (segment f g hf hg P₀ Q₀ a b).bassSerre c =
      segment f g hf hg P₀ Q₀ (a * (f (c false))⁻¹) (g (c true) * b) := by
  -- As in `segment_conj`, the labels are compared one Boolean at a time after unfolding.
  unfold bassSerre segment
  congr 1
  funext e
  cases e
  · exact congrArg (fun x => a * x⁻¹)
      (DFunLike.congr_fun (GraphOfGroups.segment_α_false ..) (c false))
  · rw [mul_inv_rev]
    exact congrArg (fun x => b⁻¹ * x⁻¹)
      (DFunLike.congr_fun (GraphOfGroups.segment_α_true ..) (c true))

/-- The simple adjustment of a single edge `(a, e, b)` by `p` at its start and `q` at the start of
its reverse gives the single edge `(p a, e, b q⁻¹)` (Kapovich, Weidmann and Myasnikov, Figure 5).
Every family indexed by the two darts is of this form. -/
theorem segment_adjust (p : P) (q : Q) :
    (segment f g hf hg P₀ Q₀ a b).adjust (fun e => Bool.rec (motive := fun e => cond e Q P) p q e) =
      segment f g hf hg P₀ Q₀ (p * a) (b * q⁻¹) := by
  -- As in `segment_conj`, the labels are compared one Boolean at a time after unfolding.
  unfold adjust segment
  congr 1
  funext e
  cases e
  · -- The vertex group at the start of the dart `false` is `P` by definition.
    rfl
  · -- The vertex group at the start of the dart `true` is `Q` by definition.
    exact ((mul_inv_rev b q⁻¹).trans (congrArg (· * b⁻¹) (inv_inv q))).symm

end segment

end AGraph

end GraphOfGroups

end TauCeti
