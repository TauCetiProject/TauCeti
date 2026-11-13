/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.AGraph.Comparison

/-!
# The auxiliary moves on `𝔸`-graphs

Kapovich, Weidmann and Myasnikov define three moves that change the labels of an `𝔸`-graph `B`
without changing its underlying graph, and that do not change the represented subgroup.

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

* `TauCeti.GraphOfGroups.AGraph.subgroup_conj`: a conjugation move that is trivial at the base
  vertex preserves the represented subgroup.
* `TauCeti.GraphOfGroups.AGraph.subgroup_bassSerre`: a Bass–Serre move preserves the represented
  subgroup.
* `TauCeti.GraphOfGroups.AGraph.subgroup_adjust`: a simple adjustment by elements of the vertex
  groups preserves the represented subgroup.
* `TauCeti.GraphOfGroups.AGraph.complexity_conj`: a conjugation move preserves the complexity.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §4.1, Definitions 4.5, 4.6 and 4.7, and Proposition 4.15.
-/

public section

universe u v w x u' v'

namespace TauCeti

namespace GraphOfGroups

namespace AGraph

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
  (B : AGraph.{u, v, w, x, u', v'} 𝔸 v₀)

/-- The rank of a vertex group depends only on its isomorphism type. -/
private theorem rankGrp_congr {B₁ B₂ : AGraph.{u, v, w, x, u', v'} 𝔸 v₀} {z₁ : B₁.graph.V}
    {z₂ : B₂.graph.V} (e : B₁.grp z₁ ≃* B₂.grp z₂) : B₁.rankGrp z₁ = B₂.rankGrp z₂ := by
  by_cases h : (B₁.grp z₁).FG
  · have : Group.FG (B₁.grp z₁) := (Group.fg_iff_subgroup_fg _).2 h
    have : Group.FG (B₂.grp z₂) := (isMulFG_congr e).1 this
    rw [rankGrp_eq, rankGrp_eq, Group.rank_congr e]
  · have h₂ : ¬ (B₂.grp z₂).FG := fun h₂ => h ((Group.fg_iff_subgroup_fg _).1
      ((isMulFG_congr e).2 ((Group.fg_iff_subgroup_fg _).2 h₂)))
    rw [rankGrp_of_not_fg _ h, rankGrp_of_not_fg _ h₂]

/-- The identity of the underlying graph of `B`, as a morphism to the underlying graph of a move of
`B`. Its maps are the identity by definition (those of `SerreGraph.Hom.id` are not exposed), so the
transports in `subgroup_le_of_hom` along it reduce. -/
private abbrev graphId : B.graph.Hom B.graph :=
  ⟨fun z => z, fun f => f, fun _ => rfl, fun _ => rfl⟩

/-! ### The conjugation move A0 -/

/-- The conjugation move A0 by a family `g_z ∈ A_[z]`: the vertex group `B_z` is replaced by
`g_z B_z g_z⁻¹` and the label `f_α` of a dart `f` by `g_{o(f)} f_α`. The underlying graph, the type
map and the base vertex are unchanged; the body is exposed so that vertices and darts of `B` are
accepted as vertices and darts of the result. -/
@[expose] def conj (g : ∀ z : B.graph.V, 𝔸.vertexGroup (B.typ.mapV z)) :
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

@[simp] theorem conj_grp (z : B.graph.V) :
    (B.conj g).grp z = (B.grp z).map (MulAut.conj (g z)).toMonoidHom :=
  rfl

@[simp] theorem conj_labelα (f : B.graph.E) : (B.conj g).labelα f =
    MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_src f).symm (g (B.graph.src f)) * B.labelα f :=
  rfl

/-- After a conjugation move the label `f_ω` of a dart `f` is `f_ω g_{t(f)}⁻¹`. -/
@[simp] theorem conj_labelω (f : B.graph.E) : (B.conj g).labelω f = B.labelω f *
    (MulEquiv.cast (M := 𝔸.vertexGroup) (B.typ.map_tgt _ f).symm (g (B.graph.tgt f)))⁻¹ := by
  unfold conj
  rw [labelω_def, labelω_def, map_mul, mul_inv_rev]
  congr 2
  -- `g` at `o(f⁻¹)` and at `t(f)`, which are the same vertex by definition.
  simp only [MulEquiv.cast_apply, cast_cast]
  rfl

/-- A conjugation move that is trivial at the base vertex preserves the represented subgroup
(Kapovich, Weidmann and Myasnikov, Proposition 4.15 for an admissible move A0). -/
theorem subgroup_conj (hg : g B.base = 1) : (B.conj g).subgroup = B.subgroup := by
  -- Both inclusions come from the identity of the underlying graph, with the families `g⁻¹`
  -- and `g`. Unfolding `conj` makes its underlying graph and types those of `B`, so that the
  -- transports in the hypotheses of `subgroup_le_of_hom` reduce.
  unfold conj
  refine le_antisymm (subgroup_le_of_hom (B' := B) (graphId B) (fun _ => rfl) (fun _ => rfl) rfl
    (fun z => (g z)⁻¹) (inv_eq_one.2 hg) (fun z => ?_) (fun f => ⟨1, one_mem _, ?_⟩))
      (subgroup_le_of_hom (graphId B) (fun _ => rfl) (fun _ => rfl) rfl g hg (fun z => ?_)
        (fun f => ⟨1, one_mem _, ?_⟩))
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    simpa [MulEquiv.cast_apply, MulAut.conj_apply, mul_assoc] using hc
  · -- The remaining transports are along the identity of the underlying graph.
    simp only [map_inv, inv_inv, one_mul]
    rfl
  · rintro _ ⟨c, hc, rfl⟩
    simpa [MulEquiv.cast_apply] using hc
  · rw [one_mul]
    exact (inv_mul_cancel_left _ _).symm

/-- A conjugation move preserves finiteness. -/
theorem isFinite_conj_iff : (B.conj g).IsFinite ↔ B.IsFinite := by
  unfold conj
  refine ⟨fun h => ⟨h.1, h.2, fun z => ?_⟩,
    fun h => ⟨h.1, h.2, fun z => have := h.3 z; inferInstance⟩⟩
  exact (isMulFG_congr (Subgroup.equivMapOfInjective (B.grp z) _
    (MulAut.conj (g z)).injective)).2 (h.3 z)

/-- A conjugation move preserves the complexity. -/
@[simp] theorem complexity_conj : (B.conj g).complexity = B.complexity := by
  rw [complexity_def, complexity_def]
  exact congrArg _ (finsum_congr fun z => rankGrp_congr
    (Subgroup.equivMapOfInjective (B.grp z) _ (MulAut.conj (g z)).injective).symm)

end conj

/-! ### The Bass–Serre move A1 -/

/-- `α` of a dart `e'` equal to the reverse of `e` is `ω` of `e`, read through the identifications
of the edge groups and of the vertex groups. -/
private theorem cast_α_eq_ω {e e' : Γ.E} (he : e' = Γ.rev e) (h₁ : Γ.src e' = Γ.tgt e)
    (h₂ : Γ.toGeomEdge e = Γ.toGeomEdge e') (d : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    MulEquiv.cast (M := 𝔸.vertexGroup) h₁ (𝔸.α e' (MulEquiv.cast (M := 𝔸.edgeGroup) h₂ d)) =
      𝔸.ω e d := by
  subst he
  rw [α_rev_apply]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
  -- What remains is a transport from `A_{o(e⁻¹)}` to `A_{t(e)}`, the same group by definition.
  rfl

/-- Moving an edge group element across the dart of a letter `f_α, [f], f_ω`:
`a α(c)⁻¹, e, ω(c) b ∼ a, e, b`, for a dart `e` of `Γ` read as an arrow from `a` to `b`. -/
private theorem homotopic_bassSerre_letter {a b : Γ.V} (e : Γ.E) (ha : Γ.src e = a)
    (hb : Γ.tgt e = b) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) (x : 𝔸.vertexGroup a)
    (y : 𝔸.vertexGroup b) :
    Path.Homotopic (((Path.ofVertex (x * (MulEquiv.cast (M := 𝔸.vertexGroup) ha (𝔸.α e c))⁻¹)).comp
      (Path.ofDart ⟨e, ha, hb⟩)).comp (Path.ofVertex (MulEquiv.cast (M := 𝔸.vertexGroup) hb
        (𝔸.ω e c) * y))) (((Path.ofVertex x).comp (Path.ofDart ⟨e, ha, hb⟩)).comp
          (Path.ofVertex y)) := by
  rw [← αArrow_apply 𝔸 (⟨e, ha, hb⟩ : a ⟶ b), ← ωArrow_apply 𝔸 (⟨e, ha, hb⟩ : a ⟶ b)]
  simp only [Path.ofVertex_eq_nil_cons, Path.ofDart_eq_nil_cons, Quiver.Path.comp_cons,
    Quiver.Path.comp_nil]
  have h := Path.Homotopic.dart_ωArrow (Quiver.Path.nil.cons
    (Letter.vertex (x * (𝔸.αArrow (⟨e, ha, hb⟩ : a ⟶ b) c)⁻¹))) ⟨e, ha, hb⟩ c
  refine (Path.Homotopic.mul _ _ _).symm.trans ((h.cons _).trans ?_)
  refine (((Path.Homotopic.mul _ _ _).cons _).cons _).trans ?_
  rw [inv_mul_cancel_right]
  exact .refl _

/-- The Bass–Serre move A1 by a family `c_f ∈ A_[f]`: the label `f_α` of a dart `f` is replaced by
`f_α α_[f](c_f)⁻¹`. When `c` takes the same value on a dart and on its reverse, the label
`(a, e, b)` of `f` becomes `(a α_e(c_f)⁻¹, e, ω_e(c_f) b)`. -/
@[expose] def bassSerre (c : ∀ f : B.graph.E, 𝔸.edgeGroup (Γ.toGeomEdge (B.typ.mapE f))) :
    AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := B.graph
  typ := B.typ
  base := B.base
  typ_base := B.typ_base
  grp := B.grp
  labelα f := B.labelα f * (𝔸.α (B.typ.mapE f) (c f))⁻¹

section bassSerre

variable (c : ∀ f : B.graph.E, 𝔸.edgeGroup (Γ.toGeomEdge (B.typ.mapE f)))

@[simp] theorem bassSerre_grp (z : B.graph.V) : (B.bassSerre c).grp z = B.grp z :=
  rfl

@[simp] theorem bassSerre_labelα (f : B.graph.E) :
    (B.bassSerre c).labelα f = B.labelα f * (𝔸.α (B.typ.mapE f) (c f))⁻¹ :=
  rfl

/-- After a Bass–Serre move by a family taking the same value on a dart and on its reverse, the
label `f_ω` of a dart `f` is `ω_[f](c_f) f_ω`. -/
theorem bassSerre_labelω (hc : ∀ f, c (B.graph.rev f) = MulEquiv.cast (M := 𝔸.edgeGroup)
      ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm (c f))
    (f : B.graph.E) : (B.bassSerre c).labelω f = 𝔸.ω (B.typ.mapE f) (c f) * B.labelω f := by
  unfold bassSerre
  rw [labelω_def, labelω_def, map_mul, mul_inv_rev, map_inv, inv_inv, hc f]
  exact congrArg (· * _) (cast_α_eq_ω (B.typ.map_rev f) _ _ _)

/-- A Bass–Serre move by a family taking the same value on a dart and on its reverse preserves the
represented subgroup (Kapovich, Weidmann and Myasnikov, Proposition 4.15 for the move A1). -/
theorem subgroup_bassSerre (hc : ∀ f, c (B.graph.rev f) = MulEquiv.cast (M := 𝔸.edgeGroup)
    ((congrArg Γ.toGeomEdge (B.typ.map_rev f)).trans (Γ.toGeomEdge_rev _)).symm (c f)) :
    (B.bassSerre c).subgroup = B.subgroup := by
  have hω := B.bassSerre_labelω c hc
  -- Every `𝔹`-path reads homotopic `𝔸`-paths in `B` and in `B.bassSerre c`: the letter of a dart
  -- changes from `a, e, b` to `a α(c)⁻¹, e, ω(c) b`.
  have key : ∀ {y z : B.toGraphOfGroups.LetterVertex} (p : B.toGraphOfGroups.Path y z),
      Path.Homotopic ((B.bassSerre c).pathMap p) (B.pathMap p) := by
    unfold bassSerre at hω ⊢
    intro y z p
    induction p with
    | nil =>
      rw [pathMap_nil, pathMap_nil]
      exact .refl _
    | cons p l ih =>
      rw [pathMap_cons, pathMap_cons]
      refine ih.comp ?_
      cases l with
      | vertex b =>
        rw [letterPath_vertex, letterPath_vertex]
        exact .refl _
      | dart f =>
        obtain ⟨e, rfl, rfl⟩ := f
        rw [letterPath_dart_arrow, letterPath_dart_arrow, hω e, map_mul, map_mul, map_inv]
        exact homotopic_bassSerre_letter (B.typ.mapE e) (B.typ.map_src e) (B.typ.map_tgt _ e)
          (c e) _ _
  ext x
  rw [mem_subgroup_iff, mem_subgroup_iff]
  constructor <;> rintro ⟨p, rfl⟩ <;> refine ⟨p, ?_⟩
  exacts [congrArg _ (π₁.mk_eq_mk_iff.2 (key p).symm), congrArg _ (π₁.mk_eq_mk_iff.2 (key p))]

/-- A Bass–Serre move preserves finiteness. -/
theorem isFinite_bassSerre_iff : (B.bassSerre c).IsFinite ↔ B.IsFinite :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-- A Bass–Serre move preserves the complexity. -/
@[simp] theorem complexity_bassSerre : (B.bassSerre c).complexity = B.complexity := by
  rw [complexity_def, complexity_def]
  exact congrArg _ (finsum_congr fun z => rankGrp_congr (MulEquiv.refl _))

end bassSerre

/-! ### The simple adjustment A2 -/

/-- The simple adjustment A2 by a family `a_f ∈ A_{o([f])}`: the label `f_α` of a dart `f` is
replaced by `a_f f_α`. The move of Kapovich, Weidmann and Myasnikov takes `a_f` in the vertex group
`B_{o(f)}`. -/
@[expose] def adjust (a : ∀ f : B.graph.E, 𝔸.vertexGroup (Γ.src (B.typ.mapE f))) :
    AGraph.{u, v, w, x, u', v'} 𝔸 v₀ where
  graph := B.graph
  typ := B.typ
  base := B.base
  typ_base := B.typ_base
  grp := B.grp
  labelα f := a f * B.labelα f

section adjust

variable (a : ∀ f : B.graph.E, 𝔸.vertexGroup (Γ.src (B.typ.mapE f)))

@[simp] theorem adjust_grp (z : B.graph.V) : (B.adjust a).grp z = B.grp z :=
  rfl

@[simp] theorem adjust_labelα (f : B.graph.E) : (B.adjust a).labelα f = a f * B.labelα f :=
  rfl

/-- After a simple adjustment the label `f_ω` of a dart `f` is `f_ω a_{f⁻¹}⁻¹`. -/
@[simp] theorem adjust_labelω (f : B.graph.E) : (B.adjust a).labelω f = B.labelω f *
    (MulEquiv.cast (M := 𝔸.vertexGroup) ((congrArg Γ.src (B.typ.map_rev f)).trans (Γ.src_rev _))
      (a (B.graph.rev f)))⁻¹ := by
  unfold adjust
  rw [labelω_def, labelω_def, map_mul, mul_inv_rev]

/-- A simple adjustment by elements of the vertex groups preserves the represented subgroup
(Kapovich, Weidmann and Myasnikov, Proposition 4.15 for the move A2). -/
theorem subgroup_adjust (ha : ∀ f, a f ∈ B.grpSrc f) : (B.adjust a).subgroup = B.subgroup := by
  -- Both inclusions come from the identity of the underlying graph, with `g = 1` and the elements
  -- `a_f` and `a_f⁻¹` of the vertex groups; `adjust` is unfolded as `conj` in `subgroup_conj`.
  unfold adjust
  refine le_antisymm (subgroup_le_of_hom (B' := B) (graphId B) (fun _ => rfl) (fun _ => rfl) rfl 1
    rfl (fun z => ?_) (fun f => ⟨a f, ha f, ?_⟩)) (subgroup_le_of_hom (graphId B) (fun _ => rfl)
      (fun _ => rfl) rfl 1 rfl (fun z => ?_) (fun f => ⟨(a f)⁻¹, (mem_grpSrc _).2 ?_, ?_⟩))
  · rintro _ ⟨c, hc, rfl⟩
    simpa [MulEquiv.cast_apply] using hc
  · -- The remaining transports are along the identity of the underlying graph.
    simp only [Pi.one_apply, map_one, inv_one, one_mul]
    rfl
  · rintro _ ⟨c, hc, rfl⟩
    simpa [MulEquiv.cast_apply] using hc
  · rw [map_inv]
    exact inv_mem ((mem_grpSrc B).1 (ha f))
  · simp only [Pi.one_apply, map_one, inv_one, one_mul, inv_mul_cancel_left]
    rfl

/-- A simple adjustment preserves finiteness. -/
theorem isFinite_adjust_iff : (B.adjust a).IsFinite ↔ B.IsFinite :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-- A simple adjustment preserves the complexity. -/
@[simp] theorem complexity_adjust : (B.adjust a).complexity = B.complexity := by
  rw [complexity_def, complexity_def]
  exact congrArg _ (finsum_congr fun z => rankGrp_congr (MulEquiv.refl _))

end adjust

/-! ### The moves on a single edge -/

section segment

variable {P Q : Type w} {C : Type x} [Group P] [Group Q] [Group C] (f : C →* P) (g : C →* Q)
  (hf : Function.Injective f) (hg : Function.Injective g)
  (P₀ : Subgroup P) (Q₀ : Subgroup Q) (a : P) (b : Q)

/-- The conjugation move at the end of a single edge `(a, e, b)` by `q ∈ Q` gives the single edge
`(a, e, b q⁻¹)` with the group `q Q₀ q⁻¹` at its end (Kapovich, Weidmann and Myasnikov,
Figure 3). -/
theorem segment_conj (q : Q) :
    (segment f g hf hg P₀ Q₀ a b).conj
        (fun z => Bool.rec (motive := fun z => cond z Q P) (1 : P) q z) =
      segment f g hf hg P₀ (Q₀.map (MulAut.conj q).toMonoidHom) a (b * q⁻¹) := by
  -- The vertices and darts of the single edge are the Booleans, and its vertex groups `P` and `Q`,
  -- only after unfolding; the components are then compared one Boolean at a time.
  unfold conj segment
  congr 1
  · funext z
    cases z
    · -- The vertex group at `false` is `P` only after unfolding, so `conj 1` is computed in `P`.
      have key : ∀ y : P, MulAut.conj (1 : P) y = y := fun y => by simp
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (congrArg (· ∈ P₀) (key y)).mpr hy
      · exact fun hx => ⟨x, hx, key x⟩
    · rfl
  · funext e
    cases e
    · exact one_mul a
    · simp only [mul_inv_rev, inv_inv]
      rfl

/-- The Bass–Serre move on a single edge `(a, e, b)` by `c ∈ C` gives the single edge
`(a f(c)⁻¹, e, g(c) b)` (Kapovich, Weidmann and Myasnikov, Figure 4). -/
theorem segment_bassSerre (c : C) :
    (segment f g hf hg P₀ Q₀ a b).bassSerre (fun _ => c) =
      segment f g hf hg P₀ Q₀ (a * (f c)⁻¹) (g c * b) := by
  -- As in `segment_conj`, the labels are compared one Boolean at a time after unfolding.
  unfold bassSerre segment
  congr 1
  funext e
  cases e
  · exact congrArg (fun x => a * x⁻¹) (DFunLike.congr_fun (GraphOfGroups.segment_α_false ..) c)
  · rw [mul_inv_rev]
    exact congrArg (fun x => b⁻¹ * x⁻¹) (DFunLike.congr_fun (GraphOfGroups.segment_α_true ..) c)

/-- The simple adjustment of a single edge `(a, e, b)` at its start by `p` gives the single edge
`(p a, e, b)` (Kapovich, Weidmann and Myasnikov, Figure 5). -/
theorem segment_adjust (p : P) :
    (segment f g hf hg P₀ Q₀ a b).adjust
        (fun z => Bool.rec (motive := fun z => cond z Q P) p (1 : Q) z) =
      segment f g hf hg P₀ Q₀ (p * a) b := by
  -- As in `segment_conj`, the labels are compared one Boolean at a time after unfolding.
  unfold adjust segment
  congr 1
  funext e
  cases e
  · rfl
  · exact one_mul _

end segment

end AGraph

end GraphOfGroups

end TauCeti
