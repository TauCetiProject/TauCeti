/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Presentation
public import Mathlib.Tactic.Group

/-!
# Morphisms of graphs of groups

A morphism `Φ : 𝔸 → 𝔹` of graphs of groups over Serre graphs `Γ` and `Δ` consists of

* a morphism of graphs `Γ → Δ`, written `[·]`;
* homomorphisms `φ_v : A_v →* B_[v]` of vertex groups;
* homomorphisms `φ_e : A_e →* B_[e]` of edge groups, with `φ_{rev e} = φ_e`;
* for each dart `e` a *twisting element* `δ_e ∈ B_[src e]`,

such that `φ_{src e} (α_e c) = δ_e · α_[e] (φ_e c) · δ_e⁻¹` for every dart `e` and `c ∈ A_e`.
Applied to `rev e` this gives `φ_{tgt e} (ω_e c) = δ_{rev e} · ω_[e] (φ_e c) · δ_{rev e}⁻¹`.
A morphism sends a vertex group element `a` to `φ a` and a dart `e` to the path
`δ_e, [e], δ_{rev e}⁻¹`; this respects the defining relations of the fundamental group.

These are the morphisms of Bass. In the notation of Kapovich, Weidmann and Myasnikov, an
`𝔸`-graph `ℬ` with edge labels `(f_α, [f], f_ω)` is exactly such a morphism into `𝔸` from the
graph of groups it defines, with `φ` the inclusions of subgroups and `δ_f = f_α`: their condition
`(f⁻¹)_α = (f_ω)⁻¹` is `f_ω = δ_{rev f}⁻¹`, their formula `α_f(g) = f_α α_[f](g) f_α⁻¹` is the
compatibility condition, and their map `μ` of paths, which replaces `f` by `f_α, [f], f_ω`, is the
induced map described above.

Morphisms compose, with `δ^{ΨΦ}_e = ψ(δ^Φ_e) · δ^Ψ_[e]`, and composition is associative and
unital. A morphism `Φ` induces a homomorphism `π₁(𝔸, T) →* π₁(𝔹, T')` of the groups relative to
sets of darts, provided the image `δ_e · [e] · δ_{rev e}⁻¹` of every dart of `T` is trivial in
`π₁(𝔹, T')`; this holds when `Φ` maps `T` into `T'` and has trivial twisting elements on the darts
of `T` and their reverses, and always holds for `T = ∅`. The induced homomorphisms are functorial.

`Hom.id` and `Hom.comp` are reducible, with underlying graph morphisms given by structure
literals, so that `A_{(Hom.id 𝔸).graph.mapV v}` reduces to `A_v` and the vertex group homomorphisms
of identities and composites can be stated without transport; `Hom.id_graph` and `Hom.comp_graph`
identify the underlying graph morphisms with the identity and the composite.

## Main definitions

* `TauCeti.GraphOfGroups.Hom`: morphisms of graphs of groups, with twisting elements.
* `TauCeti.GraphOfGroups.Hom.twistArrow`: the twisting element of an arrow of the quiver of `Γ`.
* `TauCeti.GraphOfGroups.Hom.id`, `TauCeti.GraphOfGroups.Hom.comp`: identities and composition.
* `TauCeti.GraphOfGroups.Hom.edgeImage`: the image `δ_e · [e] · δ_{rev e}⁻¹` of a dart in
  `π₁(𝔹, T')`.
* `TauCeti.GraphOfGroups.π₁Tree.map`: the homomorphism `π₁(𝔸, T) →* π₁(𝔹, T')` induced by a
  morphism.

## Main results

* `TauCeti.GraphOfGroups.Hom.ext`: a morphism is determined by its graph morphism, its vertex
  group homomorphisms and its twisting elements.
* `TauCeti.GraphOfGroups.Hom.vertexHom_ω`: the compatibility of a morphism with the maps `ω`.
* `TauCeti.GraphOfGroups.Hom.comp_assoc`, `TauCeti.GraphOfGroups.Hom.id_comp`,
  `TauCeti.GraphOfGroups.Hom.comp_id`: composition is associative and unital.
* `TauCeti.GraphOfGroups.π₁Tree.map_id`, `TauCeti.GraphOfGroups.π₁Tree.map_comp_map`:
  functoriality of the induced homomorphisms.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §3, Definitions 3.1 and 3.3, Convention 3.5 and
  Proposition 3.7.
* H. Bass, *Covering theory for graphs of groups*, J. Pure Appl. Algebra 89 (1993), §2.
-/

public section

universe u₁ v₁ w₁ x₁ u₂ v₂ w₂ x₂ u₃ v₃ w₃ x₃ u₄ v₄ w₄ x₄

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u₁, v₁}} {Δ : SerreGraph.{u₂, v₂}} {Θ : SerreGraph.{u₃, v₃}}
  {Ξ : SerreGraph.{u₄, v₄}} {𝔸 : GraphOfGroups.{u₁, v₁, w₁, x₁} Γ}
  {𝔹 : GraphOfGroups.{u₂, v₂, w₂, x₂} Δ} {ℂ : GraphOfGroups.{u₃, v₃, w₃, x₃} Θ}
  {𝔻 : GraphOfGroups.{u₄, v₄, w₄, x₄} Ξ}

/-- A morphism of graphs of groups `𝔸 → 𝔹`: a morphism `[·]` of the underlying graphs,
homomorphisms `φ_v : A_v →* B_[v]` and `φ_e : A_e →* B_[e]` with `φ_{rev e} = φ_e`, and twisting
elements `δ_e ∈ B_[src e]` such that `φ_{src e} (α_e c) = δ_e · α_[e] (φ_e c) · δ_e⁻¹`. -/
structure Hom (𝔸 : GraphOfGroups.{u₁, v₁, w₁, x₁} Γ) (𝔹 : GraphOfGroups.{u₂, v₂, w₂, x₂} Δ) where
  /-- The underlying morphism of graphs. -/
  graph : Γ.Hom Δ
  /-- The homomorphisms of vertex groups `φ_v : A_v →* B_[v]`. -/
  vertexHom : ∀ v, 𝔸.vertexGroup v →* 𝔹.vertexGroup (graph.mapV v)
  /-- The homomorphisms of edge groups `φ_e : A_e →* B_[e]`, indexed by darts. -/
  edgeHom : ∀ e, 𝔸.edgeGroup (Γ.toGeomEdge e) →* 𝔹.edgeGroup (Δ.toGeomEdge (graph.mapE e))
  /-- The twisting element `δ_e ∈ B_[src e]` of a dart. -/
  twist : ∀ e, 𝔹.vertexGroup (graph.mapV (Γ.src e))
  /-- A dart and its reverse have the same homomorphism of edge groups. -/
  edgeHom_rev : ∀ e c, edgeHom (Γ.rev e) c =
    MulEquiv.cast (M := 𝔹.edgeGroup) (graph.toGeomEdge_mapE_congr (Γ.toGeomEdge_rev e).symm)
      (edgeHom e (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e) c))
  /-- Compatibility with the boundary monomorphisms `α`, up to conjugation by the twisting
  element: `φ_{src e} (α_e c) = δ_e · α_[e] (φ_e c) · δ_e⁻¹`. -/
  vertexHom_α : ∀ e c, vertexHom (Γ.src e) (𝔸.α e c) =
    twist e * MulEquiv.cast (M := 𝔹.vertexGroup) (graph.map_src e)
      (𝔹.α (graph.mapE e) (edgeHom e c)) * (twist e)⁻¹

namespace Hom

/-- Two morphisms of graphs of groups are equal when they have the same underlying graph
morphism, the same vertex group homomorphisms and the same twisting elements. The edge group
homomorphisms are then equal too, since `α` is injective. -/
@[ext]
theorem ext {Φ Ψ : Hom 𝔸 𝔹} (hgraph : Φ.graph = Ψ.graph)
    (hvertex : ∀ v a, Φ.vertexHom v a ≍ Ψ.vertexHom v a) (htwist : ∀ e, Φ.twist e ≍ Ψ.twist e) :
    Φ = Ψ := by
  cases Φ with | mk f φ ε δ _ hα => ?_
  cases Ψ with | mk g ψ ε' δ' _ hα' => ?_
  subst hgraph
  obtain rfl : φ = ψ := funext fun v => MonoidHom.ext fun a => eq_of_heq (hvertex v a)
  obtain rfl : δ = δ' := funext fun e => eq_of_heq (htwist e)
  obtain rfl : ε = ε' := funext fun e => MonoidHom.ext fun c => 𝔹.α_injective _ <|
    (MulEquiv.cast _).injective <| mul_left_cancel <| mul_right_cancel <|
      (hα e c).symm.trans (hα' e c)
  rfl

/-! ### Transport along equalities of vertices and darts -/

/-- The vertex group homomorphisms of a morphism commute with transport along an equality of
vertices. -/
theorem vertexHom_cast (Φ : Hom 𝔸 𝔹) {v v' : Γ.V} (h : v = v') (a : 𝔸.vertexGroup v) :
    Φ.vertexHom v' (MulEquiv.cast (M := 𝔸.vertexGroup) h a) =
      MulEquiv.cast (M := 𝔹.vertexGroup) (congrArg Φ.graph.mapV h) (Φ.vertexHom v a) := by
  subst h
  rfl

/-- The edge group homomorphism of a morphism depends only on the geometric edge: for darts `e`
and `e'` with the same geometric edge, `φ_{e'} = φ_e` up to transport. -/
theorem edgeHom_cast (Φ : Hom 𝔸 𝔹) {e e' : Γ.E} (h : Γ.toGeomEdge e = Γ.toGeomEdge e')
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    Φ.edgeHom e' (MulEquiv.cast (M := 𝔸.edgeGroup) h c) =
      MulEquiv.cast (M := 𝔹.edgeGroup) (Φ.graph.toGeomEdge_mapE_congr h) (Φ.edgeHom e c) := by
  obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 h
  · simp only [MulEquiv.cast_apply, cast_eq]
  · simp only [Φ.edgeHom_rev, MulEquiv.cast_apply, cast_cast, cast_eq]

/-- Compatibility of a morphism with the boundary monomorphisms `ω`, up to conjugation by the
twisting element of the reverse dart: `φ_{tgt e} (ω_e c) = δ_{rev e} · ω_[e] (φ_e c) · δ_{rev e}⁻¹`,
with `δ_{rev e} ∈ B_[src (rev e)]` transported to `B_[tgt e]`. -/
theorem vertexHom_ω (Φ : Hom 𝔸 𝔹) (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    Φ.vertexHom (Γ.tgt e) (𝔸.ω e c) =
      MulEquiv.cast (M := 𝔹.vertexGroup) (congrArg Φ.graph.mapV (Γ.src_rev e))
          (Φ.twist (Γ.rev e)) *
        MulEquiv.cast (M := 𝔹.vertexGroup) (Φ.graph.map_tgt _ e)
          (𝔹.ω (Φ.graph.mapE e) (Φ.edgeHom e c)) *
        (MulEquiv.cast (M := 𝔹.vertexGroup) (congrArg Φ.graph.mapV (Γ.src_rev e))
          (Φ.twist (Γ.rev e)))⁻¹ := by
  -- `α` at a dart equal to `rev (Φ.graph.mapE e)` is `ω` at `Φ.graph.mapE e`, up to transport.
  have key : ∀ (e' : Δ.E) (_ : e' = Δ.rev (Φ.graph.mapE e))
      (h₁ : Δ.toGeomEdge (Φ.graph.mapE e) = Δ.toGeomEdge e')
      (h₂ : Δ.src e' = Φ.graph.mapV (Γ.src (Γ.rev e)))
      (x : 𝔹.edgeGroup (Δ.toGeomEdge (Φ.graph.mapE e))),
      MulEquiv.cast (M := 𝔹.vertexGroup) h₂ (𝔹.α e' (MulEquiv.cast (M := 𝔹.edgeGroup) h₁ x)) =
        MulEquiv.cast (M := 𝔹.vertexGroup) (Φ.graph.map_tgt _ e) (𝔹.ω (Φ.graph.mapE e) x) := by
    rintro _ rfl h₁ h₂ x
    simp only [α_rev_apply, MulEquiv.cast_apply, cast_cast, cast_eq]
    -- Both sides are now `ω_[e] x` transported to the same vertex group; the two transports
    -- start at `src (rev [e])` and at `tgt [e]`, which agree by unfolding `SerreGraph.tgt`.
    rfl
  have h := Φ.vertexHom_α (Γ.rev e) (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e).symm c)
  rw [Φ.edgeHom_rev, key _ (Φ.graph.map_rev e)] at h
  -- `h` is the claim at the vertex `src (rev e)`; the transports along `src (rev e) = tgt e` in
  -- the claim are identities, since `tgt e` unfolds to `src (rev e)`.
  simp only [α_rev_apply, MulEquiv.cast_apply, cast_cast, cast_eq] at h ⊢
  exact h

/-! ### Twisting elements of arrows -/

section twistArrow

variable (Φ : Hom 𝔸 𝔹) {a b : Γ.V}

/-- The twisting element `δ_e ∈ B_[a]` of an arrow `e : a ⟶ b` of the quiver of `Γ`: the twisting
element of the underlying dart, read in `B_[a]` through `src e = a`. -/
def twistArrow (e : a ⟶ b) : 𝔹.vertexGroup (Φ.graph.mapV a) :=
  MulEquiv.cast (M := 𝔹.vertexGroup) (congrArg Φ.graph.mapV e.2.1) (Φ.twist e.1)

theorem twistArrow_def (e : a ⟶ b) : Φ.twistArrow e =
    MulEquiv.cast (M := 𝔹.vertexGroup) (congrArg Φ.graph.mapV e.2.1) (Φ.twist e.1) :=
  (rfl)

/-- The twisting element of an arrow whose dart is `e'` is `δ_{e'}`, transported along any equality
of vertices. -/
theorem twistArrow_eq_cast (e : a ⟶ b) {e' : Γ.E} (h : e.1 = e')
    (ha : Φ.graph.mapV (Γ.src e') = Φ.graph.mapV a) :
    Φ.twistArrow e = MulEquiv.cast (M := 𝔹.vertexGroup) ha (Φ.twist e') := by
  obtain ⟨e, rfl, rfl⟩ := e
  subst h
  rfl

@[simp] theorem twistArrow_mk (e : Γ.E) :
    Φ.twistArrow (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) = Φ.twist e :=
  (rfl)

@[simp] theorem twistArrow_dart (e : Γ.E) : Φ.twistArrow (Γ.dart e) = Φ.twist e := by
  rw [Γ.dart_def, twistArrow_mk]

/-- The twisting element of the reverse of the arrow of a dart `e` is `δ_{rev e}`, transported
along `src (rev e) = tgt e`. -/
@[simp] theorem twistArrow_reverse_dart (e : Γ.E) :
    Φ.twistArrow (Quiver.reverse (Γ.dart e)) =
      MulEquiv.cast (M := 𝔹.vertexGroup) (congrArg Φ.graph.mapV (Γ.src_rev e))
        (Φ.twist (Γ.rev e)) :=
  Φ.twistArrow_eq_cast _ (by simp) _

end twistArrow

/-! ### Identities and composition -/

variable (𝔸) in
/-- The identity morphism of a graph of groups, with trivial twisting elements. -/
protected abbrev id : Hom 𝔸 𝔸 where
  graph := ⟨fun v => v, fun e => e, fun _ => rfl, fun _ => rfl⟩
  vertexHom _ := MonoidHom.id _
  edgeHom _ := MonoidHom.id _
  twist _ := 1
  edgeHom_rev e c := by simp only [MonoidHom.id_apply, MulEquiv.cast_apply, cast_cast, cast_eq]
  vertexHom_α e c := by simp only [MonoidHom.id_apply, MulEquiv.cast_apply, cast_eq, one_mul,
    inv_one, mul_one]

/-- The composite of two morphisms of graphs of groups. Its twisting elements are
`ψ(δ^Φ_e) · δ^Ψ_[e]`. -/
abbrev comp (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) : Hom 𝔸 ℂ where
  graph := ⟨fun v => Ψ.graph.mapV (Φ.graph.mapV v), fun e => Ψ.graph.mapE (Φ.graph.mapE e),
    fun e => by rw [Ψ.graph.map_src, Φ.graph.map_src],
    fun e => by rw [Φ.graph.map_rev, Ψ.graph.map_rev]⟩
  vertexHom v := (Ψ.vertexHom (Φ.graph.mapV v)).comp (Φ.vertexHom v)
  edgeHom e := (Ψ.edgeHom (Φ.graph.mapE e)).comp (Φ.edgeHom e)
  twist e := Ψ.vertexHom (Φ.graph.mapV (Γ.src e)) (Φ.twist e) *
    MulEquiv.cast (M := ℂ.vertexGroup) (congrArg Ψ.graph.mapV (Φ.graph.map_src e))
      (Ψ.twist (Φ.graph.mapE e))
  edgeHom_rev e c := by
    simp only [MonoidHom.comp_apply, Φ.edgeHom_rev]
    -- The transport on the right is along `[ΨΦ e]`, which unfolds to `Ψ [Φ e]` because the graph
    -- morphism above is a structure literal; `exact` sees through this.
    exact Ψ.edgeHom_cast _ _
  vertexHom_α e c := by
    simp only [MonoidHom.comp_apply, Φ.vertexHom_α, map_mul, map_inv, Ψ.vertexHom_cast,
      Ψ.vertexHom_α, mul_inv_rev, mul_assoc]
    simp only [MulEquiv.cast_apply, cast_cast]

section id

variable (𝔸)

theorem id_graph_mapV (v : Γ.V) : (Hom.id 𝔸).graph.mapV v = v := rfl

theorem id_graph_mapE (e : Γ.E) : (Hom.id 𝔸).graph.mapE e = e := rfl

/-- The graph morphism underlying the identity morphism is the identity. -/
theorem id_graph : (Hom.id 𝔸).graph = SerreGraph.Hom.id Γ := by
  ext <;> simp

theorem id_vertexHom (v : Γ.V) : (Hom.id 𝔸).vertexHom v = MonoidHom.id _ := (rfl)

theorem id_edgeHom (e : Γ.E) : (Hom.id 𝔸).edgeHom e = MonoidHom.id _ := (rfl)

theorem id_twist (e : Γ.E) : (Hom.id 𝔸).twist e = 1 := (rfl)

@[simp] theorem id_twistArrow {a b : Γ.V} (e : a ⟶ b) : (Hom.id 𝔸).twistArrow e = 1 :=
  map_one _

end id

section comp

variable (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹)

theorem comp_graph_mapV (v : Γ.V) :
    (Ψ.comp Φ).graph.mapV v = Ψ.graph.mapV (Φ.graph.mapV v) := rfl

theorem comp_graph_mapE (e : Γ.E) :
    (Ψ.comp Φ).graph.mapE e = Ψ.graph.mapE (Φ.graph.mapE e) := rfl

/-- The graph morphism underlying a composite is the composite of the graph morphisms. -/
theorem comp_graph : (Ψ.comp Φ).graph = Ψ.graph.comp Φ.graph := by
  ext <;> simp

theorem comp_vertexHom (v : Γ.V) :
    (Ψ.comp Φ).vertexHom v = (Ψ.vertexHom (Φ.graph.mapV v)).comp (Φ.vertexHom v) := (rfl)

theorem comp_edgeHom (e : Γ.E) :
    (Ψ.comp Φ).edgeHom e = (Ψ.edgeHom (Φ.graph.mapE e)).comp (Φ.edgeHom e) := (rfl)

/-- The twisting elements of a composite: `δ^{ΨΦ}_e = ψ(δ^Φ_e) · δ^Ψ_[e]`. -/
theorem comp_twist (e : Γ.E) :
    (Ψ.comp Φ).twist e = Ψ.vertexHom (Φ.graph.mapV (Γ.src e)) (Φ.twist e) *
      MulEquiv.cast (M := ℂ.vertexGroup) (congrArg Ψ.graph.mapV (Φ.graph.map_src e))
        (Ψ.twist (Φ.graph.mapE e)) := (rfl)

/-- The twisting element of a composite at an arrow `e : a ⟶ b`: `δ^{ΨΦ}_e = ψ(δ^Φ_e) · δ^Ψ_[e]`. -/
@[simp] theorem comp_twistArrow {a b : Γ.V} (e : a ⟶ b) : (Ψ.comp Φ).twistArrow e =
    Ψ.vertexHom _ (Φ.twistArrow e) * Ψ.twistArrow (Φ.graph.mapArrow e) := by
  -- For the arrow of a dart all transports are along `rfl`, and `Hom.comp` is reducible.
  obtain ⟨e, rfl, rfl⟩ := e
  rfl

end comp

-- In the next three proofs `rfl` identifies the underlying graph morphisms: `Hom.id` and
-- `Hom.comp` are reducible and give them as structure literals. The vertex groups at the image
-- vertices then agree, and `heq_of_eq` reduces the remaining fields to equations.

/-- The identity morphism is a left unit for composition. -/
@[simp] theorem id_comp (Φ : Hom 𝔸 𝔹) : (Hom.id 𝔹).comp Φ = Φ :=
  Hom.ext rfl (fun _ _ => heq_of_eq <| by simp) fun _ => heq_of_eq <| by
    simp only [MonoidHom.id_apply, map_one, mul_one]

/-- The identity morphism is a right unit for composition. -/
@[simp] theorem comp_id (Φ : Hom 𝔸 𝔹) : Φ.comp (Hom.id 𝔸) = Φ :=
  Hom.ext rfl (fun _ _ => heq_of_eq <| by simp) fun _ => heq_of_eq <| by simp

/-- Composition of morphisms of graphs of groups is associative. -/
theorem comp_assoc (Ω : Hom ℂ 𝔻) (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) :
    (Ω.comp Ψ).comp Φ = Ω.comp (Ψ.comp Φ) :=
  Hom.ext rfl (fun _ _ => heq_of_eq <| by simp) fun _ => heq_of_eq <| by
    simp only [MonoidHom.comp_apply, map_mul, vertexHom_cast, mul_assoc]
    simp only [MulEquiv.cast_apply, cast_cast]

/-! ### The induced homomorphism of fundamental groups relative to sets of darts -/

section edgeImage

variable (Φ : Hom 𝔸 𝔹) (T' : Set Δ.E)

/-- The image of a dart `e` under a morphism, as an element of `π₁(𝔹, T')`: the product
`δ_e · [e] · δ_{rev e}⁻¹` of the twisting element of `e`, the image dart, and the inverse of the
twisting element of the reverse dart. -/
def edgeImage (e : Γ.E) : π₁Tree 𝔹 T' :=
  π₁Tree.of T' _ (Φ.twist e) * π₁Tree.edge T' (Φ.graph.mapE e) *
    (π₁Tree.of T' _ (Φ.twist (Γ.rev e)))⁻¹

theorem edgeImage_def (e : Γ.E) :
    Φ.edgeImage T' e = π₁Tree.of T' _ (Φ.twist e) * π₁Tree.edge T' (Φ.graph.mapE e) *
      (π₁Tree.of T' _ (Φ.twist (Γ.rev e)))⁻¹ := (rfl)

-- The image in `π₁(𝔹, T')` of a twisting element does not see how the dart is written.
private theorem of_twist_congr {e e' : Γ.E} (h : e = e') :
    π₁Tree.of T' _ (Φ.twist e) = π₁Tree.of T' _ (Φ.twist e') := by
  subst h
  rfl

/-- The image of the reverse dart is the inverse of the image of the dart. -/
@[simp] theorem edgeImage_rev (e : Γ.E) : Φ.edgeImage T' (Γ.rev e) = (Φ.edgeImage T' e)⁻¹ := by
  simp only [edgeImage_def, Φ.graph.map_rev, π₁Tree.edge_rev, mul_inv_rev, inv_inv, mul_assoc,
    of_twist_congr Φ T' (Γ.rev_rev e)]

/-- The images of the darts satisfy the defining relation `e ω_e(c) e⁻¹ = α_e(c)` of the
fundamental group, read through the vertex group homomorphisms. -/
theorem edgeImage_mul_of_ω_mul_edgeImage_inv (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    Φ.edgeImage T' e * π₁Tree.of T' _ (Φ.vertexHom (Γ.tgt e) (𝔸.ω e c)) *
        (Φ.edgeImage T' e)⁻¹ =
      π₁Tree.of T' _ (Φ.vertexHom (Γ.src e) (𝔸.α e c)) := by
  simp only [Φ.vertexHom_ω, Φ.vertexHom_α, edgeImage_def, map_mul, map_inv, π₁Tree.of_cast]
  rw [← π₁Tree.edge_mul_of_ω_mul_edge_inv]
  group

/-- A dart mapped into `T'` with trivial twisting elements at both ends has trivial image in
`π₁(𝔹, T')`. -/
theorem edgeImage_eq_one {e : Γ.E} (he : Φ.graph.mapE e ∈ T') (h : Φ.twist e = 1)
    (h' : Φ.twist (Γ.rev e) = 1) : Φ.edgeImage T' e = 1 := by
  simp only [edgeImage_def, h, h', map_one, π₁Tree.edge_eq_one he, mul_one, inv_one]

end edgeImage

@[simp] theorem edgeImage_id (T : Set Γ.E) (e : Γ.E) :
    (Hom.id 𝔸).edgeImage T e = π₁Tree.edge T e := by
  simp [edgeImage_def]

end Hom

namespace π₁Tree

variable {T : Set Γ.E} {T' : Set Δ.E} {T'' : Set Θ.E}

/-- The homomorphism `π₁(𝔸, T) →* π₁(𝔹, T')` induced by a morphism `Φ : 𝔸 → 𝔹` of graphs of
groups under which every dart of `T` has trivial image in `π₁(𝔹, T')`: it sends `a ∈ A_v` to
`φ_v a` and a dart `e` to `δ_e · [e] · δ_{rev e}⁻¹`. -/
def map (Φ : Hom 𝔸 𝔹) (hT : ∀ e ∈ T, Φ.edgeImage T' e = 1) : π₁Tree 𝔸 T →* π₁Tree 𝔹 T' :=
  lift (fun v => (of T' (Φ.graph.mapV v)).comp (Φ.vertexHom v)) (Φ.edgeImage T') hT
    (Φ.edgeImage_rev T') (Φ.edgeImage_mul_of_ω_mul_edgeImage_inv T')

section map

variable (Φ : Hom 𝔸 𝔹) (hT : ∀ e ∈ T, Φ.edgeImage T' e = 1)

@[simp] theorem map_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    map Φ hT (of T v a) = of T' (Φ.graph.mapV v) (Φ.vertexHom v a) :=
  lift_of ..

@[simp] theorem map_comp_of (v : Γ.V) :
    (map Φ hT).comp (of T v) = (of T' (Φ.graph.mapV v)).comp (Φ.vertexHom v) :=
  lift_comp_of ..

@[simp] theorem map_edge (e : Γ.E) : map Φ hT (edge T e) = Φ.edgeImage T' e :=
  lift_edge ..

end map

/-- The identity morphism induces the identity of `π₁(𝔸, T)`. -/
@[simp] theorem map_id (hT : ∀ e ∈ T, (Hom.id 𝔸).edgeImage T e = 1 := fun e he => by
      rw [Hom.edgeImage_id, edge_eq_one he]) :
    map (Hom.id 𝔸) hT = MonoidHom.id (π₁Tree 𝔸 T) :=
  hom_ext (fun v => by rw [map_comp_of, Hom.id_vertexHom, MonoidHom.comp_id, MonoidHom.id_comp])
    fun e => by simp

/-- Homomorphisms induced by equal morphisms are equal. -/
theorem map_congr {Φ Ψ : Hom 𝔸 𝔹} (h : Φ = Ψ) (hΦ : ∀ e ∈ T, Φ.edgeImage T' e = 1)
    (hΨ : ∀ e ∈ T, Ψ.edgeImage T' e = 1) : map Φ hΦ = map Ψ hΨ := by
  subst h
  rfl

/-- The image under `Ψ` of the image of a dart under `Φ` is its image under the composite. -/
@[simp] theorem map_edgeImage (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹)
    (hΨ : ∀ e ∈ T', Ψ.edgeImage T'' e = 1) (e : Γ.E) :
    map Ψ hΨ (Φ.edgeImage T' e) = (Ψ.comp Φ).edgeImage T'' e := by
  simp only [Hom.edgeImage_def, map_mul, map_inv, map_of, map_edge, of_cast,
    mul_inv_rev, mul_assoc, Hom.of_twist_congr Ψ T'' (Φ.graph.map_rev e)]

/-- If the darts of `T'` have trivial image under `Ψ` and a dart `e` has trivial image under `Φ`,
then `e` has trivial image under `Ψ.comp Φ`. -/
theorem _root_.TauCeti.GraphOfGroups.Hom.edgeImage_comp_eq_one (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹)
    (hΨ : ∀ e ∈ T', Ψ.edgeImage T'' e = 1) {e : Γ.E} (he : Φ.edgeImage T' e = 1) :
    (Ψ.comp Φ).edgeImage T'' e = 1 := by
  rw [← map_edgeImage Ψ Φ hΨ, he, map_one]

/-- The homomorphism induced by a composite morphism is the composite of the induced
homomorphisms. -/
@[simp] theorem map_comp_map (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) (hΨ : ∀ e ∈ T', Ψ.edgeImage T'' e = 1)
    (hΦ : ∀ e ∈ T, Φ.edgeImage T' e = 1)
    (h : ∀ e ∈ T, (Ψ.comp Φ).edgeImage T'' e = 1 := fun _ he =>
      Hom.edgeImage_comp_eq_one Ψ Φ hΨ (hΦ _ he)) :
    (map Ψ hΨ).comp (map Φ hΦ) = map (Ψ.comp Φ) h :=
  hom_ext (fun v => MonoidHom.ext fun a => by simp only [MonoidHom.comp_apply, map_of])
    fun e => by simp

/-- The image of an element under the homomorphism induced by a composite morphism. -/
@[simp] theorem map_map (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) (hΨ : ∀ e ∈ T', Ψ.edgeImage T'' e = 1)
    (hΦ : ∀ e ∈ T, Φ.edgeImage T' e = 1)
    (h : ∀ e ∈ T, (Ψ.comp Φ).edgeImage T'' e = 1 := fun _ he =>
      Hom.edgeImage_comp_eq_one Ψ Φ hΨ (hΦ _ he)) (x : π₁Tree 𝔸 T) :
    map Ψ hΨ (map Φ hΦ x) = map (Ψ.comp Φ) h x :=
  DFunLike.congr_fun (map_comp_map Ψ Φ hΨ hΦ h) x

end π₁Tree

end GraphOfGroups

end TauCeti
