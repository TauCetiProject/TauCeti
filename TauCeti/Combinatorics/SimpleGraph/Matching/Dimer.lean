/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Dynamics.SymbolicDynamics.Subshift

/-!
# Dimer configurations of a graph

A *dimer configuration* of a simple graph `G` is a configuration `ω : G.edgeSet → Bool` in which
every vertex lies in exactly one edge of value `true` (`TauCeti.IsDimerConfiguration`). These are
the indicators of the edge sets of the perfect matchings of `G`: the spanning subgraph
`TauCeti.dimerSubgraph G ω` with the edges of value `true` is a perfect matching exactly when `ω` is
a dimer configuration, and `TauCeti.dimerConfigurationEquiv` is the resulting bijection with
Mathlib's perfect matchings `SimpleGraph.Subgraph.IsPerfectMatching`.

For a locally finite graph the dimer configurations form a closed set of configurations
(`TauCeti.isClosed_setOf_isDimerConfiguration`): whether a vertex is covered exactly once depends
only on the finitely many edges at that vertex. A graph isomorphism transports dimer
configurations (`TauCeti.IsDimerConfiguration.comp_mapEdgeSet`), so for a group `Γ` acting on the
edges through graph automorphisms the dimer configurations form a subshift,
`TauCeti.dimerSubshift G Γ`, the configuration space `𝔛(G)`. The automorphism group itself acts
on the edges (`TauCeti.instMulActionIsoEdgeSet`), and a homomorphism `τ : Γ →* (G ≃g G)` induces
an action of `Γ` of this kind by `MulAction.compHom`.

For a finite set `F` of edges and a configuration `ω`, the *completion set*
`TauCeti.dimerCompletionSet G F ω` is the set of dimer configurations agreeing with `ω` off `F`.
It is finite (`TauCeti.dimerCompletionSet_finite`) and contains `ω` when `ω` is a dimer
configuration. Its members are the gluings `TauCeti.dimerGlue F η ω` of a configuration `η` on `F`
to `ω` off `F` that cover every endpoint of an edge of `F` exactly once
(`TauCeti.dimerCompletionSet_eq_image`), so the set of their restrictions to `F` depends only on
the values of `ω` on the edges outside `F` that share a vertex with an edge of `F`
(`TauCeti.restrict_dimerCompletionSet_eq`).

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
-/

@[expose] public section

open Set Function

namespace TauCeti

variable {V W : Type*} (G : SimpleGraph V) {G' : SimpleGraph W}

/-- A dimer configuration of a simple graph `G`: a configuration on the edges of `G` in which
every vertex lies in exactly one edge of value `true`, the indicator of the edge set of a perfect
matching. -/
def IsDimerConfiguration (ω : G.edgeSet → Bool) : Prop :=
  ∀ v : V, ∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V)

variable {G}

theorem isDimerConfiguration_iff {ω : G.edgeSet → Bool} :
    IsDimerConfiguration G ω ↔ ∀ v : V, ∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V) :=
  Iff.rfl

/-- Whether a configuration covers a vertex exactly once depends only on its values on the edges
at that vertex. -/
theorem existsUnique_congr_of_eqOn_incident {ω ω' : G.edgeSet → Bool} {v : V}
    (h : ∀ e : G.edgeSet, v ∈ (e : Sym2 V) → ω e = ω' e) :
    (∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V)) ↔
      ∃! e : G.edgeSet, ω' e = true ∧ v ∈ (e : Sym2 V) :=
  existsUnique_congr fun e => ⟨fun ⟨h₁, h₂⟩ => ⟨h e h₂ ▸ h₁, h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨(h e h₂).symm ▸ h₁, h₂⟩⟩

/-- A graph isomorphism transports dimer configurations. -/
theorem IsDimerConfiguration.comp_mapEdgeSet (φ : G ≃g G') {ω : G'.edgeSet → Bool}
    (hω : IsDimerConfiguration G' ω) : IsDimerConfiguration G (ω ∘ φ.mapEdgeSet) := by
  intro v
  rw [φ.mapEdgeSet.existsUnique_congr_left]
  refine (existsUnique_congr fun e => ?_).1 (hω (φ v))
  simp only [comp_apply, Equiv.apply_symm_apply]
  refine and_congr_right fun _ => ?_
  change φ v ∈ (e : Sym2 W) ↔ v ∈ Sym2.map φ.symm e
  rw [Sym2.mem_map]
  exact ⟨fun h => ⟨φ v, h, φ.symm_apply_apply v⟩, fun ⟨a, ha, hav⟩ => by
    rw [← hav, φ.apply_symm_apply]; exact ha⟩

/-! ### Perfect matchings -/

/-- The spanning subgraph of `G` whose edges are the edges of value `true` under `ω`. -/
def dimerSubgraph (G : SimpleGraph V) (ω : G.edgeSet → Bool) : G.Subgraph where
  verts := univ
  Adj u v := ∃ h : G.Adj u v, ω ⟨s(u, v), h⟩ = true
  adj_sub := fun ⟨h, _⟩ => h
  edge_vert _ := mem_univ _
  symm := ⟨fun _ _ ⟨h, hω⟩ => ⟨h.symm, by simpa only [Sym2.eq_swap] using hω⟩⟩

@[simp]
theorem dimerSubgraph_verts (ω : G.edgeSet → Bool) : (dimerSubgraph G ω).verts = univ :=
  rfl

@[simp]
theorem dimerSubgraph_adj {ω : G.edgeSet → Bool} {u v : V} :
    (dimerSubgraph G ω).Adj u v ↔ ∃ h : G.Adj u v, ω ⟨s(u, v), h⟩ = true :=
  Iff.rfl

/-- The edges of value `true` at a vertex `v` correspond to the neighbours of `v` in the
subgraph of edges of value `true`. -/
private theorem existsUnique_edge_iff_existsUnique_adj (ω : G.edgeSet → Bool) (v : V) :
    (∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V)) ↔
      ∃! w, ∃ h : G.Adj v w, ω ⟨s(v, w), h⟩ = true := by
  constructor
  · rintro ⟨⟨e, he⟩, ⟨hωe, hve⟩, huniq⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve
    refine ⟨w, ⟨he, hωe⟩, fun w' ⟨h', hω'⟩ => ?_⟩
    have := huniq ⟨s(v, w'), h'⟩ ⟨hω', Sym2.mem_mk_left _ _⟩
    exact Sym2.congr_right.1 (congrArg Subtype.val this)
  · rintro ⟨w, ⟨h, hω⟩, huniq⟩
    refine ⟨⟨s(v, w), h⟩, ⟨hω, Sym2.mem_mk_left _ _⟩, fun ⟨e', he'⟩ ⟨hωe', hve'⟩ => ?_⟩
    obtain ⟨w', rfl⟩ := Sym2.mem_iff_exists.1 hve'
    obtain rfl := huniq w' ⟨he', hωe'⟩
    rfl

/-- The subgraph of edges of value `true` is a perfect matching exactly when the configuration is
a dimer configuration. -/
theorem isPerfectMatching_dimerSubgraph_iff {ω : G.edgeSet → Bool} :
    (dimerSubgraph G ω).IsPerfectMatching ↔ IsDimerConfiguration G ω := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  exact forall_congr' fun v => (existsUnique_edge_iff_existsUnique_adj ω v).symm

open scoped Classical in
/-- The indicator of the edge set of a subgraph, as a configuration on the edges of `G`. -/
noncomputable def subgraphIndicator (M : G.Subgraph) (e : G.edgeSet) : Bool :=
  decide ((e : Sym2 V) ∈ M.edgeSet)

@[simp]
theorem subgraphIndicator_eq_true {M : G.Subgraph} {e : G.edgeSet} :
    subgraphIndicator M e = true ↔ (e : Sym2 V) ∈ M.edgeSet := by
  simp [subgraphIndicator]

theorem dimerSubgraph_subgraphIndicator {M : G.Subgraph} (hM : M.IsSpanning) :
    dimerSubgraph G (subgraphIndicator M) = M := by
  refine SimpleGraph.Subgraph.ext ?_ ?_
  · exact (Set.eq_univ_of_forall hM).symm
  · ext u v
    simp only [dimerSubgraph_adj, subgraphIndicator_eq_true, SimpleGraph.Subgraph.mem_edgeSet]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨M.adj_sub h, h⟩⟩

theorem subgraphIndicator_dimerSubgraph (ω : G.edgeSet → Bool) :
    subgraphIndicator (dimerSubgraph G ω) = ω := by
  funext ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    rw [Bool.eq_iff_iff, subgraphIndicator_eq_true, SimpleGraph.Subgraph.mem_edgeSet]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨G.mem_edgeSet.1 he, h⟩⟩

/-- Dimer configurations are the indicators of the edge sets of the perfect matchings. -/
noncomputable def dimerConfigurationEquiv :
    {ω : G.edgeSet → Bool // IsDimerConfiguration G ω} ≃ {M : G.Subgraph // M.IsPerfectMatching}
    where
  toFun ω := ⟨dimerSubgraph G ω, isPerfectMatching_dimerSubgraph_iff.2 ω.property⟩
  invFun M := ⟨subgraphIndicator M.val, by
    rw [← isPerfectMatching_dimerSubgraph_iff, dimerSubgraph_subgraphIndicator M.property.2]
    exact M.property⟩
  left_inv ω := Subtype.ext (subgraphIndicator_dimerSubgraph ω.val)
  right_inv M := Subtype.ext (dimerSubgraph_subgraphIndicator M.property.2)

@[simp]
theorem coe_dimerConfigurationEquiv_apply (ω : {ω : G.edgeSet → Bool // IsDimerConfiguration G ω}) :
    (dimerConfigurationEquiv ω : G.Subgraph) = dimerSubgraph G ω :=
  rfl

/-! ### Closedness -/

/-- For a locally finite graph the dimer configurations form a closed set: whether a vertex is
covered exactly once depends only on the finitely many edges at it. -/
theorem isClosed_setOf_isDimerConfiguration [G.LocallyFinite] :
    IsClosed {ω : G.edgeSet → Bool | IsDimerConfiguration G ω} := by
  classical
  simp only [IsDimerConfiguration, ofPred_forall]
  refine isClosed_iInter fun v => ?_
  let T := {e : G.edgeSet // v ∈ (e : Sym2 V)}
  have : Finite T := by
    have : Finite (G.incidenceSet v) :=
      (G.incidenceSetEquivNeighborSet v).finite_iff.2 inferInstance
    exact Finite.of_injective
      (fun e : T => (⟨e.val.val, e.val.property, e.property⟩ : G.incidenceSet v))
      fun e e' h => by
        have := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext this)
  let r : (G.edgeSet → Bool) → T → Bool := fun ω e => ω e.val
  have hr : Continuous r := continuous_pi fun e => continuous_apply e.val
  have hs : {ω : G.edgeSet → Bool | ∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V)} =
      r ⁻¹' (r '' {ω | ∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V)}) := by
    refine (subset_preimage_image _ _).antisymm ?_
    rintro ω ⟨ω', hω', hrω⟩
    exact (existsUnique_congr_of_eqOn_incident fun e he => congrFun hrω ⟨e, he⟩).1 hω'
  rw [hs]
  exact (isClosed_discrete _).preimage hr

/-! ### The subshift of dimer configurations -/

/-- The automorphism group of `G` acts on its edges. -/
instance instMulActionIsoEdgeSet : MulAction (G ≃g G) G.edgeSet where
  smul φ e := φ.mapEdgeSet e
  one_smul e := Subtype.ext <| by
    change Sym2.map (⇑(1 : G ≃g G)) e.val = e.val
    rw [RelIso.coe_one, Sym2.map_id, id]
  mul_smul φ ψ e := Subtype.ext <| by
    change Sym2.map (⇑(φ * ψ)) e.val = Sym2.map φ (Sym2.map ψ e.val)
    rw [RelIso.coe_mul, Sym2.map_map]

theorem iso_smul_edgeSet (φ : G ≃g G) (e : G.edgeSet) : φ • e = φ.mapEdgeSet e :=
  rfl

variable (G) in
/-- The subshift `𝔛(G)` of dimer configurations of a locally finite graph `G`, for a group `Γ`
acting on the edges through graph automorphisms. -/
def dimerSubshift [G.LocallyFinite] (Γ : Type*) [Group Γ] [MulAction Γ G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) :
    Subshift Γ G.edgeSet Bool where
  carrier := {ω | IsDimerConfiguration G ω}
  isClosed := isClosed_setOf_isDimerConfiguration
  smul_mem' g ω hω := by
    obtain ⟨φ, hφ⟩ := hΓ g⁻¹
    have : (fun e => ω (g⁻¹ • e)) = ω ∘ φ.mapEdgeSet := funext fun e => by simp [hφ e]
    simpa only [mem_ofPred_eq, this] using hω.comp_mapEdgeSet φ

@[simp]
theorem mem_dimerSubshift [G.LocallyFinite] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
    {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e} {ω : G.edgeSet → Bool} :
    ω ∈ dimerSubshift G Γ hΓ ↔ IsDimerConfiguration G ω :=
  Iff.rfl

/-- The action of the automorphism group on the edges is through graph automorphisms. -/
theorem exists_iso_smul_eq (φ : G ≃g G) : ∃ ψ : G ≃g G, ∀ e, φ • e = ψ.mapEdgeSet e :=
  ⟨φ, fun _ => rfl⟩

/-! ### Completion sets -/

variable (G) in
/-- The completion set `Ω_F(ω)` of a configuration `ω` at a finite set `F` of edges: the dimer
configurations agreeing with `ω` off `F`. -/
def dimerCompletionSet (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) : Set (G.edgeSet → Bool) :=
  {ω' | IsDimerConfiguration G ω' ∧ ∀ e ∉ F, ω' e = ω e}

theorem mem_dimerCompletionSet {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool} :
    ω' ∈ dimerCompletionSet G F ω ↔ IsDimerConfiguration G ω' ∧ ∀ e ∉ F, ω' e = ω e :=
  Iff.rfl

theorem mem_dimerCompletionSet_self {F : Finset G.edgeSet} {ω : G.edgeSet → Bool}
    (hω : IsDimerConfiguration G ω) : ω ∈ dimerCompletionSet G F ω :=
  ⟨hω, fun _ _ => rfl⟩

/-- A completion set is finite: its members are determined by their values on `F`. -/
theorem dimerCompletionSet_finite (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    (dimerCompletionSet G F ω).Finite := by
  refine Finite.of_finite_image (f := (F : Set G.edgeSet).domRestrict) (toFinite _) ?_
  intro ω₁ h₁ ω₂ h₂ h
  funext e
  by_cases he : e ∈ F
  · exact congrFun h ⟨e, he⟩
  · rw [h₁.2 e he, h₂.2 e he]

open scoped Classical in
/-- The gluing of a configuration `η` on a finite set `F` of edges to a configuration `ω` off
`F`. -/
noncomputable def dimerGlue (F : Finset G.edgeSet) (η : F → Bool) (ω : G.edgeSet → Bool)
    (e : G.edgeSet) : Bool :=
  if h : e ∈ F then η ⟨e, h⟩ else ω e

theorem dimerGlue_of_mem {F : Finset G.edgeSet} {η : F → Bool} {ω : G.edgeSet → Bool}
    {e : G.edgeSet} (h : e ∈ F) : dimerGlue F η ω e = η ⟨e, h⟩ :=
  dite_eq_left h

theorem dimerGlue_of_notMem {F : Finset G.edgeSet} {η : F → Bool} {ω : G.edgeSet → Bool}
    {e : G.edgeSet} (h : e ∉ F) : dimerGlue F η ω e = ω e :=
  dite_eq_right h

theorem restrict_dimerGlue (F : Finset G.edgeSet) (η : F → Bool) (ω : G.edgeSet → Bool) :
    (F : Set G.edgeSet).domRestrict (dimerGlue F η ω) = η :=
  funext fun e => dimerGlue_of_mem e.property

/-- The members of the completion set of a dimer configuration `ω` at `F` are the gluings of
configurations `η` on `F` to `ω` that cover every endpoint of an edge of `F` exactly once. -/
theorem dimerCompletionSet_eq_image {F : Finset G.edgeSet} {ω : G.edgeSet → Bool}
    (hω : IsDimerConfiguration G ω) :
    dimerCompletionSet G F ω = (fun η => dimerGlue F η ω) ''
      {η | ∀ v : V, (∃ e ∈ F, v ∈ (e : Sym2 V)) →
        ∃! e : G.edgeSet, dimerGlue F η ω e = true ∧ v ∈ (e : Sym2 V)} := by
  ext ω'
  constructor
  · rintro ⟨hω', hoff⟩
    have hglue : dimerGlue F ((F : Set G.edgeSet).domRestrict ω') ω = ω' := funext fun e => by
      by_cases he : e ∈ F
      · exact dimerGlue_of_mem he
      · rw [dimerGlue_of_notMem he, hoff e he]
    exact ⟨_, fun v _ => by rw [hglue]; exact hω' v, hglue⟩
  · rintro ⟨η, hη, rfl⟩
    refine ⟨fun v => ?_, fun e he => dimerGlue_of_notMem he⟩
    by_cases hv : ∃ e ∈ F, v ∈ (e : Sym2 V)
    · exact hη v hv
    · simp only [not_exists, not_and] at hv
      refine (existsUnique_congr_of_eqOn_incident fun e he => ?_).2 (hω v)
      exact dimerGlue_of_notMem fun heF => hv e heF he

/-- The restrictions to `F` of the members of a completion set depend only on the values of the
configuration on the edges outside `F` sharing a vertex with an edge of `F`. -/
theorem restrict_dimerCompletionSet_eq {F : Finset G.edgeSet} {ω₁ ω₂ : G.edgeSet → Bool}
    (h₁ : IsDimerConfiguration G ω₁) (h₂ : IsDimerConfiguration G ω₂)
    (h : ∀ e ∉ F, (∃ f ∈ F, ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ω₁ e = ω₂ e) :
    (F : Set G.edgeSet).domRestrict '' dimerCompletionSet G F ω₁ =
      (F : Set G.edgeSet).domRestrict '' dimerCompletionSet G F ω₂ := by
  have key : ∀ η : F → Bool, ∀ v : V, (∃ f ∈ F, v ∈ (f : Sym2 V)) →
      ((∃! e : G.edgeSet, dimerGlue F η ω₁ e = true ∧ v ∈ (e : Sym2 V)) ↔
        ∃! e : G.edgeSet, dimerGlue F η ω₂ e = true ∧ v ∈ (e : Sym2 V)) := by
    rintro η v ⟨f, hf, hvf⟩
    refine existsUnique_congr_of_eqOn_incident fun e hve => ?_
    by_cases he : e ∈ F
    · rw [dimerGlue_of_mem he, dimerGlue_of_mem he]
    · rw [dimerGlue_of_notMem he, dimerGlue_of_notMem he]
      exact h e he ⟨f, hf, v, hve, hvf⟩
  rw [dimerCompletionSet_eq_image h₁, dimerCompletionSet_eq_image h₂, image_image, image_image]
  simp only [restrict_dimerGlue, image_id']
  ext η
  exact forall_congr' fun v => forall_congr' fun hv => key η v hv

end TauCeti
