/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Maps
public import TauCeti.Data.Finset.Update
public import TauCeti.Dynamics.SymbolicDynamics.Subshift

/-!
# Dimer configurations of a graph

A *dimer configuration* of a simple graph `G` is a configuration `ω : G.edgeSet → Bool` in which
every vertex lies in exactly one edge of value `true` (`SimpleGraph.IsDimerConfiguration`). These
are the indicators of the edge sets of the perfect matchings of `G`: the spanning subgraph
`G.dimerSubgraph ω` with the edges of value `true` is a perfect matching exactly when `ω` is a
dimer configuration, and `SimpleGraph.dimerConfigurationEquiv` is the resulting bijection with
Mathlib's perfect matchings `SimpleGraph.Subgraph.IsPerfectMatching`, with inverse the edge
indicator `SimpleGraph.Subgraph.edgeIndicator`.

For a locally finite graph the dimer configurations form a closed set of configurations
(`SimpleGraph.isClosed_setOf_isDimerConfiguration`): whether a vertex is covered exactly once
depends only on the finitely many edges at that vertex. A graph isomorphism transports dimer
configurations (`SimpleGraph.IsDimerConfiguration.comp_mapEdgeSet`), so for a group `Γ` acting on
the edges through graph automorphisms, moving a dimer configuration by `g : Γ` gives a dimer
configuration (`SimpleGraph.IsDimerConfiguration.smul`) and the dimer configurations form a
subshift, `G.dimerSubshift Γ`, the configuration space `𝔛(G)`. The automorphism group itself acts
on the edges (`SimpleGraph.Iso.instMulActionEdgeSet`, with
`SimpleGraph.Iso.exists_smul_eq_mapEdgeSet`), and a homomorphism `τ : Γ →* (G ≃g G)` induces an
action of `Γ` of this kind by `MulAction.compHom`
(`SimpleGraph.Iso.exists_compHom_smul_eq_mapEdgeSet`).

For a finite set `F` of edges and a configuration `ω`, the *completion set*
`G.dimerCompletionSet F ω` is the set of dimer configurations agreeing with `ω` off `F`.
It depends on `ω` only off `F` (`SimpleGraph.dimerCompletionSet_congr`), is finite
(`SimpleGraph.finite_dimerCompletionSet`) and contains `ω` when `ω` is a dimer configuration; at
`F = ∅` it is then the singleton `{ω}` (`SimpleGraph.dimerCompletionSet_empty`).
Moving configurations by `g : Γ` maps `Ω_F(ω)` bijectively onto the completion set of the moved
configuration at `g • F` (`SimpleGraph.dimerCompletionSet_smul`), so sums over the two
completion sets agree (`SimpleGraph.sum_dimerCompletionSet_smul`).
Each member is the gluing of its restriction to `F` to `ω` off `F`
(`Function.updateFinset_restrict_of_eqOn_compl`), so a sum over the completion set
is a sum over the configurations `η` on `F` whose gluing to `ω` is a dimer configuration
(`SimpleGraph.sum_dimerCompletionSet_eq_sum_updateFinset`).
Its members cover the same vertices by edges of `F` of value `true`
(`SimpleGraph.dimerCoveredVertices`, `SimpleGraph.dimerCoveredVertices_eq`): the endpoints of edges
of `F` that are not covered by an edge outside `F`
(`SimpleGraph.IsDimerConfiguration.mem_dimerCoveredVertices_iff`).
When `ω` is a dimer configuration, the members of its completion set are the gluings
`Function.updateFinset ω F η` of a configuration `η` on `F` to `ω` off `F` that cover every
endpoint of an edge of `F` exactly once (`SimpleGraph.dimerCompletionSet_eq_image`), and
the restrictions to `F` of its members are exactly those configurations `η`
(`SimpleGraph.mem_image_restrict_dimerCompletionSet`). So for two dimer configurations `ω₁` and
`ω₂` that agree on the edges outside `F` sharing a vertex with an edge of `F`, the restrictions to
`F` of their completion sets coincide (`SimpleGraph.image_restrict_dimerCompletionSet_eq`).
For any `ω`, the gluing of `η` to `ω` is a dimer configuration exactly when `η` is such a
restriction (`SimpleGraph.isDimerConfiguration_updateFinset_iff`).

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
-/

public section

open Set Function

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V) {G' : SimpleGraph W}

/-- A dimer configuration of a simple graph `G`: a configuration on the edges of `G` in which
every vertex lies in exactly one edge of value `true`, the indicator of the edge set of a perfect
matching. -/
def IsDimerConfiguration (ω : G.edgeSet → Bool) : Prop :=
  ∀ v : V, ∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V)

variable {G}

theorem isDimerConfiguration_iff {ω : G.edgeSet → Bool} :
    G.IsDimerConfiguration ω ↔ ∀ v : V, ∃! e : G.edgeSet, ω e = true ∧ v ∈ (e : Sym2 V) :=
  (Iff.rfl)

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
    (hω : G'.IsDimerConfiguration ω) : G.IsDimerConfiguration (ω ∘ φ.mapEdgeSet) := by
  intro v
  rw [φ.mapEdgeSet.existsUnique_congr_left]
  refine (existsUnique_congr fun e => ?_).1 (hω (φ v))
  simp only [comp_apply, Equiv.apply_symm_apply]
  refine and_congr_right fun _ => ?_
  rw [Iso.coe_mapEdgeSet_symm, Sym2.mem_map]
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
theorem dimerSubgraph_verts (ω : G.edgeSet → Bool) : (G.dimerSubgraph ω).verts = univ :=
  (rfl)

@[simp]
theorem dimerSubgraph_adj {ω : G.edgeSet → Bool} {u v : V} :
    (G.dimerSubgraph ω).Adj u v ↔ ∃ h : G.Adj u v, ω ⟨s(u, v), h⟩ = true :=
  (Iff.rfl)

/-- The edges of `G.dimerSubgraph ω` are the edges of `G` of value `true` under `ω`. -/
@[simp]
theorem mem_edgeSet_dimerSubgraph {ω : G.edgeSet → Bool} {e : Sym2 V} :
    e ∈ (G.dimerSubgraph ω).edgeSet ↔ ∃ h : e ∈ G.edgeSet, ω ⟨e, h⟩ = true := by
  induction e using Sym2.ind with
  | _ u v => exact Iff.rfl

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
    (rfl)

/-- The subgraph of edges of value `true` is a perfect matching exactly when the configuration is
a dimer configuration. -/
theorem isPerfectMatching_dimerSubgraph_iff {ω : G.edgeSet → Bool} :
    (G.dimerSubgraph ω).IsPerfectMatching ↔ G.IsDimerConfiguration ω := by
  rw [Subgraph.isPerfectMatching_iff]
  exact forall_congr' fun v => (existsUnique_edge_iff_existsUnique_adj ω v).symm

open scoped Classical in
/-- The indicator of the edge set of a subgraph, as a configuration on the edges of `G`. -/
noncomputable def Subgraph.edgeIndicator (M : G.Subgraph) (e : G.edgeSet) : Bool :=
  decide ((e : Sym2 V) ∈ M.edgeSet)

@[simp]
theorem Subgraph.edgeIndicator_eq_true {M : G.Subgraph} {e : G.edgeSet} :
    M.edgeIndicator e = true ↔ (e : Sym2 V) ∈ M.edgeSet := by
  simp [edgeIndicator]

theorem dimerSubgraph_edgeIndicator {M : G.Subgraph} (hM : M.IsSpanning) :
    G.dimerSubgraph M.edgeIndicator = M := by
  refine Subgraph.ext ?_ ?_
  · exact (Set.eq_univ_of_forall hM).symm
  · ext u v
    simp only [dimerSubgraph_adj, Subgraph.edgeIndicator_eq_true, Subgraph.mem_edgeSet]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨M.adj_sub h, h⟩⟩

@[simp]
theorem edgeIndicator_dimerSubgraph (ω : G.edgeSet → Bool) :
    (G.dimerSubgraph ω).edgeIndicator = ω := by
  funext ⟨e, he⟩
  rw [Bool.eq_iff_iff, Subgraph.edgeIndicator_eq_true, mem_edgeSet_dimerSubgraph]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨he, h⟩⟩

/-- Dimer configurations are the indicators of the edge sets of the perfect matchings. -/
noncomputable def dimerConfigurationEquiv :
    {ω : G.edgeSet → Bool // G.IsDimerConfiguration ω} ≃ {M : G.Subgraph // M.IsPerfectMatching}
    where
  toFun ω := ⟨G.dimerSubgraph ω, isPerfectMatching_dimerSubgraph_iff.2 ω.property⟩
  invFun M := ⟨M.val.edgeIndicator, by
    rw [← isPerfectMatching_dimerSubgraph_iff, dimerSubgraph_edgeIndicator M.property.2]
    exact M.property⟩
  left_inv ω := Subtype.ext (edgeIndicator_dimerSubgraph ω.val)
  right_inv M := Subtype.ext (dimerSubgraph_edgeIndicator M.property.2)

@[simp]
theorem coe_dimerConfigurationEquiv_apply (ω : {ω : G.edgeSet → Bool // G.IsDimerConfiguration ω}) :
    (dimerConfigurationEquiv ω : G.Subgraph) = G.dimerSubgraph ω :=
  (rfl)

@[simp]
theorem coe_dimerConfigurationEquiv_symm_apply (M : {M : G.Subgraph // M.IsPerfectMatching}) :
    (dimerConfigurationEquiv.symm M : G.edgeSet → Bool) = M.val.edgeIndicator :=
  (rfl)

/-! ### Closedness -/

/-- For a locally finite graph the dimer configurations form a closed set: whether a vertex is
covered exactly once depends only on the finitely many edges at it. -/
theorem isClosed_setOf_isDimerConfiguration [G.LocallyFinite] :
    IsClosed {ω : G.edgeSet → Bool | G.IsDimerConfiguration ω} := by
  classical
  simp only [IsDimerConfiguration, ofPred_forall]
  refine isClosed_iInter fun v => ?_
  let T := {e : G.edgeSet // v ∈ (e : Sym2 V)}
  have : Finite T := Finite.of_injective
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

/-- For a group `Γ` acting on the edges through graph automorphisms, moving a dimer configuration
by an element of `Γ` gives a dimer configuration. -/
theorem IsDimerConfiguration.smul {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) {ω : G.edgeSet → Bool}
    (hω : G.IsDimerConfiguration ω) (g : Γ) : G.IsDimerConfiguration fun e => ω (g⁻¹ • e) := by
  obtain ⟨φ, hφ⟩ := hΓ g⁻¹
  have : (fun e => ω (g⁻¹ • e)) = ω ∘ φ.mapEdgeSet := funext fun e => by simp [hφ e]
  simpa only [this] using hω.comp_mapEdgeSet φ

variable (G) in
/-- The subshift `𝔛(G)` of dimer configurations of a locally finite graph `G`, for a group `Γ`
acting on the edges through graph automorphisms. -/
def dimerSubshift [G.LocallyFinite] (Γ : Type*) [Group Γ] [MulAction Γ G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) :
    TauCeti.Subshift Γ G.edgeSet Bool where
  carrier := {ω | G.IsDimerConfiguration ω}
  isClosed := isClosed_setOf_isDimerConfiguration
  smul_mem' g _ hω := hω.smul hΓ g

@[simp]
theorem mem_dimerSubshift [G.LocallyFinite] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
    {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e} {ω : G.edgeSet → Bool} :
    ω ∈ G.dimerSubshift Γ hΓ ↔ G.IsDimerConfiguration ω :=
  (Iff.rfl)

@[simp]
theorem coe_dimerSubshift [G.LocallyFinite] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
    {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e} :
    (G.dimerSubshift Γ hΓ : Set (G.edgeSet → Bool)) = {ω | G.IsDimerConfiguration ω} :=
  (rfl)

/-! ### Completion sets -/

variable (G) in
/-- The completion set `Ω_F(ω)` of a configuration `ω` at a finite set `F` of edges: the dimer
configurations agreeing with `ω` off `F`. -/
def dimerCompletionSet (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) : Set (G.edgeSet → Bool) :=
  {ω' | G.IsDimerConfiguration ω' ∧ ∀ e ∉ F, ω' e = ω e}

@[simp]
theorem mem_dimerCompletionSet {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool} :
    ω' ∈ G.dimerCompletionSet F ω ↔ G.IsDimerConfiguration ω' ∧ ∀ e ∉ F, ω' e = ω e :=
  (Iff.rfl)

theorem mem_dimerCompletionSet_self {F : Finset G.edgeSet} {ω : G.edgeSet → Bool}
    (hω : G.IsDimerConfiguration ω) : ω ∈ G.dimerCompletionSet F ω :=
  ⟨hω, fun _ _ => rfl⟩

/-- The completion set depends on `ω` only off `F`. -/
theorem dimerCompletionSet_congr {F : Finset G.edgeSet} {ω₁ ω₂ : G.edgeSet → Bool}
    (h : ∀ e ∉ F, ω₁ e = ω₂ e) : G.dimerCompletionSet F ω₁ = G.dimerCompletionSet F ω₂ := by
  ext ω'
  simp only [mem_dimerCompletionSet]
  exact and_congr_right fun _ => forall₂_congr fun e he => by rw [h e he]

variable (G) in
/-- The vertices covered by the edges of `F` of value `true` under `ω`. -/
def dimerCoveredVertices [DecidableEq V] (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    Finset V :=
  (F.filter fun e => ω e = true).biUnion fun e => (e : Sym2 V).toFinset

theorem dimerCoveredVertices_def [DecidableEq V] (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerCoveredVertices F ω =
      (F.filter fun e => ω e = true).biUnion fun e => (e : Sym2 V).toFinset :=
  (rfl)

@[simp]
theorem mem_dimerCoveredVertices [DecidableEq V] {F : Finset G.edgeSet} {ω : G.edgeSet → Bool}
    {v : V} : v ∈ G.dimerCoveredVertices F ω ↔ ∃ e ∈ F, ω e = true ∧ v ∈ (e : Sym2 V) := by
  simp [dimerCoveredVertices_def, and_assoc]

/-- For a dimer configuration, a vertex is covered by an edge of `F` of value `true` exactly when
it is an endpoint of an edge of `F` and not covered by an edge outside `F`. -/
theorem IsDimerConfiguration.mem_dimerCoveredVertices_iff [DecidableEq V] {F : Finset G.edgeSet}
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) {v : V} :
    v ∈ G.dimerCoveredVertices F ω ↔
      (∃ f ∈ F, v ∈ (f : Sym2 V)) ∧ ∀ e ∉ F, ω e = true → v ∉ (e : Sym2 V) := by
  rw [mem_dimerCoveredVertices]
  obtain ⟨e₀, he₀, huniq⟩ := isDimerConfiguration_iff.1 hω v
  constructor
  · rintro ⟨e, heF, hωe, hve⟩
    refine ⟨⟨e, heF, hve⟩, fun e' he'F hωe' hve' => he'F ?_⟩
    rw [huniq e' ⟨hωe', hve'⟩, ← huniq e ⟨hωe, hve⟩]
    exact heF
  · rintro ⟨-, hout⟩
    by_cases h : e₀ ∈ F
    · exact ⟨e₀, h, he₀⟩
    · exact absurd he₀.2 (hout e₀ h he₀.1)

/-- **The covered vertices are determined off `F`.** Two dimer configurations agreeing off `F`
cover the same vertices by edges of `F`. -/
theorem dimerCoveredVertices_eq [DecidableEq V] {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool}
    (hω : G.IsDimerConfiguration ω) (hω' : G.IsDimerConfiguration ω')
    (h : ∀ e ∉ F, ω e = ω' e) : G.dimerCoveredVertices F ω = G.dimerCoveredVertices F ω' := by
  ext v
  rw [hω.mem_dimerCoveredVertices_iff, hω'.mem_dimerCoveredVertices_iff]
  exact and_congr_right fun _ => forall₂_congr fun e he => by rw [h e he]

/-- The completion set of a dimer configuration at `F = ∅` is the singleton of it. -/
@[simp]
theorem dimerCompletionSet_empty {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    G.dimerCompletionSet ∅ ω = {ω} := by
  ext ω'
  simp only [mem_dimerCompletionSet, Finset.notMem_empty, not_false_eq_true, forall_const,
    mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => funext h, by rintro rfl; exact ⟨hω, fun _ => rfl⟩⟩

/-- A completion set is finite: its members are determined by their values on `F`. -/
theorem finite_dimerCompletionSet (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    (G.dimerCompletionSet F ω).Finite := by
  refine Finite.of_finite_image (f := F.restrict) (toFinite _) ?_
  intro ω₁ h₁ ω₂ h₂ h
  funext e
  by_cases he : e ∈ F
  · exact congrFun h ⟨e, he⟩
  · rw [h₁.2 e he, h₂.2 e he]

open scoped Pointwise in
/-- **Moving a completion set.** For a group `Γ` acting on the edges through graph automorphisms,
the map `σ_g ω = (e ↦ ω (g⁻¹ • e))` carries the completion set `Ω_F(ω)` onto
`Ω_{g • F}(σ_g ω)`. -/
theorem dimerCompletionSet_smul {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) [DecidableEq G.edgeSet] (g : Γ)
    (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerCompletionSet (g • F) (fun e => ω (g⁻¹ • e)) =
      (fun ω' e => ω' (g⁻¹ • e)) '' G.dimerCompletionSet F ω := by
  ext ω'
  simp only [mem_image, mem_dimerCompletionSet]
  constructor
  · rintro ⟨hω', hF⟩
    refine ⟨fun e => ω' (g • e), ⟨by simpa using hω'.smul hΓ g⁻¹, fun e he => ?_⟩, by simp⟩
    dsimp only
    rw [hF _ fun h => he ((Finset.smul_mem_smul_finset_iff g).1 h), inv_smul_smul]
  · rintro ⟨ω'', ⟨hω'', hF⟩, rfl⟩
    refine ⟨hω''.smul hΓ g, fun e he => hF _ fun h => he ?_⟩
    rwa [← Finset.inv_smul_mem_iff]

open scoped Pointwise in
/-- Since `σ_g ω = (e ↦ ω (g⁻¹ • e))` is a bijection from `Ω_F(ω)` onto `Ω_{g • F}(σ_g ω)`
(`SimpleGraph.dimerCompletionSet_smul`), sums over the two completion sets agree. -/
theorem sum_dimerCompletionSet_smul [DecidableEq G.edgeSet] {Γ : Type*} [Group Γ]
    [MulAction Γ G.edgeSet] (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e)
    {M : Type*} [AddCommMonoid M] (g : Γ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool)
    (f : (G.edgeSet → Bool) → M) :
    ∑ ω' ∈ (G.finite_dimerCompletionSet (g • F) fun e => ω (g⁻¹ • e)).toFinset, f ω' =
      ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, f fun e => ω' (g⁻¹ • e) := by
  classical
  have hσ : Injective fun (ω' : G.edgeSet → Bool) e => ω' (g⁻¹ • e) :=
    fun ω₁ ω₂ h => funext fun e => by simpa using congrFun h (g • e)
  rw [← Finset.sum_image fun _ _ _ _ h => hσ h]
  congr 1
  ext ω'
  simp only [Finite.mem_toFinset, Finset.mem_image, dimerCompletionSet_smul hΓ, mem_image]

/-- The members of the completion set of a dimer configuration `ω` at `F` are the gluings of
configurations `η` on `F` to `ω` that cover every endpoint of an edge of `F` exactly once. -/
theorem dimerCompletionSet_eq_image [DecidableEq G.edgeSet] {F : Finset G.edgeSet}
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    G.dimerCompletionSet F ω = (fun η => updateFinset ω F η) ''
      {η | ∀ v : V, (∃ e ∈ F, v ∈ (e : Sym2 V)) →
        ∃! e : G.edgeSet, updateFinset ω F η e = true ∧ v ∈ (e : Sym2 V)} := by
  ext ω'
  constructor
  · intro hω'
    have hglue := updateFinset_restrict_of_eqOn_compl hω'.2
    exact ⟨_, fun v _ => by rw [hglue]; exact hω'.1 v, hglue⟩
  · rintro ⟨η, hη, rfl⟩
    refine ⟨fun v => ?_, fun e he => updateFinset_apply_of_notMem he⟩
    by_cases hv : ∃ e ∈ F, v ∈ (e : Sym2 V)
    · exact hη v hv
    · simp only [not_exists, not_and] at hv
      refine (existsUnique_congr_of_eqOn_incident fun e he => ?_).2 (hω v)
      exact updateFinset_apply_of_notMem fun heF => hv e heF he

/-- A sum over the completion set `Ω_F(ω)` is a sum over the configurations `η` on `F` whose
gluing to `ω` off `F` is a dimer configuration. -/
theorem sum_dimerCompletionSet_eq_sum_updateFinset [DecidableEq G.edgeSet] {M : Type*}
    [AddCommMonoid M] (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) (f : (G.edgeSet → Bool) → M)
    [DecidablePred fun η : F → Bool => G.IsDimerConfiguration (updateFinset ω F η)] :
    ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, f ω' =
      ∑ η with G.IsDimerConfiguration (updateFinset ω F η), f (updateFinset ω F η) := by
  symm
  refine Finset.sum_nbij' (fun η => updateFinset ω F η) (fun ω' => F.restrict ω') ?_ ?_ ?_ ?_
    fun _ _ => rfl
  · intro η hη
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet]
    exact ⟨hη, fun e he => updateFinset_apply_of_notMem he⟩
  · intro ω' hω'
    rw [Finite.mem_toFinset] at hω'
    simpa [updateFinset_restrict_of_eqOn_compl hω'.2] using hω'.1
  · intro η _
    exact restrict_updateFinset ω η
  · intro ω' hω'
    exact updateFinset_restrict_of_eqOn_compl ((Finite.mem_toFinset _).1 hω').2

/-- The restrictions to `F` of the members of the completion set of a dimer configuration `ω` at
`F` are the configurations `η` on `F` whose gluing to `ω` off `F` covers every endpoint of an edge
of `F` exactly once. -/
theorem mem_image_restrict_dimerCompletionSet [DecidableEq G.edgeSet] {F : Finset G.edgeSet}
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) {η : F → Bool} :
    η ∈ F.restrict '' G.dimerCompletionSet F ω ↔ ∀ v : V, (∃ e ∈ F, v ∈ (e : Sym2 V)) →
      ∃! e : G.edgeSet, updateFinset ω F η e = true ∧ v ∈ (e : Sym2 V) := by
  rw [dimerCompletionSet_eq_image hω, image_image]
  simp only [restrict_updateFinset, image_id']
  exact Iff.rfl

/-- The gluing of a configuration `η` on `F` to `ω` off `F` is a dimer configuration exactly when
`η` is the restriction to `F` of a member of the completion set `Ω_F(ω)`. -/
theorem isDimerConfiguration_updateFinset_iff [DecidableEq G.edgeSet] {F : Finset G.edgeSet}
    {ω : G.edgeSet → Bool} {η : F → Bool} :
    G.IsDimerConfiguration (updateFinset ω F η) ↔ η ∈ F.restrict '' G.dimerCompletionSet F ω := by
  constructor
  · exact fun h => ⟨_, ⟨h, fun e he => updateFinset_apply_of_notMem he⟩, restrict_updateFinset ω η⟩
  · rintro ⟨ω', hω', rfl⟩
    rw [updateFinset_restrict_of_eqOn_compl hω'.2]
    exact hω'.1

/-- For two dimer configurations that agree on the edges outside `F` sharing a vertex with an edge
of `F`, the restrictions to `F` of their completion sets coincide. -/
theorem image_restrict_dimerCompletionSet_eq {F : Finset G.edgeSet} {ω₁ ω₂ : G.edgeSet → Bool}
    (h₁ : G.IsDimerConfiguration ω₁) (h₂ : G.IsDimerConfiguration ω₂)
    (h : ∀ e ∉ F, (∃ f ∈ F, ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ω₁ e = ω₂ e) :
    F.restrict '' G.dimerCompletionSet F ω₁ = F.restrict '' G.dimerCompletionSet F ω₂ := by
  classical
  have key : ∀ η : F → Bool, ∀ v : V, (∃ f ∈ F, v ∈ (f : Sym2 V)) →
      ((∃! e : G.edgeSet, updateFinset ω₁ F η e = true ∧ v ∈ (e : Sym2 V)) ↔
        ∃! e : G.edgeSet, updateFinset ω₂ F η e = true ∧ v ∈ (e : Sym2 V)) := by
    rintro η v ⟨f, hf, hvf⟩
    refine existsUnique_congr_of_eqOn_incident fun e hve => ?_
    by_cases he : e ∈ F
    · rw [updateFinset_apply_of_mem he, updateFinset_apply_of_mem he]
    · rw [updateFinset_apply_of_notMem he, updateFinset_apply_of_notMem he]
      exact h e he ⟨f, hf, v, hve, hvf⟩
  ext η
  rw [mem_image_restrict_dimerCompletionSet h₁, mem_image_restrict_dimerCompletionSet h₂]
  exact forall_congr' fun v => forall_congr' fun hv => key η v hv

end SimpleGraph
