/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Language
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The functional coding space

A structure on a carrier `V` in a language `L` with function symbols is coded by a *functional
configuration*: a *function table*, giving the value at each function symbol `f` of `L` and each
tuple of arguments in `V`, together with a relational configuration recording which atomic
relations hold. With `V` discrete, the table space carries the product topology, and the
functional coding space the product of that with the topology of relational configurations. On a
countable carrier, with countably many symbols, it is Polish.

Permutations of `V` act by transporting the decoded structure: `σ` sends a table `F` to
`(f, v) ↦ σ (F (f, σ⁻¹ ∘ v))`, and acts on relational configurations by the logic action. The
action is continuous, and its orbits are the isomorphism classes of decoded structures.

The *graph code* of a functional configuration is the relational configuration, in the graph
language `L.graphLanguage`, of the graph expansion of its decoded structure: it keeps the
relations, and records the graph of each function symbol. The graph code is continuous,
injective and equivariant, and two functional configurations decode to isomorphic structures
exactly when their graph codes are isomorphic. Its range is the set of codes in which the graph
relation of every function symbol is the graph of a total function (`IsGraphCode`), and it is a
homeomorphism onto this range. With countably many symbols on a countable carrier the range is a
Gδ set. It is not closed when `L` has a function symbol and `V` is infinite: tables taking a
constant value `y` converge, as `y` escapes to infinity, to a code with empty graph relations.
For a relational language it is the whole coding space.

This reduces questions about the isomorphism relation of structures with function symbols to
relational languages, where they are stated for `TauCeti.RelationalConfiguration`.

## Main definitions

* `TauCeti.FunctionalConfiguration L V`: the functional coding space, pairs of a function table
  and a relational configuration.
* `TauCeti.FunctionalConfiguration.toStructure`: the decoded `L`-structure.
* `TauCeti.FunctionalConfiguration.isoSetoid`: isomorphism of decoded structures.
* `TauCeti.FunctionalConfiguration.graphCode`: the graph code.
* `TauCeti.FunctionalConfiguration.IsGraphCode`: every graph relation is the graph of a total
  function.
* `TauCeti.FunctionalConfiguration.graphCodeHomeomorph`: the graph code as a homeomorphism onto
  its range.

## Main results

* `TauCeti.FunctionalConfiguration.isoSetoid_eq_orbitRel`: isomorphism is the orbit relation of
  the action of `Equiv.Perm V`.
* `TauCeti.FunctionalConfiguration.instContinuousSMulPerm`: the action is jointly continuous.
* `TauCeti.FunctionalConfiguration.continuous_graphCode`,
  `TauCeti.FunctionalConfiguration.graphCode_injective` and
  `TauCeti.FunctionalConfiguration.graphCode_perm_smul`: the graph code is continuous, injective
  and equivariant.
* `TauCeti.FunctionalConfiguration.isoSetoid_graphCode_iff`: graph codes are isomorphic exactly
  when the functional configurations are.
* `TauCeti.FunctionalConfiguration.range_graphCode`,
  `TauCeti.FunctionalConfiguration.isEmbedding_graphCode`,
  `TauCeti.FunctionalConfiguration.isGδ_setOf_isGraphCode`,
  `TauCeti.FunctionalConfiguration.not_isClosed_setOf_isGraphCode` and
  `TauCeti.FunctionalConfiguration.isGraphCode_of_isRelational`: the range of the graph code, a
  Gδ set onto which the graph code is a homeomorphism, not closed in the presence of a function
  symbol on an infinite carrier, and everything for a relational language.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, §16.C (the space of countable
  structures, with function symbols coded by their graphs).
* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1 (function symbols reduce to relations).
-/

public section

open FirstOrder FirstOrder.Language Set Topology TopologicalSpace

namespace TauCeti

open RelationalConfiguration

variable {L : Language} {V : Type*}

/-- The arguments of the function symbols of `L` in `V`: a function symbol together with a tuple
of arguments of its arity. -/
@[expose] def FunctionalConfiguration.Arg (L : Language) (V : Type*) : Type _ :=
  Σ f : (Σ l, L.Functions l), Fin f.1 → V

/-- The **functional coding space**: a function table, giving a value at each function symbol of
`L` and tuple of arguments in `V`, together with a relational configuration recording which
atomic relations hold. -/
@[expose] def FunctionalConfiguration (L : Language) (V : Type*) : Type _ :=
  (FunctionalConfiguration.Arg L V → V) × RelationalConfiguration L V

namespace FunctionalConfiguration

instance [∀ n, Countable (L.Functions n)] [Countable V] : Countable (Arg L V) :=
  inferInstanceAs (Countable (Σ f : (Σ l, L.Functions l), Fin f.1 → V))

/-- The argument of a function symbol `f` and a tuple `v`. -/
@[expose] def arg {k : ℕ} (f : L.Functions k) (v : Fin k → V) : Arg L V := ⟨⟨k, f⟩, v⟩

/-- The functional configuration with a given function table and relational configuration. -/
@[expose] def mk (T : Arg L V → V) (c : RelationalConfiguration L V) :
    FunctionalConfiguration L V :=
  (T, c)

/-- The function table of a functional configuration. -/
@[expose] def table (F : FunctionalConfiguration L V) : Arg L V → V := F.1

/-- The relational configuration of a functional configuration. -/
@[expose] def rel (F : FunctionalConfiguration L V) : RelationalConfiguration L V := F.2

@[simp]
theorem table_mk (T : Arg L V → V) (c : RelationalConfiguration L V) : (mk T c).table = T :=
  (rfl)

@[simp]
theorem rel_mk (T : Arg L V → V) (c : RelationalConfiguration L V) : (mk T c).rel = c :=
  (rfl)

@[simp]
theorem mk_table_rel (F : FunctionalConfiguration L V) : mk F.table F.rel = F := (rfl)

@[ext]
theorem ext {F G : FunctionalConfiguration L V} (htable : F.table = G.table)
    (hrel : F.rel = G.rel) : F = G :=
  Prod.ext htable hrel

/-! ### Decoding -/

/-- The `L`-structure decoded from a functional configuration: functions are read from the table,
relations from the relational configuration. -/
@[instance_reducible]
def toStructure (F : FunctionalConfiguration L V) : L.Structure V where
  funMap f v := F.table (arg f v)
  RelMap R v := F.rel.eval (atom R v)

@[simp]
theorem toStructure_funMap (F : FunctionalConfiguration L V) {k : ℕ} (f : L.Functions k)
    (v : Fin k → V) : F.toStructure.funMap f v = F.table (arg f v) :=
  (rfl)

@[simp]
theorem toStructure_relMap (F : FunctionalConfiguration L V) {k : ℕ} (R : L.Relations k)
    (v : Fin k → V) : F.toStructure.RelMap R v ↔ F.rel.eval (atom R v) :=
  Iff.rfl

/-! ### The action of permutations -/

/-- Permutations of `V` act on functional configurations by transporting the decoded structure:
`σ` sends the table `F` to `(f, v) ↦ σ (F (f, σ⁻¹ ∘ v))`, and acts on the relational
configuration by the logic action. -/
instance instSMulPerm : SMul (Equiv.Perm V) (FunctionalConfiguration L V) :=
  ⟨fun σ F => mk (fun p => σ (F.table ⟨p.1, ⇑σ⁻¹ ∘ p.2⟩)) (σ • F.rel)⟩

theorem table_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) (p : Arg L V) :
    (σ • F).table p = σ (F.table ⟨p.1, ⇑σ⁻¹ ∘ p.2⟩) :=
  (rfl)

@[simp]
theorem table_perm_smul_arg (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) {k : ℕ}
    (f : L.Functions k) (v : Fin k → V) :
    (σ • F).table (arg f v) = σ (F.table (arg f (⇑σ⁻¹ ∘ v))) :=
  (rfl)

@[simp]
theorem rel_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) :
    (σ • F).rel = σ • F.rel :=
  (rfl)

instance instMulActionPerm : MulAction (Equiv.Perm V) (FunctionalConfiguration L V) where
  one_smul F := ext (funext fun _ => rfl) (one_smul _ F.rel)
  mul_smul σ τ F := ext (funext fun _ => rfl) (mul_smul σ τ F.rel)

variable (L V) in
/-- Isomorphism of decoded structures, as a setoid on functional configurations. -/
def isoSetoid : Setoid (FunctionalConfiguration L V) where
  r F G := Nonempty (@Language.Equiv L V V F.toStructure G.toStructure)
  iseqv :=
    { refl F := ⟨@Language.Equiv.refl L V F.toStructure⟩
      symm {F G} := fun ⟨e⟩ => ⟨@Language.Equiv.symm L V V F.toStructure G.toStructure e⟩
      trans {F G H} := fun ⟨e⟩ ⟨e'⟩ =>
        ⟨@Language.Equiv.comp L V V F.toStructure G.toStructure V H.toStructure e' e⟩ }

/-- Two functional configurations are isomorphic exactly when their decoded structures are. -/
theorem isoSetoid_apply {F G : FunctionalConfiguration L V} :
    isoSetoid L V F G ↔ Nonempty (@Language.Equiv L V V F.toStructure G.toStructure) :=
  Iff.rfl

/-- A permutation `σ` relabels `F` into `G` exactly when it is an isomorphism of the decoded
structures. -/
private theorem perm_smul_eq_iff (σ : Equiv.Perm V) (F G : FunctionalConfiguration L V) :
    σ • F = G ↔ (∀ {k} (f : L.Functions k) (v : Fin k → V),
        σ (F.table (arg f v)) = G.table (arg f (σ ∘ v))) ∧
      ∀ {k} (R : L.Relations k) (v : Fin k → V),
        G.rel.eval (atom R (σ ∘ v)) = F.rel.eval (atom R v) := by
  constructor
  · rintro rfl
    refine ⟨fun f v => ?_, fun R v => ?_⟩
    · simp [Function.comp_def]
    · simp [Function.comp_def]
  · rintro ⟨hf, hR⟩
    refine ext (funext fun ⟨⟨k, f⟩, v⟩ => ?_) (RelationalConfiguration.ext fun a => ?_)
    · change (σ • F).table (arg f v) = G.table (arg f v)
      simpa [Function.comp_def] using hf f (⇑σ⁻¹ ∘ v)
    · induction a using Atom.induction_atom with
      | h R v =>
        simpa [Function.comp_def] using (hR R (⇑σ⁻¹ ∘ v)).symm

/-- Isomorphism of functional configurations is relabelling by a permutation of the carrier. -/
theorem isoSetoid_iff_exists_perm_smul_eq {F G : FunctionalConfiguration L V} :
    isoSetoid L V F G ↔ ∃ σ : Equiv.Perm V, σ • F = G := by
  constructor
  · rintro ⟨e⟩
    refine ⟨@Language.Equiv.toEquiv L V V F.toStructure G.toStructure e,
      (perm_smul_eq_iff _ _ _).2 ⟨fun f v => ?_, fun R v => ?_⟩⟩
    · have h := @Language.Equiv.map_fun L V V F.toStructure G.toStructure e _ f v
      simp only [toStructure_funMap] at h
      exact h
    · have h := @Language.Equiv.map_rel L V V F.toStructure G.toStructure e _ R v
      simp only [toStructure_relMap] at h
      exact Bool.eq_iff_iff.2 h
  · rintro ⟨σ, hσ⟩
    obtain ⟨hf, hR⟩ := (perm_smul_eq_iff _ _ _).1 hσ
    exact ⟨@Language.Equiv.mk L V V F.toStructure G.toStructure σ
      (fun f v => by simpa using hf f v) (fun R v => by simpa using hR R v)⟩

/-- **The orbits are the isomorphism classes.** Isomorphism of functional configurations is the
orbit relation of the action of the permutations of the carrier. -/
theorem isoSetoid_eq_orbitRel :
    isoSetoid L V = MulAction.orbitRel (Equiv.Perm V) (FunctionalConfiguration L V) := by
  ext F G
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, ← (isoSetoid L V).comm',
    isoSetoid_iff_exists_perm_smul_eq]

/-! ### The graph code -/

/-- The **graph code** of a functional configuration: the relational configuration, in the graph
language, of the graph expansion of the decoded structure. -/
noncomputable def graphCode (F : FunctionalConfiguration L V) :
    RelationalConfiguration L.graphLanguage V :=
  @ofStructure L.graphLanguage V (@graphExpansion L V F.toStructure)

@[simp]
theorem graphCode_eval_base (F : FunctionalConfiguration L V) {n : ℕ} (R : L.Relations n)
    (v : Fin n → V) :
    (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.base R) v) =
      F.rel.eval (atom R v) := by
  simp [graphCode]

@[simp]
theorem graphCode_eval_graph (F : FunctionalConfiguration L V) {k : ℕ} (f : L.Functions k)
    (w : Fin (k + 1) → V) :
    (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.graph f) w) = true ↔
      F.table (arg f (Fin.init w)) = w (Fin.last k) := by
  simp [graphCode]

/-- **The graph code is injective.** -/
theorem graphCode_injective : Function.Injective (graphCode (L := L) (V := V)) := by
  intro F G h
  refine ext (funext fun ⟨⟨k, f⟩, v⟩ => ?_) (RelationalConfiguration.ext fun a => ?_)
  · change F.table (arg f v) = G.table (arg f v)
    have hF := (graphCode_eval_graph F f (Fin.snoc v (F.table (arg f v)))).2 (by simp)
    rw [h, graphCode_eval_graph] at hF
    simpa using hF.symm
  · induction a using Atom.induction_atom with
    | h R v => rw [← graphCode_eval_base, h, graphCode_eval_base]

/-- **The graph code is equivariant.** -/
theorem graphCode_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) :
    graphCode (σ • F) = σ • graphCode F := by
  ext a
  induction a using Atom.induction_atom with
  | h R w =>
    cases R with
    | base R => simp
    | graph f =>
      rw [Bool.eq_iff_iff, graphCode_eval_graph, eval_perm_smul, Atom.map_atom,
        graphCode_eval_graph, table_perm_smul_arg, Equiv.Perm.eq_inv_iff_eq.symm]
      rfl

/-- **Graph codes are isomorphic exactly when the functional configurations are.** -/
theorem isoSetoid_graphCode_iff {F G : FunctionalConfiguration L V} :
    RelationalConfiguration.isoSetoid L.graphLanguage V (graphCode F) (graphCode G) ↔
      isoSetoid L V F G := by
  simp only [RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq,
    isoSetoid_iff_exists_perm_smul_eq, ← graphCode_perm_smul, graphCode_injective.eq_iff]

/-! ### The range of the graph code -/

/-- A code in the graph language **is a graph code** when the graph relation of every function
symbol is the graph of a total function: every tuple of arguments has exactly one value. -/
def IsGraphCode (c : RelationalConfiguration L.graphLanguage V) : Prop :=
  ∀ ⦃k : ℕ⦄ (f : L.Functions k) (v : Fin k → V),
    ∃! y, c.eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) = true

theorem isGraphCode_graphCode (F : FunctionalConfiguration L V) : IsGraphCode (graphCode F) :=
  fun k f v => ⟨F.table (arg f v), by simp, fun y hy => by
    have := (graphCode_eval_graph F f _).1 hy
    rw [Fin.init_snoc, Fin.snoc_last] at this
    exact this.symm⟩

/-- In a relational language every code is a graph code. -/
theorem isGraphCode_of_isRelational [L.IsRelational]
    (c : RelationalConfiguration L.graphLanguage V) : IsGraphCode c :=
  fun _ f => isEmptyElim f

/-- The functional configuration read off a graph code: the table records the value of each graph
relation, and the relational configuration the base relations. -/
noncomputable def ofGraphCode
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) :
    FunctionalConfiguration L V :=
  mk (fun p => (c.property p.1.2 p.2).exists.choose)
    (@ofStructure L V
      { funMap f v := (c.property f v).exists.choose
        RelMap R v := c.val.eval (atom (L := L.graphLanguage) (GraphRelation.base R) v) })

@[simp]
theorem rel_ofGraphCode_eval
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) {n : ℕ}
    (R : L.Relations n) (v : Fin n → V) :
    (ofGraphCode c).rel.eval (atom R v) =
      c.val.eval (atom (L := L.graphLanguage) (GraphRelation.base R) v) := by
  simp [ofGraphCode]

theorem table_ofGraphCode_eq_iff
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) {k : ℕ}
    (f : L.Functions k) (v : Fin k → V) (y : V) :
    (ofGraphCode c).table (arg f v) = y ↔
      c.val.eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) = true := by
  have h := (c.property f v).exists.choose_spec
  exact ⟨fun hy => hy ▸ h, fun hy => (c.property f v).unique h hy⟩

@[simp]
theorem graphCode_ofGraphCode
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) :
    graphCode (ofGraphCode c) = c.val := by
  ext a
  induction a using Atom.induction_atom with
  | h R w =>
    cases R with
    | base R => simp
    | graph f =>
      rw [Bool.eq_iff_iff, graphCode_eval_graph, table_ofGraphCode_eq_iff, Fin.snoc_init_self]

@[simp]
theorem ofGraphCode_graphCode (F : FunctionalConfiguration L V) :
    ofGraphCode ⟨graphCode F, isGraphCode_graphCode F⟩ = F :=
  graphCode_injective (graphCode_ofGraphCode _)

/-- **The range of the graph code** is the set of graph codes. -/
theorem range_graphCode : range (graphCode (L := L) (V := V)) = {c | IsGraphCode c} :=
  Subset.antisymm (range_subset_iff.2 isGraphCode_graphCode)
    fun c hc => ⟨ofGraphCode ⟨c, hc⟩, graphCode_ofGraphCode _⟩

/-- In a relational language the graph code is onto. -/
theorem range_graphCode_of_isRelational [L.IsRelational] :
    range (graphCode (L := L) (V := V)) = univ :=
  range_graphCode.trans (eq_univ_of_forall isGraphCode_of_isRelational)

/-- **The graph codes form a Gδ set** on a countable carrier with countably many function
symbols: totality of each graph relation at each tuple is an open condition, and so is the
failure of two distinct values. -/
theorem isGδ_setOf_isGraphCode [∀ n, Countable (L.Functions n)] [Countable V] :
    IsGδ {c : RelationalConfiguration L.graphLanguage V | IsGraphCode c} := by
  have hopen (g : Bool → Bool → Prop) (a b : Atom L.graphLanguage V) :
      IsOpen {c : RelationalConfiguration L.graphLanguage V | g (c.eval a) (c.eval b)} :=
    (isOpen_discrete {q : Bool × Bool | g q.1 q.2}).preimage
      ((continuous_eval a).prodMk (continuous_eval b))
  have : {c : RelationalConfiguration L.graphLanguage V | IsGraphCode c} =
      ⋂ (p : Arg L V), ((⋃ y, {c | c.eval (atom (L := L.graphLanguage)
          (GraphRelation.graph p.1.2) (Fin.snoc p.2 y)) = true}) ∩
        ⋂ (y : V) (y' : V), {c | c.eval (atom (L := L.graphLanguage)
          (GraphRelation.graph p.1.2) (Fin.snoc p.2 y)) = true →
          c.eval (atom (L := L.graphLanguage) (GraphRelation.graph p.1.2)
            (Fin.snoc p.2 y')) = true → y = y'}) := by
    ext c
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_iUnion, IsGraphCode]
    refine ⟨fun h p => ⟨(h p.1.2 p.2).exists, fun y y' hy hy' => (h p.1.2 p.2).unique hy hy'⟩,
      fun h k f v => ?_⟩
    obtain ⟨⟨y, hy⟩, huniq⟩ := h ⟨⟨k, f⟩, v⟩
    exact ⟨y, hy, fun y' hy' => huniq y' y hy' hy⟩
  rw [this]
  refine IsGδ.iInter fun p => (IsOpen.isGδ ?_).inter (IsGδ.iInter fun y => IsGδ.iInter fun y' =>
    IsOpen.isGδ ?_)
  · exact isOpen_iUnion fun y => (isClopen_setOf_eval _ true).isOpen
  · by_cases hyy : y = y'
    · simp [hyy]
    · simpa [hyy] using hopen (fun s t => ¬(s = true ∧ t = true)) _ _

/-- **The graph codes are not closed** in the presence of a function symbol on an infinite
carrier: tables with constant value `y` converge, as `y` leaves every finite set, to the code
whose relations are all empty, in which `f` has no value. -/
theorem not_isClosed_setOf_isGraphCode [Infinite V] {k : ℕ} (f : L.Functions k) :
    ¬IsClosed {c : RelationalConfiguration L.graphLanguage V | IsGraphCode c} := by
  intro hclosed
  let c₀ : RelationalConfiguration L.graphLanguage V := RelationalConfiguration.mk fun _ => false
  let F : V → FunctionalConfiguration L V := fun y =>
    mk (fun _ => y) (RelationalConfiguration.mk fun _ => false)
  have htend : Filter.Tendsto (fun y => graphCode (F y)) Filter.cofinite (𝓝 c₀) := by
    refine tendsto_pi_nhds.2 fun a => ?_
    have hev : ∀ y, graphCode (F y) a = (graphCode (F y)).eval a := fun y => (eval_def _ _).symm
    simp only [hev, ← eval_def c₀ a]
    refine tendsto_nhds_of_eventually_eq ?_
    induction a using Atom.induction_atom with
    | h R w =>
      cases R with
      | base R => exact Filter.Eventually.of_forall fun y => by simp [F, c₀]
      | graph g =>
        filter_upwards [Filter.eventually_cofinite_ne (w (Fin.last _))] with y hy
        simp only [c₀, eval_mk]
        rw [← Bool.not_eq_true, graphCode_eval_graph]
        simpa [F] using hy
  have hmem := hclosed.mem_of_tendsto htend
    (Filter.Eventually.of_forall fun y => isGraphCode_graphCode (F y))
  obtain ⟨y, hy, -⟩ := hmem f (fun _ => Classical.arbitrary V)
  simp [c₀] at hy

/-! ### Topology -/

variable [TopologicalSpace V]

instance : TopologicalSpace (FunctionalConfiguration L V) :=
  inferInstanceAs (TopologicalSpace ((Arg L V → V) × RelationalConfiguration L V))

@[fun_prop]
theorem continuous_table : Continuous (table : FunctionalConfiguration L V → Arg L V → V) :=
  continuous_fst

@[fun_prop]
theorem continuous_rel :
    Continuous (rel : FunctionalConfiguration L V → RelationalConfiguration L V) :=
  continuous_snd

/-- Continuity into functional configurations is continuity of the table and of the relational
configuration. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : X → FunctionalConfiguration L V} :
    Continuous g ↔ Continuous (fun x => (g x).table) ∧ Continuous (fun x => (g x).rel) :=
  continuous_prodMk

instance [T2Space V] : T2Space (FunctionalConfiguration L V) :=
  inferInstanceAs (T2Space ((Arg L V → V) × RelationalConfiguration L V))

instance [∀ n, Countable (L.Functions n)] [∀ n, Countable (L.Relations n)] [Countable V]
    [SecondCountableTopology V] : SecondCountableTopology (FunctionalConfiguration L V) :=
  inferInstanceAs (SecondCountableTopology ((Arg L V → V) × RelationalConfiguration L V))

/-- **The functional coding space is Polish** on a countable discrete carrier, with countably many
symbols. -/
instance [∀ n, Countable (L.Functions n)] [∀ n, Countable (L.Relations n)] [Countable V]
    [DiscreteTopology V] : PolishSpace (FunctionalConfiguration L V) := by
  have : IsCompletelyMetrizableSpace (Arg L V → V) := IsCompletelyMetrizableSpace.pi_countable
  have : PolishSpace (Arg L V → V) := {}
  exact inferInstanceAs (PolishSpace ((Arg L V → V) × RelationalConfiguration L V))

/-- Reading a graph code back into a functional configuration is continuous, for every topology on
the carrier: the value at `(f, v)` is `y` on the open set of graph codes whose graph relation
holds at `(v, y)`, so it is locally constant. -/
theorem continuous_ofGraphCode : Continuous (ofGraphCode (L := L) (V := V)) := by
  refine continuous_iff.2 ⟨continuous_pi fun ⟨⟨k, f⟩, v⟩ => ?_,
    RelationalConfiguration.continuous_iff.2 fun a => ?_⟩
  · refine (IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_).continuous
    have : (fun c => (ofGraphCode c).table ⟨⟨k, f⟩, v⟩) ⁻¹' {y} =
        Subtype.val ⁻¹' {c : RelationalConfiguration L.graphLanguage V |
          c.eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) = true} := by
      ext c
      exact table_ofGraphCode_eq_iff c f v y
    rw [this]
    exact ((isClopen_setOf_eval _ true).isOpen).preimage continuous_subtypeVal
  · induction a using Atom.induction_atom with
    | h R v =>
      simp only [rel_ofGraphCode_eval]
      exact (continuous_eval _).comp continuous_subtypeVal

variable [DiscreteTopology V]

/-- **The action is jointly continuous** on a discrete carrier: the value of `σ • F` at `(f, v)`
reads `σ⁻¹` at the finitely many entries of `v`, then `F` at a point of the discrete space of
tuples, then applies `σ`. -/
instance instContinuousSMulPerm :
    ContinuousSMul (Equiv.Perm V) (FunctionalConfiguration L V) where
  continuous_smul := by
    refine continuous_iff.2 ⟨continuous_pi fun p => ?_, ?_⟩
    · -- Reading the table at the argument `(f, w)` is continuous in the table and, trivially, in
      -- the tuple `w`, which ranges over a discrete space.
      have hread : Continuous fun q : (Arg L V → V) × (Fin p.1.1 → V) => q.1 ⟨p.1, q.2⟩ :=
        continuous_prod_of_discrete_right.2 fun w =>
          (continuous_apply _ : Continuous fun T : Arg L V → V => T ⟨p.1, w⟩)
      have hinv : Continuous fun q : Equiv.Perm V × FunctionalConfiguration L V =>
          (⇑q.1⁻¹ ∘ p.2 : Fin p.1.1 → V) :=
        continuous_pi fun i => (Equiv.Perm.continuous_inv_apply _).comp continuous_fst
      exact Equiv.Perm.continuous_eval.comp (continuous_fst.prodMk
        (hread.comp ((continuous_table.comp continuous_snd).prodMk hinv)))
    · exact continuous_smul.comp (continuous_fst.prodMk (continuous_rel.comp continuous_snd))

/-- **The graph code is continuous.** -/
@[fun_prop]
theorem continuous_graphCode : Continuous (graphCode (L := L) (V := V)) := by
  classical
  refine RelationalConfiguration.continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with
  | h R w =>
    cases R with
    | base R =>
      simp only [graphCode_eval_base]
      exact (continuous_eval (atom R w)).comp continuous_rel
    | graph f =>
      have : (fun F : FunctionalConfiguration L V =>
          (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.graph f) w)) =
          (fun y => decide (y = w (Fin.last _))) ∘ fun F => F.table (arg f (Fin.init w)) := by
        ext F
        rw [Function.comp_apply, Bool.eq_iff_iff, graphCode_eval_graph, decide_eq_true_iff]
      rw [this]
      exact continuous_of_discreteTopology.comp ((continuous_apply _).comp continuous_table)

/-- **The graph code is a homeomorphism onto its range**, the graph codes. -/
noncomputable def graphCodeHomeomorph :
    FunctionalConfiguration L V ≃ₜ {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}
    where
  toFun F := ⟨graphCode F, isGraphCode_graphCode F⟩
  invFun := ofGraphCode
  left_inv := ofGraphCode_graphCode
  right_inv c := Subtype.ext (graphCode_ofGraphCode c)
  continuous_toFun := continuous_graphCode.subtype_mk _
  continuous_invFun := continuous_ofGraphCode

@[simp]
theorem coe_graphCodeHomeomorph_apply (F : FunctionalConfiguration L V) :
    (graphCodeHomeomorph F : RelationalConfiguration L.graphLanguage V) = graphCode F :=
  (rfl)

@[simp]
theorem graphCodeHomeomorph_symm_apply
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) :
    graphCodeHomeomorph.symm c = ofGraphCode c :=
  (rfl)

/-- The graph code is a topological embedding. -/
theorem isEmbedding_graphCode : IsEmbedding (graphCode (L := L) (V := V)) :=
  IsEmbedding.subtypeVal.comp graphCodeHomeomorph.isEmbedding

end FunctionalConfiguration

end TauCeti
