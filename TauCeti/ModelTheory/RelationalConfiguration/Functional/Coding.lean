/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Language
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The functional coding space

A structure on a carrier `V` in a language `L` with function symbols is coded by a *functional
configuration*: a *function table*, giving the value at each function symbol `f` of `L` and each
tuple of arguments in `V`, together with a relational configuration recording which atomic
relations hold. The table space carries the product topology induced from `V`, and the functional
coding space the product of that with the topology of relational configurations. It is Polish when
`V` is Polish and there are countably many table and atom coordinates, for instance on a countable
discrete carrier with countably many symbols. It carries the Borel σ-algebra of this topology.

Permutations of `V` act by transporting the decoded structure: `σ` sends a table `F` to
`(f, v) ↦ σ (F (f, σ⁻¹ ∘ v))`, and acts on relational configurations by the logic action. For
discrete `V` the action is continuous, and its orbits are the isomorphism classes of decoded
structures.

The *graph code* of a functional configuration is the relational configuration, in the graph
language `L.graphLanguage`, of the graph expansion of its decoded structure: it keeps the relations,
and records the graph of each function symbol. The graph code is injective and equivariant,
continuous when `V` is discrete or `L` is relational, and two functional configurations decode to
isomorphic structures exactly when their graph codes are isomorphic. Its range is the set of codes
in which the graph relation of every function symbol is the graph of a total function
(`IsGraphCode`), and it is a homeomorphism onto this range whenever it is continuous. With
countably many symbols on a countable carrier the range is a Gδ set. It is not closed when `L`
has a function symbol and `V` is infinite: the graph codes of the configurations with constant
table value `y` and empty base relations converge, as `y` leaves every finite set, to the
all-false code. For a relational language it is the whole coding space.

Thus the graph code preserves and reflects isomorphism (`isoSetoid_graphCode_iff`) and is
equivariant. On a discrete carrier it is a topological embedding onto the set of graph codes, which
is invariant under permutations and, with countably many symbols on a countable carrier, Gδ.

## Main definitions

* `TauCeti.FunctionalConfiguration L V`: the functional coding space, pairs of a function table
  and a relational configuration.
* `TauCeti.FunctionalConfiguration.toStructure`: the decoded `L`-structure, and
  `TauCeti.FunctionalConfiguration.ofStructure`: the configuration of an `L`-structure.
* `TauCeti.FunctionalConfiguration.isoSetoid`: isomorphism of decoded structures, and
  `TauCeti.FunctionalConfiguration.IsomorphismInvariant`: closure of a set under it.
* `TauCeti.FunctionalConfiguration.graphCode`: the graph code.
* `TauCeti.FunctionalConfiguration.IsGraphCode`: every graph relation is the graph of a total
  function.
* `TauCeti.FunctionalConfiguration.graphCodeHomeomorph`: the graph code as a homeomorphism onto
  its range.

## Main results

* `TauCeti.FunctionalConfiguration.isoSetoid_eq_orbitRel`: isomorphism is the orbit relation of
  the action of `Equiv.Perm V`.
* `TauCeti.FunctionalConfiguration.isomorphismInvariant_iff_isInvariantBlock`: isomorphism
  invariance is invariance under the action of `Equiv.Perm V`; isomorphism-invariant sets are
  closed under complements and arbitrary unions and intersections.
* `TauCeti.FunctionalConfiguration.instContinuousSMulPerm`: for discrete `V`, the action is jointly
  continuous.
* `TauCeti.FunctionalConfiguration.continuous_graphCode`,
  `TauCeti.FunctionalConfiguration.graphCode_injective` and
  `TauCeti.FunctionalConfiguration.graphCode_perm_smul`: the graph code is continuous (for discrete
  `V`), injective and equivariant.
* `TauCeti.FunctionalConfiguration.isoSetoid_graphCode_iff`: graph codes are isomorphic exactly
  when the functional configurations are.
* `TauCeti.FunctionalConfiguration.isoSetoid_iff_isoSetoid_rel` and
  `TauCeti.FunctionalConfiguration.isomorphismInvariant_preimage_rel`: for a relational language,
  isomorphism is isomorphism of relational parts, so the preimage of an invariant class under the
  relational part is invariant.
* `TauCeti.FunctionalConfiguration.range_graphCode`,
  `TauCeti.FunctionalConfiguration.isEmbedding_graphCode`,
  `TauCeti.FunctionalConfiguration.isGδ_setOf_isGraphCode`,
  `TauCeti.FunctionalConfiguration.not_isClosed_setOf_isGraphCode` and
  `TauCeti.FunctionalConfiguration.isGraphCode_of_isRelational`: the range of the graph code, onto
  which the graph code is a homeomorphism for discrete `V`, a Gδ set for countable `V` with
  countably many function symbols in each arity, not closed in the presence of a function symbol
  on an infinite carrier, and everything for a relational language.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, §16.C (the space of countable
  structures, with function symbols coded by their graphs).
* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1.
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
def arg {k : ℕ} (f : L.Functions k) (v : Fin k → V) : Arg L V := ⟨⟨k, f⟩, v⟩

/-- Every argument is `arg f v` for a function symbol `f` and a tuple `v`. -/
@[elab_as_elim]
theorem Arg.induction_arg {motive : Arg L V → Prop}
    (h : ∀ {k : ℕ} (f : L.Functions k) (v : Fin k → V), motive (arg f v)) (p : Arg L V) :
    motive p := by
  obtain ⟨⟨k, f⟩, v⟩ := p
  exact h f v

/-- Define a function on arguments by its value at `arg f v` for each function symbol `f` and
tuple `v`. -/
@[elab_as_elim]
def Arg.recArg {motive : Arg L V → Sort*}
    (h : ∀ {k : ℕ} (f : L.Functions k) (v : Fin k → V), motive (arg f v)) (p : Arg L V) :
    motive p :=
  h p.1.2 p.2

@[simp]
theorem Arg.recArg_arg {motive : Arg L V → Sort*}
    (h : ∀ {k : ℕ} (f : L.Functions k) (v : Fin k → V), motive (arg f v)) {k : ℕ}
    (f : L.Functions k) (v : Fin k → V) :
    Arg.recArg (motive := motive) h (arg f v) = h f v :=
  (rfl)

/-- Relabel the entries of an argument along a map of carriers. -/
def Arg.map {W : Type*} (g : V → W) (p : Arg L V) : Arg L W := ⟨p.1, g ∘ p.2⟩

@[simp]
theorem Arg.map_arg {W : Type*} (g : V → W) {k : ℕ} (f : L.Functions k) (v : Fin k → V) :
    (arg f v).map g = arg f (g ∘ v) :=
  (rfl)

@[simp]
theorem Arg.map_id (p : Arg L V) : p.map id = p := (rfl)

@[simp]
theorem Arg.map_map {W X : Type*} (g : V → W) (g' : W → X) (p : Arg L V) :
    (p.map g).map g' = p.map (g' ∘ g) :=
  (rfl)

/-- The functional configuration with a given function table and relational configuration. -/
def mk (T : Arg L V → V) (c : RelationalConfiguration L V) : FunctionalConfiguration L V :=
  (T, c)

/-- The function table of a functional configuration. -/
def table (F : FunctionalConfiguration L V) : Arg L V → V := F.1

/-- The relational configuration of a functional configuration. -/
def rel (F : FunctionalConfiguration L V) : RelationalConfiguration L V := F.2

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

variable (L V) in
/-- The functional configuration of an `L`-structure: the table records its function values and
the relational configuration its relations. -/
noncomputable def ofStructure [L.Structure V] : FunctionalConfiguration L V :=
  mk (fun p => Structure.funMap p.1.2 p.2) (RelationalConfiguration.ofStructure L V)

@[simp]
theorem table_ofStructure [L.Structure V] {k : ℕ} (f : L.Functions k) (v : Fin k → V) :
    (ofStructure L V).table (arg f v) = Structure.funMap f v :=
  (rfl)

@[simp]
theorem rel_ofStructure [L.Structure V] :
    (ofStructure L V).rel = RelationalConfiguration.ofStructure L V :=
  (rfl)

/-- Decoding after encoding recovers the structure. -/
@[simp]
theorem toStructure_ofStructure (S : L.Structure V) : (@ofStructure L V S).toStructure = S := by
  classical
  apply Structure.ext
  · funext n f v
    rfl
  · funext n R v
    exact propext (by simp)

/-- Encoding after decoding recovers the functional configuration. -/
@[simp]
theorem ofStructure_toStructure (F : FunctionalConfiguration L V) :
    @ofStructure L V F.toStructure = F := by
  classical
  refine ext (funext fun p => ?_) (RelationalConfiguration.ext fun a => ?_)
  · induction p using Arg.induction_arg with
    | h f v => rfl
  · induction a using Atom.induction_atom with
    | h R v => simp

/-! ### The action of permutations -/

/-- Permutations of `V` act on functional configurations by transporting the decoded structure:
`σ` sends the table `F` to `(f, v) ↦ σ (F (f, σ⁻¹ ∘ v))`, and acts on the relational
configuration by the logic action. -/
instance instSMulPerm : SMul (Equiv.Perm V) (FunctionalConfiguration L V) :=
  ⟨fun σ F => mk (fun p => σ (F.table (p.map ⇑σ⁻¹))) (σ • F.rel)⟩

theorem table_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) (p : Arg L V) :
    (σ • F).table p = σ (F.table (p.map ⇑σ⁻¹)) :=
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
  one_smul F := ext (funext fun p => by simp [table_perm_smul])
    (by rw [rel_perm_smul, one_smul])
  mul_smul σ τ F := ext (funext fun p => by simp [table_perm_smul])
    (by rw [rel_perm_smul, rel_perm_smul, rel_perm_smul, mul_smul])

/-- Relabelling by `σ` decodes to the structure transported along `σ`. -/
@[simp]
theorem toStructure_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) :
    (σ • F).toStructure = @Equiv.inducedStructure L V V F.toStructure σ := by
  apply Structure.ext
  · funext k f v
    rfl
  · funext k R v
    exact propext (by simp [Function.comp_def])

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
    refine ext (funext fun p => ?_) (RelationalConfiguration.ext fun a => ?_)
    · induction p using Arg.induction_arg with
      | h f v => simpa [Function.comp_def] using hf f (⇑σ⁻¹ ∘ v)
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

/-- A set of functional configurations is **isomorphism-invariant** when it is closed under
isomorphism of decoded structures. -/
def IsomorphismInvariant (K : Set (FunctionalConfiguration L V)) : Prop :=
  ∀ ⦃F G⦄, isoSetoid L V F G → F ∈ K → G ∈ K

/-- Unfolding lemma for `IsomorphismInvariant`. -/
theorem isomorphismInvariant_iff {K : Set (FunctionalConfiguration L V)} :
    IsomorphismInvariant K ↔ ∀ ⦃F G⦄, isoSetoid L V F G → F ∈ K → G ∈ K :=
  Iff.rfl

/-- Isomorphic functional configurations lie in the same isomorphism-invariant sets. -/
theorem IsomorphismInvariant.mem_iff {K : Set (FunctionalConfiguration L V)}
    (hK : IsomorphismInvariant K) {F G : FunctionalConfiguration L V} (h : isoSetoid L V F G) :
    F ∈ K ↔ G ∈ K :=
  ⟨hK h, hK ((isoSetoid L V).symm h)⟩

/-- **Isomorphism invariance is invariance under the logic action**: a set of functional
configurations is isomorphism invariant exactly when every permutation of the carrier maps it into
itself. -/
theorem isomorphismInvariant_iff_isInvariantBlock {K : Set (FunctionalConfiguration L V)} :
    IsomorphismInvariant K ↔ MulAction.IsInvariantBlock (Equiv.Perm V) K := by
  refine ⟨fun hK σ => ?_, fun hK F G h hF => ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact hK (isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, rfl⟩) hF
  · obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
    exact hK σ (smul_mem_smul_set hF)

/-- The preimage of any set of isomorphism classes is isomorphism invariant. -/
theorem isomorphismInvariant_preimage_quotientMk (s : Set (Quotient (isoSetoid L V))) :
    IsomorphismInvariant (Quotient.mk (isoSetoid L V) ⁻¹' s) :=
  fun _ _ h hF => by rwa [mem_preimage, ← Quotient.sound h]

/-- A set is isomorphism invariant exactly when it is its own saturation under isomorphism. -/
theorem isomorphismInvariant_iff_preimage_image_quotientMk
    {K : Set (FunctionalConfiguration L V)} :
    IsomorphismInvariant K ↔
      Quotient.mk (isoSetoid L V) ⁻¹' (Quotient.mk (isoSetoid L V) '' K) = K := by
  refine ⟨fun hK => (subset_preimage_image _ _).antisymm' ?_, fun h => ?_⟩
  · rintro G ⟨F, hF, hFG⟩
    exact hK (Quotient.exact hFG) hF
  · rw [← h]
    exact isomorphismInvariant_preimage_quotientMk _

/-- The empty set is isomorphism invariant. -/
@[simp]
theorem isomorphismInvariant_empty :
    IsomorphismInvariant (∅ : Set (FunctionalConfiguration L V)) :=
  fun _ _ _ h => h

/-- The set of all functional configurations is isomorphism invariant. -/
@[simp]
theorem isomorphismInvariant_univ :
    IsomorphismInvariant (univ : Set (FunctionalConfiguration L V)) :=
  fun _ _ _ _ => mem_univ _

/-- The complement of an isomorphism-invariant set is isomorphism invariant. -/
theorem IsomorphismInvariant.compl {K : Set (FunctionalConfiguration L V)}
    (hK : IsomorphismInvariant K) : IsomorphismInvariant Kᶜ :=
  fun _ _ h hF hG => hF (hK ((isoSetoid L V).symm h) hG)

/-- The intersection of two isomorphism-invariant sets is isomorphism invariant. -/
theorem IsomorphismInvariant.inter {K K' : Set (FunctionalConfiguration L V)}
    (hK : IsomorphismInvariant K) (hK' : IsomorphismInvariant K') :
    IsomorphismInvariant (K ∩ K') :=
  fun _ _ h hF => ⟨hK h hF.1, hK' h hF.2⟩

/-- The union of two isomorphism-invariant sets is isomorphism invariant. -/
theorem IsomorphismInvariant.union {K K' : Set (FunctionalConfiguration L V)}
    (hK : IsomorphismInvariant K) (hK' : IsomorphismInvariant K') :
    IsomorphismInvariant (K ∪ K') :=
  fun _ _ h hF => hF.imp (hK h) (hK' h)

/-- An intersection of isomorphism-invariant sets is isomorphism invariant. -/
theorem isomorphismInvariant_iInter {ι : Sort*} {K : ι → Set (FunctionalConfiguration L V)}
    (hK : ∀ i, IsomorphismInvariant (K i)) : IsomorphismInvariant (⋂ i, K i) :=
  fun _ _ h hF => mem_iInter.2 fun i => hK i h (mem_iInter.1 hF i)

/-- A union of isomorphism-invariant sets is isomorphism invariant. -/
theorem isomorphismInvariant_iUnion {ι : Sort*} {K : ι → Set (FunctionalConfiguration L V)}
    (hK : ∀ i, IsomorphismInvariant (K i)) : IsomorphismInvariant (⋃ i, K i) :=
  fun _ _ h hF => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hF
    exact mem_iUnion.2 ⟨i, hK i h hi⟩

/-! ### Relational languages -/

section Relational

variable [L.IsRelational]

/-- For a relational language there are no function arguments. -/
instance isEmpty_arg : IsEmpty (Arg L V) :=
  inferInstanceAs (IsEmpty (Σ f : (Σ l, L.Functions l), Fin f.1 → V))

/-- For a relational language a functional configuration is determined by its relational part. -/
theorem rel_injective : Function.Injective (rel : FunctionalConfiguration L V → _) :=
  fun _ _ h => ext (funext isEmptyElim) h

/-- For a relational language every relational configuration is the relational part of the
functional configuration with the empty table. -/
theorem rel_surjective : Function.Surjective (rel : FunctionalConfiguration L V → _) :=
  fun c => ⟨mk isEmptyElim c, rel_mk _ _⟩

/-- For a relational language two functional configurations are isomorphic exactly when their
relational parts are. -/
theorem isoSetoid_iff_isoSetoid_rel {F G : FunctionalConfiguration L V} :
    isoSetoid L V F G ↔ RelationalConfiguration.isoSetoid L V F.rel G.rel := by
  rw [isoSetoid_iff_exists_perm_smul_eq, RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq]
  refine exists_congr fun σ => ⟨fun h => h ▸ (rel_perm_smul σ F).symm, fun h => ?_⟩
  exact rel_injective ((rel_perm_smul σ F).trans h)

/-- For a relational language, the functional configurations whose relational part lies in an
invariant class form an invariant class. -/
theorem isomorphismInvariant_preimage_rel {K : Set (RelationalConfiguration L V)}
    (hK : RelationalConfiguration.IsomorphismInvariant K) :
    IsomorphismInvariant (rel ⁻¹' K : Set (FunctionalConfiguration L V)) := by
  rw [isomorphismInvariant_iff]
  intro F G h hF
  exact RelationalConfiguration.isomorphismInvariant_iff.1 hK
    (isoSetoid_iff_isoSetoid_rel.1 h) hF

end Relational

/-! ### The graph code -/

/-- The **graph code** of a functional configuration: the relational configuration, in the graph
language, of the graph expansion of the decoded structure (function symbols coded by their graphs,
as in Kechris, §16.C). -/
noncomputable def graphCode (F : FunctionalConfiguration L V) :
    RelationalConfiguration L.graphLanguage V :=
  @RelationalConfiguration.ofStructure L.graphLanguage V (@graphExpansion L V F.toStructure)

/-- The graph code is the configuration of the graph expansion of the decoded structure. -/
theorem graphCode_def (F : FunctionalConfiguration L V) :
    graphCode F =
      @RelationalConfiguration.ofStructure L.graphLanguage V (@graphExpansion L V F.toStructure) :=
  (rfl)

/-- The base coordinates of the graph code are the relation values of the configuration. -/
@[simp]
theorem eval_graphCode_base (F : FunctionalConfiguration L V) {n : ℕ} (R : L.Relations n)
    (v : Fin n → V) :
    (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.base R) v) =
      F.rel.eval (atom R v) := by
  simp [graphCode]

/-- The graph coordinate of `f` at `w` tests whether the table value at `f` and the first `k`
entries of `w` is the last entry of `w`. -/
@[simp]
theorem eval_graphCode_graph (F : FunctionalConfiguration L V) {k : ℕ} (f : L.Functions k)
    (w : Fin (k + 1) → V) [Decidable (F.table (arg f (Fin.init w)) = w (Fin.last k))] :
    (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.graph f) w) =
      decide (F.table (arg f (Fin.init w)) = w (Fin.last k)) := by
  simp [graphCode]

/-- The graph coordinate of `f` at `w` holds exactly when the table value at `f` and the first `k`
entries of `w` is the last entry of `w`. -/
@[simp]
theorem eval_graphCode_graph_eq_true (F : FunctionalConfiguration L V) {k : ℕ}
    (f : L.Functions k) (w : Fin (k + 1) → V) :
    (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.graph f) w) = true ↔
      F.table (arg f (Fin.init w)) = w (Fin.last k) := by
  classical
  simp

/-- The graph coordinate of `f` at `Fin.snoc v y` holds exactly when the table value at `(f, v)`
is `y`. -/
theorem eval_graphCode_graph_snoc_eq_true (F : FunctionalConfiguration L V) {k : ℕ}
    (f : L.Functions k) (v : Fin k → V) (y : V) :
    (graphCode F).eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) =
        true ↔ F.table (arg f v) = y := by
  rw [eval_graphCode_graph_eq_true, Fin.init_snoc, Fin.snoc_last]

/-- **The graph code is injective.** -/
theorem graphCode_injective : Function.Injective (graphCode (L := L) (V := V)) := by
  intro F G h
  refine ext (funext fun p => ?_) (RelationalConfiguration.ext fun a => ?_)
  · induction p using Arg.induction_arg with
    | h f v =>
      have hF := (eval_graphCode_graph_snoc_eq_true F f v _).2 rfl
      rw [h, eval_graphCode_graph_snoc_eq_true] at hF
      exact hF.symm
  · induction a using Atom.induction_atom with
    | h R v => rw [← eval_graphCode_base, h, eval_graphCode_base]

/-- **The graph code is equivariant.** -/
@[simp]
theorem graphCode_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V) :
    graphCode (σ • F) = σ • graphCode F := by
  ext a
  induction a using Atom.induction_atom with
  | h R w =>
    cases R with
    | base R => simp
    | graph f =>
      classical
      simp [Equiv.Perm.eq_inv_iff_eq.symm, Fin.comp_init]

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

theorem isGraphCode_iff {c : RelationalConfiguration L.graphLanguage V} :
    IsGraphCode c ↔ ∀ ⦃k : ℕ⦄ (f : L.Functions k) (v : Fin k → V),
      ∃! y, c.eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) = true :=
  Iff.rfl

@[simp]
theorem isGraphCode_graphCode (F : FunctionalConfiguration L V) : IsGraphCode (graphCode F) :=
  fun _ f v => ⟨F.table (arg f v), (eval_graphCode_graph_snoc_eq_true F f v _).2 rfl,
    fun y hy => ((eval_graphCode_graph_snoc_eq_true F f v y).1 hy).symm⟩

/-- In a relational language every code is a graph code. -/
@[simp]
theorem isGraphCode_of_isRelational [L.IsRelational]
    (c : RelationalConfiguration L.graphLanguage V) : IsGraphCode c :=
  fun _ f => isEmptyElim f

/-- The functional configuration read off a graph code: the table records the value of each graph
relation, and the relational configuration the base relations. -/
noncomputable def ofGraphCode
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) :
    FunctionalConfiguration L V :=
  mk (fun p => (c.property p.1.2 p.2).exists.choose)
    (@RelationalConfiguration.ofStructure L V
      { funMap f v := (c.property f v).exists.choose
        RelMap R v := c.val.eval (atom (L := L.graphLanguage) (GraphRelation.base R) v) })

/-- The relations of `ofGraphCode c` are the base coordinates of `c`. -/
@[simp]
theorem eval_rel_ofGraphCode
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) {n : ℕ}
    (R : L.Relations n) (v : Fin n → V) :
    (ofGraphCode c).rel.eval (atom R v) =
      c.val.eval (atom (L := L.graphLanguage) (GraphRelation.base R) v) := by
  simp [ofGraphCode]

/-- The table of `ofGraphCode c` takes the value `y` at `(f, v)` exactly when the graph relation of
`f` in `c` holds at `Fin.snoc v y`. -/
@[simp]
theorem table_ofGraphCode_eq_iff
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) {k : ℕ}
    (f : L.Functions k) (v : Fin k → V) (y : V) :
    (ofGraphCode c).table (arg f v) = y ↔
      c.val.eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) = true := by
  have h := (c.property f v).exists.choose_spec
  exact ⟨fun hy => hy ▸ h, fun hy => (c.property f v).unique h hy⟩

/-- The graph relation of `f` in a graph code holds at the tuple `v` and the value of the table of
`ofGraphCode c` at `(f, v)`. -/
@[simp]
theorem eval_graph_snoc_table_ofGraphCode
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) {k : ℕ}
    (f : L.Functions k) (v : Fin k → V) :
    c.val.eval (atom (L := L.graphLanguage) (GraphRelation.graph f)
      (Fin.snoc v ((ofGraphCode c).table (arg f v)))) = true :=
  (table_ofGraphCode_eq_iff c f v _).1 rfl

/-- The graph code of `ofGraphCode c` is `c`. -/
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
      rw [Bool.eq_iff_iff, eval_graphCode_graph_eq_true, table_ofGraphCode_eq_iff,
        Fin.snoc_init_self]

/-- Reading back the graph code of `F` recovers `F`. -/
@[simp]
theorem ofGraphCode_graphCode (F : FunctionalConfiguration L V) :
    ofGraphCode ⟨graphCode F, isGraphCode_graphCode F⟩ = F :=
  graphCode_injective (graphCode_ofGraphCode _)

/-- **The range of the graph code** is the set of graph codes. -/
theorem range_graphCode : range (graphCode (L := L) (V := V)) = {c | IsGraphCode c} :=
  Subset.antisymm (range_subset_iff.2 isGraphCode_graphCode)
    fun c hc => ⟨ofGraphCode ⟨c, hc⟩, graphCode_ofGraphCode _⟩

/-- A code is in the range of the graph code exactly when it is a graph code. -/
theorem mem_range_graphCode_iff {c : RelationalConfiguration L.graphLanguage V} :
    c ∈ range graphCode ↔ IsGraphCode c := by
  rw [range_graphCode, mem_ofPred_eq]

/-- In a relational language the graph code is onto. -/
theorem range_graphCode_of_isRelational [L.IsRelational] :
    range (graphCode (L := L) (V := V)) = univ :=
  range_graphCode.trans (eq_univ_of_forall isGraphCode_of_isRelational)

/-- **The graph codes are invariant under permutations** of the carrier. -/
@[simp]
theorem isGraphCode_perm_smul_iff (σ : Equiv.Perm V)
    {c : RelationalConfiguration L.graphLanguage V} : IsGraphCode (σ • c) ↔ IsGraphCode c := by
  have key (τ : Equiv.Perm V) {c : RelationalConfiguration L.graphLanguage V}
      (hc : IsGraphCode c) : IsGraphCode (τ • c) := by
    obtain ⟨F, rfl⟩ : c ∈ range graphCode := range_graphCode ▸ hc
    rw [← graphCode_perm_smul]
    exact isGraphCode_graphCode _
  exact ⟨fun h => by simpa using key σ⁻¹ h, key σ⟩

/-- **The graph codes form a Gδ set** on a countable carrier with countably many function
symbols of each arity. -/
theorem isGδ_setOf_isGraphCode [∀ n, Countable (L.Functions n)] [Countable V] :
    IsGδ {c : RelationalConfiguration L.graphLanguage V | IsGraphCode c} := by
  -- Totality of each graph relation at each tuple is an open condition, and so is the failure of
  -- two distinct values: both are built from the clopen sets `{c | c.eval a = true}`.
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
    · have hset : ∀ a b : Atom L.graphLanguage V,
          {c : RelationalConfiguration L.graphLanguage V |
            c.eval a = true → c.eval b = true → y = y'} =
          {c | c.eval a = true}ᶜ ∪ {c | c.eval b = true}ᶜ := fun a b => by
        ext; simp [hyy, imp_iff_not_or]
      rw [hset]
      exact (isClopen_setOf_eval _ true).isClosed.isOpen_compl.union
        (isClopen_setOf_eval _ true).isClosed.isOpen_compl

/-- **The graph codes are not closed** when `L` has a function symbol and the carrier is
infinite. -/
theorem not_isClosed_setOf_isGraphCode [Infinite V] {k : ℕ} (f : L.Functions k) :
    ¬IsClosed {c : RelationalConfiguration L.graphLanguage V | IsGraphCode c} := by
  -- The graph codes of the configurations with constant table value `y` and empty base relations
  -- converge, as `y` leaves every finite set, to the all-false code, in which `f` has no value.
  classical
  intro hclosed
  let c₀ : RelationalConfiguration L.graphLanguage V := RelationalConfiguration.mk fun _ => false
  let F : V → FunctionalConfiguration L V := fun y =>
    mk (fun _ => y) (RelationalConfiguration.mk fun _ => false)
  have htend : Filter.Tendsto (fun y => graphCode (F y)) Filter.cofinite (𝓝 c₀) := by
    refine RelationalConfiguration.tendsto_nhds_iff.2 fun a => tendsto_nhds_of_eventually_eq ?_
    induction a using Atom.induction_atom with
    | h R w =>
      cases R with
      | base R => exact Filter.Eventually.of_forall fun y => by simp [F, c₀]
      | graph g =>
        filter_upwards [Filter.eventually_cofinite_ne (w (Fin.last _))] with y hy
        simpa [F, c₀] using hy
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

@[fun_prop]
theorem continuous_mk {X : Type*} [TopologicalSpace X] {T : X → Arg L V → V}
    {c : X → RelationalConfiguration L V} (hT : Continuous T) (hc : Continuous c) :
    Continuous fun x => mk (T x) (c x) :=
  hT.prodMk hc

/-- The Borel σ-algebra of the functional coding space. -/
instance instMeasurableSpace : MeasurableSpace (FunctionalConfiguration L V) :=
  borel _

instance instBorelSpace : BorelSpace (FunctionalConfiguration L V) :=
  ⟨rfl⟩

instance [T2Space V] : T2Space (FunctionalConfiguration L V) :=
  inferInstanceAs (T2Space ((Arg L V → V) × RelationalConfiguration L V))

instance [Countable (Arg L V)] [Countable (Atom L V)] [SecondCountableTopology V] :
    SecondCountableTopology (FunctionalConfiguration L V) :=
  inferInstanceAs (SecondCountableTopology ((Arg L V → V) × (Atom L V → Bool)))

/-- **The functional coding space is Polish** on a Polish carrier when the table and the
relational configuration have countably many coordinates, for instance on a countable discrete
carrier with countably many symbols. -/
instance [Countable (Arg L V)] [Countable (Atom L V)] [PolishSpace V] :
    PolishSpace (FunctionalConfiguration L V) := by
  have : IsCompletelyMetrizableSpace (Arg L V → V) := IsCompletelyMetrizableSpace.pi_countable
  have : PolishSpace (Arg L V → V) := {}
  have : IsCompletelyMetrizableSpace (Atom L V → Bool) := IsCompletelyMetrizableSpace.pi_countable
  have : PolishSpace (Atom L V → Bool) := {}
  exact inferInstanceAs (PolishSpace ((Arg L V → V) × (Atom L V → Bool)))

/-- Reading a graph code back into a functional configuration is continuous, for every topology on
the carrier. -/
@[fun_prop]
theorem continuous_ofGraphCode : Continuous (ofGraphCode (L := L) (V := V)) := by
  refine continuous_iff.2 ⟨continuous_pi fun p => ?_,
    RelationalConfiguration.continuous_iff.2 fun a => ?_⟩
  · -- The value at `(f, v)` is `y` on the open set of graph codes whose graph relation holds at
    -- `(v, y)`, so it is locally constant.
    induction p using Arg.induction_arg with | h f v => ?_
    refine (IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_).continuous
    have : (fun c => (ofGraphCode c).table (arg f v)) ⁻¹' {y} =
        Subtype.val ⁻¹' {c : RelationalConfiguration L.graphLanguage V |
          c.eval (atom (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc v y)) = true} := by
      ext c
      exact table_ofGraphCode_eq_iff c f v y
    rw [this]
    exact ((isClopen_setOf_eval _ true).isOpen).preimage continuous_subtypeVal
  · induction a using Atom.induction_atom with
    | h R v =>
      simp only [eval_rel_ofGraphCode]
      exact (continuous_eval _).comp continuous_subtypeVal

/-- In a relational language the graph code is continuous, for every topology on the carrier. -/
theorem continuous_graphCode_of_isRelational [L.IsRelational] :
    Continuous (graphCode (L := L) (V := V)) := by
  refine RelationalConfiguration.continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with
  | h R w =>
    cases R with
    | base R =>
      simp only [eval_graphCode_base]
      exact (continuous_eval (atom R w)).comp continuous_rel
    | graph f => exact isEmptyElim f

/-- A continuous graph code is a homeomorphism onto its range, the graph codes. -/
noncomputable def graphCodeHomeomorphOfContinuous (h : Continuous (graphCode (L := L) (V := V))) :
    FunctionalConfiguration L V ≃ₜ {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}
    where
  toFun F := ⟨graphCode F, isGraphCode_graphCode F⟩
  invFun := ofGraphCode
  left_inv := ofGraphCode_graphCode
  right_inv c := Subtype.ext (graphCode_ofGraphCode c)
  continuous_toFun := h.subtype_mk _
  continuous_invFun := continuous_ofGraphCode

@[simp]
theorem coe_graphCodeHomeomorphOfContinuous_apply (h : Continuous (graphCode (L := L) (V := V)))
    (F : FunctionalConfiguration L V) :
    (graphCodeHomeomorphOfContinuous h F : RelationalConfiguration L.graphLanguage V) =
      graphCode F :=
  (rfl)

@[simp]
theorem graphCodeHomeomorphOfContinuous_symm_apply
    (h : Continuous (graphCode (L := L) (V := V)))
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) :
    (graphCodeHomeomorphOfContinuous h).symm c = ofGraphCode c :=
  (rfl)

/-- A continuous graph code is a topological embedding. -/
theorem isEmbedding_graphCode_of_continuous (h : Continuous (graphCode (L := L) (V := V))) :
    IsEmbedding (graphCode (L := L) (V := V)) :=
  IsEmbedding.subtypeVal.comp (graphCodeHomeomorphOfContinuous h).isEmbedding

variable [DiscreteTopology V]

/-- **The action is jointly continuous** on a discrete carrier. -/
instance instContinuousSMulPerm :
    ContinuousSMul (Equiv.Perm V) (FunctionalConfiguration L V) where
  continuous_smul := by
    -- The value of `σ • F` at `(f, v)` reads `σ⁻¹` at the finitely many entries of `v`, then `F`
    -- at a point of the discrete space of tuples, then applies `σ`.
    refine continuous_iff.2 ⟨continuous_pi fun p => ?_, ?_⟩
    · induction p using Arg.induction_arg with | h f v => ?_
      simp only [table_perm_smul_arg]
      -- Reading the table at the argument `(f, w)` is continuous in the table and, trivially, in
      -- the tuple `w`, which ranges over a discrete space.
      have hread : Continuous fun q : (Arg L V → V) × (Fin _ → V) => q.1 (arg f q.2) :=
        continuous_prod_of_discrete_right.2 fun w =>
          (continuous_apply _ : Continuous fun T : Arg L V → V => T (arg f w))
      have hinv : Continuous fun q : Equiv.Perm V × FunctionalConfiguration L V =>
          (⇑q.1⁻¹ ∘ v : Fin _ → V) :=
        continuous_pi fun i => (Equiv.Perm.continuous_inv_apply _).comp continuous_fst
      exact Equiv.Perm.continuous_eval.comp (continuous_fst.prodMk
        (hread.comp ((continuous_table.comp continuous_snd).prodMk hinv)))
    · exact continuous_smul.comp (continuous_fst.prodMk (continuous_rel.comp continuous_snd))

/-- **The graph code is continuous** on a discrete carrier. -/
@[fun_prop]
theorem continuous_graphCode : Continuous (graphCode (L := L) (V := V)) := by
  classical
  refine RelationalConfiguration.continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with
  | h R w =>
    cases R with
    | base R =>
      simp only [eval_graphCode_base]
      exact (continuous_eval (atom R w)).comp continuous_rel
    | graph f =>
      simp only [eval_graphCode_graph]
      exact Continuous.comp' (g := fun y => decide (y = w (Fin.last _)))
        continuous_of_discreteTopology
        ((continuous_apply (arg f (Fin.init w))).comp continuous_table)

/-- **The graph code is a homeomorphism onto its range**, the graph codes, on a discrete
carrier. -/
noncomputable def graphCodeHomeomorph :
    FunctionalConfiguration L V ≃ₜ
      {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c} :=
  graphCodeHomeomorphOfContinuous continuous_graphCode

@[simp]
theorem coe_graphCodeHomeomorph_apply (F : FunctionalConfiguration L V) :
    (graphCodeHomeomorph F : RelationalConfiguration L.graphLanguage V) = graphCode F :=
  (rfl)

@[simp]
theorem graphCodeHomeomorph_symm_apply
    (c : {c : RelationalConfiguration L.graphLanguage V // IsGraphCode c}) :
    graphCodeHomeomorph.symm c = ofGraphCode c :=
  (rfl)

/-- The graph code is a topological embedding on a discrete carrier. -/
theorem isEmbedding_graphCode : IsEmbedding (graphCode (L := L) (V := V)) :=
  isEmbedding_graphCode_of_continuous continuous_graphCode

end FunctionalConfiguration

end TauCeti
