/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Basic.ExistsUnique
public import TauCeti.Combinatorics.SimpleGraph.Matching.Dimer
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Data.ZMod.Basic

/-!
# Checks for dimer configurations

* **The line.** On the nearest-neighbour graph of `ℤ` there are exactly two dimer
  configurations, the even edges `{2k, 2k + 1}` and the odd edges `{2k + 1, 2k + 2}`
  (`setOf_isDimerConfiguration_int`); with `2ℤ` acting by translations they form the subshift
  `dimerSubshiftInt`. For `F = ∅` the two completion sets are the two different singletons, while
  their sets of restrictions to `F` agree: the completion set itself is not determined by `ω` near
  `F`, only its restrictions to `F` are (`dimerCompletionSet_empty_evenConfig_ne_oddConfig`,
  `image_restrict_dimerCompletionSet_empty_eq`).
* **Local finiteness is needed for closedness.** On the vertices `c, d, x_n, y_n` (`n : ℕ`) with
  edges `c x_n`, `d y_n`, `x_n y_n`, the perfect matchings
  `M_k = {c x_k, d y_k} ∪ {x_n y_n : n ≠ k}` converge coordinatewise to the rungs
  `{x_n y_n}`, which leave `c` uncovered (`tendsto_combMatching`,
  `not_isDimerConfiguration_combRungs`), so the dimer configurations of this graph, in which `c`
  and `d` have infinite degree, do not form a closed set
  (`not_isClosed_setOf_isDimerConfiguration_combGraph`).
* **The hexagon.** The `6`-cycle, the nearest-neighbour graph of `ZMod 6`, has exactly two dimer
  configurations (`setOf_isDimerConfiguration_zmod_six`), the two lozenge tilings of the unit
  hexagon.

On the nearest-neighbour graph of a ring `R` with `2 ≠ 0`, every vertex `v` lies in exactly the
two edges `{v − 1, v}` and `{v, v + 1}`, so a configuration is a dimer configuration exactly when
consecutive edges have different values (`isDimerConfiguration_nnGraph_iff`), and then the value
at `{n, n + 1}` is the value at `{0, 1}`, flipped when `n` is odd (`apply_edge_intCast`).
-/

public section

noncomputable section

open SimpleGraph Function Filter Topology Set

namespace TauCeti.Examples.DimerConfiguration

/-! ### Nearest-neighbour graphs of rings -/

section Ring

variable {R : Type*} [Ring R]

variable (R) in
/-- The nearest-neighbour graph of a ring: `a` and `b` are adjacent when one is the other plus
one. -/
def nnGraph : SimpleGraph R :=
  SimpleGraph.fromRel fun a b => b = a + 1

@[simp]
theorem nnGraph_adj {a b : R} : (nnGraph R).Adj a b ↔ a ≠ b ∧ (b = a + 1 ∨ a = b + 1) :=
  fromRel_adj _ a b

variable [Nontrivial R]

theorem nnGraph_adj_add_one (a : R) : (nnGraph R).Adj a (a + 1) := by
  refine nnGraph_adj.2 ⟨fun h => one_ne_zero (α := R) ?_, Or.inl rfl⟩
  simpa using congrArg (· - a) h

/-- The edge `{a, a + 1}` of the nearest-neighbour graph. -/
def edge (a : R) : (nnGraph R).edgeSet :=
  ⟨s(a, a + 1), nnGraph_adj_add_one a⟩

@[simp]
theorem coe_edge (a : R) : (edge a : Sym2 R) = s(a, a + 1) :=
  (rfl)

/-- Every edge is `{a, a + 1}` for some `a`. -/
theorem exists_edge_eq (e : (nnGraph R).edgeSet) : ∃ a, edge a = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
    rcases (nnGraph_adj.1 he).2 with h | h <;> dsimp only at h <;> subst h
    · exact ⟨u, rfl⟩
    · exact ⟨v, Subtype.ext Sym2.eq_swap⟩

/-- The edges at `v` are `{v − 1, v}` and `{v, v + 1}`. -/
theorem mem_iff_eq_edge_sub_one_or_eq_edge {v : R} {e : (nnGraph R).edgeSet} :
    v ∈ (e : Sym2 R) ↔ e = edge (v - 1) ∨ e = edge v := by
  obtain ⟨a, rfl⟩ := exists_edge_eq e
  rw [coe_edge, Sym2.mem_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (by simp)
  · rintro (h | h) <;> have := congrArg (fun e : (nnGraph R).edgeSet => (e : Sym2 R)) h <;>
      simp only [coe_edge, Sym2.eq_iff, sub_add_cancel] at this
    · rcases this with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact Or.inr h₂.symm
      · exact Or.inl h₁.symm
    · rcases this with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact Or.inl h₁.symm
      · exact Or.inr h₂.symm

/-- When `2 ≠ 0`, distinct points give distinct edges. -/
theorem edge_injective (h2 : (2 : R) ≠ 0) : Injective (edge (R := R)) := by
  intro a b h
  have := congrArg (fun e : (nnGraph R).edgeSet => (e : Sym2 R)) h
  simp only [coe_edge, Sym2.eq_iff] at this
  rcases this with ⟨h, -⟩ | ⟨rfl, h⟩
  · exact h
  · exact absurd (by simpa [add_assoc, one_add_one_eq_two] using congrArg (· - b) h) h2

/-- When `2 ≠ 0`, the point chosen for the edge `{a, a + 1}` is `a`. -/
theorem choose_exists_edge_eq (h2 : (2 : R) ≠ 0) (a : R) :
    Classical.choose (exists_edge_eq (edge a)) = a :=
  edge_injective h2 (Classical.choose_spec (exists_edge_eq (edge a)))

/-- **Dimer configurations of a nearest-neighbour graph.** When `2 ≠ 0`, a configuration is a
dimer configuration exactly when consecutive edges have different values. -/
theorem isDimerConfiguration_nnGraph_iff (h2 : (2 : R) ≠ 0) {ω : (nnGraph R).edgeSet → Bool} :
    (nnGraph R).IsDimerConfiguration ω ↔ ∀ a, ω (edge (a + 1)) = !ω (edge a) := by
  have hv (v : R) : (∃! e, ω e = true ∧ (e = edge (v - 1) ∨ e = edge v)) ↔
      ω (edge v) = !ω (edge (v - 1)) := by
    rw [TauCeti.existsUnique_and_eq_or_eq_iff_xor fun h => by simpa using edge_injective h2 h]
    cases ω (edge v) <;> cases ω (edge (v - 1)) <;> simp [Xor]
  simp only [isDimerConfiguration_iff, mem_iff_eq_edge_sub_one_or_eq_edge, hv]
  exact ⟨fun h a => by simpa using h (a + 1), fun h v => by simpa using h (v - 1)⟩

/-- When consecutive edges have different values, the value at the edge `{n, n + 1}` is the value
at `{0, 1}`, flipped when `n` is odd. -/
theorem apply_edge_intCast {ω : (nnGraph R).edgeSet → Bool}
    (h : ∀ a, ω (edge (a + 1)) = !ω (edge a)) (n : ℤ) :
    ω (edge (n : R)) = (ω (edge 0) ^^ decide (Odd n)) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [Int.cast_add, Int.cast_one, h, ih]
    cases ω (edge 0) <;> simp [← Nat.not_even_iff_odd]
  | pred n ih =>
    have h' := h ((-(n : ℤ) - 1 : ℤ) : R)
    rw [show ((-(n : ℤ) - 1 : ℤ) : R) + 1 = ((-(n : ℤ) : ℤ) : R) by simp, ih] at h'
    rw [← Bool.not_not (ω (edge _)), ← h']
    cases ω (edge 0) <;> simp [← Nat.not_even_iff_odd]

end Ring

/-! ### The line -/

/-- The even edges `{2k, 2k + 1}` of `ℤ`. -/
def evenConfig (e : (nnGraph ℤ).edgeSet) : Bool :=
  decide (Even (Classical.choose (exists_edge_eq e)))

/-- The odd edges `{2k + 1, 2k + 2}` of `ℤ`. -/
def oddConfig (e : (nnGraph ℤ).edgeSet) : Bool :=
  decide (Odd (Classical.choose (exists_edge_eq e)))

@[simp]
theorem evenConfig_edge (a : ℤ) : evenConfig (edge a) = decide (Even a) := by
  rw [evenConfig, choose_exists_edge_eq (by decide)]

@[simp]
theorem oddConfig_edge (a : ℤ) : oddConfig (edge a) = decide (Odd a) := by
  rw [oddConfig, choose_exists_edge_eq (by decide)]

theorem evenConfig_ne_oddConfig : evenConfig ≠ oddConfig := fun h => by
  simpa using congrFun h (edge 0)

theorem isDimerConfiguration_evenConfig : (nnGraph ℤ).IsDimerConfiguration evenConfig :=
  (isDimerConfiguration_nnGraph_iff (by decide)).2 fun a => by simp [← Int.not_even_iff_odd]

theorem isDimerConfiguration_oddConfig : (nnGraph ℤ).IsDimerConfiguration oddConfig :=
  (isDimerConfiguration_nnGraph_iff (by decide)).2 fun a => by simp [← Int.not_even_iff_odd]

/-- **The two dimer configurations of the line**: the even and the odd edges. -/
theorem setOf_isDimerConfiguration_int :
    {ω | (nnGraph ℤ).IsDimerConfiguration ω} = {evenConfig, oddConfig} := by
  ext ω
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun hω => ?_, by
    rintro (rfl | rfl)
    exacts [isDimerConfiguration_evenConfig, isDimerConfiguration_oddConfig]⟩
  have key (a : ℤ) : ω (edge a) = (ω (edge 0) ^^ decide (Odd a)) := by
    simpa using apply_edge_intCast ((isDimerConfiguration_nnGraph_iff (by decide)).1 hω) a
  cases h0 : ω (edge 0)
  · refine Or.inr (funext fun e => ?_)
    obtain ⟨a, rfl⟩ := exists_edge_eq e
    simp [key a, h0]
  · refine Or.inl (funext fun e => ?_)
    obtain ⟨a, rfl⟩ := exists_edge_eq e
    simp [key a, h0, ← Int.not_odd_iff_even]

instance : (nnGraph ℤ).LocallyFinite := fun v =>
  ((toFinite {v - 1, v + 1}).subset fun w hw => by
    rcases (nnGraph_adj.1 hw).2 with rfl | rfl <;> simp).fintype

/-- Translation by `2` as an automorphism of the line. -/
def shiftTwo : nnGraph ℤ ≃g nnGraph ℤ where
  toEquiv := Equiv.addRight 2
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_addRight, nnGraph_adj]
    omega

/-- The group `2ℤ`, written multiplicatively as `Multiplicative ℤ` with `ofAdd 1` acting as
translation by `2`, acting on the edges of the line. -/
instance instMulActionMultiplicativeIntEdgeSetNNGraph :
    MulAction (Multiplicative ℤ) (nnGraph ℤ).edgeSet :=
  MulAction.compHom _ (zpowersHom _ shiftTwo)

/-- The subshift of dimer configurations of the line, for `2ℤ` acting by translations. -/
def dimerSubshiftInt : Subshift (Multiplicative ℤ) (nnGraph ℤ).edgeSet Bool :=
  (nnGraph ℤ).dimerSubshift (Multiplicative ℤ)
    (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo))

/-- The subshift of dimer configurations of the line has exactly two points. -/
theorem coe_dimerSubshiftInt :
    (dimerSubshiftInt : Set ((nnGraph ℤ).edgeSet → Bool)) = {evenConfig, oddConfig} := by
  rw [← setOf_isDimerConfiguration_int]
  ext ω
  simp only [dimerSubshiftInt, SetLike.mem_coe, mem_dimerSubshift, mem_ofPred_eq]

/-- At `F = ∅` the completion set of the even edges is the singleton of it. -/
theorem dimerCompletionSet_empty_evenConfig :
    (nnGraph ℤ).dimerCompletionSet ∅ evenConfig = {evenConfig} :=
  dimerCompletionSet_empty isDimerConfiguration_evenConfig

/-- At `F = ∅` the completion set of the odd edges is the singleton of it. -/
theorem dimerCompletionSet_empty_oddConfig :
    (nnGraph ℤ).dimerCompletionSet ∅ oddConfig = {oddConfig} :=
  dimerCompletionSet_empty isDimerConfiguration_oddConfig

/-- At `F = ∅` the completion sets of the two dimer configurations of the line are different. -/
theorem dimerCompletionSet_empty_evenConfig_ne_oddConfig :
    (nnGraph ℤ).dimerCompletionSet ∅ evenConfig ≠ (nnGraph ℤ).dimerCompletionSet ∅ oddConfig := by
  rw [dimerCompletionSet_empty_evenConfig, dimerCompletionSet_empty_oddConfig]
  exact fun h => evenConfig_ne_oddConfig (singleton_eq_singleton_iff.1 h)

/-- At `F = ∅` the restriction sets of the two dimer configurations of the line are both the
singleton of the empty configuration. -/
theorem image_restrict_dimerCompletionSet_empty_eq :
    (∅ : Finset (nnGraph ℤ).edgeSet).restrict '' (nnGraph ℤ).dimerCompletionSet ∅ evenConfig =
        {isEmptyElim} ∧
      (∅ : Finset (nnGraph ℤ).edgeSet).restrict ''
        (nnGraph ℤ).dimerCompletionSet ∅ oddConfig = {isEmptyElim} := by
  rw [dimerCompletionSet_empty_evenConfig, dimerCompletionSet_empty_oddConfig, image_singleton,
    image_singleton]
  exact ⟨congrArg _ (funext fun e => isEmptyElim e), congrArg _ (funext fun e => isEmptyElim e)⟩

/-! ### Local finiteness is needed for closedness -/

/-- The vertices `c`, `d`, `x_n`, `y_n` of the comb graph. -/
inductive CombVertex
  | c
  | d
  | x (n : ℕ)
  | y (n : ℕ)
  deriving DecidableEq

open CombVertex

/-- The edges `c x_n`, `d y_n` and `x_n y_n` of the comb graph, in one direction. -/
def combRel : CombVertex → CombVertex → Prop
  | c, x _ => True
  | d, y _ => True
  | x n, y m => n = m
  | _, _ => False

/-- The comb graph, with edges `c x_n`, `d y_n`, `x_n y_n`. The vertices `c` and `d` have
infinite degree. -/
def combGraph : SimpleGraph CombVertex :=
  SimpleGraph.fromRel combRel

/-- The edge set of the perfect matching `M_k = {c x_k, d y_k} ∪ {x_n y_n : n ≠ k}`. -/
def combMatchingSet (k : ℕ) : Set (Sym2 CombVertex) :=
  {s(c, x k), s(d, y k)} ∪ {e | ∃ n ≠ k, e = s(x n, y n)}

/-- The edge set of the rungs `{x_n y_n}`. -/
def combRungsSet : Set (Sym2 CombVertex) :=
  {e | ∃ n, e = s(x n, y n)}

open scoped Classical in
/-- The configuration of the perfect matching `M_k`. -/
def combMatching (k : ℕ) (e : combGraph.edgeSet) : Bool :=
  decide ((e : Sym2 CombVertex) ∈ combMatchingSet k)

open scoped Classical in
/-- The configuration of the rungs. -/
def combRungs (e : combGraph.edgeSet) : Bool :=
  decide ((e : Sym2 CombVertex) ∈ combRungsSet)

/-- The partner of a vertex in `M_k`. -/
private def combPartner (k : ℕ) : CombVertex → CombVertex
  | c => x k
  | d => y k
  | x n => if n = k then c else y n
  | y n => if n = k then d else x n

private theorem combGraph_adj_and_mem_iff (k : ℕ) (v w : CombVertex) :
    (combGraph.Adj v w ∧ s(v, w) ∈ combMatchingSet k) ↔ w = combPartner k v := by
  cases v <;> cases w <;>
    simp [combGraph, combRel, combMatchingSet, combPartner, fromRel_adj] <;>
    grind

/-- Each `M_k` is a perfect matching. -/
theorem isDimerConfiguration_combMatching (k : ℕ) :
    combGraph.IsDimerConfiguration (combMatching k) := by
  rw [← isPerfectMatching_dimerSubgraph_iff, Subgraph.isPerfectMatching_iff]
  intro v
  refine ⟨combPartner k v, ?_, fun w hw => ?_⟩
  · have := (combGraph_adj_and_mem_iff k v (combPartner k v)).2 rfl
    exact dimerSubgraph_adj.2 ⟨this.1, by simpa [combMatching] using this.2⟩
  · obtain ⟨h, hw⟩ := dimerSubgraph_adj.1 hw
    exact (combGraph_adj_and_mem_iff k v w).1 ⟨h, by simpa [combMatching] using hw⟩

/-- The rungs leave `c` uncovered. -/
theorem not_isDimerConfiguration_combRungs : ¬ combGraph.IsDimerConfiguration combRungs := by
  intro h
  obtain ⟨⟨e, he⟩, ⟨hω, hc⟩, -⟩ := isDimerConfiguration_iff.1 h c
  have hω' : e ∈ combRungsSet := by simpa [combRungs] using hω
  obtain ⟨n, rfl⟩ := hω'
  simp at hc

/-- The index `n` of `x_n` and `y_n`, and `0` for `c` and `d`. -/
private def combIndex : CombVertex → ℕ
  | c => 0
  | d => 0
  | x n => n
  | y n => n

/-- `M_k` converges coordinatewise to the rungs. -/
theorem tendsto_combMatching : Tendsto combMatching atTop (𝓝 combRungs) := by
  refine tendsto_pi_nhds.2 fun ⟨e, he⟩ => ?_
  rw [nhds_discrete, tendsto_pure]
  induction e using Sym2.ind with
  | _ u v =>
    filter_upwards [eventually_gt_atTop (combIndex u + combIndex v)] with k hk
    simp only [combMatching, combRungs, decide_eq_decide]
    cases u <;> cases v <;>
      simp [combMatchingSet, combRungsSet, combIndex] at hk ⊢ <;> grind

/-- **Local finiteness is needed for closedness**: the dimer configurations of the comb graph do
not form a closed set. -/
theorem not_isClosed_setOf_isDimerConfiguration_combGraph :
    ¬ IsClosed {ω | combGraph.IsDimerConfiguration ω} := fun h =>
  not_isDimerConfiguration_combRungs <|
    h.mem_of_tendsto tendsto_combMatching (Eventually.of_forall isDimerConfiguration_combMatching)

/-! ### The hexagon -/

/-- `1 < 6`, so that `ZMod 6` is nontrivial. -/
local instance fact_one_lt_six : Fact (1 < 6) :=
  ⟨by decide⟩

/-- The configuration of the hexagon `ZMod 6` taking the value `b` on the edges `{a, a + 1}`
with `a` even and `!b` on the others. -/
def hexConfig (b : Bool) (e : (nnGraph (ZMod 6)).edgeSet) : Bool :=
  b ^^ decide ((Classical.choose (exists_edge_eq e)).val % 2 = 1)

private theorem two_ne_zero_zmod_six : (2 : ZMod 6) ≠ 0 := by decide

@[simp]
theorem hexConfig_edge (b : Bool) (a : ZMod 6) :
    hexConfig b (edge a) = (b ^^ decide (a.val % 2 = 1)) := by
  rw [hexConfig, choose_exists_edge_eq two_ne_zero_zmod_six]

theorem hexConfig_injective : Injective hexConfig := fun b b' h => by
  simpa using congrFun h (edge 0)

/-- **The two dimer configurations of the hexagon**, the two lozenge tilings of the unit
hexagon. -/
theorem setOf_isDimerConfiguration_zmod_six :
    {ω | (nnGraph (ZMod 6)).IsDimerConfiguration ω} = {hexConfig true, hexConfig false} := by
  ext ω
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff,
    isDimerConfiguration_nnGraph_iff two_ne_zero_zmod_six]
  constructor
  · intro h
    have key' (a : ZMod 6) : ω (edge a) = hexConfig (ω (edge 0)) (edge a) := by
      simpa only [hexConfig_edge, Int.cast_natCast, ZMod.natCast_zmod_val, Int.odd_natCast,
        Nat.odd_iff] using apply_edge_intCast h (a.val : ℤ)
    cases h0 : ω (edge 0)
    · refine Or.inr (funext fun e => ?_)
      obtain ⟨a, rfl⟩ := exists_edge_eq e
      rw [key', h0]
    · refine Or.inl (funext fun e => ?_)
      obtain ⟨a, rfl⟩ := exists_edge_eq e
      rw [key', h0]
  · have hpar : ∀ a : ZMod 6, decide ((a + 1).val % 2 = 1) = !decide (a.val % 2 = 1) := by
      decide
    rintro (rfl | rfl) a <;> simp only [hexConfig_edge, hpar] <;> simp

end TauCeti.Examples.DimerConfiguration
