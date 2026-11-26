/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.GroupTheory.Perm.ParityRetract
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.SimpleGraph.OddTriple
import TauCeti.Combinatorics.SimpleGraph.Staircase
import TauCeti.Data.Fin.Basic
import TauCeti.Order.Hom.PowersetCard

/-!
# Binary and swap-valued 1-cochains on the complete two-complex

Any group element `g : G` satisfying `g * g = 1` equals its own inverse, so assigning `g` to the
edges of a `SimpleGraph` `Γ` on `V` (where `X` also has an edge) and `1` elsewhere defines a
`G`-valued 1-cochain `Cochain.ofSimpleGraph X Γ hg`. Conversely, every cochain `α : Cochain X G`
has a support graph `Cochain.supportGraph α` whose edges are the pairs with `α u v ≠ 1`.

On the complete two-complex `complete V`:

* the holonomy of `Cochain.ofSimpleGraph (complete V) Γ hg` around `(u, v, w)` is `g` when
  `{u, v, w} ∈ Γ.oddTriangleFinset` and `1` otherwise, so its triangle defect under any `GroupNorm`
  `ℓ` is `ℓ g * #Γ.oddTriangleFinset`;
* the `{1, g}`-valued gauge `fun v => if v ∈ S then g else 1` transforms the underlying graph by
  symmetric difference with the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ`, giving cost
  `ℓ g * #(Γ.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset)`;
* when `G = Equiv.Perm α` equipped with `Equiv.Perm.movedNorm α` and `ht : t.IsSwap`, retracting
  an arbitrary permutation gauge along `Equiv.Perm.parityRetract ht` does not increase cost, so
  the gauge distance equals `2 * #Γ.edgeFinset` if and only if `Γ.IsCutMinimal`, and any
  cut-minimal graph with at least one edge bounds `h1 (complete V) (Equiv.Perm.movedNorm α)` from
  above by `#Γ.oddTriangleFinset / #Γ.edgeFinset`
  (`TauCeti.h1_complete_movedNorm_le_div_of_isCutMinimal`);
* for `G = Equiv.Perm (Fin 2)`, `Cochain.supportGraphEquiv` identifies `Cochain (complete V)
  (Equiv.Perm (Fin 2))` with `SimpleGraph V`, identifying coboundaries with complete-graph cuts
  (`Cochain.isCoboundary_fin_two_complete_iff`) and translating `holonomy`, `cost`, `defect`, and
  `gaugeDist` of every binary cochain into odd-triangle membership, cut symmetric differences,
  odd-triangle counts, and cut-minimality.

Combining this bridge with Kozlov's cut-minimal staircase graphs `SimpleGraph.staircase` and the
star lower bound proves Kozlov's theorem (`TauCeti.h1_complete_movedNorm_fin_two`): whenever
`3 ≤ Fintype.card V` and `Fintype.card V` is not a power of two,
`h1 (complete V) (Equiv.Perm.movedNorm (Fin 2)) = Fintype.card V / 3` (and in normalized form
`Fintype.card V / (Fintype.card V - 2)`). Because the parity retraction applies in every nontrivial
symmetric group, the same witness simultaneously establishes Beasley's non-power-of-two evaluation
`h1 (complete V) (Equiv.Perm.movedNorm α) = Fintype.card V / 3` for every finite nontrivial `α`,
and hence `h1Sym (complete V) = Fintype.card V / 3` whenever `Fintype.card V ≥ 3` is not a power of
two.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Sections 2–3 and
  Theorem 3.1.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.23245792, version 7, Corollary 7.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2 and §3.
-/

public section

open scoped symmDiff
open Finset

namespace TauCeti

open TwoComplex

namespace Cochain

/-! ### Cochains supported on simple graphs and support graphs of cochains -/

section SimpleGraphBridge

variable {V W G H : Type*} [Group G] [Group H] {X : TwoComplex V}

/-- The `G`-valued 1-cochain on `X` supported on a simple graph `Γ`, taking value `g` on edges of
`X` that are edges of `Γ` and `1` elsewhere, for an element `g` satisfying `g * g = 1`. -/
noncomputable def ofSimpleGraph (X : TwoComplex V) (Γ : SimpleGraph V) {g : G}
    (hg : g * g = 1) : Cochain X G := by
  classical
  exact ofFn X (fun u v => if Γ.Adj u v then g else 1) fun u v _ => by
    rw [Γ.adj_comm v u]
    split_ifs <;> simp [inv_eq_of_mul_eq_one_left hg]

/-- Evaluating `ofSimpleGraph` on an edge of `X` with respect to a decidable adjacency relation on
`Γ`. -/
theorem ofSimpleGraph_apply (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {g : G} (hg : g * g = 1)
    {u v : V} (hX : X.Adj u v) :
    ofSimpleGraph X Γ hg u v = if Γ.Adj u v then g else 1 := by
  classical
  rw [ofSimpleGraph, ofFn_apply_of_adj _ hX]
  split_ifs <;> rfl

@[simp, grind =]
theorem ofSimpleGraph_apply_of_adj {Γ : SimpleGraph V} {g : G} (hg : g * g = 1) {u v : V}
    (hX : X.Adj u v) (hΓ : Γ.Adj u v) :
    ofSimpleGraph X Γ hg u v = g := by
  classical
  simp [ofSimpleGraph_apply Γ hg hX, hΓ]

@[simp, grind =]
theorem ofSimpleGraph_apply_of_not_adj_right {Γ : SimpleGraph V} {g : G} (hg : g * g = 1) {u v : V}
    (hΓ : ¬ Γ.Adj u v) :
    ofSimpleGraph X Γ hg u v = 1 := by
  classical
  by_cases hX : X.Adj u v
  · simp [ofSimpleGraph_apply Γ hg hX, hΓ]
  · exact apply_eq_one_of_not_adj _ hX

/-- On `complete V`, `ofSimpleGraph` evaluates to `if Γ.Adj u v then g else 1` on all pairs of
vertices, including `u = v`. -/
@[simp, grind =]
theorem ofSimpleGraph_apply_complete [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {g : G}
    (hg : g * g = 1) (u v : V) :
    ofSimpleGraph (complete V) Γ hg u v = if Γ.Adj u v then g else 1 := by
  rcases eq_or_ne u v with rfl | huv
  · simp
  · exact ofSimpleGraph_apply Γ hg ((adj_complete u v).mpr huv)

@[simp]
theorem ofSimpleGraph_bot {g : G} (hg : g * g = 1) : ofSimpleGraph X ⊥ hg = 1 := by
  ext u v _
  simp

@[simp]
theorem ofSimpleGraph_one (Γ : SimpleGraph V) : ofSimpleGraph X Γ (mul_one (1 : G)) = 1 := by
  classical
  ext u v huv
  simp [ofSimpleGraph_apply Γ (mul_one (1 : G)) huv]

/-- Pushing `ofSimpleGraph` forward along a group homomorphism replaces `g` by `φ g`. -/
@[simp]
theorem map_ofSimpleGraph (φ : G →* H) (Γ : SimpleGraph V) {g : G} (hg : g * g = 1) :
    (ofSimpleGraph X Γ hg).map φ =
      ofSimpleGraph X Γ (g := φ g) (by rw [← map_mul, hg, _root_.map_one]) := by
  classical
  refine Cochain.ext fun u v huv => ?_
  simp only [map_apply, ofSimpleGraph_apply _ _ huv]
  split_ifs <;> simp

/-- Relabelling `ofSimpleGraph` on `complete V` along a graph isomorphism `Γ ≃g Γ'` gives
`ofSimpleGraph` of `Γ'`. -/
theorem relabelComplete_ofSimpleGraph [Fintype V] [Fintype W] {Γ : SimpleGraph V}
    {Γ' : SimpleGraph W} (f : Γ ≃g Γ') {g : G} (hg : g * g = 1) :
    (ofSimpleGraph (complete V) Γ hg).relabelComplete f.toEquiv =
      ofSimpleGraph (complete W) Γ' hg := by
  classical
  refine Cochain.ext fun u v _ => ?_
  have hadj : Γ.Adj (f.toEquiv.symm u) (f.toEquiv.symm v) ↔ Γ'.Adj u v := f.symm.map_adj_iff
  simp only [relabelComplete_apply, ofSimpleGraph_apply_complete, hadj]

/-- The simple graph of vertex pairs on which a cochain `α` takes a non-identity value. -/
def supportGraph (α : Cochain X G) : SimpleGraph V where
  Adj u v := α u v ≠ 1
  symm := ⟨fun _ _ h => by rwa [α.apply_swap, ne_eq, inv_eq_one]⟩
  loopless := ⟨fun u h => h (α.apply_self u)⟩

@[simp, grind =]
theorem supportGraph_adj (α : Cochain X G) (u v : V) :
    α.supportGraph.Adj u v ↔ α u v ≠ 1 :=
  (Iff.rfl)

/-- Decidable equality in the coefficient group makes adjacency in `Cochain.supportGraph`
decidable. -/
instance instDecidableRelSupportGraphAdj [DecidableEq G] (α : Cochain X G) :
    DecidableRel α.supportGraph.Adj :=
  fun u v => decidable_of_iff' (α u v ≠ 1) (α.supportGraph_adj u v)

@[simp]
theorem supportGraph_one : (1 : Cochain X G).supportGraph = ⊥ := by
  ext u v
  simp

@[simp]
theorem supportGraph_eq_bot_iff (α : Cochain X G) : α.supportGraph = ⊥ ↔ α = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, supportGraph_one]⟩
  ext u v _
  simpa [supportGraph_adj] using congrArg (fun Γ => Γ.Adj u v) h

@[simp]
theorem supportGraph_relabel (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).supportGraph = α.supportGraph.comap e.symm := by
  ext u v
  simp

@[simp]
theorem supportGraph_relabelComplete [Fintype V] [Fintype W] (α : Cochain (complete V) G)
    (e : V ≃ W) :
    (α.relabelComplete e).supportGraph = α.supportGraph.comap e.symm := by
  ext u v
  simp

/-- On `complete V`, the support graph of `ofSimpleGraph` for a non-identity involution `g ≠ 1`
recovers `Γ`. -/
@[simp]
theorem supportGraph_ofSimpleGraph_complete [Fintype V] (Γ : SimpleGraph V) {g : G}
    (hg : g * g = 1) (hg1 : g ≠ 1) :
    (ofSimpleGraph (complete V) Γ hg).supportGraph = Γ := by
  classical
  ext u v
  simp only [supportGraph_adj, ofSimpleGraph_apply_complete]
  split_ifs with h <;> simp [h, hg1]

/-- For a non-identity involution `g ≠ 1`, `ofSimpleGraph (complete V) · hg` is injective. -/
theorem ofSimpleGraph_complete_injective [Fintype V] {g : G} (hg : g * g = 1) (hg1 : g ≠ 1) :
    Function.Injective fun Γ : SimpleGraph V => ofSimpleGraph (complete V) Γ hg :=
  Function.LeftInverse.injective fun Γ => supportGraph_ofSimpleGraph_complete Γ hg hg1

@[simp]
theorem ofSimpleGraph_complete_inj [Fintype V] {Γ₁ Γ₂ : SimpleGraph V} {g : G} (hg : g * g = 1)
    (hg1 : g ≠ 1) :
    ofSimpleGraph (complete V) Γ₁ hg = ofSimpleGraph (complete V) Γ₂ hg ↔ Γ₁ = Γ₂ :=
  (ofSimpleGraph_complete_injective hg hg1).eq_iff

@[simp]
theorem ofSimpleGraph_complete_eq_one_iff [Fintype V] {Γ : SimpleGraph V} {g : G}
    (hg : g * g = 1) (hg1 : g ≠ 1) :
    ofSimpleGraph (complete V) Γ hg = 1 ↔ Γ = ⊥ := by
  rw [← ofSimpleGraph_bot (X := complete V) hg, ofSimpleGraph_complete_inj hg hg1]

/-! ### Holonomy, defect, and cut-gauge action on the complete two-complex -/

/-- On `complete V`, the holonomy of `ofSimpleGraph` around `(u, v, w)` equals `g` when
`{u, v, w} ∈ Γ.oddTriangleFinset` and `1` otherwise (including degenerate triples). -/
@[simp]
theorem holonomy_ofSimpleGraph_complete [Fintype V] [DecidableEq V] (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] {g : G} (hg : g * g = 1) (u v w : V) :
    (ofSimpleGraph (complete V) Γ hg).holonomy u v w =
      if ({u, v, w} : Finset V) ∈ Γ.oddTriangleFinset then g else 1 := by
  have hodd : ({u, v, w} : Finset V) ∈ Γ.oddTriangleFinset ↔
      Xor (Γ.Adj u v) (Xor (Γ.Adj u w) (Γ.Adj v w)) := by
    rw [SimpleGraph.mem_oddTriangleFinset, SimpleGraph.filter_edgeFinset_toFinset_subset,
      ← SimpleGraph.mem_oddTripleFinset, SimpleGraph.triple_mem_oddTripleFinset_iff]
  simp only [holonomy_def, ofSimpleGraph_apply_complete, hodd, Γ.adj_comm w u]
  by_cases h₁ : Γ.Adj u v <;> by_cases h₂ : Γ.Adj v w <;> by_cases h₃ : Γ.Adj u w <;>
    simp [h₁, h₂, h₃, xor_def, hg]

/-- On `complete V`, the triangle defect of `ofSimpleGraph` under any group norm `ℓ` is `ℓ g` times
the number of odd triangles of `Γ`. -/
@[simp]
theorem defect_ofSimpleGraph_complete [Fintype V] [LinearOrder V] (ℓ : GroupNorm G)
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {g : G} (hg : g * g = 1) :
    (ofSimpleGraph (complete V) Γ hg).defect ℓ = ℓ g * (#Γ.oddTriangleFinset : ℝ) := by
  rw [defect_complete]
  have hsum :
      (∑ p ∈ univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2),
          ℓ ((ofSimpleGraph (complete V) Γ hg).holonomy p.1 p.2.1 p.2.2)) =
        ∑ _ ∈ univ.filter (fun p : V × V × V =>
            (p.1 < p.2.1 ∧ p.2.1 < p.2.2) ∧
              ({p.1, p.2.1, p.2.2} : Finset V) ∈ Γ.oddTriangleFinset),
          ℓ g := by
    conv_rhs => rw [← filter_filter, sum_filter]
    refine sum_congr rfl fun _ _ => ?_
    rw [holonomy_ofSimpleGraph_complete]
    split_ifs <;> simp
  have hcard :
      #{p : V × V × V | (p.1 < p.2.1 ∧ p.2.1 < p.2.2) ∧
          ({p.1, p.2.1, p.2.2} : Finset V) ∈ Γ.oddTriangleFinset} =
        #Γ.oddTriangleFinset := by
    refine card_bij (fun p _ => ({p.1, p.2.1, p.2.2} : Finset V))
      (fun p hp => (mem_filter.mp hp).2.2) ?_ ?_
    · rintro ⟨u₁, v₁, w₁⟩ hp₁ ⟨u₂, v₂, w₂⟩ hp₂ htri
      obtain ⟨⟨huv₁, hvw₁⟩, _⟩ := (mem_filter.mp hp₁).2
      obtain ⟨⟨huv₂, hvw₂⟩, _⟩ := (mem_filter.mp hp₂).2
      exact congrArg Subtype.val
        (Set.powersetCard.ofLtTriple.injective
          (a₁ := ⟨(u₁, v₁, w₁), huv₁, hvw₁⟩) (a₂ := ⟨(u₂, v₂, w₂), huv₂, hvw₂⟩)
          (Subtype.ext <| (Set.powersetCard.val_ofLtTriple ⟨(u₁, v₁, w₁), huv₁, hvw₁⟩).trans
            (htri.trans (Set.powersetCard.val_ofLtTriple ⟨(u₂, v₂, w₂), huv₂, hvw₂⟩).symm)))
    · intro s hs
      obtain ⟨u, v, w, huv, hvw, hval⟩ :=
        Set.powersetCard.exists_lt_lt_val_eq ⟨s, (SimpleGraph.mem_oddTriangleFinset.mp hs).1⟩
      exact ⟨(u, v, w), mem_filter.mpr ⟨mem_univ _, ⟨huv, hvw⟩, hval ▸ hs⟩, hval.symm⟩
  rw [hsum, sum_const, hcard, nsmul_eq_mul, mul_comm]

/-- Acting on `ofSimpleGraph (complete V) Γ hg` by the `{1, g}`-valued gauge supported on `S`
replaces `Γ` by its symmetric difference with the complete-graph cut `(S, Sᶜ)`. -/
theorem smul_ite_ofSimpleGraph_complete [Fintype V] (Γ : SimpleGraph V) (S : Set V)
    [DecidablePred (· ∈ S)] {g : G} (hg : g * g = 1) :
    (fun v => if v ∈ S then g else 1) • ofSimpleGraph (complete V) Γ hg =
      ofSimpleGraph (complete V) (Γ ∆ (⊤ : SimpleGraph V).between S Sᶜ) hg := by
  classical
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg
  ext u v huv
  have hne : u ≠ v := (adj_complete u v).mp huv
  simp only [smul_apply_complete, ofSimpleGraph_apply_complete, symmDiff_def,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, SimpleGraph.between_adj, SimpleGraph.top_adj,
    Set.mem_compl_iff]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hΓ : Γ.Adj u v <;>
    simp [hu, hv, hΓ, hne, hinv, hg]

/-- On `complete V`, the cost of the trivial gauge `1` against `ofSimpleGraph` is `ℓ g` times the
edge count of `Γ`. -/
@[simp]
theorem cost_ofSimpleGraph_complete_one [Fintype V] [LinearOrder V] (ℓ : GroupNorm G)
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {g : G} (hg : g * g = 1) :
    (ofSimpleGraph (complete V) Γ hg).cost ℓ 1 = ℓ g * (#Γ.edgeFinset : ℝ) := by
  rw [cost_complete]
  have hsum :
      (∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
          ℓ (((1 : V → G) p.1)⁻¹ * ofSimpleGraph (complete V) Γ hg p.1 p.2 *
            (1 : V → G) p.2)) =
        ∑ _ ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ Γ.Adj p.1 p.2), ℓ g := by
    conv_rhs => rw [← filter_filter, sum_filter]
    refine sum_congr rfl fun _ _ => ?_
    simp only [Pi.one_apply, inv_one, one_mul, mul_one, ofSimpleGraph_apply_complete]
    split_ifs <;> simp
  have hcard : #{p : V × V | p.1 < p.2 ∧ Γ.Adj p.1 p.2} = #Γ.edgeFinset := by
    refine card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · rintro ⟨u, v⟩ hp
      exact Γ.mem_edgeFinset.mpr (Γ.mem_edgeSet.mpr (mem_filter.mp hp).2.2)
    · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ h
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact (lt_asymm (mem_filter.mp hp₁).2.1 (mem_filter.mp hp₂).2.1).elim
    · intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : Γ.Adj u v := Γ.mem_edgeSet.mp (Γ.mem_edgeFinset.mp he)
        rcases lt_trichotomy u v with hlt | rfl | hgt
        · exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, hlt, hadj⟩, rfl⟩
        · exact (hadj.ne rfl).elim
        · exact ⟨(v, u), mem_filter.mpr ⟨mem_univ _, hgt, hadj.symm⟩, Sym2.eq_swap⟩
  rw [hsum, sum_const, hcard, nsmul_eq_mul, mul_comm]

/-- On `complete V`, the cost of the `{1, g}`-valued gauge supported on `S` equals `ℓ g` times the
cardinality of the symmetric difference of `Γ.edgeFinset` with the cut `(S, Sᶜ)`. -/
theorem cost_ofSimpleGraph_complete_ite [Fintype V] [LinearOrder V] (ℓ : GroupNorm G)
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (S : Set V) [DecidablePred (· ∈ S)]
    {g : G} (hg : g * g = 1) :
    (ofSimpleGraph (complete V) Γ hg).cost ℓ (fun v => if v ∈ S then g else 1) =
      ℓ g * (#(Γ.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by
  classical
  let β : V → G := fun v => if v ∈ S then g else 1
  have hcost : (ofSimpleGraph (complete V) Γ hg).cost ℓ β =
      (β • ofSimpleGraph (complete V) Γ hg).cost ℓ 1 := by
    rw [cost_smul, mul_one]
  have hedge :
      (Γ ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset =
        Γ.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
    rw [SimpleGraph.edgeFinset_inj.mpr (symmDiff_def _ _), Finset.symmDiff_def,
      SimpleGraph.edgeFinset_sup, SimpleGraph.edgeFinset_sdiff, SimpleGraph.edgeFinset_sdiff]
  rw [hcost, smul_ite_ofSimpleGraph_complete, cost_ofSimpleGraph_complete_one, hedge]

end SimpleGraphBridge

/-! ### Transposition-valued cochains and parity retraction -/

section SwapCochains

variable {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]

/-- For a transposition `t` in `Equiv.Perm α`, the cost of any permutation gauge `β` against
`ofSimpleGraph (complete V) Γ ht.mul_self` under `movedNorm α` is at least twice the edge count of
`Γ` switched across the odd-sign cut `{v | (β v).sign = -1}` (Beasley, Corollary 7). -/
theorem two_mul_card_symmDiff_le_cost_ofSimpleGraph_isSwap (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) (β : V → Equiv.Perm α) :
    2 * (#(Γ.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | (β v).sign = -1} {v | (β v).sign = -1}ᶜ).edgeFinset) :
        ℝ) ≤
      (ofSimpleGraph (complete V) Γ ht.mul_self).cost (Equiv.Perm.movedNorm α) β := by
  have hret : (Equiv.Perm.parityRetract ht ∘ β) =
      fun v => if v ∈ {v : V | (β v).sign = -1} then t else 1 := by
    funext v
    rcases Int.units_eq_one_or (β v).sign with h | h <;> simp [h]
  calc
    2 * (#(Γ.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | (β v).sign = -1} {v | (β v).sign = -1}ᶜ).edgeFinset) :
        ℝ)
        = (ofSimpleGraph (complete V) Γ ht.mul_self).cost (Equiv.Perm.movedNorm α)
            (Equiv.Perm.parityRetract ht ∘ β) := by
          rw [hret, cost_ofSimpleGraph_complete_ite, ht.movedNorm]
    _ = ((ofSimpleGraph (complete V) Γ ht.mul_self).map (Equiv.Perm.parityRetract ht)).cost
          (Equiv.Perm.movedNorm α) (Equiv.Perm.parityRetract ht ∘ β) := by
          simp
    _ ≤ (ofSimpleGraph (complete V) Γ ht.mul_self).cost (Equiv.Perm.movedNorm α) β :=
          (ofSimpleGraph (complete V) Γ ht.mul_self).cost_map_le
            (Equiv.Perm.movedNorm_parityRetract_le ht) β

/-- The gauge distance of a transposition-valued graph cochain on `complete V` under `movedNorm α`
equals the minimum over cuts `s : Finset V` of `2 * #(Γ.edgeFinset ∆ cut s)`. -/
theorem gaugeDist_ofSimpleGraph_isSwap_eq_iInf (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    {t : Equiv.Perm α} (ht : t.IsSwap) :
    (ofSimpleGraph (complete V) Γ ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) =
      ⨅ s : Finset V,
        2 * (#(Γ.edgeFinset ∆
          ((⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset) : ℝ) := by
  have hbdd : BddBelow (Set.range fun s : Finset V =>
      2 * (#(Γ.edgeFinset ∆
        ((⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset) : ℝ)) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; positivity⟩
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun s => ?_
    exact ((ofSimpleGraph (complete V) Γ ht.mul_self).gaugeDist_le_cost
      (Equiv.Perm.movedNorm α) (fun v => if v ∈ (s : Set V) then t else 1)).trans_eq
      (by rw [cost_ofSimpleGraph_complete_ite, ht.movedNorm])
  · rw [le_gaugeDist_iff]
    intro β
    let s : Finset V := univ.filter fun v => (β v).sign = -1
    have hcut_eq :
        ((⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset =
          ((⊤ : SimpleGraph V).between {v | (β v).sign = -1}
            {v | (β v).sign = -1}ᶜ).edgeFinset := by
      ext e
      simp [SimpleGraph.mem_edgeFinset, s]
    exact (ciInf_le hbdd s).trans
      (by rw [hcut_eq]; exact two_mul_card_symmDiff_le_cost_ofSimpleGraph_isSwap Γ ht β)

/-- A transposition-valued graph cochain on `complete V` has gauge distance `2 * #Γ.edgeFinset`
under `movedNorm α` if and only if `Γ` is cut-minimal (Kozlov, Section 2; Beasley, Corollary 7). -/
theorem gaugeDist_ofSimpleGraph_isSwap_eq_iff_isCutMinimal (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (ofSimpleGraph (complete V) Γ ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) =
      2 * (#Γ.edgeFinset : ℝ) ↔ Γ.IsCutMinimal := by
  rw [SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff]
  constructor
  · intro hdist S _
    have hle :
        2 * (#Γ.edgeFinset : ℝ) ≤
          2 * (#(Γ.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by
      rw [← hdist, ← ht.movedNorm, ← cost_ofSimpleGraph_complete_ite]
      exact gaugeDist_le_cost _ _ _
    have hnat : (#Γ.edgeFinset : ℝ) ≤
        (#(Γ.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by linarith
    exact_mod_cast hnat
  · intro hcut
    refine le_antisymm ?_ ?_
    · exact ((ofSimpleGraph (complete V) Γ ht.mul_self).gaugeDist_le_cost
        (Equiv.Perm.movedNorm α) 1).trans_eq
        (by rw [cost_ofSimpleGraph_complete_one, ht.movedNorm])
    · rw [le_gaugeDist_iff]
      intro β
      have hcard : (#Γ.edgeFinset : ℝ) ≤
          (#(Γ.edgeFinset ∆
            ((⊤ : SimpleGraph V).between {v | (β v).sign = -1}
              {v | (β v).sign = -1}ᶜ).edgeFinset) : ℝ) := by
        exact_mod_cast hcut {v | (β v).sign = -1}
      exact (mul_le_mul_of_nonneg_left hcard (by norm_num)).trans
        (two_mul_card_symmDiff_le_cost_ofSimpleGraph_isSwap Γ ht β)

end SwapCochains

/-! ### Full dictionary for `Equiv.Perm (Fin 2)` cochains -/

section BinaryCochains

variable {V : Type*}

/-- Every `Equiv.Perm (Fin 2)`-valued 1-cochain is recovered from its support graph via the unique
transposition `Equiv.swap 0 1`. -/
@[simp]
theorem ofSimpleGraph_supportGraph {X : TwoComplex V} (α : Cochain X (Equiv.Perm (Fin 2))) :
    ofSimpleGraph X α.supportGraph (Equiv.swap_mul_self 0 1) = α := by
  have hne : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
  refine Cochain.ext fun u v huv => ?_
  rw [ofSimpleGraph_apply α.supportGraph (Equiv.swap_mul_self (0 : Fin 2) 1) huv]
  rcases (α u v).eq_one_or_swap_fin_two with h | h <;> simp [supportGraph_adj, h, hne]

/-- On `complete V`, `Equiv.Perm (Fin 2)`-valued 1-cochains correspond bijectively to simple graphs
on `V` via their support graph. -/
noncomputable def supportGraphEquiv [Fintype V] :
    Cochain (complete V) (Equiv.Perm (Fin 2)) ≃ SimpleGraph V where
  toFun := supportGraph
  invFun Γ := ofSimpleGraph (complete V) Γ (Equiv.swap_mul_self 0 1)
  left_inv := ofSimpleGraph_supportGraph
  right_inv Γ :=
    supportGraph_ofSimpleGraph_complete Γ (Equiv.swap_mul_self (0 : Fin 2) 1) (by decide)

@[simp]
theorem supportGraphEquiv_apply [Fintype V] (α : Cochain (complete V) (Equiv.Perm (Fin 2))) :
    supportGraphEquiv α = α.supportGraph :=
  (rfl)

@[simp]
theorem supportGraphEquiv_symm_apply [Fintype V] (Γ : SimpleGraph V) :
    supportGraphEquiv.symm Γ = ofSimpleGraph (complete V) Γ (Equiv.swap_mul_self 0 1) :=
  (rfl)

/-- Acting on a binary cochain on `complete V` by a gauge `β` switches its support graph across the
cut `{v | β v ≠ 1}`. -/
theorem supportGraph_smul_complete [Fintype V] (β : V → Equiv.Perm (Fin 2))
    (α : Cochain (complete V) (Equiv.Perm (Fin 2))) :
    (β • α).supportGraph =
      α.supportGraph ∆ (⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ := by
  have hne : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
  have hβ : β = fun v => if v ∈ {v : V | β v ≠ 1} then Equiv.swap (0 : Fin 2) 1 else 1 := by
    funext v
    rcases (β v).eq_one_or_swap_fin_two with h | h <;> simp [h, hne]
  conv_lhs => rw [hβ, ← ofSimpleGraph_supportGraph α]
  rw [smul_ite_ofSimpleGraph_complete, supportGraph_ofSimpleGraph_complete _ _ hne]

/-- For a binary cochain `α` on `complete V`, the holonomy around `(u, v, w)` equals
`Equiv.swap 0 1` when `{u, v, w} ∈ α.supportGraph.oddTriangleFinset` and `1` otherwise. -/
theorem holonomy_fin_two_complete [Fintype V] [DecidableEq V]
    (α : Cochain (complete V) (Equiv.Perm (Fin 2))) (u v w : V) :
    α.holonomy u v w =
      if ({u, v, w} : Finset V) ∈ α.supportGraph.oddTriangleFinset then
        Equiv.swap 0 1
      else 1 := by
  conv_lhs => rw [← ofSimpleGraph_supportGraph α]
  exact holonomy_ofSimpleGraph_complete α.supportGraph (Equiv.swap_mul_self (0 : Fin 2) 1) u v w

/-- A binary cochain on `complete V` is a coboundary if and only if its support graph is a
complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` (Kozlov, Section 2). -/
theorem isCoboundary_fin_two_complete_iff [Fintype V]
    (α : Cochain (complete V) (Equiv.Perm (Fin 2))) :
    α.IsCoboundary ↔ ∃ S : Set V, α.supportGraph = (⊤ : SimpleGraph V).between S Sᶜ := by
  rw [isCoboundary_iff_exists_smul_eq_one]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨{v | β v ≠ 1}, symmDiff_eq_bot.mp ?_⟩
    rw [← supportGraph_smul_complete, hβ, supportGraph_one]
  · rintro ⟨S, hS⟩
    classical
    have hne : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
    let β : V → Equiv.Perm (Fin 2) := fun v => if v ∈ S then Equiv.swap 0 1 else 1
    have hset : {v : V | β v ≠ 1} = S := by
      ext v
      by_cases hv : v ∈ S <;> simp [β, hv, hne]
    refine ⟨β, (supportGraph_eq_bot_iff _).mp ?_⟩
    rw [supportGraph_smul_complete, hset, hS, symmDiff_self]

section CompleteMetric

variable [Fintype V] [LinearOrder V]

/-- For a binary cochain `α` on `complete V`, the cost of a gauge `β : V → Equiv.Perm (Fin 2)`
under `movedNorm (Fin 2)` equals twice the edge count of `α.supportGraph` switched across the cut
`{v | β v ≠ 1}` (Kozlov, Section 2). -/
theorem cost_movedNorm_fin_two_complete (α : Cochain (complete V) (Equiv.Perm (Fin 2)))
    (β : V → Equiv.Perm (Fin 2)) :
    α.cost (Equiv.Perm.movedNorm (Fin 2)) β =
      2 * (#(α.supportGraph.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ).edgeFinset) : ℝ) := by
  have hne : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
  have hβ : β = fun v => if v ∈ {v : V | β v ≠ 1} then Equiv.swap (0 : Fin 2) 1 else 1 := by
    funext v
    rcases (β v).eq_one_or_swap_fin_two with h | h <;> simp [h, hne]
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  conv_lhs => rw [hβ, ← ofSimpleGraph_supportGraph α]
  rw [cost_ofSimpleGraph_complete_ite, hswap.movedNorm]

/-- For a binary cochain `α` on `complete V`, the triangle defect under `movedNorm (Fin 2)` equals
twice the number of odd triangles of `α.supportGraph` (Kozlov, Section 2). -/
theorem defect_movedNorm_fin_two_complete (α : Cochain (complete V) (Equiv.Perm (Fin 2))) :
    α.defect (Equiv.Perm.movedNorm (Fin 2)) = 2 * (#α.supportGraph.oddTriangleFinset : ℝ) := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  conv_lhs => rw [← ofSimpleGraph_supportGraph α]
  rw [defect_ofSimpleGraph_complete, hswap.movedNorm]

/-- For a binary cochain `α` on `complete V`, the gauge distance under `movedNorm (Fin 2)` equals
the minimum over cuts `s : Finset V` of `2 * #(α.supportGraph.edgeFinset ∆ cut s)`. -/
theorem gaugeDist_movedNorm_fin_two_complete_eq_iInf
    (α : Cochain (complete V) (Equiv.Perm (Fin 2))) :
    α.gaugeDist (Equiv.Perm.movedNorm (Fin 2)) =
      ⨅ s : Finset V,
        2 * (#(α.supportGraph.edgeFinset ∆
          ((⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset) : ℝ) := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  conv_lhs => rw [← ofSimpleGraph_supportGraph α]
  exact gaugeDist_ofSimpleGraph_isSwap_eq_iInf α.supportGraph hswap

/-- A binary cochain `α` on `complete V` has gauge distance `2 * #α.supportGraph.edgeFinset` under
`movedNorm (Fin 2)` if and only if `α.supportGraph` is cut-minimal (Kozlov, Section 2). -/
theorem gaugeDist_movedNorm_fin_two_complete_eq_iff_isCutMinimal
    (α : Cochain (complete V) (Equiv.Perm (Fin 2))) :
    α.gaugeDist (Equiv.Perm.movedNorm (Fin 2)) = 2 * (#α.supportGraph.edgeFinset : ℝ) ↔
      α.supportGraph.IsCutMinimal := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  conv_lhs =>
    lhs
    rw [← ofSimpleGraph_supportGraph α]
  exact gaugeDist_ofSimpleGraph_isSwap_eq_iff_isCutMinimal α.supportGraph hswap

end CompleteMetric

end BinaryCochains

end Cochain

/-! ### Kozlov's theorem and Beasley's non-power-of-two evaluation -/

section CompleteCheeger

variable {V α : Type*} [Fintype V] [LinearOrder V]

/-- Any cut-minimal graph `Γ` on `V` with at least one edge bounds the counting Cheeger constant
`h1 (complete V) (Equiv.Perm.movedNorm α)` from above by the odd-triangle-to-edge ratio
`#Γ.oddTriangleFinset / #Γ.edgeFinset`, for every finite nontrivial type `α`
(Kozlov, Section 2; Beasley, Corollary 7). -/
theorem h1_complete_movedNorm_le_div_of_isCutMinimal [Fintype α] [DecidableEq α] [Nontrivial α]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (hcut : Γ.IsCutMinimal)
    (hne : Γ.edgeFinset.Nonempty) :
    h1 (complete V) (Equiv.Perm.movedNorm α) ≤
      (#Γ.oddTriangleFinset : ℝ) / (#Γ.edgeFinset : ℝ) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hswap : (Equiv.swap a b).IsSwap := ⟨a, b, hab, rfl⟩
  let ω : Cochain (complete V) (Equiv.Perm α) := Cochain.ofSimpleGraph (complete V) Γ hswap.mul_self
  have hdist : ω.gaugeDist (Equiv.Perm.movedNorm α) = 2 * (#Γ.edgeFinset : ℝ) :=
    (Cochain.gaugeDist_ofSimpleGraph_isSwap_eq_iff_isCutMinimal Γ hswap).mpr hcut
  have hedges_pos : 0 < #Γ.edgeFinset := hne.card_pos
  have hdist_pos : 0 < ω.gaugeDist (Equiv.Perm.movedNorm α) := by rw [hdist]; positivity
  refine (h1_le_div hdist_pos).trans_eq ?_
  dsimp only [ω]
  rw [Cochain.defect_ofSimpleGraph_complete, hswap.movedNorm, hdist,
    mul_div_mul_left _ _ two_ne_zero]

/-- Whenever `3 ≤ Fintype.card V` and `Fintype.card V` is not a power of two, the counting Cheeger
constant of `complete V` with respect to `Equiv.Perm.movedNorm α` on any finite nontrivial type `α`
equals `Fintype.card V / 3` (Kozlov, Theorem 3.1 for `Fin 2`; Beasley, Corollary 7 in general). -/
theorem h1_complete_movedNorm_of_not_exists_two_pow [Fintype α] [DecidableEq α] [Nontrivial α]
    (hV : 3 ≤ Fintype.card V) (hpow : ¬ ∃ a : ℕ, Fintype.card V = 2 ^ a) :
    h1 (complete V) (Equiv.Perm.movedNorm α) = (Fintype.card V : ℝ) / 3 := by
  refine le_antisymm ?_
    (card_div_three_le_h1_of_nontrivial hV (Equiv.Perm.movedNorm α)
      Equiv.Perm.isConjInvariant_movedNorm)
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : Fintype.card V ≠ 0)
  obtain ⟨t, rfl⟩ := hm
  have ht_pos : 0 < t := Nat.pos_of_ne_zero fun ht0 => hpow ⟨k, by simpa [ht0] using hcard⟩
  let c : ℕ := 2 ^ k
  have hcard_sum : Fintype.card V = Fintype.card (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hcard]
    dsimp only [c]; ring
  let e : V ≃ Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c := Fintype.equivOfCardEq hcard_sum
  let Γ : SimpleGraph V := (SimpleGraph.staircase c t).comap e
  let iso : Γ ≃g SimpleGraph.staircase c t := SimpleGraph.Iso.comap e (SimpleGraph.staircase c t)
  classical
  have hΓ_edges : #Γ.edgeFinset = #(SimpleGraph.staircase c t).edgeFinset := iso.card_edgeFinset_eq
  have hedges_pos : 0 < #Γ.edgeFinset := by
    have h2 := SimpleGraph.two_mul_card_edgeFinset_staircase c t
    have hprod : 0 < c ^ 2 * t * (t + 1) := by positivity
    omega
  refine (h1_complete_movedNorm_le_div_of_isCutMinimal Γ
    (iso.isCutMinimal_iff.mpr (SimpleGraph.isCutMinimal_staircase c t))
    (card_pos.mp hedges_pos)).trans_eq ?_
  have hcard_real : (Fintype.card V : ℝ) = (c * (2 * t + 1) : ℝ) := by
    dsimp only [c]; exact_mod_cast hcard
  have hne : (#(SimpleGraph.staircase c t).edgeFinset : ℝ) ≠ 0 := by
    rw [← hΓ_edges]; positivity
  rw [iso.card_oddTriangleFinset_eq, SimpleGraph.card_oddTriangleFinset_staircase, hΓ_edges,
    ← hcard_real, mul_div_cancel_right₀ _ hne]

/-- Normalized Cheeger constant of `complete V` with respect to `Equiv.Perm.movedNorm α` on any
finite nontrivial `α` when `3 ≤ Fintype.card V` is not a power of two. -/
theorem h1Norm_complete_movedNorm_of_not_exists_two_pow [Fintype α] [DecidableEq α] [Nontrivial α]
    (hV : 3 ≤ Fintype.card V) (hpow : ¬ ∃ a : ℕ, Fintype.card V = 2 ^ a) :
    h1Norm (complete V) (Equiv.Perm.movedNorm α) =
      (Fintype.card V : ℝ) / (Fintype.card V - 2) := by
  rw [h1Norm_complete hV, h1_complete_movedNorm_of_not_exists_two_pow hV hpow]
  ring

/-- **Kozlov's theorem** (counting convention): when `3 ≤ Fintype.card V` and `Fintype.card V` is
not a power of two, the `𝔽₂` coboundary Cheeger constant of `complete V` equals
`Fintype.card V / 3` (Kozlov, arXiv:1610.07136v2, Theorem 3.1). -/
theorem h1_complete_movedNorm_fin_two (hV : 3 ≤ Fintype.card V)
    (hpow : ¬ ∃ a : ℕ, Fintype.card V = 2 ^ a) :
    h1 (complete V) (Equiv.Perm.movedNorm (Fin 2)) = (Fintype.card V : ℝ) / 3 :=
  h1_complete_movedNorm_of_not_exists_two_pow hV hpow

/-- **Kozlov's theorem** (normalized convention): when `3 ≤ Fintype.card V` and `Fintype.card V` is
not a power of two, `h1Norm (complete V) (Equiv.Perm.movedNorm (Fin 2))` equals
`Fintype.card V / (Fintype.card V - 2)` (Kozlov, arXiv:1610.07136v2, Theorem 3.1). -/
theorem h1Norm_complete_movedNorm_fin_two (hV : 3 ≤ Fintype.card V)
    (hpow : ¬ ∃ a : ℕ, Fintype.card V = 2 ^ a) :
    h1Norm (complete V) (Equiv.Perm.movedNorm (Fin 2)) =
      (Fintype.card V : ℝ) / (Fintype.card V - 2) :=
  h1Norm_complete_movedNorm_of_not_exists_two_pow hV hpow

/-- When `3 ≤ Fintype.card V` and `Fintype.card V` is not a power of two, the same-degree
permutation Cheeger constant `h1Sym (complete V)` equals `Fintype.card V / 3`. -/
theorem h1Sym_complete_of_not_exists_two_pow (hV : 3 ≤ Fintype.card V)
    (hpow : ¬ ∃ a : ℕ, Fintype.card V = 2 ^ a) :
    h1Sym (complete V) = (Fintype.card V : ℝ) / 3 :=
  le_antisymm
    ((h1Sym_le_h1_movedNorm_fin_two (complete V)).trans_eq
      (h1_complete_movedNorm_fin_two hV hpow))
    (card_div_three_le_h1Sym hV)

end CompleteCheeger

end TauCeti

end
