/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.ExceptionalPrediction
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
import TauCeti.Data.Fintype.BigOperators
import TauCeti.Order.Hom.PowersetCard
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Local induced counting at transversal placements

Let `φ` be a transversal placement of a colored pattern `F` on `k` vertices into a triadic
complex `C`, and `ψ` a route over it. The placed count `H.placedInducedCopyCount φ ψ` counts the
labelled induced copies of `F` in `H` sending every pattern vertex into its assigned cell and every
canonical pattern pair onto its assigned pair color. Its prediction `H.expectedInducedCountAt φ ψ`
is the cell-size product times the pair-color densities of the route times the relative density,
over the induced polyad, of the pattern color of every increasing pattern triple.

This file proves the local counting lemma for these placed counts: if the lower skeleton of `C`
is `ε`-regular and `H` is `η`-top-regular at rank one over the induced polyad of every increasing
pattern triple, then the placed count and its prediction differ by at most
`(k.choose 2 * ε + k.choose 3 * η)` times the cell-size product. No lower bound on the pair or
triple densities is needed, and rank one suffices.

## Main results

* `TauCeti.Colored3Graph.abs_placedInducedCopyCount_sub_expectedInducedCountAt_le`: the local
  counting lemma at a transversal placement.

## Implementation notes

The maps realizing the route without top-color constraints are counted by the pair-color
counting lemma `abs_lowerRouteCountAt_sub_expectedLowerRouteCountAt_le`. The top-color indicators
are then replaced by their relative densities one increasing pattern triple `i < j < l` at a time,
as in the telescoping proof of the graph counting lemma. Once the coordinates outside `i, j, l`
are fixed, every remaining condition (a pair color, or the top color of another pattern triple,
which misses one of `i, j, l`) constrains at most two of the three free coordinates. The
admissible values at `(i, j, l)` therefore form the support of a subpolyad of the induced polyad,
on which `IsTopRegularOverPolyad.abs_relDensityOn_sub_mul_card_le` bounds the color discrepancy
by `η` times the polyad support.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
-/

public section

open Finset Function

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}
  {F : FiniteColored3Pattern κ} (H : Colored3Graph κ V) {φ : PatternPlacement3 C F}
  (ψ : PairColorPlacement3 φ)

/-- The values of `g` at an increasing triple of coordinates. -/
private def tripleAt {k : ℕ} (g : Fin k → V)
    (t : {t : Fin k × Fin k × Fin k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) : Fin 3 → V :=
  ![g t.1.1, g t.1.2.1, g t.1.2.2]

variable (F) in
/-- The map `g` gives the increasing pattern triple `t` its pattern color. -/
private def TopHolds (g : Fin F.k → V)
    (t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) : Prop :=
  ∃ hg : Injective (tripleAt g t),
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨tripleAt g t, hg⟩) =
      F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2

/-- The map `g` realizes the pair colors of the route `ψ` and the pattern colors of the
increasing pattern triples in `s`. -/
private def RouteHolds
    (s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2})
    (g : Fin F.k → V) : Prop :=
  (∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
    C.skeleton.pairColors.colorOfPair (g p.1.1) (g p.1.2) = some (ψ.pairColor p)) ∧
  ∀ t ∈ s, H.TopHolds F g t

/-- The conditions of `RouteHolds` not involving the coordinate `m`. -/
private def RouteHoldsAway
    (s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) (m : Fin F.k)
    (g : Fin F.k → V) : Prop :=
  (∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2}, p.1.1 ≠ m → p.1.2 ≠ m →
    C.skeleton.pairColors.colorOfPair (g p.1.1) (g p.1.2) = some (ψ.pairColor p)) ∧
  ∀ t ∈ s, t.1.1 ≠ m → t.1.2.1 ≠ m → t.1.2.2 ≠ m → H.TopHolds F g t

open Classical in
/-- With the coordinates outside the increasing pattern triple `t` given by `h`, the values at
`t` realizing `RouteHolds ψ s` form a subpolyad of the polyad that `ψ` induces on `t`: each of
its three pair graphs collects the conditions avoiding one coordinate of `t`. -/
private noncomputable def slice
    (s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2})
    (t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) (h : Fin F.k → V) :
    Subpolyad3 (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) where
  pair₀₁ := {q ∈ (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2).pairSupport₀₁ |
    H.RouteHoldsAway ψ s t.1.2.2 (update (update h t.1.1 q.1.1) t.1.2.1 q.1.2)}
  pair₀₂ := {q ∈ (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2).pairSupport₀₂ |
    H.RouteHoldsAway ψ s t.1.2.1 (update (update h t.1.1 q.1.1) t.1.2.2 q.1.2)}
  pair₁₂ := {q ∈ (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2).pairSupport₁₂ |
    H.RouteHoldsAway ψ s t.1.1 (update (update h t.1.2.1 q.1.1) t.1.2.2 q.1.2)}
  pair₀₁_sub := filter_subset _ _
  pair₀₂_sub := filter_subset _ _
  pair₁₂_sub := filter_subset _ _

variable {H ψ}

omit [Fintype V] [DecidableEq V] in
private theorem injective_tripleAt {k : ℕ} {g : Fin k → V} (hg : Injective g)
    (t : {t : Fin k × Fin k × Fin k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) :
    Injective (tripleAt g t) := by
  obtain ⟨hij, hjl⟩ := t.2
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [tripleAt, hg.eq_iff, hij.ne, hjl.ne, (hij.trans hjl).ne, hij.ne', hjl.ne',
      (hij.trans hjl).ne']

omit [Fintype V] in
private theorem ofFinEmb_tripleAt {k : ℕ} {g : Fin k → V}
    {t : {t : Fin k × Fin k × Fin k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    (hg : Injective (tripleAt g t)) (hc : #{g t.1.1, g t.1.2.1, g t.1.2.2} = 3) :
    Set.powersetCard.ofFinEmb 3 V ⟨tripleAt g t, hg⟩ = Set.powersetCard.ofCard hc := by
  refine Subtype.ext (Finset.ext fun a ↦ ?_)
  simp [Set.powersetCard.val_ofFinEmb, tripleAt, Fin.exists_fin_succ, eq_comm]

omit [DecidableEq κ] [Fintype V] [DecidableEq V] in
private theorem topHolds_congr {g g' : Fin F.k → V}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    (h₁ : g t.1.1 = g' t.1.1) (h₂ : g t.1.2.1 = g' t.1.2.1) (h₃ : g t.1.2.2 = g' t.1.2.2) :
    H.TopHolds F g t ↔ H.TopHolds F g' t := by
  have : tripleAt g t = tripleAt g' t := by simp [tripleAt, h₁, h₂, h₃]
  unfold TopHolds
  rw [this]

omit [DecidableEq κ] in
private theorem routeHoldsAway_congr
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} {m : Fin F.k}
    {g g' : Fin F.k → V} (h : ∀ n, n ≠ m → g n = g' n) :
    H.RouteHoldsAway ψ s m g ↔ H.RouteHoldsAway ψ s m g' := by
  unfold RouteHoldsAway
  refine and_congr (forall_congr' fun p ↦ ?_) (forall₂_congr fun t _ ↦ ?_)
  · refine imp_congr_right fun h₁ ↦ imp_congr_right fun h₂ ↦ ?_
    rw [h _ h₁, h _ h₂]
  · exact imp_congr_right fun h₁ ↦ imp_congr_right fun h₂ ↦ imp_congr_right fun h₃ ↦
      topHolds_congr (h _ h₁) (h _ h₂) (h _ h₃)

omit [DecidableEq κ] in
/-- A pair of pattern vertices misses some vertex of every increasing triple. -/
private theorem pair_avoids (p : {p : Fin F.k × Fin F.k // p.1 < p.2})
    (t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) :
    (p.1.1 ≠ t.1.2.2 ∧ p.1.2 ≠ t.1.2.2) ∨ (p.1.1 ≠ t.1.2.1 ∧ p.1.2 ≠ t.1.2.1) ∨
      (p.1.1 ≠ t.1.1 ∧ p.1.2 ≠ t.1.1) := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨i, j, l⟩, hij, hjl⟩ := t
  have : (a : ℕ) < b := hab
  have : (i : ℕ) < j := hij
  have : (j : ℕ) < l := hjl
  simp only [ne_eq, Fin.ext_iff]
  omega

omit [DecidableEq κ] in
/-- A second increasing triple misses some vertex of the first. -/
private theorem triple_avoids
    {u t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (hut : u ≠ t) :
    (u.1.1 ≠ t.1.2.2 ∧ u.1.2.1 ≠ t.1.2.2 ∧ u.1.2.2 ≠ t.1.2.2) ∨
      (u.1.1 ≠ t.1.2.1 ∧ u.1.2.1 ≠ t.1.2.1 ∧ u.1.2.2 ≠ t.1.2.1) ∨
        (u.1.1 ≠ t.1.1 ∧ u.1.2.1 ≠ t.1.1 ∧ u.1.2.2 ≠ t.1.1) := by
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := u
  obtain ⟨⟨i, j, l⟩, hij, hjl⟩ := t
  have : (a : ℕ) < b := hab
  have : (b : ℕ) < c := hbc
  have : (i : ℕ) < j := hij
  have : (j : ℕ) < l := hjl
  simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff] at hut ⊢
  omega

omit [DecidableEq κ] in
/-- Away from the triples of `s`, the conditions of `RouteHolds` split into those avoiding each
vertex of `t`. -/
private theorem routeHolds_iff_routeHoldsAway
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (ht : t ∉ s)
    (g : Fin F.k → V) :
    H.RouteHolds ψ s g ↔ H.RouteHoldsAway ψ s t.1.2.2 g ∧ H.RouteHoldsAway ψ s t.1.2.1 g ∧
      H.RouteHoldsAway ψ s t.1.1 g := by
  refine ⟨fun ⟨hp, hs⟩ ↦ ⟨⟨fun p _ _ ↦ hp p, fun u hu _ _ _ ↦ hs u hu⟩,
    ⟨fun p _ _ ↦ hp p, fun u hu _ _ _ ↦ hs u hu⟩, ⟨fun p _ _ ↦ hp p, fun u hu _ _ _ ↦ hs u hu⟩⟩,
    fun ⟨h₃, h₂, h₁⟩ ↦ ⟨fun p ↦ ?_, fun u hu ↦ ?_⟩⟩
  · rcases pair_avoids p t with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    exacts [h₃.1 p ha hb, h₂.1 p ha hb, h₁.1 p ha hb]
  · rcases triple_avoids (ne_of_mem_of_not_mem hu ht) with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ |
      ⟨ha, hb, hc⟩
    exacts [h₃.2 u hu ha hb hc, h₂.2 u hu ha hb hc, h₁.2 u hu ha hb hc]

omit [DecidableEq κ] in
private theorem routeHolds_insert
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (g : Fin F.k → V) :
    H.RouteHolds ψ (insert t s) g ↔ H.RouteHolds ψ s g ∧ H.TopHolds F g t := by
  simp only [RouteHolds, forall_mem_insert]
  tauto

omit [DecidableEq κ] in
/-- The values at the increasing pattern triple `t` lying in the slice over `h` are exactly the
values in the assigned cells whose substitution into `h` realizes `RouteHolds ψ s`. -/
private theorem mem_slice_support
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (ht : t ∉ s)
    (h : Fin F.k → V) (w : {w : Fin 3 → V // Injective w}) :
    w ∈ (H.slice ψ s t h).support ↔
      (w.1 0 ∈ φ.vertexCell t.1.1 ∧ w.1 1 ∈ φ.vertexCell t.1.2.1 ∧
        w.1 2 ∈ φ.vertexCell t.1.2.2) ∧
      H.RouteHolds ψ s
        (update (update (update h t.1.1 (w.1 0)) t.1.2.1 (w.1 1)) t.1.2.2 (w.1 2)) := by
  classical
  obtain ⟨hij, hjl⟩ := t.2
  have hil := hij.trans hjl
  set g := update (update (update h t.1.1 (w.1 0)) t.1.2.1 (w.1 1)) t.1.2.2 (w.1 2)
  have gi : g t.1.1 = w.1 0 := by simp [g, hij.ne, hil.ne]
  have gj : g t.1.2.1 = w.1 1 := by simp [g, hjl.ne]
  have gl : g t.1.2.2 = w.1 2 := by simp [g]
  -- Each pair graph of the slice tests the conditions avoiding one vertex of `t` on `g`.
  have h₃ : H.RouteHoldsAway ψ s t.1.2.2 (update (update h t.1.1 (w.1 0)) t.1.2.1 (w.1 1)) ↔
      H.RouteHoldsAway ψ s t.1.2.2 g :=
    routeHoldsAway_congr fun n hn ↦ by simp [g, hn]
  have h₂ : H.RouteHoldsAway ψ s t.1.2.1 (update (update h t.1.1 (w.1 0)) t.1.2.2 (w.1 2)) ↔
      H.RouteHoldsAway ψ s t.1.2.1 g :=
    routeHoldsAway_congr fun n hn ↦ by simp only [g, update_apply]; split_ifs <;> simp_all
  have h₁ : H.RouteHoldsAway ψ s t.1.1 (update (update h t.1.2.1 (w.1 1)) t.1.2.2 (w.1 2)) ↔
      H.RouteHoldsAway ψ s t.1.1 g :=
    routeHoldsAway_congr fun n hn ↦ by simp only [g, update_apply]; split_ifs <;> simp_all
  rw [Subpolyad3.mem_support, routeHolds_iff_routeHoldsAway ht]
  simp only [slice, mem_filter, coe_coordPair, h₃, h₂, h₁]
  constructor
  · rintro ⟨hw, ⟨-, a₃⟩, ⟨-, a₂⟩, ⟨-, a₁⟩⟩
    obtain ⟨hc₀, hc₁, hc₂, -⟩ := (Polyad3.mem_support _ w).1 hw
    exact ⟨⟨by simpa using hc₀, by simpa using hc₁, by simpa using hc₂⟩, a₃, a₂, a₁⟩
  · rintro ⟨⟨hc₀, hc₁, hc₂⟩, a₃, a₂, a₁⟩
    have k₀₁ := a₃.1 ⟨(t.1.1, t.1.2.1), hij⟩ hil.ne hjl.ne
    have k₀₂ := a₂.1 ⟨(t.1.1, t.1.2.2), hil⟩ hij.ne hjl.ne'
    have k₁₂ := a₁.1 ⟨(t.1.2.1, t.1.2.2), hjl⟩ hij.ne' hil.ne'
    simp only [gi, gj, gl] at k₀₁ k₀₂ k₁₂
    have hw : w ∈ (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2).support :=
      (Polyad3.mem_support _ w).2 ⟨by simpa using hc₀, by simpa using hc₁, by simpa using hc₂,
        by simpa using k₀₁, by simpa using k₀₂, by simpa using k₁₂⟩
    exact ⟨hw, ⟨coordPair_mem_pairSupport₀₁ hw, a₃⟩, ⟨coordPair_mem_pairSupport₀₂ hw, a₂⟩,
      ⟨coordPair_mem_pairSupport₁₂ hw, a₁⟩⟩

omit [DecidableEq κ] in
open Classical in
/-- Over the box of assigned cells at `t`, the values whose substitution into `h` realizes
`RouteHolds ψ s` and satisfies a test `Y` on the substituted triple correspond to the triples of
the slice satisfying `Y`. -/
private theorem card_filter_product_eq_card_filter_slice
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (ht : t ∉ s)
    (h : Fin F.k → V) (Y : {w : Fin 3 → V // Injective w} → Prop) [DecidablePred Y] :
    #{q ∈ φ.vertexCell t.1.1 ×ˢ φ.vertexCell t.1.2.1 ×ˢ φ.vertexCell t.1.2.2 |
        H.RouteHolds ψ s (update (update (update h t.1.1 q.1) t.1.2.1 q.2.1) t.1.2.2 q.2.2) ∧
          ∃ hq : Injective ![q.1, q.2.1, q.2.2], Y ⟨_, hq⟩} =
      #{w ∈ (H.slice ψ s t h).support | Y w} := by
  symm
  refine card_nbij (fun w ↦ (w.1 0, w.1 1, w.1 2)) (fun w hw ↦ ?_)
    fin_three_coords_injective.injOn (fun q hq ↦ ?_)
  · obtain ⟨hw, hY⟩ := mem_filter.1 hw
    obtain ⟨⟨h₀, h₁, h₂⟩, hR⟩ := (mem_slice_support ht h w).1 hw
    have e : ![w.1 0, w.1 1, w.1 2] = w.1 := FinVec.etaExpand_eq w.1
    refine mem_filter.2 ⟨mem_product.2 ⟨h₀, mem_product.2 ⟨h₁, h₂⟩⟩, hR, by rw [e]; exact w.2, ?_⟩
    exact (congrArg Y (Subtype.ext e)).mpr hY
  · obtain ⟨hq, hR, hinj, hY⟩ := mem_filter.1 (mem_coe.1 hq)
    obtain ⟨h₀, h₁, h₂⟩ : q.1 ∈ _ ∧ q.2.1 ∈ _ ∧ q.2.2 ∈ _ := by simpa using hq
    exact ⟨⟨_, hinj⟩, mem_filter.2 ⟨(mem_slice_support ht h _).2 ⟨⟨h₀, h₁, h₂⟩, hR⟩, hY⟩, rfl⟩

open Classical in
/-- Over the fibre of maps agreeing with `h` outside the increasing pattern triple `t`, the
top-color indicator of `t` minus `d` times the route indicator sums to the color discrepancy
`relDensityOn - d` on the slice, times the size of the slice. -/
private theorem sum_sum_sum_update_eq
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (ht : t ∉ s)
    (h : Fin F.k → V) (d : ℝ) :
    ∑ x ∈ φ.vertexCell t.1.1, ∑ y ∈ φ.vertexCell t.1.2.1, ∑ z ∈ φ.vertexCell t.1.2.2,
      ((if H.RouteHolds ψ s (update (update (update h t.1.1 x) t.1.2.1 y) t.1.2.2 z) ∧
          H.TopHolds F (update (update (update h t.1.1 x) t.1.2.1 y) t.1.2.2 z) t then 1 else 0) -
        d * if H.RouteHolds ψ s (update (update (update h t.1.1 x) t.1.2.1 y) t.1.2.2 z) then 1
          else 0) =
      ((H.relDensityOn (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
        (H.slice ψ s t h).support : ℝ) - d) * #(H.slice ψ s t h).support := by
  set c := F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2
  set Q := H.slice ψ s t h
  set A := φ.vertexCell
  obtain ⟨hij, hjl⟩ := t.2
  have hc : (H.relDensityOn c Q.support : ℝ) * #Q.support =
      #{w ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨w.1, w.2⟩) = c} := by
    exact_mod_cast H.relDensityOn_mul_card c _
  have hY := card_filter_product_eq_card_filter_slice (H := H) (ψ := ψ) ht h
    fun w ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨w.1, w.2⟩) = c
  have hT := card_filter_product_eq_card_filter_slice (H := H) (ψ := ψ) ht h fun _ ↦ True
  dsimp only at hY hT
  -- Substituting `(x, y, z)` into `h` puts these values at `t`.
  have htri (x y z : V) :
      tripleAt (update (update (update h t.1.1 x) t.1.2.1 y) t.1.2.2 z) t = ![x, y, z] := by
    ext m
    fin_cases m <;> simp [tripleAt, hij.ne, (hij.trans hjl).ne, hjl.ne]
  have hR : {q ∈ A t.1.1 ×ˢ A t.1.2.1 ×ˢ A t.1.2.2 |
      H.RouteHolds ψ s (update (update (update h t.1.1 q.1) t.1.2.1 q.2.1) t.1.2.2 q.2.2)} =
      {q ∈ A t.1.1 ×ˢ A t.1.2.1 ×ˢ A t.1.2.2 |
        H.RouteHolds ψ s (update (update (update h t.1.1 q.1) t.1.2.1 q.2.1) t.1.2.2 q.2.2) ∧
          ∃ _ : Injective ![q.1, q.2.1, q.2.2], True} := by
    refine filter_congr fun q _ ↦ ⟨fun hq ↦ ⟨hq, ?_, trivial⟩, And.left⟩
    rw [← htri]
    exact injective_tripleAt (injective_of_forall_colorOfPair_eq_some hq.1) t
  have hRT : {q ∈ A t.1.1 ×ˢ A t.1.2.1 ×ˢ A t.1.2.2 |
      H.RouteHolds ψ s (update (update (update h t.1.1 q.1) t.1.2.1 q.2.1) t.1.2.2 q.2.2) ∧
        H.TopHolds F (update (update (update h t.1.1 q.1) t.1.2.1 q.2.1) t.1.2.2 q.2.2) t} =
      {q ∈ A t.1.1 ×ˢ A t.1.2.1 ×ˢ A t.1.2.2 |
        H.RouteHolds ψ s (update (update (update h t.1.1 q.1) t.1.2.1 q.2.1) t.1.2.2 q.2.2) ∧
          ∃ hq : Injective ![q.1, q.2.1, q.2.2],
            H.color (Set.powersetCard.ofFinEmb 3 V ⟨![q.1, q.2.1, q.2.2], hq⟩) = c} := by
    refine filter_congr fun q _ ↦ and_congr_right fun _ ↦ ?_
    unfold TopHolds
    rw [htri]
  simp only [← sum_product', sum_sub_distrib, ← mul_sum]
  rw [← natCast_card_filter, ← natCast_card_filter, hRT, hR, hY, hT, filter_true, ← hc]
  ring

open Classical in
/-- **One telescoping step.** Testing the deviation of the top-color indicator of a triple `t`
outside `s` from its relative density against the maps realizing `RouteHolds ψ s` costs at most
`η` times the cell-size product, when `H` is `η`-top-regular at rank one over the polyad of `t`. -/
private theorem abs_card_filter_topHolds_sub_le
    {s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}}
    {t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}} (ht : t ∉ s) {η : ℝ}
    (hP : H.IsTopRegularOverPolyad (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) η 1) :
    |(#{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ s g ∧ H.TopHolds F g t} : ℝ) -
        (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
          (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ) *
          #{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ s g}| ≤
      η * ∏ m, (#(φ.vertexCell m) : ℝ) := by
  set P := ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2
  set c := F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2
  set d : ℝ := (H.relativeDensity c P : ℝ)
  set A := φ.vertexCell
  have : Nonempty κ := ⟨c⟩
  have hη := hP.nonneg
  obtain ⟨hij, hjl⟩ := t.2
  have hil := hij.trans hjl
  -- The difference is a sum over the box of a weight `G`.
  set G : (Fin F.k → V) → ℝ := fun g ↦ (if H.RouteHolds ψ s g ∧ H.TopHolds F g t then 1 else 0) -
    d * if H.RouteHolds ψ s g then 1 else 0
  have hG : (#{g ∈ Fintype.piFinset A | H.RouteHolds ψ s g ∧ H.TopHolds F g t} : ℝ) -
      d * #{g ∈ Fintype.piFinset A | H.RouteHolds ψ s g} = ∑ g ∈ Fintype.piFinset A, G g := by
    simp only [G, sum_sub_distrib, ← mul_sum, natCast_card_filter]
  rw [hG]
  rcases (Fintype.piFinset A).eq_empty_or_nonempty with hbox | ⟨g₀, hg₀⟩
  · rw [hbox, sum_empty, abs_zero]
    exact mul_nonneg hη (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  have hg₀' := Fintype.mem_piFinset.1 hg₀
  have hsplit := Fintype.sum_piFinset_eq_sum_filter_sum_sum_sum_update (M := ℝ) hij.ne hil.ne
    hjl.ne A (hg₀' t.1.1) (hg₀' t.1.2.1) (hg₀' t.1.2.2)
  -- The box volume is the number of fibres times the volume of the cells at `t`.
  have hvol : (∏ m, (#(A m) : ℝ)) =
      #{h ∈ Fintype.piFinset A | h t.1.1 = g₀ t.1.1 ∧ h t.1.2.1 = g₀ t.1.2.1 ∧
        h t.1.2.2 = g₀ t.1.2.2} * (#(A t.1.1) * #(A t.1.2.1) * #(A t.1.2.2)) := by
    have := hsplit fun _ ↦ (1 : ℝ)
    simp only [sum_const, nsmul_eq_mul, mul_one, Fintype.card_piFinset] at this
    push_cast at this
    linear_combination this
  rw [hsplit, hvol]
  refine (abs_sum_le_card_nsmul (B := η * (#(A t.1.1) * #(A t.1.2.1) * #(A t.1.2.2)))
    fun h _ ↦ ?_).trans_eq (by rw [nsmul_eq_mul]; ring)
  -- Over each fibre, rank-one top regularity bounds the color discrepancy on the slice.
  simp only [G]
  rw [sum_sum_sum_update_eq ht h d, abs_mul, Nat.abs_cast]
  calc _ ≤ η * #P.support := (hP.abs_relDensityOn_sub_mul_card_le c _)
    _ ≤ η * (#(A t.1.1) * #(A t.1.2.1) * #(A t.1.2.2)) := by
      gcongr
      have := P.card_support_le
      simp only [P, PairColorPlacement3.polyad_c₀, PairColorPlacement3.polyad_c₁,
        PairColorPlacement3.polyad_c₂] at this
      exact_mod_cast this

omit [DecidableEq κ] [Fintype V] in
/-- For an injective `g`, giving the increasing pattern triple `t` its pattern color is a
condition on the image triple `{g i, g j, g l}`. -/
private theorem topHolds_iff_of_injective {g : Fin F.k → V} (hg : Injective g)
    (t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) :
    H.TopHolds F g t ↔ H.color (Set.powersetCard.ofCard (s := {g t.1.1, g t.1.2.1, g t.1.2.2})
      (Finset.card_eq_three.2 ⟨g t.1.1, g t.1.2.1, g t.1.2.2, hg.ne t.2.1.ne,
        hg.ne (t.2.1.trans t.2.2).ne, hg.ne t.2.2.ne, rfl⟩)) =
      F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2 := by
  unfold TopHolds
  refine ⟨fun ⟨hx, h⟩ ↦ ?_, fun h ↦ ⟨injective_tripleAt hg t, ?_⟩⟩
  · rwa [ofFinEmb_tripleAt hx] at h
  · rwa [ofFinEmb_tripleAt]

omit [DecidableEq κ] in
open Classical in
/-- The placed count is the number of maps into the box of assigned cells realizing the pair
colors of the route and the pattern colors of all increasing pattern triples. -/
private theorem placedInducedCopyCount_eq_card_filter :
    H.placedInducedCopyCount φ ψ =
      #{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ univ g} := by
  rw [placedInducedCopyCount_def]
  refine card_bij (fun f _ ↦ ⇑f) (fun f hf ↦ ?_) (fun f _ f' _ h ↦ DFunLike.coe_injective h)
    (fun g hg ↦ ?_)
  · obtain ⟨hcopy, hcell, hcolor⟩ := mem_placedInducedCopies.1 hf
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 hcell, hcolor, fun t _ ↦ ?_⟩
    exact (topHolds_iff_of_injective f.injective t).2
      ((isInducedCopy_iff_forall_lt H F f).1 hcopy _ _ _ t.2.1 t.2.2)
  · obtain ⟨hcell, hR⟩ := mem_filter.1 hg
    let f : Fin F.k ↪ V := ⟨g, injective_of_forall_colorOfPair_eq_some hR.1⟩
    refine ⟨f, mem_placedInducedCopies.2 ⟨(isInducedCopy_iff_forall_lt H F f).2
      fun i j l hij hjl ↦ ?_, Fintype.mem_piFinset.1 hcell, hR.1⟩, rfl⟩
    exact (topHolds_iff_of_injective f.injective ⟨(i, j, l), hij, hjl⟩).1 (hR.2 _ (mem_univ _))

omit [DecidableEq κ] in
open Classical in
/-- Without top-color constraints, the maps realizing the route are those counted by
`lowerRouteCountAt`. -/
private theorem lowerRouteCountAt_eq_card_filter :
    lowerRouteCountAt φ ψ = #{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ ∅ g} := by
  rw [lowerRouteCountAt_def, lowerRouteMaps_eq_filter_piFinset]
  congr 1
  exact filter_congr fun g _ ↦ by simp [RouteHolds]

/-- Replacing `b` by `c` inside `|a - d * b|` costs at most `|b - c|` when `0 ≤ d ≤ 1`. -/
private theorem abs_sub_mul_le_of_le_one {a b c d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    |a - d * c| ≤ |a - d * b| + |b - c| :=
  calc |a - d * c| = |(a - d * b) + d * (b - c)| := by congr 1; ring
    _ ≤ |a - d * b| + |d * (b - c)| := abs_add_le _ _
    _ ≤ |a - d * b| + |b - c| := by
      rw [abs_mul, abs_of_nonneg hd₀]
      exact add_le_add_right (mul_le_of_le_one_left (abs_nonneg _) hd₁) _

open Classical in
/-- **Telescoping.** Replacing the top-color indicators of the triples of `s` by their relative
densities changes the number of maps realizing the route by at most `#s * η` times the cell-size
product. -/
private theorem abs_card_filter_routeHolds_sub_le
    (s : Finset {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) {η : ℝ}
    (hs : ∀ t ∈ s, H.IsTopRegularOverPolyad (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) η 1) :
    |(#{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ s g} : ℝ) -
        (∏ t ∈ s, (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
          (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ)) *
          #{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ ∅ g}| ≤
      #s * η * ∏ m, (#(φ.vertexCell m) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s ht ih =>
    set d : ℝ := (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
      (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ)
    have hd₀ : 0 ≤ d := Rat.cast_nonneg.2 (H.relativeDensity_nonneg _ _)
    have hd₁ : d ≤ 1 := by
      simpa only [d, Rat.cast_one] using Rat.cast_le.2 (H.relativeDensity_le_one _ _)
    have hstep := abs_card_filter_topHolds_sub_le ht (hs t (mem_insert_self t s))
    have hih := ih fun u hu ↦ hs u (mem_insert_of_mem hu)
    have hfilter : {g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ (insert t s) g} =
        {g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ s g ∧ H.TopHolds F g t} :=
      filter_congr fun g _ ↦ routeHolds_insert g
    rw [hfilter, prod_insert ht, card_insert_of_notMem ht]
    set a : ℝ :=
      ((#{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ s g ∧ H.TopHolds F g t} : ℕ) : ℝ)
    set b : ℝ := ((#{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ s g} : ℕ) : ℝ)
    set n₀ : ℝ := ((#{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ ∅ g} : ℕ) : ℝ)
    set q := ∏ t ∈ s, (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
      (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ)
    -- Replace the indicator of `t` by `d`, then the remaining indicators by induction.
    calc |a - d * q * n₀| ≤ |a - d * b| + |b - q * n₀| := by
          rw [mul_assoc]
          exact abs_sub_mul_le_of_le_one hd₀ hd₁
      _ ≤ η * ∏ m, (#(φ.vertexCell m) : ℝ) + #s * η * ∏ m, (#(φ.vertexCell m) : ℝ) :=
        add_le_add hstep hih
      _ = _ := by push_cast; ring

/-- **Local induced counting.** Let `φ` be a transversal placement of a pattern `F` on `k`
vertices into a triadic complex `C` whose lower skeleton is `ε`-regular, and let `ψ` be a route
over `φ` such that `H` is `η`-top-regular at rank one over the polyad of every increasing pattern
triple. Then the number of labelled induced copies of `F` in `H` realizing `φ` and `ψ` differs from
its prediction `H.expectedInducedCountAt φ ψ` by at most `(k.choose 2 * ε + k.choose 3 * η)`
times the cell-size product. No lower bound on the pair or triple densities is assumed. -/
theorem abs_placedInducedCopyCount_sub_expectedInducedCountAt_le (hφ : φ.Transversal)
    {ε η : ℝ} (hlower : C.skeleton.IsPairColorRegular ε) (hroute : ψ.IsTopRegularRoute H η 1) :
    |(H.placedInducedCopyCount φ ψ : ℝ) - H.expectedInducedCountAt φ ψ| ≤
      (F.k.choose 2 * ε + F.k.choose 3 * η) * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  classical
  set D : ℝ := ∏ t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2},
    (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
      (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ)
  have hD₀ : 0 ≤ D := prod_nonneg fun _ _ ↦ by exact_mod_cast H.relativeDensity_nonneg _ _
  have hD₁ : D ≤ 1 := prod_le_one₀ (fun _ _ ↦ by exact_mod_cast H.relativeDensity_nonneg _ _)
    fun _ _ ↦ by exact_mod_cast H.relativeDensity_le_one _ _
  -- At a transversal placement the prediction is the lower-route prediction times `D`.
  have hexp : H.expectedInducedCountAt φ ψ = D * expectedLowerRouteCountAt φ ψ := by
    rw [expectedInducedCountAt_def, expectedLowerRouteCountAt_def,
      placementInjectionCount_eq_prod_of_transversal hφ]
    push_cast
    ring
  have htop := abs_card_filter_routeHolds_sub_le (H := H) (ψ := ψ) univ
    fun t _ ↦ (ψ.isTopRegularRoute_iff H η 1).1 hroute t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2
  rw [card_univ, Set.powersetCard.card_lt_triple, Fintype.card_fin,
    ← lowerRouteCountAt_eq_card_filter (H := H)] at htop
  have hpair := abs_lowerRouteCountAt_sub_expectedLowerRouteCountAt_le hφ ψ hlower
  rw [hexp, placedInducedCopyCount_eq_card_filter]
  set N : ℝ := ((#{g ∈ Fintype.piFinset φ.vertexCell | H.RouteHolds ψ univ g} : ℕ) : ℝ)
  set L : ℝ := ((lowerRouteCountAt φ ψ : ℕ) : ℝ)
  set E := expectedLowerRouteCountAt φ ψ
  -- Compare with the lower-route count, first replacing the top colors, then the pair colors.
  calc |N - D * E| ≤ |N - D * L| + |L - E| := abs_sub_mul_le_of_le_one hD₀ hD₁
    _ ≤ F.k.choose 3 * η * ∏ i, (#(φ.vertexCell i) : ℝ) +
        F.k.choose 2 * ε * ∏ i, (#(φ.vertexCell i) : ℝ) := add_le_add htop hpair
    _ = _ := by ring

end Colored3Graph

end TauCeti
