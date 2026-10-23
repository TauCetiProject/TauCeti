/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Density
public import TauCeti.Combinatorics.Hypergraph.Polyad.Subpolyad
import Mathlib.Tactic.Linarith

/-!
# Top regularity over polyads

A coloring `H` of the unordered triples is `(δ, r)`-top-regular over a polyad `P` when, for every
top color `c` and every union of at most `r` subpolyads of `P` carrying at least a `δ`-fraction of
the support of `P`, the relative density of `c` on that union is within `δ` of its relative density
over `P`. Subpolyads select arbitrary subgraphs of the three pair graphs of `P`, so this is the
rank-`r` test surface of Rödl–Schacht and Nagle–Rödl–Schacht; rank one is the disc-regular case.
Each top color is controlled separately.

The weaker vertex-box condition `IsVertexBoxRegularOverPolyad` only tests restrictions of the
three vertex cells, keeping the full pair graphs. It follows from top regularity at any positive
rank.

## Main definitions

* `TauCeti.Colored3Graph.IsTopRegularOverPolyad`: `(δ, r)`-regularity over a polyad.
* `TauCeti.Colored3Graph.IsVertexBoxRegularOverPolyad`: regularity on vertex-box restrictions.

## Main results

* `TauCeti.Colored3Graph.IsTopRegularOverPolyad.abs_relDensityOn_sub_le`: the test applies to
  every family of at most `r` subpolyads, indexed by any finite type.
* `TauCeti.Colored3Graph.IsTopRegularOverPolyad.of_rank_le`: regularity at a higher rank implies
  regularity at every lower rank.
* `TauCeti.Colored3Graph.isTopRegularOverPolyad_one_iff`: at rank one the condition tests single
  subpolyads.
* `TauCeti.Colored3Graph.IsTopRegularOverPolyad.isVertexBoxRegularOverPolyad`: top regularity at a
  positive rank implies vertex-box regularity.
* `TauCeti.Colored3Graph.isTopRegularOverPolyad_const`: a constant coloring is top-regular over
  every polyad, at every rank and every positive parameter.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
-/

public section

open Finset

namespace TauCeti

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}

namespace Colored3Graph

open Subpolyad3

variable [DecidableEq κ] {H : Colored3Graph κ V} {δ δ' : ℝ} {r r' : ℕ}

variable (H P) in
/-- `H` is `(δ, r)`-top-regular over the polyad `P` when, for every top color `c` and every
family of `r` subpolyads of `P` whose union support has at least `δ` times the size of the
support of `P`, the relative density of `c` on that union is within `δ` of the relative density
of `c` over `P`. Members of the family may repeat, so this tests unions of at most `r`
subpolyads. -/
def IsTopRegularOverPolyad (δ : ℝ) (r : ℕ) : Prop :=
  ∀ (c : κ) (Q : Fin r → Subpolyad3 P), δ * #P.support ≤ #(unionSupport Q) →
    |(H.relDensityOn c (unionSupport Q) : ℝ) - H.relativeDensity c P| ≤ δ

/-- Unfolded form of `Colored3Graph.IsTopRegularOverPolyad`. -/
theorem isTopRegularOverPolyad_iff : H.IsTopRegularOverPolyad P δ r ↔
    ∀ (c : κ) (Q : Fin r → Subpolyad3 P), δ * #P.support ≤ #(unionSupport Q) →
      |(H.relDensityOn c (unionSupport Q) : ℝ) - H.relativeDensity c P| ≤ δ :=
  Iff.rfl

/-- **The rank-`r` test.** A `(δ, r)`-top-regular coloring passes the test on the union of any
family of at most `r` subpolyads, indexed by an arbitrary finite type. -/
theorem IsTopRegularOverPolyad.abs_relDensityOn_sub_le (h : H.IsTopRegularOverPolyad P δ r)
    (c : κ) {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ r) (Q : ι → Subpolyad3 P)
    (hQ : δ * #P.support ≤ #(unionSupport Q)) :
    |(H.relDensityOn c (unionSupport Q) : ℝ) - H.relativeDensity c P| ≤ δ := by
  obtain ⟨Q', hQ'⟩ := exists_unionSupport_eq_of_card_le Q hι
  rw [← hQ'] at hQ ⊢
  exact h c Q' hQ

/-- Top regularity at a rank implies top regularity at every lower rank. -/
theorem IsTopRegularOverPolyad.of_rank_le (h : H.IsTopRegularOverPolyad P δ r') (hr : r ≤ r') :
    H.IsTopRegularOverPolyad P δ r :=
  fun c Q hQ ↦ h.abs_relDensityOn_sub_le c (by simpa using hr) Q hQ

/-- Top regularity is monotone in its parameter. -/
theorem IsTopRegularOverPolyad.mono (h : H.IsTopRegularOverPolyad P δ r) (hδ : δ ≤ δ') :
    H.IsTopRegularOverPolyad P δ' r :=
  fun c Q hQ ↦ (h c Q ((mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans hQ)).trans hδ

/-- At rank one, top regularity tests single subpolyads. -/
theorem isTopRegularOverPolyad_one_iff : H.IsTopRegularOverPolyad P δ 1 ↔
    ∀ (c : κ) (Q : Subpolyad3 P), δ * #P.support ≤ #Q.support →
      |(H.relDensityOn c Q.support : ℝ) - H.relativeDensity c P| ≤ δ := by
  refine ⟨fun h c Q hQ ↦ ?_, fun h c Q hQ ↦ ?_⟩
  · simpa using h c (fun _ ↦ Q) (by simpa using hQ)
  · rw [unionSupport_unique] at hQ ⊢
    exact h c _ hQ

variable (H P r) in
/-- Every coloring is top-regular once `1 ≤ δ`, since relative densities lie in `[0, 1]`. -/
theorem isTopRegularOverPolyad_of_one_le (hδ : 1 ≤ δ) : H.IsTopRegularOverPolyad P δ r := by
  intro c Q _
  have h₀ : (0 : ℝ) ≤ H.relDensityOn c (unionSupport Q) := mod_cast H.relDensityOn_nonneg c _
  have h₁ : (H.relDensityOn c (unionSupport Q) : ℝ) ≤ 1 := mod_cast H.relDensityOn_le_one c _
  have h₀' : (0 : ℝ) ≤ H.relativeDensity c P := mod_cast H.relativeDensity_nonneg c P
  have h₁' : (H.relativeDensity c P : ℝ) ≤ 1 := mod_cast H.relativeDensity_le_one c P
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

variable (P r) in
/-- A constant coloring is `(δ, r)`-top-regular over every polyad, for every rank and every
positive parameter. -/
theorem isTopRegularOverPolyad_const (c₀ : κ) (hδ : 0 < δ) :
    (const c₀ : Colored3Graph κ V).IsTopRegularOverPolyad P δ r := by
  intro c Q hQ
  obtain hP | hP := P.support.eq_empty_or_nonempty
  · have hU : unionSupport Q = ∅ := subset_empty.1 (hP ▸ unionSupport_subset Q)
    rw [relativeDensity_of_support_eq_empty _ _ hP, hU]
    simpa using hδ.le
  · have hU : (unionSupport Q).Nonempty := by
      rw [← card_pos, ← Nat.cast_pos (α := ℝ)]
      exact (mul_pos hδ (Nat.cast_pos.2 hP.card_pos)).trans_le hQ
    rw [relativeDensity_def]
    by_cases hc : c₀ = c
    · subst hc
      simpa [relDensityOn_const_self hU, relDensityOn_const_self hP] using hδ.le
    · simpa [relDensityOn_const_of_ne hc] using hδ.le

variable (H P) in
/-- `H` is `ε`-vertex-box-regular over the polyad `P` when, for every top color `c` and all
subsets of the three cells of `P` whose restriction of `P` keeps at least an `ε`-fraction of
its support, the relative density of `c` on the restriction is within `ε` of the relative density
of `c` over `P`. The restriction keeps the full pair graphs of `P` between the subsets. -/
def IsVertexBoxRegularOverPolyad (ε : ℝ) : Prop :=
  ∀ (c : κ), ∀ a₀ ⊆ P.c₀, ∀ a₁ ⊆ P.c₁, ∀ a₂ ⊆ P.c₂,
    ε * #P.support ≤ #(ofSubcells P a₀ a₁ a₂).support →
      |(H.relDensityOn c (ofSubcells P a₀ a₁ a₂).support : ℝ) - H.relativeDensity c P| ≤ ε

/-- Unfolded form of `Colored3Graph.IsVertexBoxRegularOverPolyad`, with the restricted support
written as a filter of the support of `P`. -/
theorem isVertexBoxRegularOverPolyad_iff {ε : ℝ} : H.IsVertexBoxRegularOverPolyad P ε ↔
    ∀ (c : κ), ∀ a₀ ⊆ P.c₀, ∀ a₁ ⊆ P.c₁, ∀ a₂ ⊆ P.c₂,
      ε * #P.support ≤ #{x ∈ P.support | x.1 0 ∈ a₀ ∧ x.1 1 ∈ a₁ ∧ x.1 2 ∈ a₂} →
        |(H.relDensityOn c {x ∈ P.support | x.1 0 ∈ a₀ ∧ x.1 1 ∈ a₁ ∧ x.1 2 ∈ a₂} : ℝ) -
          H.relativeDensity c P| ≤ ε := by
  simp only [IsVertexBoxRegularOverPolyad, support_ofSubcells]

/-- Vertex-box regularity is monotone in its parameter. -/
theorem IsVertexBoxRegularOverPolyad.mono {ε ε' : ℝ} (h : H.IsVertexBoxRegularOverPolyad P ε)
    (hε : ε ≤ ε') : H.IsVertexBoxRegularOverPolyad P ε' :=
  fun c a₀ h₀ a₁ h₁ a₂ h₂ hs ↦
    (h c a₀ h₀ a₁ h₁ a₂ h₂ ((mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans hs)).trans
      hε

/-- Top regularity at a positive rank implies vertex-box regularity: a vertex-box restriction is
a single subpolyad. -/
theorem IsTopRegularOverPolyad.isVertexBoxRegularOverPolyad (h : H.IsTopRegularOverPolyad P δ r)
    (hr : 1 ≤ r) : H.IsVertexBoxRegularOverPolyad P δ :=
  fun c _ _ _ _ _ _ hs ↦ isTopRegularOverPolyad_one_iff.1 (h.of_rank_le hr) c _ hs

end Colored3Graph

end TauCeti
