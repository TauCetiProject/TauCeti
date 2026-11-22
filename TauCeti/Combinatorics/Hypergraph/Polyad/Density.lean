/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Density
public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relative color densities over polyads

`H.relativeDensity c P` is the relative density `H.relDensityOn c P.support` of the color `c` over
the computed support of the polyad `P`: the fraction of the supported role-ordered injective
triples whose underlying unordered triple has color `c`. It inherits the bounds, the value `0` on
an empty support, and the sum to one over colors on a nonempty support.

## Main definitions

* `TauCeti.Colored3Graph.relativeDensity`: the relative density of a color over a polyad.

## Main results

* `TauCeti.Colored3Graph.sum_relativeDensity`: over a polyad with nonempty support, the densities
  of all colors sum to one.
* `TauCeti.Colored3Graph.relDensityOn_sub_mul_card_eq_sum_inter_support`: the count-scaled
  deviation of a color density on a set of triples splits over the polyads of any skeleton.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_mul_card_le_sum_polyadMap` and
  `TauCeti.Colored3Graph.abs_relativeDensity_sub_mul_card_support_le_of_polyadMap`: along any map
  `π : Polyad3 T → Polyad3 S`, count-scaled deviations on `W ⊆ P.support` and of
  `H.relativeDensity c P` from `a ∈ [0, 1]` are controlled by the fiber `π Q = P` and moved
  triples.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V] {κ₂ : Type*}
  {S : PairSkeleton3 κ₂ V}

/-- The relative density of the color `c` over the support of a polyad. -/
noncomputable def relativeDensity (H : Colored3Graph κ V) (c : κ) (P : Polyad3 S) : ℚ :=
  H.relDensityOn c P.support

/-- The relative density over a polyad is the relative density over its support. -/
theorem relativeDensity_def (H : Colored3Graph κ V) (c : κ) (P : Polyad3 S) :
    H.relativeDensity c P = H.relDensityOn c P.support :=
  (rfl)

/-- Relative densities over a polyad are nonnegative. -/
theorem relativeDensity_nonneg (H : Colored3Graph κ V) (c : κ) (P : Polyad3 S) :
    0 ≤ H.relativeDensity c P :=
  H.relDensityOn_nonneg c P.support

/-- Relative densities over a polyad are at most one. -/
theorem relativeDensity_le_one (H : Colored3Graph κ V) (c : κ) (P : Polyad3 S) :
    H.relativeDensity c P ≤ 1 :=
  H.relDensityOn_le_one c P.support

/-- The relative density on any set of triples and the relative density over a polyad differ
by at most one, since both lie in `[0, 1]`. -/
theorem abs_relDensityOn_sub_relativeDensity_le_one (H : Colored3Graph κ V) (c : κ)
    (s : Finset {x : Fin 3 → V // Function.Injective x}) (P : Polyad3 S) :
    |(H.relDensityOn c s : ℝ) - H.relativeDensity c P| ≤ 1 :=
  abs_sub_le_of_nonneg_of_le (mod_cast H.relDensityOn_nonneg c s)
    (mod_cast H.relDensityOn_le_one c s) (mod_cast H.relativeDensity_nonneg c P)
    (mod_cast H.relativeDensity_le_one c P)

/-- Every relative density over a polyad with empty support is `0`. -/
theorem relativeDensity_of_support_eq_empty (H : Colored3Graph κ V) (c : κ) {P : Polyad3 S}
    (hP : P.support = ∅) : H.relativeDensity c P = 0 := by
  rw [relativeDensity_def, hP, relDensityOn_empty]

/-- The relative densities of all colors over a polyad with nonempty support sum to one. -/
theorem sum_relativeDensity [Fintype κ] (H : Colored3Graph κ V) {P : Polyad3 S}
    (hP : P.support.Nonempty) : ∑ c, H.relativeDensity c P = 1 :=
  H.sum_relDensityOn hP

variable (S) in
/-- The count-scaled deviation of a color density on a finite set of injective triples from a
constant splits over the polyads of any lower skeleton. -/
theorem relDensityOn_sub_mul_card_eq_sum_inter_support [Fintype κ₂] (H : Colored3Graph κ V)
    (c : κ) (s : Finset {x : Fin 3 → V // Function.Injective x}) (a : ℝ) :
    ((H.relDensityOn c s : ℝ) - a) * #s =
      ∑ P : Polyad3 S, ((H.relDensityOn c (s ∩ P.support) : ℝ) - a) * #(s ∩ P.support) := by
  have hcount (t : Finset {x : Fin 3 → V // Function.Injective x}) :
      (H.relDensityOn c t : ℝ) * #t =
        #{x ∈ t | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} := by
    exact_mod_cast H.relDensityOn_mul_card c t
  simp_rw [sub_mul, hcount, ← filter_inter]
  rw [sum_sub_distrib, ← mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, Polyad3.sum_card_inter_support,
    Polyad3.sum_card_inter_support]

open Classical in
/-- For `W ⊆ P.support` and `a ∈ [0, 1]`, fine polyads `Q` with `π Q ≠ P` contribute at most the
moved triples inside `P.support`. -/
private theorem sum_abs_relDensityOn_inter_ne_polyadMap_le {κ₂' : Type*} [Fintype κ₂']
    {T : PairSkeleton3 κ₂' V} (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S)
    {P : Polyad3 S} {W : Finset {x : Fin 3 → V // Function.Injective x}} (hWP : W ⊆ P.support)
    (c : κ) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∑ Q : Polyad3 T with π Q ≠ P,
        |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| ≤
      #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  have hQ (Q : Polyad3 T) (hπ : π Q ≠ P) :
      |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| ≤
        #((M ∩ P.support) ∩ Q.support) := by
    have hd : |(H.relDensityOn c (W ∩ Q.support) : ℝ) - a| ≤ 1 :=
      abs_sub_le_of_nonneg_of_le (mod_cast H.relDensityOn_nonneg _ _)
        (mod_cast H.relDensityOn_le_one _ _) ha₀ ha₁
    have hsub : W ∩ Q.support ⊆ (M ∩ P.support) ∩ Q.support :=
      (inter_subset_inter hWP Subset.rfl).trans
        (subset_inter (subset_inter (Polyad3.inter_support_subset_filter_ofTriple_ne hπ)
          inter_subset_left) inter_subset_right)
    rw [abs_mul, Nat.abs_cast]
    exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hd).trans (Nat.cast_le.2 (card_le_card hsub))
  calc ∑ Q : Polyad3 T with π Q ≠ P,
          |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)|
      ≤ ∑ Q : Polyad3 T with π Q ≠ P, (#((M ∩ P.support) ∩ Q.support) : ℝ) :=
        sum_le_sum fun Q h ↦ hQ Q (mem_filter.1 h).2
    _ ≤ ∑ Q : Polyad3 T, (#((M ∩ P.support) ∩ Q.support) : ℝ) :=
        sum_le_univ_sum_of_nonneg fun _ ↦ Nat.cast_nonneg _
    _ = #(M ∩ P.support) := by
        exact_mod_cast Polyad3.sum_card_inter_support (S := T) (M ∩ P.support)

open Classical in
/-- For any subset `W ⊆ P.support`, map `π : Polyad3 T → Polyad3 S`, and `a ∈ [0, 1]`, the
count-scaled deviation of `H.relDensityOn c W` from `a` is bounded by the count-scaled deviations
on `W ∩ Q.support` over fine children `π Q = P`, plus the moved triples inside `P.support`. -/
theorem abs_relDensityOn_sub_mul_card_le_sum_polyadMap {κ₂' : Type*} [Fintype κ₂']
    {T : PairSkeleton3 κ₂' V} (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S)
    {P : Polyad3 S} {W : Finset {x : Fin 3 → V // Function.Injective x}} (hWP : W ⊆ P.support)
    (c : κ) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    |((H.relDensityOn c W : ℝ) - a) * #W| ≤
      ∑ Q : Polyad3 T with π Q = P,
          |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| +
        #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) := by
  calc |((H.relDensityOn c W : ℝ) - a) * #W|
      = |∑ Q : Polyad3 T, ((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| := by
        rw [← H.relDensityOn_sub_mul_card_eq_sum_inter_support T]
    _ ≤ ∑ Q : Polyad3 T, |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ Q : Polyad3 T with π Q = P,
          |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| +
        ∑ Q : Polyad3 T with π Q ≠ P,
          |((H.relDensityOn c (W ∩ Q.support) : ℝ) - a) * #(W ∩ Q.support)| :=
        (sum_filter_add_sum_filter_not _ (fun Q : Polyad3 T ↦ π Q = P) _).symm
    _ ≤ _ := add_le_add le_rfl
        (sum_abs_relDensityOn_inter_ne_polyadMap_le H π hWP c ha₀ ha₁)

open Classical in
/-- On a fine child `Q` with `π Q = P`, replacing `P.support ∩ Q.support` by `Q.support` in the
count-scaled deviation from `a` costs at most the moved triples inside `Q.support`. -/
private theorem abs_relDensityOn_inter_support_sub_mul_card_le {κ₂' : Type*}
    {T : PairSkeleton3 κ₂' V} (H : Colored3Graph κ V) {π : Polyad3 T → Polyad3 S}
    {P : Polyad3 S} {Q : Polyad3 T} (hπ : π Q = P) (c : κ) (a : ℝ) :
    |((H.relDensityOn c (P.support ∩ Q.support) : ℝ) - a) * #(P.support ∩ Q.support)| ≤
      #Q.support * |(H.relativeDensity c Q : ℝ) - a| +
        #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ Q.support) := by
  set I := P.support ∩ Q.support
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)}
  have hIQ : (#I : ℝ) ≤ #Q.support := Nat.cast_le.2 (card_le_card inter_subset_right)
  have hI₀ : (0 : ℝ) ≤ #I := Nat.cast_nonneg _
  have hsdiff : |(H.relDensityOn c I : ℝ) - H.relDensityOn c Q.support| * #I ≤
      #(M ∩ Q.support) := by
    have hd : |(H.relDensityOn c I : ℝ) - H.relDensityOn c Q.support| * #I ≤
        (#(I \ Q.support) : ℝ) + #(Q.support \ I) := by
      exact_mod_cast H.abs_relDensityOn_sub_mul_card_le c I Q.support
    have h₁ : I \ Q.support = ∅ := sdiff_eq_empty_iff_subset.2 inter_subset_right
    have h₂ : Q.support \ I ⊆ M ∩ Q.support := by
      rw [sdiff_inter_self_right]
      exact subset_inter (Polyad3.support_sdiff_subset_filter_ofTriple_ne hπ) sdiff_subset
    rw [h₁, card_empty, Nat.cast_zero, zero_add] at hd
    exact hd.trans (Nat.cast_le.2 (card_le_card h₂))
  calc |((H.relDensityOn c I : ℝ) - a) * #I|
      = |((H.relDensityOn c I : ℝ) - H.relDensityOn c Q.support) * #I +
          ((H.relativeDensity c Q : ℝ) - a) * #I| := by rw [relativeDensity_def]; ring_nf
    _ ≤ |(H.relDensityOn c I : ℝ) - H.relDensityOn c Q.support| * #I +
          |(H.relativeDensity c Q : ℝ) - a| * #I := by
        grw [abs_add_le, abs_mul, abs_mul, abs_of_nonneg hI₀]
    _ ≤ #(M ∩ Q.support) + #Q.support * |(H.relativeDensity c Q : ℝ) - a| :=
        add_le_add hsdiff (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hIQ (abs_nonneg _))
    _ = #Q.support * |(H.relativeDensity c Q : ℝ) - a| + #(M ∩ Q.support) := add_comm _ _

open Classical in
/-- **Coarse polyad density vs a reference target.** For any map `π : Polyad3 T → Polyad3 S` and
`a ∈ [0, 1]`, the count-scaled deviation of `H.relativeDensity c P` from `a` is bounded by the
support-weighted deviations of `H.relativeDensity c Q` from `a` over fine children `π Q = P`, plus
the moved triples in those children and in `P.support`. No regularity of `H` over `Q` is required.
-/
theorem abs_relativeDensity_sub_mul_card_support_le_of_polyadMap {κ₂' : Type*} [Fintype κ₂']
    {T : PairSkeleton3 κ₂' V} (H : Colored3Graph κ V) (π : Polyad3 T → Polyad3 S)
    (P : Polyad3 S) (c : κ) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    |(H.relativeDensity c P : ℝ) - a| * #P.support ≤
      ∑ Q : Polyad3 T with π Q = P, #Q.support * |(H.relativeDensity c Q : ℝ) - a| +
        ∑ Q : Polyad3 T with π Q = P,
          (#(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ Q.support) : ℝ) +
        #(({x | Polyad3.ofTriple S x ≠ π (Polyad3.ofTriple T x)} : Finset _) ∩ P.support) := by
  have h₁ := H.abs_relDensityOn_sub_mul_card_le_sum_polyadMap π (P := P) Subset.rfl c ha₀ ha₁
  have h₂ := (sum_le_sum (s := univ.filter fun Q : Polyad3 T ↦ π Q = P)
    fun Q h ↦ abs_relDensityOn_inter_support_sub_mul_card_le H (mem_filter.1 h).2 c a).trans_eq
    sum_add_distrib
  rw [relativeDensity_def, ← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) #P.support), ← abs_mul]
  linarith

end Colored3Graph

end TauCeti
