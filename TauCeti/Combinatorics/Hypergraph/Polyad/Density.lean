/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Density
public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import Mathlib.Data.Rat.Cast.Order

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
        #{x ∈ t | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
    exact_mod_cast H.relDensityOn_mul_card c t
  simp_rw [sub_mul, hcount, ← filter_inter]
  rw [sum_sub_distrib, ← mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, Polyad3.sum_card_inter_support,
    Polyad3.sum_card_inter_support]

end Colored3Graph

end TauCeti
