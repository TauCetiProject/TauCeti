/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Relative color densities over supports of injective triples

For a coloring `H` of the unordered triples of `V`, the relative density `H.relDensityOn c supp`
of a color `c` over a finite support of injective triples is the fraction of the supported
triples whose underlying unordered triple has color `c`. Colors are read through the underlying
unordered triple, while the normalization counts the supported ordered injections, so a triple
contributes once for each of its supported orderings, both to the count and to the normalization.
The relative density is `0` on the empty support.

Relative densities lie between `0` and `1`, and on a nonempty support the densities of all colors
sum to one.

## Main definitions

* `TauCeti.Colored3Graph.relDensityOn`: the relative density of a color over a support.

## Main results

* `TauCeti.Colored3Graph.sum_relDensityOn`: on a nonempty support the densities sum to one.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ]

/-- The relative density of the color `c` over a finite support of injective triples: the fraction
of supported triples whose underlying unordered triple has color `c`. It is `0` on the empty
support. -/
def relDensityOn (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : ℚ :=
  #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} / #supp

/-- The relative density counts supported triples whose underlying triple has color `c`. -/
theorem relDensityOn_def (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.relDensityOn c supp =
      #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} / #supp :=
  (rfl)

/-- Relative densities are nonnegative. -/
theorem relDensityOn_nonneg (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : 0 ≤ H.relDensityOn c supp := by
  rw [relDensityOn_def]
  positivity

/-- Relative densities are at most one. -/
theorem relDensityOn_le_one (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : H.relDensityOn c supp ≤ 1 := by
  rw [relDensityOn_def]
  exact div_le_one_of_le₀ (mod_cast card_filter_le _ _) (by positivity)

/-- Every relative density over the empty support is `0`. -/
@[simp]
theorem relDensityOn_empty (H : Colored3Graph κ V) (c : κ) : H.relDensityOn c ∅ = 0 := by
  simp [relDensityOn_def]

/-- The relative density of the color of a constant coloring is one on a nonempty support. -/
theorem relDensityOn_const_self {c : κ} {supp : Finset {x : Fin 3 → V // Function.Injective x}}
    (h : supp.Nonempty) : (const c : Colored3Graph κ V).relDensityOn c supp = 1 := by
  rw [relDensityOn_def, div_eq_one_iff_eq (by exact_mod_cast h.card_pos.ne')]
  simp

/-- The relative density of any other color of a constant coloring is zero. -/
@[simp]
theorem relDensityOn_const_of_ne {c₀ c : κ} (h : c₀ ≠ c)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    (const c₀ : Colored3Graph κ V).relDensityOn c supp = 0 := by
  simp [relDensityOn_def, h]

/-- **The relative densities of all colors sum to one** on a nonempty support. -/
theorem sum_relDensityOn [Fintype κ] (H : Colored3Graph κ V)
    {supp : Finset {x : Fin 3 → V // Function.Injective x}} (h : supp.Nonempty) :
    ∑ c, H.relDensityOn c supp = 1 := by
  simp only [relDensityOn_def, ← sum_div]
  rw [div_eq_one_iff_eq (by exact_mod_cast h.card_pos.ne')]
  -- Every supported triple has exactly one color.
  exact_mod_cast (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm

end Colored3Graph

end TauCeti
