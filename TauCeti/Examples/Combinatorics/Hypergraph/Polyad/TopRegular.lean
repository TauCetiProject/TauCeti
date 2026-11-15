/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular

/-!
# Regression examples for top regularity over polyads

These downstream examples check the test supports of top regularity through the public API.
Repeating a subpolyad in a family does not double-count its support. A polyad with empty support
is top-regular for every nonnegative parameter and every rank, since every test support is empty.
At parameter `0` the size threshold admits the empty test support, whose relative density is `0`,
so at rank one a constant coloring of a polyad with nonempty support is not top-regular; a positive
parameter is needed in `isTopRegularOverPolyad_const`.
-/

open Finset

namespace TauCeti

open Colored3Graph

variable {κ₂ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}

-- A repeated subpolyad contributes its support once.
example (Q : Subpolyad3 P) : Subpolyad3.unionSupport (fun _ : Fin 2 ↦ Q) = Q.support := by
  ext x
  simp [Subpolyad3.mem_unionSupport]

-- A polyad with empty support is top-regular for every nonnegative parameter and every rank.
example {κ : Type*} [DecidableEq κ] (H : Colored3Graph κ V) (hP : P.support = ∅) {δ : ℝ}
    (hδ : 0 ≤ δ) (r : ℕ) : H.IsTopRegularOverPolyad P δ r := by
  refine isTopRegularOverPolyad_iff.2 fun c Q _ ↦ ?_
  have hQ : Subpolyad3.unionSupport Q = ∅ :=
    subset_empty.1 (hP ▸ Subpolyad3.unionSupport_subset Q)
  simpa [hQ, relativeDensity_of_support_eq_empty _ _ hP] using hδ

-- At parameter `0` the empty test support is admitted, so at rank one a constant coloring of a
-- polyad with nonempty support is not top-regular: the empty support has density `0`, the
-- parent `1`.
example {κ : Type*} [DecidableEq κ] (c : κ) (hP : P.support.Nonempty) :
    ¬ (const c : Colored3Graph κ V).IsTopRegularOverPolyad P 0 1 := by
  intro h
  let Q₀ : Subpolyad3 P := ⟨∅, ∅, ∅, empty_subset _, empty_subset _, empty_subset _⟩
  have hQ₀ : Q₀.support = ∅ := by
    ext x
    simp [Q₀]
  have hpar : (const c : Colored3Graph κ V).relDensityOn c P.support = 1 :=
    relDensityOn_const_self hP
  have := isTopRegularOverPolyad_one_iff.1 h c Q₀ (by simp [hQ₀])
  simp [hQ₀, relativeDensity_def, hpar, not_le.2 (zero_lt_one' ℝ)] at this

end TauCeti
