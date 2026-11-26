/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import TauCeti.Analysis.Matrix.Eigenvalues.Basic

/-!
# The sorted Laplacian eigenvalues of a finite simple graph

For a finite simple graph `G` on `n` vertices, `SimpleGraph.lapEigenvalues G : Fin n → ℝ` lists
the eigenvalues of the Laplacian `G.lapMatrix ℝ`, with multiplicity, in nonincreasing order:
index `0` carries the largest eigenvalue `ν₁` and index `n - 1` the smallest `νₙ`. They are
Mathlib's `Matrix.IsHermitian.eigenvalues₀` of the Laplacian.

The Laplacian is positive semidefinite, so all its eigenvalues are nonnegative. Its kernel has
one dimension for every connected component, so its rank is `n` minus the number `c` of
components (`SimpleGraph.rank_lapMatrix_add_card_connectedComponent`). The positive eigenvalues
of a positive-semidefinite matrix are the first `rank` entries of the sorted list, so the
eigenvalue at index `i` vanishes exactly when `n ≤ i + c`
(`SimpleGraph.lapEigenvalues_eq_zero_iff`), and the eigenvalue `0` occurs exactly `c` times
(`SimpleGraph.card_lapEigenvalues_eq_zero`). In particular the smallest eigenvalue is `0`.

The largest eigenvalue `SimpleGraph.largestLapEigenvalue` is the entry at index `0` on a nonempty
vertex type. The algebraic connectivity `SimpleGraph.algebraicConnectivity` is the second smallest
eigenvalue `νₙ₋₁`, at index `n - 2`, and `0` by convention when `n ≤ 1`; for `n ≥ 2` it is
positive exactly when the graph is connected
(`SimpleGraph.algebraicConnectivity_pos_iff_connected`).

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012),
  Proposition 1.3.7 (the multiplicity of the Laplacian eigenvalue `0` is the number of
  connected components).
* M. Fiedler, *Algebraic connectivity of graphs*, Czechoslovak Math. J. 23 (1973).
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The rank of the Laplacian plus the number of connected components is the number of
vertices: the kernel of the Laplacian has one dimension for every connected component. -/
theorem rank_lapMatrix_add_card_connectedComponent :
    (G.lapMatrix ℝ).rank + Fintype.card G.ConnectedComponent = Fintype.card V := by
  rw [card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix, ← finrank_range_mulVecLin,
    ← toLin'_apply', LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-! ### The sorted eigenvalues -/

/-- The Laplacian eigenvalues of `G`, with multiplicity, in nonincreasing order: index `0`
carries the largest one and index `n - 1` the smallest. -/
noncomputable def lapEigenvalues : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀

theorem lapEigenvalues_def :
    G.lapEigenvalues = (G.isHermitian_lapMatrix ℝ).eigenvalues₀ := (rfl)

/-- The Laplacian eigenvalues are listed in nonincreasing order. -/
theorem lapEigenvalues_antitone : Antitone G.lapEigenvalues :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone

/-- The Laplacian eigenvalues are nonnegative. -/
theorem lapEigenvalues_nonneg (i : Fin (Fintype.card V)) : 0 ≤ G.lapEigenvalues i :=
  (posSemidef_lapMatrix ℝ G).eigenvalues₀_nonneg i

/-- The Laplacian eigenvalue at index `i` is positive exactly when `i + c < n`, where `c` is the
number of connected components. -/
theorem lapEigenvalues_pos_iff (i : Fin (Fintype.card V)) :
    0 < G.lapEigenvalues i ↔ (i : ℕ) + Fintype.card G.ConnectedComponent < Fintype.card V := by
  have hrank := G.rank_lapMatrix_add_card_connectedComponent
  exact ((posSemidef_lapMatrix ℝ G).eigenvalues₀_pos_iff i).trans (by omega)

/-- The Laplacian eigenvalue at index `i` vanishes exactly when `n ≤ i + c`, where `c` is the
number of connected components: the zero eigenvalues are the last `c` entries. -/
theorem lapEigenvalues_eq_zero_iff (i : Fin (Fintype.card V)) :
    G.lapEigenvalues i = 0 ↔ Fintype.card V ≤ i + Fintype.card G.ConnectedComponent := by
  have hrank := G.rank_lapMatrix_add_card_connectedComponent
  exact ((posSemidef_lapMatrix ℝ G).eigenvalues₀_eq_zero_iff i).trans (by omega)

/-- The eigenvalue `0` of the Laplacian occurs exactly as often as there are connected
components (Brouwer–Haemers, Proposition 1.3.7). -/
theorem card_lapEigenvalues_eq_zero :
    #{i | G.lapEigenvalues i = 0} = Fintype.card G.ConnectedComponent := by
  have hsplit := card_filter_add_card_filter_not (s := univ)
    (fun i : Fin (Fintype.card V) ↦ G.lapEigenvalues i = 0)
  have hrank := (G.isHermitian_lapMatrix ℝ).rank_eq_card_non_zero_eigenvalues₀
  rw [Fintype.card_subtype, ← lapEigenvalues_def] at hrank
  rw [card_univ, Fintype.card_fin, ← hrank] at hsplit
  have := G.rank_lapMatrix_add_card_connectedComponent
  omega

/-- The smallest Laplacian eigenvalue, at index `n - 1`, is `0`. -/
theorem lapEigenvalues_eq_zero_of_add_one_eq {i : Fin (Fintype.card V)}
    (hi : (i : ℕ) + 1 = Fintype.card V) : G.lapEigenvalues i = 0 := by
  have : Nonempty V := Fintype.card_pos_iff.mp (Fin.pos i)
  have := Fintype.card_pos (α := G.ConnectedComponent)
  exact (G.lapEigenvalues_eq_zero_iff i).mpr (by omega)

/-! ### The largest eigenvalue -/

/-- The largest Laplacian eigenvalue `ν₁` of a graph on a nonempty vertex type, at index `0`. -/
noncomputable def largestLapEigenvalue [Nonempty V] : ℝ :=
  G.lapEigenvalues ⟨0, Fintype.card_pos⟩

theorem largestLapEigenvalue_def [Nonempty V] :
    G.largestLapEigenvalue = G.lapEigenvalues ⟨0, Fintype.card_pos⟩ := (rfl)

/-- Every Laplacian eigenvalue is at most the largest one. -/
theorem lapEigenvalues_le_largestLapEigenvalue [Nonempty V] (i : Fin (Fintype.card V)) :
    G.lapEigenvalues i ≤ G.largestLapEigenvalue :=
  G.lapEigenvalues_antitone (Fin.mk_le_mk.mpr (Nat.zero_le i))

theorem largestLapEigenvalue_nonneg [Nonempty V] : 0 ≤ G.largestLapEigenvalue :=
  G.lapEigenvalues_nonneg _

/-! ### The algebraic connectivity -/

/-- The algebraic connectivity `a(G)`: the second smallest Laplacian eigenvalue `νₙ₋₁`, at
index `n - 2`, when `G` has at least two vertices, and `0` otherwise. -/
noncomputable def algebraicConnectivity : ℝ :=
  if h : 2 ≤ Fintype.card V then G.lapEigenvalues ⟨Fintype.card V - 2, by omega⟩ else 0

theorem algebraicConnectivity_of_two_le (h : 2 ≤ Fintype.card V) :
    G.algebraicConnectivity = G.lapEigenvalues ⟨Fintype.card V - 2, by omega⟩ :=
  dite_eq_left h

theorem algebraicConnectivity_of_lt_two (h : Fintype.card V < 2) :
    G.algebraicConnectivity = 0 :=
  dite_eq_right (by omega)

theorem algebraicConnectivity_nonneg : 0 ≤ G.algebraicConnectivity := by
  unfold algebraicConnectivity
  split_ifs
  exacts [G.lapEigenvalues_nonneg _, le_rfl]

/-- On at least two vertices, the algebraic connectivity is positive exactly when the graph is
connected (Fiedler). -/
theorem algebraicConnectivity_pos_iff_connected (h : 2 ≤ Fintype.card V) :
    0 < G.algebraicConnectivity ↔ G.Connected := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have := Fintype.card_pos (α := G.ConnectedComponent)
  rw [G.algebraicConnectivity_of_two_le h, lapEigenvalues_pos_iff, Fin.val_mk,
    ← card_connectedComponent_eq_one_iff, Nat.card_eq_fintype_card]
  omega

end SimpleGraph
