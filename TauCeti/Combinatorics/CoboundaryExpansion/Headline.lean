/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Bridge
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Staircase
public import Mathlib.Tactic.LinearCombination

/-!
# The `Sym(3)` constant of the complete complex is `k/3`

`h1_complete_movedNorm_fin_three` and `h1Norm_complete_movedNorm_fin_three`, for the
definitions of `Defs`.

Route: `Bridge.h1_eq_card` reduces to `Sym3.h1_eq_card_div_three` (Beasley, Theorem 8), which
uses the replicated `k = 4` seed at powers of two and replicated `Sym(3)` staircase seeds on
`K_{2t+1}` elsewhere, with the star bound `Sym3.k_div_three_le_h1`. The staircase seeds are
`Sym(3)`-valued cochains whose gauge distance is proved directly (parity of the gauge, then a cut
count); the `𝔽₂` constant is not used.

Attribution: the seeds are Kozlov's staircase graphs [D. N. Kozlov, arXiv:1610.07136, Def. 3.2
and §3.1]; the cut-minimality bound is proved directly here, following [Kozlov, Lemma 3.8 and
Cor. 3.13] (triangle count after [Kozlov, Lemma 3.10]); the `Sym(3)` transfer (parity retraction)
and the `k/3` theorem are [Beasley, Cor. 7, Thm. 8], concept DOI 10.5281/zenodo.22090958,
current version DOI 10.5281/zenodo.23245792 (the deposit that contains paper_v7.pdf). The Lean
source of this development is
https://github.com/dicipler-pixel/coboundary-k3-lean at commit
`34fac54a6d60eae744e7bc6a849d79c0c09409ad`.
-/

public section

open Finset Equiv Equiv.Perm
open TauCeti.TwoComplex

namespace TauCeti.CoboundaryExpansion

open Bridge

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The permutation coboundary constant of the complete complex is `k/3` for every
`k ≥ 4`, attained with values in `Sym(3)`. -/
theorem h1_complete_movedNorm_fin_three (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  rw [h1_eq_card]
  exact Sym3.h1_eq_card_div_three _ (by omega)

/-- Normalized form: `(k choose 2) / (k choose 3) · k/3 = k/(k-2)`. -/
theorem h1Norm_complete_movedNorm_fin_three (hV : 4 ≤ Fintype.card V) :
    h1Norm (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / (Fintype.card V - 2) := by
  unfold h1Norm
  rw [h1_complete_movedNorm_fin_three hV]
  simp only [card_edges_complete, card_triangles_complete]
  set n := Fintype.card V with hn
  have h3 := Nat.choose_succ_right_eq n 2
  have hpos : 0 < n.choose 3 := Nat.choose_pos (by omega)
  have hR : ((n.choose 3 : ℕ) : ℝ) * 3 = (n.choose 2 : ℝ) * ((n : ℝ) - 2) := by
    have h3' : ((n.choose (2 + 1) * (2 + 1) : ℕ) : ℝ) = ((n.choose 2 * (n - 2) : ℕ) : ℝ) :=
      congrArg _ h3
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)] at h3'
    linarith
  have hC3 : ((n.choose 3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hn2 : (n : ℝ) - 2 ≠ 0 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hV
    linarith
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hC3 (by norm_num)) hn2]
  linear_combination (-(n : ℝ)) * hR

end TauCeti.CoboundaryExpansion
