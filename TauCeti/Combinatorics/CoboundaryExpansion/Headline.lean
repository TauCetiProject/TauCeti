/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Bridge
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Staircase

/-!
# The `Sym(3)` constant of the complete complex is `k/3`

The general results are `h1_complete_movedNorm_fin_three_of_three_le` and
`h1Norm_complete_movedNorm_fin_three_of_three_le`, for every `k = card V ≥ 3`. The theorems
`h1_complete_movedNorm_fin_three` and `h1Norm_complete_movedNorm_fin_three` keep the
hypothesis `4 ≤ card V` and follow in one line each.

Route: `Bridge.h1_eq_card` reduces to `Sym3.h1_eq_card_div_three`, which uses the replicated
`k = 4` seed at powers of two and replicated `Sym(3)` staircase seeds on `K_{2t+1}`
elsewhere, with the star bound `Sym3.k_div_three_le_h1`. Kozlov's `𝔽₂` constant is not used
as a hypothesis; instead Kozlov's staircase witnesses [Kozlov, Cor. 4.5] are built and
checked directly in Lean: their `Sym(3)` gauge distance is proved here (parity of the gauge,
then a cut count).

Attribution: the seeds are Kozlov's staircase graphs [D. N. Kozlov, arXiv:1610.07136, Def. 3.2,
§3.1, Cor. 4.5, giving Thm. 4.2 and Cor. 4.3]; the cut-minimality bound is proved directly
here, following [Kozlov, Lemma 3.8 and Cor. 3.13] (triangle count after [Kozlov, Lemma 3.10]).
The `Sym(3)` transfer (parity retraction) and the `k/3` theorem for `k ≥ 4` are [Beasley, Cor.
7, Thm. 8], concept DOI 10.5281/zenodo.22090958, current version DOI 10.5281/zenodo.23245792
(the deposit that contains paper_v7.pdf). The case `k = 3` (the single-triangle staircase on
`K_3`) is not covered by [Beasley, Thm. 8] and is proved in this development. The Lean source
of this development is https://github.com/dicipler-pixel/coboundary-k3-lean at commit
`34fac54a6d60eae744e7bc6a849d79c0c09409ad`.
-/

public section

open Finset Equiv Equiv.Perm
open TauCeti.TwoComplex

namespace TauCeti.CoboundaryExpansion

open Bridge

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The permutation coboundary constant of the complete complex is `k/3` for every
`k ≥ 3`, attained with values in `Sym(3)`. For `k ≥ 4` this is [Beasley, Thm. 8]; the case
`k = 3` is proved here. -/
theorem h1_complete_movedNorm_fin_three_of_three_le (hV : 3 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  rw [h1_eq_card]
  exact Sym3.h1_eq_card_div_three _ hV

/-- Normalized form for every `k ≥ 3`: `(k choose 2) / (k choose 3) · k/3 = k/(k-2)`. -/
theorem h1Norm_complete_movedNorm_fin_three_of_three_le (hV : 3 ≤ Fintype.card V) :
    h1Norm (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / (Fintype.card V - 2) := by
  rw [h1Norm_def, h1_complete_movedNorm_fin_three_of_three_le hV, natCast_card_edges_complete,
    natCast_card_triangles_complete]
  have : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  field_simp [show (Fintype.card V : ℝ) - 1 ≠ 0 by linarith,
    show (Fintype.card V : ℝ) - 2 ≠ 0 by linarith]
  ring

/-- The permutation coboundary constant of the complete complex is `k/3` for every
`k ≥ 4`, attained with values in `Sym(3)`. A corollary of
`h1_complete_movedNorm_fin_three_of_three_le`. -/
theorem h1_complete_movedNorm_fin_three (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 :=
  h1_complete_movedNorm_fin_three_of_three_le (by omega)

/-- Normalized form for every `k ≥ 4`: `(k choose 2) / (k choose 3) · k/3 = k/(k-2)`. -/
theorem h1Norm_complete_movedNorm_fin_three (hV : 4 ≤ Fintype.card V) :
    h1Norm (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / (Fintype.card V - 2) :=
  h1Norm_complete_movedNorm_fin_three_of_three_le (by omega)

end TauCeti.CoboundaryExpansion
