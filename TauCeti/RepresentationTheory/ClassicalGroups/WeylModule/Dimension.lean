/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Dimension
import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Tableau
public import TauCeti.RepresentationTheory.ClassicalGroups.HookContent
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# The Weyl dimension formula for the rational Weyl modules of `GL n`

Over a field `k` of characteristic zero, the rational Weyl module `TauCeti.rationalWeylFDRep k n λ`
of a dominant weight `λ` (irreducible by `TauCeti.isIrreducible_rationalWeylRep`) has dimension

`dim V_λ = ∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i) = TauCeti.weylDimension λ`.

The two sides were built independently.  The dimension of a Weyl module `𝕊^μ(kⁿ)` is the number
of semistandard tableaux of shape `μ` in the alphabet `{0, …, n - 1}`, read off its character
(`TauCeti.finrank_weylModuleOfShape`), and `TauCeti.weylDimension` is a product formula.  They are
matched through the Gelfand-Tsetlin patterns: the tableaux of shape `μ` are in bijection with the
patterns whose top row is the row-length sequence of `μ` (`TauCeti.gtPatternEquivSSYT`), and those
patterns are counted by the Weyl product (`TauCeti.GTPattern.card_topRow_eq_weylDimension`).  The
determinant twist by `det ^ λₙ` changes neither the dimension nor the Weyl product, so the
polynomial case gives every dominant weight.  Identifying `TauCeti.rationalWeylFDRep k n λ` as the
irreducible representation of highest weight `λ` belongs to the highest-weight classification and
is not claimed here.

For a Young diagram, the hook-content formula `TauCeti.weylDimension_weightOfShape_eq_prod_div`
then expresses the same dimension as a product over the cells of the diagram.  That form needs no
bound on the number of rows: when `μ` has more than `n` rows the Weyl module vanishes, and so does
the factor `n + 0 - n` of the cell `(n, 0)`.

## Main results

* `TauCeti.finrank_weylModuleOfShape_eq_weylDimension`: the Weyl module of a Young diagram with at
  most `n` rows has dimension the Weyl dimension of the weight it determines.
* `TauCeti.finrank_rationalWeylFDRep`: **the Weyl dimension formula** — the rational Weyl module
  of a dominant weight `λ` has dimension `TauCeti.weylDimension λ`.
* `TauCeti.finrank_weylModuleOfShape_eq_prod_div`: **the hook-content formula** for the dimension
  of the Weyl module of a Young diagram, `∏_{(i, j) ∈ μ} (n + j - i) / hookLength μ (i, j)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Theorem 6.3 and
  Exercise 6.4 (the hook-content formula for `𝕊_λ(ℂⁿ)`), and §15.3 (Gelfand-Tsetlin patterns and
  the Weyl dimension formula for `GL n`).
-/

public section

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- **The dimension of a polynomial Weyl module is its Weyl dimension**: for a Young diagram `μ`
with at most `n` rows, the Weyl module `𝕊^μ(kⁿ)` has dimension
`∏_{i < j} (μᵢ - μⱼ + j - i) / (j - i)`, the Weyl dimension of the weight `(μ₀, …, μ_{n-1})`. -/
theorem finrank_weylModuleOfShape_eq_weylDimension {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ n) :
    Module.finrank k (weylModuleOfShape k n μ).toSubmodule =
      weylDimension (weightOfShape n μ) := by
  rw [finrank_weylModuleOfShape, ← card_gtPattern_topRow_eq_card_ssyt n μ hμ,
    ← GTPattern.card_topRow_eq_weylDimension]
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun P => by
    simp only [funext_iff, weightOfShape_apply]

/-- **The Weyl dimension formula for `GL n`**: over a field of characteristic zero, the rational
Weyl module of a dominant weight `λ` has dimension `∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i)`, the
Weyl dimension of `λ`. -/
theorem finrank_rationalWeylFDRep (l : DominantWeight n) :
    Module.finrank k (rationalWeylFDRep k n l) = weylDimension l := by
  rw [finrank_weylModuleOfShape_eq_weylDimension k n l.colLen_zero_detShiftShape_le,
    DominantWeight.weightOfShape_detShiftShape, weylDimension_shift]

/-- **The hook-content formula for the dimension of a Weyl module**: over a field of
characteristic zero, the Weyl module `𝕊^μ(kⁿ)` of a Young diagram `μ` has dimension
`∏_{(i, j) ∈ μ} (n + j - i) / hookLength μ (i, j)`.  No bound on the number of rows is needed:
when `μ` has more than `n` rows both sides vanish, the right-hand side through the cell `(n, 0)`. -/
theorem finrank_weylModuleOfShape_eq_prod_div (μ : YoungDiagram) :
    (Module.finrank k (weylModuleOfShape k n μ).toSubmodule : ℚ) =
      ∏ c ∈ μ.cells, (((n : ℚ) + c.2 - c.1) / μ.hookLength c) := by
  rcases le_or_gt (μ.colLen 0) n with hμ | hμ
  · rw [finrank_weylModuleOfShape_eq_weylDimension k n hμ,
      weylDimension_weightOfShape_eq_prod_div hμ]
  · have := BoundedSSYT.isEmpty_of_lt_colLen hμ
    rw [finrank_weylModuleOfShape, Nat.card_of_isEmpty, Nat.cast_zero, eq_comm]
    refine Finset.prod_eq_zero (i := (n, 0)) ?_ (by simp)
    exact (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_colLen.mpr hμ)

end TauCeti
