/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.HookLength.Formula
public import TauCeti.RepresentationTheory.Symmetric.Specht.StandardBasis

/-!
# The hook-length formula for the degrees of the irreducible representations of `Sₙ`

The Specht modules `S^μ` are the irreducible rational representations of `Sₙ`, and the standard
polytabloids are a basis of `S^μ`, so `dim_ℚ S^μ` is the number `f^μ` of standard Young tableaux
of shape `μ` (`TauCeti.finrank_spechtModule`).  The hook-length formula
(`TauCeti.standardCount_mul_prod_hookLength`) computes that number from the shape alone.  This
file transports the combinatorial statement to the representation it counts:

`dim_ℚ S^μ · ∏_{c ∈ μ} hookLength μ c = n !`,

and reads off the quotient form `dim_ℚ S^μ = n ! / ∏ hooks`, over `ℕ` and over `ℚ`.

Nothing new is proved about Specht modules here; the content is the identification of the two
sides, which needs `TauCeti.card_diagramOf` to see the Young diagram of a partition of `n` as a
diagram with `n` cells.  The shapes are written as `TauCeti.diagramOf μ` throughout, matching
`TauCeti.finrank_spechtModule`, because the hook lengths are attached to the diagram and not to
the partition.

## Main results

* `TauCeti.finrank_spechtModule_mul_prod_hookLength`: **the hook-length formula for the dimension
  of a Specht module**, in multiplicative form.
* `TauCeti.finrank_spechtModule_eq_factorial_div_prod_hookLength` and
  `TauCeti.cast_finrank_spechtModule_eq_factorial_div_prod_hookLength`: its quotient form, over
  `ℕ` and over `ℚ`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 20.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10.
-/

public section

open Finset Module Nat

namespace TauCeti

variable {n : ℕ} (μ : n.Partition)

/-- **The hook-length formula for the dimension of a Specht module.** The degree of the
irreducible rational representation `S^μ` of `Sₙ`, times the product of the hook lengths of the
shape `μ`, is `n !`.

This is `TauCeti.standardCount_mul_prod_hookLength` read through
`TauCeti.finrank_spechtModule`, the standard polytabloids being a basis of `S^μ`. It carries no
division obligation; the quotient form is
`TauCeti.finrank_spechtModule_eq_factorial_div_prod_hookLength`. -/
theorem finrank_spechtModule_mul_prod_hookLength :
    finrank ℚ (spechtModule μ) * ∏ c ∈ (diagramOf μ).cells, (diagramOf μ).hookLength c = n ! := by
  rw [finrank_spechtModule, standardCount_mul_prod_hookLength, card_diagramOf]

/-- **The hook-length formula in quotient form**: the degree of `S^μ` is `n !` divided by the
product of the hook lengths of the shape `μ`. The division is exact, by
`YoungDiagram.prod_hookLength_dvd_factorial` at the shape `TauCeti.diagramOf μ`, which has `n`
cells. -/
theorem finrank_spechtModule_eq_factorial_div_prod_hookLength :
    finrank ℚ (spechtModule μ)
      = n ! / ∏ c ∈ (diagramOf μ).cells, (diagramOf μ).hookLength c := by
  rw [finrank_spechtModule, standardCount_eq_factorial_div_prod_hookLength, card_diagramOf]

/-- **The hook-length formula in quotient form over `ℚ`**, the field the Specht modules live
over. -/
theorem cast_finrank_spechtModule_eq_factorial_div_prod_hookLength :
    (finrank ℚ (spechtModule μ) : ℚ)
      = (n ! : ℚ) / ∏ c ∈ (diagramOf μ).cells, ((diagramOf μ).hookLength c : ℚ) := by
  rw [finrank_spechtModule, cast_standardCount_eq_factorial_div_prod_hookLength, card_diagramOf]

end TauCeti
