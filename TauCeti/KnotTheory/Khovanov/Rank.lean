/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.CircleTensor

/-!
# Ranks of the quantum pieces of circle tensors

The degree-`p` piece of the circle tensor `V^{⊗ ι}` of a finite circle set `ι` is free, with basis
the labellings of degree `p` (`TauCeti.Khovanov.circlePieceBasis`). This file computes its rank,
both as a count of labellings and as the coefficient of `q ^ p` in `(q + q⁻¹) ^ |ι|`, the graded
rank of `V^{⊗ ι}`.

For an oriented PD-code `D`, the chain group of the Khovanov complex in bidegree `(i, j)` is the
direct sum, over the states `s` of cochain degree `i`, of the degree-`j` pieces of the shifted
circle tensors `V(Circle s)⟨|S| + n₊ - 2 n₋⟩`, that is, of the degree `j - (|S| + n₊ - 2 n₋)`
pieces of `V(Circle s)`. The graded Euler characteristic of these chain groups is therefore the
signed sum of the ranks of those pieces. `TauCeti.OrientedPDCode.coeff_enhancedStateSum` shows that
this signed sum is the coefficient of `q ^ j` in the enhanced state sum, which is `(q + q⁻¹)` times
the Jones polynomial at `t ^ (1/2) = -q`
(`TauCeti.OrientedPDCode.enhancedStateSum_eq_mul_eval₂_jonesPolynomial`). This is the chain-level
half of the identification of the graded Euler characteristic of Khovanov homology with the Jones
polynomial; Euler–Poincaré for the Khovanov complex supplies the other half.

The ranks are computed over any nontrivial commutative ring, so they apply to the integral
complex and to each of its scalar extensions.

## Main results

* `TauCeti.Khovanov.finrank_circleQuantumGrading_piece`: the degree-`p` piece of the circle tensor
  has rank the number of labellings of degree `p`.
* `TauCeti.Khovanov.coeff_pow_eq_finrank_circleQuantumGrading_piece`: that rank is the
  coefficient of `q ^ p` in `(q + q⁻¹) ^ |ι|`.
* `TauCeti.OrientedPDCode.coeff_enhancedStateSum`: the coefficient of `q ^ j` in the enhanced
  state sum is `∑ₛ (-1) ^ (|S| - n₋) rank V(Circle s)_{j - (|S| + n₊ - 2 n₋)}`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §1.3 and §2.
-/

public section

open LaurentPolynomial Finset

namespace TauCeti

namespace Khovanov

universe u

variable (R : Type u) [CommRing R] [Nontrivial R] {ι : Type*} [Fintype ι]

/-- The degree-`p` piece of the circle tensor has rank the number of labellings of degree `p`. -/
theorem finrank_circleQuantumGrading_piece [DecidableEq ι] (p : ℤ) :
    Module.finrank R ((circleQuantumGrading R ι).piece p) =
      #{l : ι → Bool | labelingQuantumDegree ι l = p} := by
  rw [Module.finrank_eq_card_basis (circlePieceBasis R ι p), Fintype.card_subtype]

/-- **The graded rank of the circle tensor**: the rank of its degree-`p` piece is the coefficient
of `q ^ p` in `(q + q⁻¹) ^ |ι|`. -/
theorem coeff_pow_eq_finrank_circleQuantumGrading_piece (p : ℤ) :
    ((T 1 + T (-1)) ^ Fintype.card ι : ℤ[T;T⁻¹]).coeff p =
      Module.finrank R ((circleQuantumGrading R ι).piece p) := by
  classical
  rw [← sum_T_labelingQuantumDegree, finrank_circleQuantumGrading_piece,
    AddMonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

end Khovanov

namespace OrientedPDCode

variable {n : ℕ}

/-- **The enhanced state sum as a graded Euler characteristic of circle tensors**: the coefficient
of `q ^ j` in the enhanced state sum is the signed sum, over the states `s`, of the ranks of the
degree-`j` pieces of the shifted circle tensors `V(Circle s)⟨|S| + n₊ - 2 n₋⟩`, with sign
`(-1) ^ (|S| - n₋)`. Here `S` is the set of crossings smoothed by `B`, and the ranks may be taken
over any nontrivial commutative ring `R`. -/
theorem coeff_enhancedStateSum (D : OrientedPDCode n) (R : Type*) [CommRing R] [Nontrivial R]
    (j : ℤ) :
    D.enhancedStateSum.coeff j = ∑ s : Fin n → Bool, (D.stateCochainDegree s).negOnePow •
      (Module.finrank R ((Khovanov.circleQuantumGrading R (D.toPDCode.ResolvedCircle s)).piece
        (j - D.stateQuantumShift s)) : ℤ) := by
  classical
  rw [enhancedStateSum_def, Fintype.sum_sigma, AddMonoidAlgebra.coeff_sum,
    Finset.sum_apply']
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Khovanov.finrank_circleQuantumGrading_piece, AddMonoidAlgebra.coeff_sum,
    Finset.sum_apply', Finset.natCast_card_filter, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_smul_apply, T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, enhancedQuantumDegree_def]
  simp only [eq_sub_iff_add_eq']

end OrientedPDCode

end TauCeti
