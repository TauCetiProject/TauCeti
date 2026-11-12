/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MorseInequalities
public import TauCeti.Geometry.Manifold.Morse.CWModel
import TauCeti.Geometry.Manifold.Morse.Cell.Band
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# The Morse polynomial identity with Betti numbers

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `m`, with `cⱼ`
critical points of index `j`, and let `bⱼ = bettiNumber k M j` be the Betti numbers of `M` over a
division ring `k`. The **Morse polynomial identity** says that

`∑ⱼ cⱼ tʲ = ∑ⱼ bⱼ tʲ + (1 + t) Q(t)`

for a polynomial `Q` with natural number coefficients and degree below `m`
(`TauCeti.IsMorse.exists_criticalCount_eq_bettiNumber_add_coeff`). It is stated coefficientwise,
with the critical counts in `ℕ∞`, so it includes the finiteness of every count; above `m` both
counts vanish (`TauCeti.criticalCount_eq_zero_of_finrank_lt` and
`TauCeti.bettiNumber_eq_zero_of_finrank_lt`). Since `1 + t` is not a zero divisor, `Q` is
determined by the identity, and its coefficient of `tⁿ` is the gap
`(cₙ - cₙ₋₁ + ⋯ ± c₀) - (bₙ - bₙ₋₁ + ⋯ ± b₀)` in the `n`-th strong Morse inequality, as recorded in
`TauCeti.IsMorse.exists_sum_range_monomial_eq_add_mul`.

The coefficients of `Q` are ranks of cellular differentials. The manifold `M` is homotopy
equivalent to a finite CW complex `W` with one `j`-cell for each critical point of index `j`
(`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`), and for this model the coefficient of
`tⁱ` in `Q` may be taken to be the rank of the cellular differential of `W` with coefficients in
`k` from degree `i + 1` to degree `i`
(`TauCeti.IsMorse.exists_cwComplex_criticalCount_eq_bettiNumber_add_coeff`). This is the
polynomial identity of the cellular chain complex of `W`
(`TauCeti.natCard_cell_eq_bettiNumber_add_coeff_of_cwComplex`), transported to `M` by homotopy
invariance of Betti numbers.

## Main results

* `TauCeti.bettiNumber_eq_zero_of_finrank_lt`: the Betti numbers of a compact boundaryless
  manifold vanish above its dimension.
* `TauCeti.IsMorse.exists_cwComplex_criticalCount_eq_bettiNumber_add_coeff`: the Morse polynomial
  identity, with the coefficients of `Q` the ranks of the cellular differentials of a CW model of
  `M` with one cell for each critical point.
* `TauCeti.IsMorse.exists_criticalCount_eq_bettiNumber_add_coeff`: **the Morse polynomial
  identity** `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)`, coefficientwise in `ℕ∞`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory: Lecture Notes*, Corollary 5.11 and
  its proof.
-/

public section

noncomputable section

open Module Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped Manifold ContDiff ContinuousMap Polynomial

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

variable (I M) in
include I in
omit [FiniteDimensional ℝ E] in
/-- **The Betti numbers of a compact manifold vanish above its dimension.** For a compact
boundaryless manifold `M` of dimension `m` and a nontrivial ring `k`, `bⱼ(M; k) = 0` for `j > m`:
a Morse function on `M` has no critical points of index above `m`. -/
theorem bettiNumber_eq_zero_of_finrank_lt (k : Type u) [Ring k] [Nontrivial k] {j : ℕ}
    (hj : finrank ℝ E < j) : bettiNumber k M j = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  have := ModuleCat.isZero_iff_subsingleton.1
    (hf.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le
      (fun _ _ ↦ manifoldMorseIndex_le_finrank) (ModuleCat.of k k) hj)
  rw [bettiNumber_def]
  exact finrank_zero_of_subsingleton

/-- **The Morse polynomial identity, with the cellular coefficients.** A compact boundaryless
manifold `M` with a Morse function `f` is homotopy equivalent to a finite CW complex `W` with one
`j`-cell for each critical point of `f` of index `j`. For every division ring `k` and every degree
`j`, the number `cⱼ` of critical points of index `j` is then the Betti number `bⱼ(M; k)` plus the
coefficient of `tʲ` in `(1 + t) Q(t)`, where the coefficient of `tⁱ` in `Q` is the rank of the
cellular differential of `W` with coefficients in `k` from degree `i + 1` to degree `i`, for `i`
below the dimension of `M`, and zero otherwise. -/
theorem IsMorse.exists_cwComplex_criticalCount_eq_bettiNumber_add_coeff (hf : IsMorse I f) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ M) ∧
      (∀ m, ENat.card (cell (univ : Set W) m) = criticalCount I f m) ∧
      ∀ (k : Type u) [DivisionRing k] (j : ℕ), criticalCount I f j =
        (bettiNumber k M j + ((1 + X) * ∑ i ∈ Finset.range (finrank ℝ E), monomial i (finrank k
          (LinearMap.range ((cellularChainComplex (univ : Set W) (ModuleCat.of k k)).d (i + 1)
            i).hom))).coeff j : ℕ) := by
  obtain ⟨W, _, _, _, _, ⟨e⟩, hcell⟩ := hf.exists_finite_cwComplex_homotopyEquiv
  have hcount (m : ℕ) : ENat.card (cell (univ : Set W) m) = criticalCount I f m := by
    obtain ⟨c⟩ := hcell m
    rw [ENat.card_congr c, ENat.card_coe_set_eq, criticalCount_def]
  refine ⟨W, _, ‹_›, ‹_›, ‹_›, ⟨e⟩, hcount, fun k _ j ↦ ?_⟩
  have hfinite (i : ℕ) : Finite (cell (univ : Set W) i) := FiniteType.finite_cell i
  have := hfinite j
  have hempty (i : ℕ) (hi : finrank ℝ E < i) : IsEmpty (cell (univ : Set W) i) := by
    rw [← ENat.card_eq_zero_iff_empty, hcount, criticalCount_eq_zero_of_finrank_lt hi]
  rw [← hcount, ENat.card_eq_coe_natCard,
    natCard_cell_eq_bettiNumber_add_coeff_of_cwComplex (k := k) (univ : Set W)
      (fun i _ ↦ hfinite i) hempty j,
    ((Homeomorph.Set.univ W).toHomotopyEquiv.trans e).bettiNumber_eq k j]

/-- **The Morse polynomial identity.** Let `f` be a Morse function on a compact boundaryless
manifold `M` of dimension `m`, with `cⱼ` critical points of index `j`, and let `bⱼ` be the Betti
numbers of `M` over a division ring `k`. Then `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)` for a polynomial
`Q` with natural number coefficients and degree below `m`. The identity is stated coefficientwise,
with the critical counts in `ℕ∞`, so that it includes the finiteness of every count. -/
theorem IsMorse.exists_criticalCount_eq_bettiNumber_add_coeff (hf : IsMorse I f) (k : Type u)
    [DivisionRing k] :
    ∃ Q : ℕ[X], Q.degree < finrank ℝ E ∧
      ∀ j, criticalCount I f j = (bettiNumber k M j + ((1 + X) * Q).coeff j : ℕ) := by
  obtain ⟨W, _, _, _, -, -, -, h⟩ := hf.exists_cwComplex_criticalCount_eq_bettiNumber_add_coeff
  refine ⟨_, ?_, h k⟩
  refine Polynomial.degree_lt_iff_coeff_zero _ _ |>.2 fun i hi ↦ ?_
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  exact Finset.sum_eq_zero fun l hl ↦ by grind

end TauCeti
