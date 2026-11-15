/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.ExpLog

/-!
# The logarithm of `det (1 - a A)`

Let `S` be a complete, separated, linearly topologized commutative `ℚ`-algebra, `a : S` a
topologically nilpotent element, and `A` a square matrix over an integral domain `K` with an
algebra map `K → S`, whose characteristic polynomial splits over `K`. Then `det (1 - a A)`, the
reversed characteristic polynomial `Matrix.charpolyRev A` evaluated at `a`, has the series of
traces of the powers of `A` as its logarithm
(`IsTopologicallyNilpotent.hasSum_log_aeval_charpolyRev_of_splits`):

`log det (1 - a A) = -∑ₖ tr (Aᵏ) aᵏ / k`.

Since `exp` and `log` are mutually inverse on units `u` with `u - 1` topologically nilpotent,
equivalently
`exp (∑ₖ tr (Aᵏ) aᵏ / k) = det (1 - a A)⁻¹`. This is the identity behind the zeta function of a
linear map, the exponential of the logarithmic generating series of the traces of its iterates.

Since the characteristic polynomial of `A` splits, `det (1 - X A) = ∏ (1 - λ X)` over the
characteristic roots `λ` of `A`, counted with algebraic multiplicity
(`Matrix.charpolyRev_eq_prod_roots_charpoly_of_splits`), and `tr (Aᵏ) = ∑ λᵏ`
(`Matrix.trace_aeval_eq_sum_roots_charpoly_of_splits`). So the identity is the sum over `λ` of
the series `log (1 - λ a) = -∑ₖ λᵏ aᵏ / k`, since the logarithm turns finite products of principal
units into sums (`IsTopologicallyNilpotent.hasSum_log_prod_one_sub`).

## Main results

* `IsTopologicallyNilpotent.hasSum_log_aeval_charpolyRev_of_splits`: for a matrix `A` over an
  integral domain whose characteristic polynomial splits,
  `log det (1 - a A) = -∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), 369–396.
-/

public section

open Polynomial

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsTopologicalRing S] [IsLinearTopology S S] [T2Space S] [CompleteSpace S] [Algebra ℚ S]

namespace IsTopologicallyNilpotent

variable {a : S}

/-- **The logarithm of `det (1 - a A)`.** For a square matrix `A` over an integral domain `K`
whose characteristic polynomial splits and a topologically nilpotent `a`, the logarithm of
`det (1 - a A)` is `-∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)`. -/
theorem hasSum_log_aeval_charpolyRev_of_splits {K : Type*} [CommRing K] [IsDomain K]
    [Algebra K S] {n : Type*} [Fintype n] [DecidableEq n] (ha : IsTopologicallyNilpotent a)
    {A : Matrix n n K} (hA : A.charpoly.Splits) :
    HasSum (fun k : ℕ ↦ -(((k + 1 : ℕ) : ℚ)⁻¹ • ((A ^ (k + 1)).trace • a ^ (k + 1))))
      (NormedSpace.log (aeval a A.charpolyRev)) := by
  have hu : aeval a A.charpolyRev =
      (A.charpoly.roots.map fun μ ↦ 1 - algebraMap K S μ * a).prod := by
    rw [Matrix.charpolyRev_eq_prod_roots_charpoly_of_splits hA, map_multiset_prod, Multiset.map_map]
    simp
  have htr (k : ℕ) : (A ^ k).trace = (A.charpoly.roots.map (· ^ k)).sum := by
    simpa using Matrix.trace_aeval_eq_sum_roots_charpoly_of_splits hA (X ^ k)
  simpa only [hu, htr] using ha.hasSum_log_prod_one_sub A.charpoly.roots

end IsTopologicallyNilpotent
