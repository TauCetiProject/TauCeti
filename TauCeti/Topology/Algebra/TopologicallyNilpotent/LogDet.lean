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
topologically nilpotent element, and `A` a square matrix over an algebraically closed field `K`
with an algebra map `K → S`. Then `det (1 - a A)`, the reversed characteristic polynomial
`Matrix.charpolyRev A` evaluated at `a`, has the series of traces of the powers of `A` as its
logarithm (`IsTopologicallyNilpotent.hasSum_log_aeval_charpolyRev`):

`log det (1 - a A) = -∑ₖ tr (Aᵏ) aᵏ / k`.

Since `exp` and `log` are mutually inverse on units `u` with `u - 1` topologically nilpotent,
equivalently
`exp (∑ₖ tr (Aᵏ) aᵏ / k) = det (1 - a A)⁻¹`. This is the identity behind the zeta function of a
linear map, the exponential of the logarithmic generating series of the traces of its iterates.

The characteristic polynomial of `A` splits, so `det (1 - X A) = ∏ (1 - λ X)` over the
characteristic roots `λ` of `A`, counted with algebraic multiplicity
(`Matrix.charpolyRev_eq_prod_roots_charpoly`), and `tr (Aᵏ) = ∑ λᵏ`
(`Matrix.trace_aeval_eq_sum_roots_charpoly`). So the identity is the sum over `λ` of the series
`log (1 - λ a) = -∑ₖ λᵏ aᵏ / k` (`IsTopologicallyNilpotent.hasSum_log_one_sub`), since the
logarithm turns finite products of principal units into sums.

## Main results

* `IsTopologicallyNilpotent.hasSum_log_aeval_charpolyRev`: for a matrix `A` over an algebraically
  closed field, `log det (1 - a A) = -∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)`.

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

/-- For a multiset `s` of scalars, `∏_{μ ∈ s} (1 - μ a) - 1` is topologically nilpotent, and the
logarithm of `∏_{μ ∈ s} (1 - μ a)` is `-∑ₖ (∑_{μ ∈ s} μᵏ⁺¹) aᵏ⁺¹ / (k + 1)`. -/
private theorem hasSum_log_prod_one_sub {K : Type*} [CommRing K] [Algebra K S]
    (ha : IsTopologicallyNilpotent a) (s : Multiset K) :
    IsTopologicallyNilpotent ((s.map fun μ ↦ 1 - algebraMap K S μ * a).prod - 1) ∧
      HasSum (fun k : ℕ ↦ -(((k + 1 : ℕ) : ℚ)⁻¹ •
          ((s.map (· ^ (k + 1))).sum • a ^ (k + 1))))
        (NormedSpace.log (s.map fun μ ↦ 1 - algebraMap K S μ * a).prod) := by
  induction s using Multiset.induction_on with
  | empty =>
    simpa [NormedSpace.log_one] using
      And.intro IsTopologicallyNilpotent.zero (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : S)) 0)
  | cons μ s ih =>
    have hμ : IsTopologicallyNilpotent (algebraMap K S μ * a) := ha.mul_left _
    have h1 : IsTopologicallyNilpotent ((1 - algebraMap K S μ * a) - 1) := by simpa using hμ.neg
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [show (1 - algebraMap K S μ * a) * (s.map fun μ ↦ 1 - algebraMap K S μ * a).prod - 1 =
          ((s.map fun μ ↦ 1 - algebraMap K S μ * a).prod - 1) +
            -(algebraMap K S μ * a * (s.map fun μ ↦ 1 - algebraMap K S μ * a).prod) by ring]
      exact ih.1.add (hμ.mul_right _).neg
    · rw [h1.log_mul ih.1]
      convert hμ.hasSum_log_one_sub.add ih.2 using 1
      funext k
      simp only [Multiset.map_cons, Multiset.sum_cons, ← Algebra.smul_def, smul_pow,
        add_smul, smul_add, neg_add]

/-- **The logarithm of `det (1 - a A)`.** For a square matrix `A` over an algebraically closed
field `K` and a topologically nilpotent `a`, the logarithm of `det (1 - a A)` is
`-∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)`. -/
theorem hasSum_log_aeval_charpolyRev {K : Type*} [Field K] [IsAlgClosed K] [Algebra K S]
    {n : Type*} [Fintype n] [DecidableEq n] (ha : IsTopologicallyNilpotent a)
    (A : Matrix n n K) :
    HasSum (fun k : ℕ ↦ -(((k + 1 : ℕ) : ℚ)⁻¹ • ((A ^ (k + 1)).trace • a ^ (k + 1))))
      (NormedSpace.log (aeval a A.charpolyRev)) := by
  have hu : aeval a A.charpolyRev =
      (A.charpoly.roots.map fun μ ↦ 1 - algebraMap K S μ * a).prod := by
    rw [A.charpolyRev_eq_prod_roots_charpoly, map_multiset_prod, Multiset.map_map]
    simp
  have htr (k : ℕ) : (A ^ k).trace = (A.charpoly.roots.map (· ^ k)).sum := by
    simpa using A.trace_aeval_eq_sum_roots_charpoly (X ^ k)
  simpa only [hu, htr] using (ha.hasSum_log_prod_one_sub _).2

end IsTopologicallyNilpotent
