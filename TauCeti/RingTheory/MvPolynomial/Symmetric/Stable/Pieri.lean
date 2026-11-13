/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.Combinatorics.Young.VerticalStrip
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Omega
import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Pieri
import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.JacobiTrudi

/-!
# The Pieri rules in the symmetric functions

In the ring `Λ_R` of symmetric functions, multiplying a Schur function by `h_r` adds horizontal
strips and multiplying it by `e_r` adds vertical strips:

`h_r · s_ν = ∑_μ s_μ` and `e_r · s_ν = ∑_μ s_μ`,

the first sum running over the partitions `μ` of `|ν| + r` whose Young diagram interlaces that of
`ν` (the skew shape `μ / ν` is a horizontal strip), the second over those for which `μ / ν` is a
vertical strip.

The involution `ω` exchanges the two rules. It sends `h_r` to `e_r` and `s_μ` to `s_(μᵗ)`
(`TauCeti.SymmetricFunction.omega_of_stableSchur`), and a skew shape is a vertical strip exactly
when its transpose is a horizontal strip
(`YoungDiagram.isVerticalStrip_iff_interlacedBy_transpose`).
So applying `ω` to either rule for `νᵗ` and reindexing the sum by conjugation gives the other rule
for `ν`. Here the horizontal-strip rule descends from the Pieri rule in finitely many variables,
`TauCeti.hsymm_mul_schurPoly`, and the vertical-strip rule is recovered from it under `ω`.

## Main results

* `TauCeti.SymmetricFunction.of_stableHsymm_mul_of_stableSchur`: **the Pieri rule**
  `h_r · s_ν = ∑ s_μ` over horizontal strips.
* `TauCeti.SymmetricFunction.of_stableEsymm_mul_of_stableSchur`: **the dual Pieri rule**
  `e_r · s_ν = ∑ s_μ` over vertical strips.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (5.16) and (5.17).
-/

public section

namespace TauCeti

open MvPolynomial DirectSum YoungDiagram

namespace SymmetricFunction

open scoped Classical in
/-- **The Pieri rule** in the symmetric functions: for a partition `ν` of `n` and every `r`,
`h_r · s_ν = ∑_μ s_μ`, the sum running over the partitions `μ` of `n + r` whose Young diagram
contains that of `ν` with a horizontal strip as complement. -/
theorem of_stableHsymm_mul_of_stableSchur {R : Type*} [CommSemiring R] {n : ℕ}
    (ν : n.Partition) (r : ℕ) :
    DirectSum.of _ r (stableHsymm R r) * DirectSum.of _ n (stableSchur R ν) =
      ∑ μ : (n + r).Partition with (ofPartition μ).InterlacedBy (ofPartition ν),
        (DirectSum.of _ (n + r) (stableSchur R μ) : SymmetricFunction R) :=
  ext_specialization fun d => by
    simp only [map_mul, map_sum, specialization_of, coe_stableSymmetricProj_stableHsymm,
      coe_stableSymmetricProj_stableSchur]
    -- The finite rule is stated with the classical decidable equality on the alphabet, so the two
    -- `hsymm (Fin d)` differ only in that instance.
    convert hsymm_mul_schurPoly (R := R) (σ := Fin d) ν r using 3

open scoped Classical in
/-- **The dual Pieri rule** in the symmetric functions: for a partition `ν` of `n` and every `r`,
`e_r · s_ν = ∑_μ s_μ`, the sum running over the partitions `μ` of `n + r` whose Young diagram
contains that of `ν` with a vertical strip as complement. -/
theorem of_stableEsymm_mul_of_stableSchur {R : Type*} [CommRing R] {n : ℕ}
    (ν : n.Partition) (r : ℕ) :
    DirectSum.of _ r (stableEsymm R r) * DirectSum.of _ n (stableSchur R ν) =
      ∑ μ : (n + r).Partition with (ofPartition μ).IsVerticalStrip (ofPartition ν),
        (DirectSum.of _ (n + r) (stableSchur R μ) : SymmetricFunction R) := by
  -- Apply `ω` to the Pieri rule for `νᵗ`, then reindex the sum by conjugation, which matches
  -- the horizontal strips over `νᵗ` with the vertical strips over `ν`.
  have h := congrArg (omega R) (of_stableHsymm_mul_of_stableSchur (R := R) ν.conjugate r)
  rw [map_mul, omega_of_stableHsymm, omega_of_stableSchur, Nat.Partition.conjugate_conjugate,
    map_sum] at h
  rw [h]
  refine Finset.sum_nbij' Nat.Partition.conjugate Nat.Partition.conjugate ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ ⊢
    rwa [isVerticalStrip_iff_interlacedBy_transpose, ← ofPartition_conjugate,
      ← ofPartition_conjugate, Nat.Partition.conjugate_conjugate]
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ ⊢
    rwa [isVerticalStrip_iff_interlacedBy_transpose, ← ofPartition_conjugate,
      ← ofPartition_conjugate] at hμ
  · intro μ _
    exact Nat.Partition.conjugate_conjugate μ
  · intro μ _
    exact Nat.Partition.conjugate_conjugate μ
  · intro μ _
    rw [omega_of_stableSchur]

end SymmetricFunction

end TauCeti
