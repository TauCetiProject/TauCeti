/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Pieri
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.JacobiTrudi
import TauCeti.Combinatorics.Enumerative.Partition.Conjugate

/-!
# The Pieri rules for symmetric functions and their `ω`-duality

Multiplying a Schur function `s_ν` by the complete homogeneous symmetric function `h_r` sums the
Schur functions `s_μ` obtained from `ν` by adding a horizontal strip of `r` cells
(`YoungDiagram.InterlacedBy`), and multiplying it by the elementary symmetric function `e_r` sums
those obtained by adding a vertical strip of `r` cells (`YoungDiagram.IsVerticalStrip`):

`h_r · s_ν = ∑_μ s_μ` and `e_r · s_ν = ∑_μ s_μ`.

Both identities hold over any commutative semiring, both in homogeneous degree `n + r`
(`TauCeti.stableSymmetricMul_stableSchur_stableHsymm` and
`TauCeti.stableSymmetricMul_stableSchur_stableEsymm`) and in the graded ring `Λ_R`
(`TauCeti.SymmetricFunction.of_stableHsymm_mul_of_stableSchur` and
`TauCeti.SymmetricFunction.of_stableEsymm_mul_of_stableSchur`).

Unlike the rings of symmetric polynomials in finitely many variables, `Λ_R` over a commutative ring
carries the algebra involution `ω` (`TauCeti.SymmetricFunction.omega`), which exchanges `h_r` and
`e_r` and sends every Schur function `s_μ` to `s_(μᵗ)`. Because transposing Young diagrams exchanges
horizontal strips and vertical strips (`YoungDiagram.isVerticalStrip_iff_interlacedBy_transpose`),
`ω` sends the horizontal-strip sum over `ν` to the vertical-strip sum over `νᵗ` and conversely
(`TauCeti.stableOmega_sum_interlacedBy`, `TauCeti.stableOmega_sum_isVerticalStrip`,
`TauCeti.SymmetricFunction.omega_sum_interlacedBy`, and
`TauCeti.SymmetricFunction.omega_sum_isVerticalStrip`). Applying `ω` therefore carries each Pieri
rule in `Λ_R` into the other.

## Main results

* `TauCeti.stableSymmetricMul_stableSchur_stableHsymm`,
  `TauCeti.SymmetricFunction.of_stableHsymm_mul_of_stableSchur`: **the Pieri rule** for symmetric
  functions.
* `TauCeti.stableSymmetricMul_stableSchur_stableEsymm`,
  `TauCeti.SymmetricFunction.of_stableEsymm_mul_of_stableSchur`: **the dual Pieri rule** for
  symmetric functions.
* `TauCeti.stableOmega_sum_interlacedBy`, `TauCeti.stableOmega_sum_isVerticalStrip`,
  `TauCeti.SymmetricFunction.omega_sum_interlacedBy`,
  `TauCeti.SymmetricFunction.omega_sum_isVerticalStrip`: `ω` exchanges horizontal-strip and
  vertical-strip sums of Schur functions along partition conjugation.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, (5.16) and (5.17).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.15.7.
-/

public section

namespace TauCeti

open Finset MvPolynomial DirectSum

section CommSemiring

variable (R : Type*) [CommSemiring R]

open scoped Classical in
/-- **The Pieri rule for Schur functions** in degree `n + r`: multiplying the Schur function `s_ν`
of a partition `ν` of `n` by the complete homogeneous symmetric function `h_r` gives the sum of the
Schur functions `s_μ` over the partitions `μ` of `n + r` whose Young diagram contains that of `ν`
with a horizontal strip as complement. -/
theorem stableSymmetricMul_stableSchur_stableHsymm {n : ℕ} (ν : n.Partition) (r : ℕ) :
    stableSymmetricMul R n r (stableSchur R ν) (stableHsymm R r) =
      ∑ μ : (n + r).Partition with
          (YoungDiagram.ofPartition μ).InterlacedBy (YoungDiagram.ofPartition ν),
        stableSchur R μ := by
  refine stableSymmetricSubmodule_ext fun d => Subtype.ext ?_
  rw [coe_stableSymmetricProj_stableSymmetricMul, coe_stableSymmetricProj_stableSchur,
    coe_stableSymmetricProj_stableHsymm, mul_comm, map_sum, Submodule.coe_sum]
  simp only [coe_stableSymmetricProj_stableSchur]
  convert hsymm_mul_schurPoly (σ := Fin d) (R := R) ν r

open scoped Classical in
/-- **The dual Pieri rule for Schur functions** in degree `n + r`: multiplying the Schur function
`s_ν` of a partition `ν` of `n` by the elementary symmetric function `e_r` gives the sum of the
Schur functions `s_μ` over the partitions `μ` of `n + r` whose Young diagram contains that of `ν`
with a vertical strip as complement. -/
theorem stableSymmetricMul_stableSchur_stableEsymm {n : ℕ} (ν : n.Partition) (r : ℕ) :
    stableSymmetricMul R n r (stableSchur R ν) (stableEsymm R r) =
      ∑ μ : (n + r).Partition with
          (YoungDiagram.ofPartition μ).IsVerticalStrip (YoungDiagram.ofPartition ν),
        stableSchur R μ := by
  refine stableSymmetricSubmodule_ext fun d => Subtype.ext ?_
  rw [coe_stableSymmetricProj_stableSymmetricMul, coe_stableSymmetricProj_stableSchur,
    coe_stableSymmetricProj_stableEsymm, mul_comm, esymm_mul_schurPoly, map_sum, Submodule.coe_sum]
  simp only [coe_stableSymmetricProj_stableSchur]

namespace SymmetricFunction

open scoped Classical in
/-- **The Pieri rule in `Λ_R`**: `h_r · s_ν = ∑_μ s_μ`, the sum running over the partitions `μ` of
`n + r` whose Young diagram contains that of `ν` with a horizontal strip as complement. -/
theorem of_stableHsymm_mul_of_stableSchur {n : ℕ} (ν : n.Partition) (r : ℕ) :
    (DirectSum.of _ r (stableHsymm R r) : SymmetricFunction R) *
        DirectSum.of _ n (stableSchur R ν) =
      ∑ μ : (n + r).Partition with
          (YoungDiagram.ofPartition μ).InterlacedBy (YoungDiagram.ofPartition ν),
        DirectSum.of _ (n + r) (stableSchur R μ) := by
  rw [mul_comm, DirectSum.of_mul_of, gMul_mul_stableSymmetricSubmodule,
    stableSymmetricMul_stableSchur_stableHsymm, map_sum]

open scoped Classical in
/-- **The dual Pieri rule in `Λ_R`**: `e_r · s_ν = ∑_μ s_μ`, the sum running over the partitions
`μ` of `n + r` whose Young diagram contains that of `ν` with a vertical strip as complement. -/
theorem of_stableEsymm_mul_of_stableSchur {n : ℕ} (ν : n.Partition) (r : ℕ) :
    (DirectSum.of _ r (stableEsymm R r) : SymmetricFunction R) *
        DirectSum.of _ n (stableSchur R ν) =
      ∑ μ : (n + r).Partition with
          (YoungDiagram.ofPartition μ).IsVerticalStrip (YoungDiagram.ofPartition ν),
        DirectSum.of _ (n + r) (stableSchur R μ) := by
  rw [mul_comm, DirectSum.of_mul_of, gMul_mul_stableSymmetricSubmodule,
    stableSymmetricMul_stableSchur_stableEsymm, map_sum]

end SymmetricFunction

end CommSemiring

/-! ### `ω`-duality between horizontal-strip and vertical-strip sums -/

section CommRing

variable (R : Type*) [CommRing R]

open scoped Classical in
/-- **The degreewise involution `stableOmega` carries a horizontal-strip sum of Schur functions to
the vertical-strip sum over the conjugate shape.** -/
theorem stableOmega_sum_interlacedBy {n m : ℕ} (ν : n.Partition) :
    stableOmega R m
      (∑ μ : m.Partition with
          (YoungDiagram.ofPartition μ).InterlacedBy (YoungDiagram.ofPartition ν),
        stableSchur R μ) =
    ∑ μ : m.Partition with
        (YoungDiagram.ofPartition μ).IsVerticalStrip (YoungDiagram.ofPartition ν.conjugate),
      stableSchur R μ := by
  let e : m.Partition ≃ m.Partition :=
    Function.Involutive.toPerm _root_.Nat.Partition.conjugate
      _root_.Nat.Partition.conjugate_conjugate
  have he (μ : m.Partition) : e μ = μ.conjugate :=
    congrFun (Function.Involutive.coe_toPerm _) μ
  rw [map_sum]
  refine Finset.sum_equiv e (fun μ => ?_) (fun μ _ => by simp [he])
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, he,
    YoungDiagram.isVerticalStrip_iff_interlacedBy_transpose,
    YoungDiagram.ofPartition_conjugate, YoungDiagram.transpose_transpose]

open scoped Classical in
/-- **The degreewise involution `stableOmega` carries a vertical-strip sum of Schur functions to the
horizontal-strip sum over the conjugate shape.** -/
theorem stableOmega_sum_isVerticalStrip {n m : ℕ} (ν : n.Partition) :
    stableOmega R m
      (∑ μ : m.Partition with
          (YoungDiagram.ofPartition μ).IsVerticalStrip (YoungDiagram.ofPartition ν),
        stableSchur R μ) =
    ∑ μ : m.Partition with
        (YoungDiagram.ofPartition μ).InterlacedBy (YoungDiagram.ofPartition ν.conjugate),
      stableSchur R μ := by
  rw [← (stableOmega R m).eq_symm_apply, stableOmega_symm, stableOmega_sum_interlacedBy,
    _root_.Nat.Partition.conjugate_conjugate]

namespace SymmetricFunction

open scoped Classical in
/-- **In `Λ_R`, the involution `ω` carries a horizontal-strip sum of Schur functions to the
vertical-strip sum over the conjugate shape.** -/
theorem omega_sum_interlacedBy {n m : ℕ} (ν : n.Partition) :
    omega R
      (∑ μ : m.Partition with
          (YoungDiagram.ofPartition μ).InterlacedBy (YoungDiagram.ofPartition ν),
        DirectSum.of _ m (stableSchur R μ)) =
    ∑ μ : m.Partition with
        (YoungDiagram.ofPartition μ).IsVerticalStrip (YoungDiagram.ofPartition ν.conjugate),
      DirectSum.of _ m (stableSchur R μ) := by
  simp_rw [← DirectSum.lof_eq_of R]
  rw [← map_sum, DirectSum.lof_eq_of, omega_of, stableOmega_sum_interlacedBy,
    ← DirectSum.lof_eq_of R, map_sum]

open scoped Classical in
/-- **In `Λ_R`, the involution `ω` carries a vertical-strip sum of Schur functions to the
horizontal-strip sum over the conjugate shape.** -/
theorem omega_sum_isVerticalStrip {n m : ℕ} (ν : n.Partition) :
    omega R
      (∑ μ : m.Partition with
          (YoungDiagram.ofPartition μ).IsVerticalStrip (YoungDiagram.ofPartition ν),
        DirectSum.of _ m (stableSchur R μ)) =
    ∑ μ : m.Partition with
        (YoungDiagram.ofPartition μ).InterlacedBy (YoungDiagram.ofPartition ν.conjugate),
      DirectSum.of _ m (stableSchur R μ) := by
  rw [← (omega R).eq_symm_apply, omega_symm, omega_sum_interlacedBy,
    _root_.Nat.Partition.conjugate_conjugate]

end SymmetricFunction

end CommRing

end TauCeti
