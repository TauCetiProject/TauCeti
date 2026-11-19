/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.KnotTheory.Jimbo.ReducedTrace
import Mathlib.Tactic.LinearCombination

/-!
# Finite-colour comparison between Hecke Markov braid traces and Jimbo traces

Let `q : Rˣ` be a unit parameter in a commutative ring `R`, and let
`[N]_q = ∑ a : Fin N, jimboWeight q a` be the `N`-colour quantum dimension. On the Hecke side,
`MarkovBraid.heckeTrace` normalizes a Markov trace on the infinite type-A Hecke algebra to give the
one-strand unknot value `1`, while on the Turaev–Jimbo side `MarkovBraid.jimboTrace` normalizes the
`N`-colour weighted braid trace by writhe alone so that the one-strand unknot has value `[N]_q`.

Combining `KnotTheory.mul_jimboWeightedTrace_eq_ocneanuTrace_braidHom` with the writhe factors
relates the two braid-closure constructions over any commutative ring `R`, including at `q = ±1`
where `q - q⁻¹ = 0`:
* Whenever `[N]_q` has an inverse `c` (`c * [N]_q = 1`), the parameters `C = [N]_q`,
  `l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy both Markov normalization equations,
  `heckeTrace` (together with its quotient invariant `heckeBraidInvariant`) equals
  `c * β.jimboTrace (N := N) q`, and `[N]_q * heckeTrace` recovers `β.jimboTrace (N := N) q`.
* Over a field `K` with `[N]_q ≠ 0`, `heckeTrace` equals the reduced `N`-colour invariant
  `MarkovBraid.jimboReducedTrace`.

We also verify the comparison explicitly on the two-strand unlink, on both single-crossing
two-strand closures, and at the classical specialization `q = 1` (`q - q⁻¹ = 0`).

## Main results

* `TauCeti.jimboHeckeNormalization`: the positive and negative Markov normalization identities for
  `(C, l, z) = ([N]_q, (q ^ N)⁻¹, c * q ^ N)` when `c * [N]_q = 1`.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace` and
  `TauCeti.MarkovBraid.mul_heckeTrace_ocneanuTrace_eq_jimboTrace`: comparison with `jimboTrace`
  over commutative rings in which `[N]_q` is invertible.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`: comparison with
  `jimboReducedTrace` over a field.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_one_parameter`: evaluation at `q = 1` in terms of
  fixed colourings of the underlying strand permutation.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Sections 5–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public section

namespace TauCeti

open KnotTheory InfiniteTypeAHeckeAlgebra
open scoped BigOperators

section CommRing

variable {R : Type*} [CommRing R] {q : Rˣ} {N : ℕ}

/-- When `c * [N]_q = 1`, the parameters `C = [N]_q`, `l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy
both positive and negative Hecke Markov normalization equations `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`. No division by `q - q⁻¹` occurs, so this also holds when
`q - q⁻¹ = 0`. -/
theorem jimboHeckeNormalization {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * ↑((q ^ N)⁻¹ : Rˣ) * (c * ↑(q ^ N)) = 1 ∧
      (∑ a : Fin N, jimboWeight q a) * ↑(((q ^ N)⁻¹ : Rˣ)⁻¹) *
        (c * ↑(q ^ N) - ((q : R) - ↑q⁻¹)) = 1 :=
  heckeNormalization_of_mul_eq_val_inv_sub hc
    (by simpa only [inv_inv, inv_pow, mul_comm] using jimboWeight_sum (N := N) q)
    (by rw [inv_inv])

namespace MarkovBraid

/-- **Finite-colour braid-closure comparison over a commutative ring.** When `c * [N]_q = 1`, the
normalized Hecke trace of `ocneanuTrace R q (c * q ^ N)` equals `c` times the writhe-normalized
`N`-colour Jimbo trace `β.jimboTrace q`. -/
theorem heckeTrace_ocneanuTrace_eq_mul_jimboTrace {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      c * β.jimboTrace (N := N) q := by
  have htr := (mul_jimboWeightedTrace_eq_ocneanuTrace_braidHom hc β.braid).symm
  have hw : (((q ^ N)⁻¹ : Rˣ) ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) : Rˣ) =
      (q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) := by
    rw [inv_zpow, zpow_neg]
  have hpow : ((∑ a : Fin N, jimboWeight q a) * c) ^ β.predStrands = 1 := by
    rw [mul_comm, hc, one_pow]
  rw [heckeTrace_def, jimboTrace_def, htr, hw, pow_succ]
  calc
    (∑ a : Fin N, jimboWeight q a) ^ β.predStrands *
        ↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))) *
        (c ^ β.predStrands * c * jimboWeightedTrace q β.braid)
      = ((∑ a : Fin N, jimboWeight q a) * c) ^ β.predStrands *
          (c * (↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))) *
            jimboWeightedTrace q β.braid)) := by
          rw [mul_pow]
          ring
    _ = c * (↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))) *
          jimboWeightedTrace q β.braid) := by
          rw [hpow, one_mul]

/-- Multiplying the normalized Hecke trace at `z = c * q ^ N` by `[N]_q` recovers `jimboTrace` when
`c * [N]_q = 1`. -/
theorem mul_heckeTrace_ocneanuTrace_eq_jimboTrace {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      β.jimboTrace (N := N) q := by
  rw [β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc, ← mul_assoc, mul_comm _ c, hc, one_mul]

/-! ### Explicit two-strand and `q = 1` checks -/

/-- On the two-strand unlink `⟨1, 1⟩`, the normalized Ocneanu trace with unlink factor `[N]_q` and
writhe unit `(q ^ N)⁻¹` evaluates to `[N]_q` for any `z : R`. -/
theorem heckeTrace_ocneanuTrace_two_strand_unlink (z : R) :
    heckeTrace ⟨1, 1⟩ (ocneanuTrace R q z)
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      ∑ a : Fin N, jimboWeight q a := by
  rw [heckeTrace_one (ocneanuTrace_one _), pow_one]

/-- On the positive single-crossing two-strand braid `⟨1, σ₀⟩`, the normalized Ocneanu trace at
`z = c * q ^ N` evaluates to `1` when `c * [N]_q = 1`. -/
theorem heckeTrace_ocneanuTrace_sigma_two {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, BraidGroup.sigma (0 : Fin 1)⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ = 1 := by
  rw [heckeTrace_sigma (isMarkovTrace_ocneanuTrace _), pow_one, (jimboHeckeNormalization hc).1]

/-- On the negative single-crossing two-strand braid `⟨1, σ₀⁻¹⟩`, the normalized Ocneanu trace at
`z = c * q ^ N` evaluates to `1` when `c * [N]_q = 1`. -/
theorem heckeTrace_ocneanuTrace_sigma_two_inv {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, (BraidGroup.sigma (0 : Fin 1))⁻¹⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ = 1 := by
  rw [heckeTrace_sigma_inv (isMarkovTrace_ocneanuTrace _), pow_one, (jimboHeckeNormalization hc).2]

/-- **Evaluation at the zero-factor specialization `q = 1` (`q - q⁻¹ = 0`).** When `c * N = 1` in
`R`, the normalized Ocneanu trace at `(q, z, C, l) = (1, c, N, 1)` counts `N`-colourings fixed by
the underlying strand permutation of `β`, scaled by `c`. -/
theorem heckeTrace_ocneanuTrace_one_parameter {c : R} (hc : c * (N : R) = 1)
    (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R (1 : Rˣ) c) (N : R) (1 : Rˣ) =
      c * ((Finset.univ.filter fun w : Fin (β.predStrands + 1) → Fin N ↦
        w ∘ ⇑(BraidGroup.permHom (β.predStrands + 1) β.braid)⁻¹ = w).card : R) := by
  have hsum : (∑ a : Fin N, jimboWeight (1 : Rˣ) a) = (N : R) := by
    simp
  have hc' : c * ∑ a : Fin N, jimboWeight (1 : Rˣ) a = 1 := hsum ▸ hc
  have h := β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace (q := (1 : Rˣ)) hc'
  simpa only [hsum, one_pow, inv_one, Units.val_one, mul_one, jimboTrace_def, one_zpow, one_mul,
    jimboWeightedTrace_one_parameter] using h

end MarkovBraid

/-- On the quotient `Quot MarkovEquiv`, `heckeBraidInvariant` for `ocneanuTrace R q (c * q ^ N)`
agrees with the descended invariant `β ↦ c * β.jimboTrace (N := N) q`. -/
theorem heckeBraidInvariant_ocneanuTrace_eq_mul_jimboTrace {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (x : Quot MarkovEquiv) :
    heckeBraidInvariant (isMarkovTrace_ocneanuTrace (q := q) (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹
        (jimboHeckeNormalization hc).1 (jimboHeckeNormalization hc).2 x =
      Quot.lift (fun β : MarkovBraid ↦ c * β.jimboTrace (N := N) q)
        (fun _ _ h ↦ by rw [h.jimboTrace_eq]) x := by
  rcases Quot.exists_rep x with ⟨β, rfl⟩
  rw [heckeBraidInvariant_mk]
  exact β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc

end CommRing

section Field

variable {K : Type*} [Field K] {q : Kˣ} {N : ℕ}

/-- **Finite-colour braid-closure comparison with `jimboReducedTrace`.** Over a field `K` with
nonzero quantum dimension `[N]_q ≠ 0`, the normalized Hecke trace of
`ocneanuTrace K q ([N]_q⁻¹ * q ^ N)` equals the reduced `N`-colour Jimbo trace
`β.jimboReducedTrace q`. -/
theorem MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace K q ((∑ a : Fin N, jimboWeight q a)⁻¹ * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      β.jimboReducedTrace (N := N) q := by
  rw [β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace (inv_mul_cancel₀ hδ),
    MarkovBraid.jimboReducedTrace_def, div_eq_inv_mul]

/-- On `Quot MarkovEquiv` over a field with `[N]_q ≠ 0`, `heckeBraidInvariant` for
`ocneanuTrace K q ([N]_q⁻¹ * q ^ N)` equals the descended `jimboReducedTrace`. -/
theorem heckeBraidInvariant_ocneanuTrace_eq_jimboReducedTrace
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) (x : Quot MarkovEquiv) :
    heckeBraidInvariant
        (isMarkovTrace_ocneanuTrace (q := q) ((∑ a : Fin N, jimboWeight q a)⁻¹ * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹
        (jimboHeckeNormalization (inv_mul_cancel₀ hδ)).1
        (jimboHeckeNormalization (inv_mul_cancel₀ hδ)).2 x =
      Quot.lift (fun β : MarkovBraid ↦ β.jimboReducedTrace (N := N) q)
        (fun _ _ h ↦ h.jimboReducedTrace_eq q) x := by
  rcases Quot.exists_rep x with ⟨β, rfl⟩
  rw [heckeBraidInvariant_mk]
  exact β.heckeTrace_ocneanuTrace_eq_jimboReducedTrace hδ

end Field

end TauCeti
