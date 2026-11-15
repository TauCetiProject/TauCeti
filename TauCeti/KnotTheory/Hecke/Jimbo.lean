/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Detection
public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Burau.Skein
public import TauCeti.KnotTheory.Hecke
public import TauCeti.KnotTheory.Homfly.Reduced
public import TauCeti.KnotTheory.Markov.Components
import Mathlib.Tactic.LinearCombination

/-!
# Comparing the Ocneanu Hecke braid trace with the Jimbo and HOMFLY invariants

This file compares three distinct algebraic braid-closure invariants:

1. **Jones's normalized universal Hecke trace** `TauCeti.MarkovBraid.heckeTrace` applied to the
   Ocneanu trace `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace` on the infinite type-A Hecke
   tower, together with its quotient descent `TauCeti.heckeBraidInvariant` on
   `Quot TauCeti.MarkovEquiv`.
2. **Turaev's writhe-normalized `N`-colour Jimbo trace** `TauCeti.MarkovBraid.jimboTrace` (with
   unknot value equal to the quantum dimension `D_N = ∑ a : Fin N, jimboWeight q a`), its
   quotient descent `TauCeti.jimboBraidInvariant`, and its field quotient
   `TauCeti.MarkovBraid.jimboReducedTrace`.
3. **The two-variable HOMFLY Laurent polynomials** `TauCeti.MarkovBraid.homfly` and
   `TauCeti.MarkovBraid.reducedHomfly`.

Whenever `(C, l)` solves the Markov stabilization equations `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1` and `q - q⁻¹` is a unit `u`, evaluating `reducedHomfly` at
`a = l⁻¹` and `z_HOMFLY = u` recovers `β.heckeTrace (ocneanuTrace R q z) C l`
(`TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace`). At an `N`-colour Jimbo
specialization where `c * D_N = 1`, the parameter `z = c * q ^ N` and writhe unit `l = (q ^ N)⁻¹`
solve both stabilization equations in `R` without adjoining roots, and
`β.heckeTrace (ocneanuTrace R q (c * q ^ N)) D_N (q ^ N)⁻¹ = c * β.jimboTrace (N := N) q`
(`TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace`); we also check the two-strand
unlink and both one-crossing closures explicitly.

At zero-factor specializations — when `N = 0` (`D_0 = 0`), when `q = 1` (`q - q⁻¹ = 0`, and also
`D_N(1) = N = 0` in characteristic dividing `N`), or at roots of unity where `D_N(q) = 0` — naive
division by `D_N` or `q - q⁻¹` after specialization is undefined. Instead, `D_N` divides
`β.jimboTrace (N := N) q` over every commutative ring
(`TauCeti.MarkovBraid.sum_jimboWeight_dvd_jimboTrace`), and dividing prior to specialization in the
integral domain `ℤ[T;T⁻¹]` produces the universal reduced invariant
`TauCeti.MarkovBraid.universalJimboReduced` (completed at `N = 0` by the normalized Burau
Alexander invariant at `T⁻¹`). Specializing `T ↦ q` in any commutative ring `R` yields a regular
Markov invariant that recovers `heckeTrace` when `D_N` is invertible, recovers `reducedHomfly`
when `q - q⁻¹` is invertible, evaluates at `N = 0` to `β.normalizedBurauAlexander q⁻¹`, evaluates
at `q = 1` for `N = r + 1` to `(r + 1) ^ (Nat.card β.Components - 1)` in every characteristic, and
evaluates at `N = 2` when `q + q⁻¹ = 0` to `β.normalizedBurauAlexander q`.

All statements are formulated on `MarkovBraid` and `Quot MarkovEquiv`; no geometric link carrier
or geometric Markov theorem is assumed.

## Main definitions

* `TauCeti.jimboBraidInvariant`: descent of `MarkovBraid.jimboTrace` to `Quot MarkovEquiv`.
* `TauCeti.MarkovBraid.universalJimboReduced`: the universal reduced `N`-colour invariant in
  `LaurentPolynomial ℤ`, regular across all specializations `q : Rˣ`.

## Main results

* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace` and
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace_ocneanuTrace`: specialization of the
  reduced and unreduced HOMFLY polynomials to the Ocneanu Hecke braid trace.
* `TauCeti.MarkovBraid.heckeTrace_sigma_two`, `TauCeti.MarkovBraid.heckeTrace_sigma_two_inv`,
  `TauCeti.MarkovBraid.jimboTrace_sigma_two`, and `TauCeti.MarkovBraid.jimboTrace_sigma_two_inv`:
  values on both two-strand one-crossing closures.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace`,
  `TauCeti.heckeBraidInvariant_ocneanuTrace_eq_mul_jimboBraidInvariant`, and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`: comparison of the Ocneanu
  Hecke braid trace with the finite-colour Jimbo trace and its reduced field quotient.
* `TauCeti.MarkovBraid.sum_jimboWeight_dvd_jimboTrace` and
  `TauCeti.MarkovBraid.sum_jimboWeight_mul_eval₂_universalJimboReduced`: universal divisibility
  by the quantum dimension and specialization identity.
* `TauCeti.MarkovBraid.eval₂_universalJimboReduced_eq_heckeTrace_ocneanuTrace` and
  `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_eval₂_universalJimboReduced`: agreement of the
  universal Laurent invariant with the Ocneanu trace and with `reducedHomfly`.
* `TauCeti.MarkovBraid.eval₂_universalJimboReduced_zero`,
  `TauCeti.MarkovBraid.eval₂_universalJimboReduced_succ_one`, and
  `TauCeti.MarkovBraid.eval₂_universalJimboReduced_two_of_add_inv_eq_zero`: explicit evaluations
  at zero-factor specializations (`N = 0`, `q = 1`, and `q + q⁻¹ = 0`).

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett, A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

open LaurentPolynomial MonoidAlgebra
open scoped BigOperators

namespace RingHom

open TauCeti

/-- Applying a ring homomorphism to the writhe-normalized Jimbo trace maps the parameter unit
along `f`. -/
theorem map_jimboTrace {R S : Type*} [CommRing R] [CommRing S] {N : ℕ}
    (f : R →+* S) (β : MarkovBraid) (q : Rˣ) :
    f (β.jimboTrace (N := N) q) = β.jimboTrace (N := N) (Units.map f.toMonoidHom q) := by
  rw [MarkovBraid.jimboTrace_def, MarkovBraid.jimboTrace_def, map_mul, f.map_jimboWeightedTrace]
  congr 1
  rw [← map_pow (Units.map f.toMonoidHom) q N,
    ← map_zpow (Units.map f.toMonoidHom) (q ^ N), Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

end RingHom

namespace TauCeti

open BraidGroup KnotTheory InfiniteTypeAHeckeAlgebra

/-! ### Comparison of the HOMFLY polynomial with the Ocneanu Hecke braid trace -/

namespace KnotTheory

/-- When `(C, l)` solves the positive and negative Markov stabilization equations for parameter
`z` and `u = q - q⁻¹`, the HOMFLY unknot value `(a - a⁻¹) z⁻¹` specializes at `a = l⁻¹` and
`z_HOMFLY = u` to the unlink factor `C`. -/
theorem eval₂_homflyUnknot_ocneanu {K R : Type*} [Field K] [CommRing R] (φ : K →+* R)
    {q l u : Rˣ} {z C : R} (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  simp only [homflyUnknot_def, map_mul, map_sub, eval₂_C, eval₂_T, zpow_one, zpow_neg_one, inv_inv]
  rw [Units.mul_inv_eq_iff_eq_mul, hu]
  have hl : (l : R) * ↑l⁻¹ = 1 := Units.mul_inv l
  linear_combination (l : R) * hneg - (↑l⁻¹ : R) * hpos + C * ((q : R) - ↑q⁻¹) * hl

/-- At `a = q ^ N` and `z_HOMFLY = u = q - q⁻¹`, the HOMFLY unknot value specializes to the
`N`-colour quantum dimension, for every `N : ℕ` (including `N = 0`). -/
theorem eval₂_homflyUnknot_jimbo {K R : Type*} [Field K] [CommRing R] (φ : K →+* R)
    (N : ℕ) (q u : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) (q ^ N) (homflyUnknot K) = ∑ a : Fin N, jimboWeight q a := by
  simp only [homflyUnknot_def, map_mul, map_sub, eval₂_C, eval₂_T, zpow_one, zpow_neg_one,
    ← inv_pow]
  rw [Units.mul_inv_eq_iff_eq_mul, hu, mul_comm, jimboWeight_sum]

end KnotTheory

namespace MarkovBraid

/-- **Specialization of the reduced HOMFLY polynomial to the Ocneanu Hecke trace.** When `(C, l)`
solves the Markov stabilization equations for `ocneanuTrace R q z` and `u = q - q⁻¹`, evaluating
`β.reducedHomfly K` at `a = l⁻¹` and `z_HOMFLY = u` recovers
`β.heckeTrace (ocneanuTrace R q z) C l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) {q l u : Rˣ} {z C : R}
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace (ocneanuTrace R q z) C l := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) l⁻¹
  have hC : e (homflyUnknot K) = C := eval₂_homflyUnknot_ocneanu φ hpos hneg hu
  refine congrFun (eq_heckeTrace_of_skein (isMarkovTrace_ocneanuTrace z) hpos hneg
    (F := fun γ ↦ e (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun n c i ↦ ?_)
    (fun n b ↦ by simp only [reducedHomfly_strandIncl, map_mul, hC])
    (by simp [e])) β
  have h := congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
  simpa only [e, map_sub, map_mul, eval₂_T, eval₂_C, zpow_one, zpow_neg_one, inv_inv, one_mul,
    hu] using h

/-- **Specialization of the unreduced HOMFLY polynomial to the Ocneanu Hecke trace.** Under the
same hypotheses, `β.homfly K` evaluates to `C * β.heckeTrace (ocneanuTrace R q z) C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace_ocneanuTrace {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) {q l u : Rˣ} {z C : R}
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) =
      C * β.heckeTrace (ocneanuTrace R q z) C l := by
  rw [← homflyUnknot_mul_reducedHomfly K β, map_mul,
    eval₂_homflyUnknot_ocneanu φ hpos hneg hu,
    eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace φ hpos hneg hu]

/-! ### Two-strand closures, strand inclusion, and finite-colour Jimbo comparison -/

/-- On two strands, the positive one-crossing braid `σ₀` closes to the unknot and has normalized
Hecke trace `1` whenever positive stabilization holds. -/
theorem heckeTrace_sigma_two {R : Type*} [CommRing R] {q : Rˣ} {z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1) :
    heckeTrace ⟨1, sigma (n := 2) 0⟩ τ C l = 1 := by
  have h := heckeTrace_stabilize hτ C l hpos (1 : BraidGroup 1)
  simpa only [map_one, one_mul, Fin.last_zero, heckeTrace_one_strand hτ.map_one] using h

/-- On two strands, the negative one-crossing braid `σ₀⁻¹` closes to the unknot and has normalized
Hecke trace `1` whenever negative stabilization holds. -/
theorem heckeTrace_sigma_two_inv {R : Type*} [CommRing R] {q : Rˣ} {z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    heckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ τ C l = 1 := by
  have h := heckeTrace_stabilizeInv hτ C l hneg (1 : BraidGroup 1)
  simpa only [map_one, one_mul, Fin.last_zero, heckeTrace_one_strand hτ.map_one] using h

/-- Every braid on one strand has writhe-normalized Jimbo trace equal to the quantum dimension. -/
@[simp]
theorem jimboTrace_one_strand {R : Type*} [CommRing R] {N : ℕ} (q : Rˣ) (b : BraidGroup 1) :
    jimboTrace (N := N) ⟨0, b⟩ q = ∑ a : Fin N, jimboWeight q a := by
  rw [eq_one_of_le_one le_rfl b, jimboTrace_one, zero_add, pow_one]

/-- Adding an uncrossed strand multiplies the writhe-normalized Jimbo trace by the quantum
dimension. -/
@[simp]
theorem jimboTrace_strandIncl {R : Type*} [CommRing R] {N n : ℕ} (q : Rˣ)
    (b : BraidGroup (n + 1)) :
    jimboTrace (N := N) ⟨n + 1, strandIncl b⟩ q =
      (∑ a : Fin N, jimboWeight q a) * jimboTrace (N := N) ⟨n, b⟩ q := by
  rw [jimboTrace_def, jimboTrace_def, exponentSum_strandIncl, jimboWeightedTrace_strandIncl]
  ring

/-- On two strands, the positive one-crossing braid `σ₀` has writhe-normalized Jimbo trace equal
to the quantum dimension. -/
@[simp]
theorem jimboTrace_sigma_two {R : Type*} [CommRing R] {N : ℕ} (q : Rˣ) :
    jimboTrace (N := N) ⟨1, sigma (n := 2) 0⟩ q = ∑ a : Fin N, jimboWeight q a := by
  have h := jimboTrace_stabilize (N := N) q (1 : BraidGroup 1)
  simpa only [map_one, one_mul, Fin.last_zero, jimboTrace_one_strand] using h

/-- On two strands, the negative one-crossing braid `σ₀⁻¹` has writhe-normalized Jimbo trace equal
to the quantum dimension. -/
@[simp]
theorem jimboTrace_sigma_two_inv {R : Type*} [CommRing R] {N : ℕ} (q : Rˣ) :
    jimboTrace (N := N) ⟨1, (sigma (n := 2) 0)⁻¹⟩ q = ∑ a : Fin N, jimboWeight q a := by
  have h := jimboTrace_stabilizeInv (N := N) q (1 : BraidGroup 1)
  simpa only [map_one, one_mul, Fin.last_zero, jimboTrace_one_strand] using h

end MarkovBraid

/-- The writhe-normalized `N`-colour Jimbo trace descended to the quotient of braids by ordinary
unframed Markov equivalence. -/
noncomputable def jimboBraidInvariant {R : Type*} [CommRing R] (N : ℕ) (q : Rˣ) :
    Quot MarkovEquiv → R :=
  Quot.lift (fun β ↦ β.jimboTrace (N := N) q) (fun _ _ h ↦ h.jimboTrace_eq q)

/-- Evaluation of `jimboBraidInvariant` on a braid representative. -/
@[simp]
theorem jimboBraidInvariant_mk {R : Type*} [CommRing R] (N : ℕ) (q : Rˣ) (β : MarkovBraid) :
    jimboBraidInvariant N q (Quot.mk MarkovEquiv β) = β.jimboTrace (N := N) q :=
  (rfl)

/-- Positive Markov stabilization equation for the Ocneanu trace at an `N`-colour Jimbo
specialization `z = c * q ^ N`, `C = D_N`, `l = (q ^ N)⁻¹`. -/
theorem jimbo_heckeTrace_pos {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑((q ^ N)⁻¹) : R) * (c * ↑(q ^ N)) = 1 := by
  have hq : (↑((q ^ N)⁻¹) : R) * ↑(q ^ N) = 1 := Units.inv_mul (q ^ N)
  linear_combination hc + c * (∑ a : Fin N, jimboWeight q a) * hq

/-- Negative Markov stabilization equation for the Ocneanu trace at an `N`-colour Jimbo
specialization `z = c * q ^ N`, `C = D_N`, `l = (q ^ N)⁻¹`. No quadratic extension is needed:
the negative stabilization constant is `c * (q⁻¹) ^ N`. -/
theorem jimbo_heckeTrace_neg {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑((q ^ N)⁻¹)⁻¹ : R) *
        (c * ↑(q ^ N) - ((q : R) - ↑q⁻¹)) = 1 := by
  rw [inv_inv]
  have hq : (↑(q ^ N) : R) * ↑((q⁻¹) ^ N) = 1 := by
    rw [inv_pow]
    exact Units.mul_inv (q ^ N)
  have hs := jimboWeight_sum (N := N) q
  linear_combination (↑(q ^ N) : R) * ↑(q ^ N) * hc - (↑(q ^ N) : R) * hs + hq

namespace MarkovBraid

/-- **Comparison of the Ocneanu Hecke braid trace with Turaev's Jimbo trace.** When `c` inverts
the `N`-colour quantum dimension `D_N = ∑ a : Fin N, jimboWeight q a`, the normalized universal
Hecke trace of `ocneanuTrace R q (c * q ^ N)` with unlink factor `D_N` and writhe unit `(q ^ N)⁻¹`
equals `c` times the writhe-normalized `N`-colour Jimbo trace. -/
theorem heckeTrace_ocneanuTrace_eq_mul_jimboTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ}
    {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      c * β.jimboTrace (N := N) q := by
  rcases β with ⟨n, b⟩
  rw [heckeTrace_def, jimboTrace_def]
  dsimp only
  rw [← TypeAHeckeAlgebra.toInfinite_braidHom,
    ← TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace hc,
    TypeAHeckeAlgebra.jimboWeightedTrace_braidHom, inv_zpow', pow_succ']
  set D := ∑ a : Fin N, jimboWeight q a
  set w := (↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ b))) : R)
  have hpow : D ^ n * c ^ n = 1 := by rw [← mul_pow, mul_comm, hc, one_pow]
  calc
    D ^ n * w * (c * c ^ n * KnotTheory.jimboWeightedTrace (N := N) q b) =
      c * (D ^ n * c ^ n) * (w * KnotTheory.jimboWeightedTrace (N := N) q b) := by ring
    _ = c * (w * KnotTheory.jimboWeightedTrace (N := N) q b) := by rw [hpow, mul_one]

/-- Unrescaled form of `heckeTrace_ocneanuTrace_eq_mul_jimboTrace`: multiplying the Ocneanu Hecke
braid trace by the quantum dimension recovers `β.jimboTrace (N := N) q`. -/
theorem sum_jimboWeight_mul_heckeTrace_ocneanuTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ}
    {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      β.jimboTrace (N := N) q := by
  rw [heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc, ← mul_assoc, mul_comm _ c, hc, one_mul]

/-- **Comparison with the reduced Jimbo trace over a field.** Whenever the `N`-colour quantum
dimension is nonzero in a field `K`, the Ocneanu Hecke braid trace at
`z = q ^ N / ∑ a : Fin N, jimboWeight q a` equals `β.jimboReducedTrace (N := N) q`. -/
theorem heckeTrace_ocneanuTrace_eq_jimboReducedTrace {K : Type*} [Field K] {N : ℕ} {q : Kˣ}
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace K q (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      β.jimboReducedTrace (N := N) q := by
  have hc : (∑ a : Fin N, jimboWeight q a)⁻¹ * ∑ a : Fin N, jimboWeight q a = 1 :=
    inv_mul_cancel₀ hδ
  rw [div_eq_inv_mul, heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc, jimboReducedTrace_def,
    div_eq_inv_mul]

end MarkovBraid

/-- Quotient-level comparison on `Quot MarkovEquiv` between `heckeBraidInvariant` of the Ocneanu
trace and `jimboBraidInvariant`. -/
theorem heckeBraidInvariant_ocneanuTrace_eq_mul_jimboBraidInvariant {R : Type*} [CommRing R]
    {N : ℕ} {q : Rˣ} {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1)
    (L : Quot MarkovEquiv) :
    heckeBraidInvariant (isMarkovTrace_ocneanuTrace (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹
        (jimbo_heckeTrace_pos hc) (jimbo_heckeTrace_neg hc) L =
      c * jimboBraidInvariant N q L :=
  Quot.inductionOn L fun β ↦ by
    simpa only [heckeBraidInvariant_mk, jimboBraidInvariant_mk] using
      β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc

/-! ### Universal Laurent-polynomial regularity and zero-factor specializations -/

namespace KnotTheory

/-- Over any commutative ring `R`, the `N`-colour quantum dimension divides the weighted Jimbo
trace of every braid on `n + 1` strands. -/
theorem sum_jimboWeight_dvd_jimboWeightedTrace {R : Type*} [CommRing R] (N : ℕ) (q : Rˣ)
    {n : ℕ} (b : BraidGroup (n + 1)) :
    (∑ a : Fin N, jimboWeight q a) ∣ jimboWeightedTrace (N := N) q b := by
  set D : R := ∑ a : Fin N, jimboWeight q a
  induction n with
  | zero =>
    rw [eq_one_of_le_one le_rfl b, jimboWeightedTrace_one, pow_one]
  | succ m ih =>
    -- Pull back `Ideal.span {D}` along the linear extension of `jimboWeightedTrace`.
    let φ : R[BraidGroup (m + 2)] →ₗ[R] R :=
      Finsupp.linearCombination R (jimboWeightedTrace (N := N) q) ∘ₗ
        (coeffLinearEquiv R).toLinearMap
    have hφ (g : BraidGroup (m + 2)) (r : R) :
        φ (single g r) = r * jimboWeightedTrace (N := N) q g := by
      simp [φ, coeffLinearEquiv_apply, coeff_single]
    let M : Submodule R R[BraidGroup (m + 2)] :=
      Submodule.comap φ (Ideal.span ({D} : Set R))
    have hmem (x : R[BraidGroup (m + 2)]) : x ∈ M ↔ D ∣ φ x := by
      rw [Submodule.mem_comap, Ideal.mem_span_singleton]
    suffices hle : strandSpan R m ⊔ heckeSkein R ((q : R) - ↑q⁻¹) (m + 2) ≤ M by
      rw [strandSpan_sup_heckeSkein_eq_top, top_le_iff] at hle
      have hb : D ∣ φ (single b 1) := (hmem (single b 1)).mp (hle ▸ Submodule.mem_top)
      rwa [hφ, one_mul] at hb
    refine sup_le ((strandSpan_le_iff R).mpr ⟨fun d ↦ ?_, fun d e ↦ ?_⟩)
      ((heckeSkein_le_iff R ((q : R) - ↑q⁻¹)).mpr fun g h i ↦ ?_) <;> rw [hmem]
    · rw [hφ, one_mul, jimboWeightedTrace_strandIncl]
      exact dvd_mul_left D _
    · rw [hφ, one_mul, jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
        jimboWeightedTrace_stabilize]
      exact dvd_mul_of_dvd_right (ih (e * d)) _
    · rw [heckeRelator_def, map_sub, map_sub, hφ, hφ, hφ, one_mul, one_mul]
      have hs := jimboWeightedTrace_skein (N := N) q g h i
      have h0 : jimboWeightedTrace (N := N) q (g * sigma i * h) -
          jimboWeightedTrace (N := N) q (g * (sigma i)⁻¹ * h) -
          ((q : R) - ↑q⁻¹) * jimboWeightedTrace (N := N) q (g * h) = 0 := by
        linear_combination hs
      rw [h0]
      exact dvd_zero D

/-- For every `r : ℕ`, the `(r + 1)`-colour quantum dimension in `LaurentPolynomial ℤ` at
`genericUnit ℤ` is nonzero: evaluating at `1 : ℤˣ` yields `r + 1`. -/
theorem sum_jimboWeight_genericUnit_ne_zero (r : ℕ) :
    (∑ a : Fin (r + 1), jimboWeight (genericUnit ℤ) a) ≠ 0 := by
  intro h
  have heval := congrArg (laurentEval (1 : ℤˣ)) h
  simp only [map_sum, map_zero, jimboWeight_def, genericUnit_zpow_val, laurentEval_T, one_zpow,
    Units.val_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at heval
  omega

end KnotTheory

namespace MarkovBraid

/-- Over any commutative ring `R`, the `N`-colour quantum dimension divides the writhe-normalized
Jimbo trace of every braid closure. -/
theorem sum_jimboWeight_dvd_jimboTrace {R : Type*} [CommRing R] {N : ℕ} (β : MarkovBraid)
    (q : Rˣ) :
    (∑ a : Fin N, jimboWeight q a) ∣ β.jimboTrace (N := N) q := by
  rw [jimboTrace_def]
  exact dvd_mul_of_dvd_right (sum_jimboWeight_dvd_jimboWeightedTrace N q β.braid) _

/-- **The universal reduced `N`-colour Jimbo invariant** in `LaurentPolynomial ℤ`. For `N = r + 1`
it is the unique Laurent-polynomial quotient of `β.jimboTrace (N := r + 1) (genericUnit ℤ)` by the
quantum dimension; for `N = 0` it is the normalized Burau Alexander invariant at
`(genericUnit ℤ)⁻¹`. Specializing `T ↦ q` in any commutative ring gives a well-defined Markov
invariant without inverting `q - q⁻¹` or the specialized quantum dimension. -/
noncomputable def universalJimboReduced (N : ℕ) (β : MarkovBraid) : LaurentPolynomial ℤ :=
  match N with
  | 0 => β.normalizedBurauAlexander (genericUnit ℤ)⁻¹
  | r + 1 => (sum_jimboWeight_dvd_jimboTrace (N := r + 1) β (genericUnit ℤ)).choose

/-- At `N = 0`, `universalJimboReduced` is the normalized Burau Alexander invariant at
`(genericUnit ℤ)⁻¹`. -/
@[simp]
theorem universalJimboReduced_zero (β : MarkovBraid) :
    β.universalJimboReduced 0 = β.normalizedBurauAlexander (genericUnit ℤ)⁻¹ :=
  (rfl)

/-- Multiplying `universalJimboReduced N` by the universal `N`-colour quantum dimension recovers
`β.jimboTrace (N := N) (genericUnit ℤ)` for every `N : ℕ` (including `N = 0`). -/
@[simp]
theorem sum_jimboWeight_mul_universalJimboReduced (N : ℕ) (β : MarkovBraid) :
    (∑ a : Fin N, jimboWeight (genericUnit ℤ) a) * β.universalJimboReduced N =
      β.jimboTrace (N := N) (genericUnit ℤ) := by
  rcases N with _ | r
  · obtain ⟨k, hk⟩ := sum_jimboWeight_dvd_jimboTrace (N := 0) β (genericUnit ℤ)
    simpa using hk.symm
  · exact (sum_jimboWeight_dvd_jimboTrace (N := r + 1) β (genericUnit ℤ)).choose_spec.symm

/-- For `N = r + 1`, `universalJimboReduced (r + 1)` is uniquely characterized in the integral
domain `LaurentPolynomial ℤ` by multiplication by the `(r + 1)`-colour quantum dimension. -/
theorem universalJimboReduced_succ_eq_iff (r : ℕ) {β : MarkovBraid} {P : LaurentPolynomial ℤ} :
    β.universalJimboReduced (r + 1) = P ↔
      (∑ a : Fin (r + 1), jimboWeight (genericUnit ℤ) a) * P =
        β.jimboTrace (N := r + 1) (genericUnit ℤ) := by
  rw [← sum_jimboWeight_mul_universalJimboReduced (r + 1) β,
    mul_right_inj' (sum_jimboWeight_genericUnit_ne_zero r), eq_comm]

/-- On the `(n + 1)`-strand trivial braid, `universalJimboReduced N` equals the `n`-th power of
the `N`-colour quantum dimension, for every `N : ℕ`. -/
@[simp]
theorem universalJimboReduced_one (N n : ℕ) :
    universalJimboReduced N ⟨n, 1⟩ = (∑ a : Fin N, jimboWeight (genericUnit ℤ) a) ^ n := by
  rcases N with _ | r
  · rcases n with _ | m
    · simp
    · simpa [pow_succ] using
        normalizedBurauAlexander_strandIncl (genericUnit ℤ)⁻¹ (1 : BraidGroup (m + 1))
  · rw [universalJimboReduced_succ_eq_iff, jimboTrace_one, pow_succ']

/-- On any one-strand braid, `universalJimboReduced N` equals `1`. -/
@[simp]
theorem universalJimboReduced_one_strand (N : ℕ) (b : BraidGroup 1) :
    universalJimboReduced N ⟨0, b⟩ = 1 := by
  rw [eq_one_of_le_one le_rfl b, universalJimboReduced_one, pow_zero]

/-- Adding an uncrossed strand multiplies `universalJimboReduced N` by the `N`-colour quantum
dimension, for every `N : ℕ`. -/
@[simp]
theorem universalJimboReduced_strandIncl (N : ℕ) {n : ℕ} (b : BraidGroup (n + 1)) :
    universalJimboReduced N ⟨n + 1, strandIncl b⟩ =
      (∑ a : Fin N, jimboWeight (genericUnit ℤ) a) * universalJimboReduced N ⟨n, b⟩ := by
  rcases N with _ | r
  · simp
  · rw [universalJimboReduced_succ_eq_iff, jimboTrace_strandIncl, ← mul_assoc,
      mul_comm _ (∑ a : Fin (r + 1), jimboWeight (genericUnit ℤ) a), mul_assoc,
      sum_jimboWeight_mul_universalJimboReduced]

/-- `universalJimboReduced N` satisfies the oriented HOMFLY skein relation with `a = T ^ N` and
`z = T - T⁻¹`, uniformly for all `N : ℕ` (including `N = 0`). -/
theorem universalJimboReduced_skein (N : ℕ) {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    ↑((genericUnit ℤ) ^ N) *
        universalJimboReduced N ⟨n, b * sigma (n := n + 1) i * c⟩ -
      ↑(((genericUnit ℤ)⁻¹) ^ N) *
        universalJimboReduced N ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ =
      ((genericUnit ℤ : LaurentPolynomial ℤ) - ↑(genericUnit ℤ)⁻¹) *
        universalJimboReduced N ⟨n, b * c⟩ := by
  rcases N with _ | r
  · simpa using normalizedBurauAlexander_skein b c i (genericUnit ℤ)⁻¹
  · apply mul_left_cancel₀ (sum_jimboWeight_genericUnit_ne_zero r)
    simpa only [mul_sub, mul_left_comm (∑ a : Fin (r + 1), jimboWeight (genericUnit ℤ) a),
      sum_jimboWeight_mul_universalJimboReduced] using
      jimboTrace_skein (N := r + 1) (genericUnit ℤ) b c i

end MarkovBraid

/-- Markov-equivalent braids have the same universal reduced `N`-colour invariant, for all
`N : ℕ`. -/
theorem MarkovEquiv.universalJimboReduced_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) (N : ℕ) :
    β.universalJimboReduced N = γ.universalJimboReduced N := by
  rcases N with _ | r
  · exact h.normalizedBurauAlexander_eq (genericUnit ℤ)⁻¹
  · rw [MarkovBraid.universalJimboReduced_succ_eq_iff,
      MarkovBraid.sum_jimboWeight_mul_universalJimboReduced, h.jimboTrace_eq]

namespace MarkovBraid

/-- Evaluating a universal enhancement weight at `q : Rˣ` produces `jimboWeight q a`. -/
private theorem eval₂_jimboWeight_genericUnit {R : Type*} [CommRing R] {N : ℕ} (q : Rˣ)
    (a : Fin N) :
    eval₂ (Int.castRingHom R) q (jimboWeight (genericUnit ℤ) a) = jimboWeight q a := by
  rw [jimboWeight_def, jimboWeight_def, genericUnit_zpow_val, eval₂_T]

/-- **Unconditional specialization identity.** For every commutative ring `R`, unit `q : Rˣ`, and
`N : ℕ`, multiplying the specialized universal reduced invariant by the specialized quantum
dimension recovers `β.jimboTrace (N := N) q`. -/
theorem sum_jimboWeight_mul_eval₂_universalJimboReduced {R : Type*} [CommRing R] (N : ℕ)
    (β : MarkovBraid) (q : Rˣ) :
    (∑ a : Fin N, jimboWeight q a) *
        eval₂ (Int.castRingHom R) q (β.universalJimboReduced N) =
      β.jimboTrace (N := N) q := by
  have h := congrArg (eval₂ (Int.castRingHom R) q)
    (sum_jimboWeight_mul_universalJimboReduced N β)
  have hq : Units.map (eval₂ (Int.castRingHom R) q).toMonoidHom (genericUnit ℤ) = q :=
    Units.ext (by simp)
  simpa only [map_mul, map_sum, eval₂_jimboWeight_genericUnit,
    (eval₂ (Int.castRingHom R) q).map_jimboTrace, hq] using h

/-- **Agreement with the Ocneanu Hecke braid trace when `D_N` is invertible.** Even if `q - q⁻¹`
is zero or a non-unit (so `reducedHomfly` cannot be evaluated), whenever `c * D_N = 1` the
specialized universal invariant agrees with
`β.heckeTrace (ocneanuTrace R q (c * q ^ N)) D_N (q ^ N)⁻¹`. -/
theorem eval₂_universalJimboReduced_eq_heckeTrace_ocneanuTrace {R : Type*} [CommRing R]
    {N : ℕ} {q : Rˣ} {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    eval₂ (Int.castRingHom R) q (β.universalJimboReduced N) =
      β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ := by
  rw [heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc,
    ← sum_jimboWeight_mul_eval₂_universalJimboReduced N β q, ← mul_assoc, hc, one_mul]

/-- **Agreement with `jimboReducedTrace` over a field when `D_N ≠ 0`.** -/
theorem eval₂_universalJimboReduced_eq_jimboReducedTrace {K : Type*} [Field K] {N : ℕ} {q : Kˣ}
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) (β : MarkovBraid) :
    eval₂ (Int.castRingHom K) q (β.universalJimboReduced N) =
      β.jimboReducedTrace (N := N) q := by
  rw [eval₂_universalJimboReduced_eq_heckeTrace_ocneanuTrace (inv_mul_cancel₀ hδ),
    ← div_eq_inv_mul, heckeTrace_ocneanuTrace_eq_jimboReducedTrace hδ]

/-- **Agreement with the reduced HOMFLY polynomial when `q - q⁻¹` is invertible.** Even when the
specialized quantum dimension `D_N` vanishes (such as `N = 0` or roots of unity where `D_N(q) = 0`),
evaluating `β.reducedHomfly K` at `a = q ^ N` and `z_HOMFLY = u = q - q⁻¹` agrees with the
specialized universal reduced invariant
`eval₂ (Int.castRingHom R) q (β.universalJimboReduced N)`. -/
theorem eval₂_reducedHomfly_eq_eval₂_universalJimboReduced {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) (N : ℕ) (q u : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) (q ^ N) (β.reducedHomfly K) =
      eval₂ (Int.castRingHom R) q (β.universalJimboReduced N) := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) (q ^ N)
  let ev : LaurentPolynomial ℤ →+* R := eval₂ (Int.castRingHom R) q
  have hD : e (homflyUnknot K) = ∑ a : Fin N, jimboWeight q a :=
    eval₂_homflyUnknot_jimbo φ N q u hu
  refine congrFun (eq_of_skein (q ^ N) ((q : R) - ↑q⁻¹) (∑ a : Fin N, jimboWeight q a)
    (F := fun γ ↦ e (γ.reducedHomfly K)) (G := fun γ ↦ ev (γ.universalJimboReduced N))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun _ _ h ↦ congrArg ev (h.universalJimboReduced_eq N))
    (fun n c i ↦ ?_) (fun n c i ↦ ?_)
    (fun n b ↦ by simp only [reducedHomfly_strandIncl, map_mul, hD, smul_eq_mul])
    (fun n b ↦ by
      simp only [universalJimboReduced_strandIncl, map_mul, map_sum, smul_eq_mul]
      simp only [ev, eval₂_jimboWeight_genericUnit])
    (by simp [e, ev])) β
  · have h := congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
    simpa only [e, map_sub, map_mul, eval₂_T, eval₂_C, zpow_one, zpow_neg_one, one_mul, hu,
      smul_eq_mul] using h
  · have h := congrArg ev (universalJimboReduced_skein N (1 : BraidGroup (n + 1)) c i)
    simpa only [ev, ← inv_pow, map_sub, map_mul, genericUnit_val, genericUnit_inv,
      Units.val_pow_eq_pow_val, map_pow, eval₂_T, zpow_one, zpow_neg_one, one_mul,
      smul_eq_mul] using h

/-- **Unreduced `sl_N` specialization of HOMFLY over any commutative ring.** For every `N : ℕ`
(including `N = 0`), when `q - q⁻¹` is a unit `u`, evaluating `β.homfly K` at `a = q ^ N` and
`z_HOMFLY = u` recovers `β.jimboTrace (N := N) q`. -/
theorem eval₂_homfly_eq_jimboTrace {K R : Type*} [Field K] [CommRing R] (φ : K →+* R) (N : ℕ)
    (q u : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) (q ^ N) (β.homfly K) = β.jimboTrace (N := N) q := by
  rw [← homflyUnknot_mul_reducedHomfly K β, map_mul, eval₂_homflyUnknot_jimbo φ N q u hu,
    eval₂_reducedHomfly_eq_eval₂_universalJimboReduced φ N q u hu,
    sum_jimboWeight_mul_eval₂_universalJimboReduced]

/-! ### Explicit evaluation at zero-factor specializations -/

/-- **Zero-factor specialization I (`N = 0`, where `D_0 = 0` identically).** For every commutative
ring `R` and unit `q : Rˣ` (without requiring `q - q⁻¹` to be a unit, so including `q = ±1`),
`universalJimboReduced 0` specializes at `q` to `β.normalizedBurauAlexander q⁻¹`. -/
theorem eval₂_universalJimboReduced_zero {R : Type*} [CommRing R] (β : MarkovBraid) (q : Rˣ) :
    eval₂ (Int.castRingHom R) q (β.universalJimboReduced 0) =
      β.normalizedBurauAlexander q⁻¹ := by
  let ev : LaurentPolynomial ℤ →+* R := eval₂ (Int.castRingHom R) q
  refine congrFun (eq_of_skein 1 ((q : R) - ↑q⁻¹) 0
    (F := fun γ ↦ ev (γ.universalJimboReduced 0))
    (G := fun γ ↦ γ.normalizedBurauAlexander q⁻¹)
    (fun _ _ h ↦ congrArg ev (h.universalJimboReduced_eq 0))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq q⁻¹)
    (fun n c i ↦ ?_)
    (fun n c i ↦ by simpa [inv_inv] using normalizedBurauAlexander_skein 1 c i q⁻¹)
    (fun n b ↦ by simp [universalJimboReduced_strandIncl])
    (fun n b ↦ by simp)
    (by simp [ev])) β
  have h := congrArg ev (universalJimboReduced_skein 0 (1 : BraidGroup (n + 1)) c i)
  simpa only [ev, pow_zero, Units.val_one, one_mul, map_sub, map_mul, genericUnit_val,
    genericUnit_inv, eval₂_T, zpow_one, zpow_neg_one, one_smul, inv_one, smul_eq_mul] using h

/-- Markov-equivalent braids have the same number of closure components. -/
private theorem card_components_eq_of_markovEquiv {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    Nat.card β.Components = Nat.card γ.Components :=
  h.induction (motive := fun β γ ↦ Nat.card β.Components = Nat.card γ.Components)
    (fun hmove ↦ by
      cases hmove with
      | conj b c => exact (Nat.card_congr (conjComponentsEquiv b c)).symm
      | stabilize b => exact (Nat.card_congr (stabilizeComponentsEquiv b)).symm
      | stabilizeInv b => exact (Nat.card_congr (stabilizeInvComponentsEquiv b)).symm)
    (fun _ ↦ rfl) (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih')

/-- Adding an uncrossed strand adds one component to `MarkovBraid.Components`. -/
private theorem card_components_strandIncl {n : ℕ} (b : BraidGroup (n + 1)) :
    Nat.card (⟨n + 1, strandIncl b⟩ : MarkovBraid).Components =
      Nat.card (⟨n, b⟩ : MarkovBraid).Components + 1 := by
  rw [← orbitCount_def, ← orbitCount_def]
  exact (orbitCount_add_one_eq_of_semiconj
    (f := (Fin.castSucc : Fin (n + 1) → Fin (n + 2))) (p := Fin.last (n + 1))
    (σ := permHom (n + 1) b) (τ := permHom (n + 2) (strandIncl b))
    (Fin.castSucc_injective _) (fun i ↦ (Fin.castSucc_lt_last i).ne)
    (fun _ hy ↦ Fin.eq_castSucc_of_ne_last hy)
    fun i ↦ (permHom_strandIncl_castSucc b i).symm).symm

/-- Reversing the sign of a single crossing preserves `Nat.card β.Components`, since the
underlying transposition is an involution. -/
private theorem card_components_sigma_mul_eq_inv {n : ℕ} (c : BraidGroup (n + 1)) (i : Fin n) :
    Nat.card (⟨n, sigma (n := n + 1) i * c⟩ : MarkovBraid).Components =
      Nat.card (⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ : MarkovBraid).Components := by
  have hi :
      permHom (n + 1) ((sigma (n := n + 1) i)⁻¹) = permHom (n + 1) (sigma (n := n + 1) i) := by
    rw [map_inv, permHom_sigma, transposition_eq_swap, Equiv.swap_inv]
  simp only [Components, map_mul, hi]

/-- The trivial one-strand braid has exactly one component. -/
private theorem card_components_one_strand :
    Nat.card (⟨0, (1 : BraidGroup 1)⟩ : MarkovBraid).Components = 1 := by
  rw [← orbitCount_def, map_one, orbitCount_one, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- At `q = 1`, the writhe-normalized `N`-colour Jimbo trace equals `N ^ Nat.card β.Components` in
every commutative ring and for every `N : ℕ`. -/
@[simp]
theorem jimboTrace_one_param {R : Type*} [CommRing R] (N : ℕ) (β : MarkovBraid) :
    β.jimboTrace (N := N) (1 : Rˣ) = (N : R) ^ Nat.card β.Components := by
  refine congrFun (eq_of_skein 1 0 (N : R)
    (F := fun γ ↦ γ.jimboTrace (N := N) (1 : Rˣ))
    (G := fun γ ↦ (N : R) ^ Nat.card γ.Components)
    (fun _ _ h ↦ h.jimboTrace_eq 1)
    (fun _ _ h ↦ by rw [card_components_eq_of_markovEquiv h])
    (fun n c i ↦ by simpa using jimboTrace_skein (N := N) (1 : Rˣ) 1 c i)
    (fun n c i ↦ by simp [card_components_sigma_mul_eq_inv])
    (fun n b ↦ by simp [jimboTrace_strandIncl])
    (fun n b ↦ by simp [card_components_strandIncl, pow_succ'])
    (by simp [card_components_one_strand])) β

/-- **Zero-factor specialization II (`q = 1`, where `q - q⁻¹ = 0` and, in characteristic dividing
`r + 1`, also `D_{r+1}(1) = 0`).** For every commutative ring `R` and `r : ℕ`,
`universalJimboReduced (r + 1)` specializes at `1 : Rˣ` to
`((r + 1 : ℕ) : R) ^ (Nat.card β.Components - 1)`. -/
@[simp]
theorem eval₂_universalJimboReduced_succ_one {R : Type*} [CommRing R] (r : ℕ) (β : MarkovBraid) :
    eval₂ (Int.castRingHom R) (1 : Rˣ) (β.universalJimboReduced (r + 1)) =
      ((r + 1 : ℕ) : R) ^ (Nat.card β.Components - 1) := by
  let ev : LaurentPolynomial ℤ →+* R := eval₂ (Int.castRingHom R) (1 : Rˣ)
  refine congrFun (eq_of_skein 1 0 ((r + 1 : ℕ) : R)
    (F := fun γ ↦ ev (γ.universalJimboReduced (r + 1)))
    (G := fun γ ↦ ((r + 1 : ℕ) : R) ^ (Nat.card γ.Components - 1))
    (fun _ _ h ↦ congrArg ev (h.universalJimboReduced_eq (r + 1)))
    (fun _ _ h ↦ by rw [card_components_eq_of_markovEquiv h])
    (fun n c i ↦ ?_)
    (fun n c i ↦ by simp [card_components_sigma_mul_eq_inv])
    (fun n b ↦ ?_)
    (fun n b ↦ ?_)
    (by simp [ev, card_components_one_strand])) β
  · have h := congrArg ev (universalJimboReduced_skein (r + 1) (1 : BraidGroup (n + 1)) c i)
    simpa only [ev, map_sub, map_mul, genericUnit_val, genericUnit_inv,
      Units.val_pow_eq_pow_val, map_pow, eval₂_T, one_zpow, inv_one, Units.val_one, one_pow,
      one_mul, sub_self, zero_mul, one_smul, zero_smul] using h
  · simp only [universalJimboReduced_strandIncl, map_mul, map_sum, smul_eq_mul]
    simp [ev, eval₂_jimboWeight_genericUnit]
  · have hpos : 1 ≤ Nat.card (⟨n, b⟩ : MarkovBraid).Components := Nat.card_pos
    have hc : Nat.card (⟨n, b⟩ : MarkovBraid).Components + 1 - 1 =
        (Nat.card (⟨n, b⟩ : MarkovBraid).Components - 1) + 1 := by omega
    rw [card_components_strandIncl, hc, pow_succ', smul_eq_mul]

/-- **Zero-factor specialization III (`N = 2` at `q + q⁻¹ = 0`, where `D_2(q) = 0`).** At a fourth
root of unity `(q : R) + ↑q⁻¹ = 0`, the `2`-colour quantum dimension vanishes so neither
`heckeTrace` nor `jimboReducedTrace` can divide by `D_2(q)`, whereas `universalJimboReduced 2`
evaluates regularly to the link-determinant specialization `β.normalizedBurauAlexander q`. -/
theorem eval₂_universalJimboReduced_two_of_add_inv_eq_zero {R : Type*} [CommRing R] {q : Rˣ}
    (hq : (q : R) + ↑q⁻¹ = 0) (β : MarkovBraid) :
    eval₂ (Int.castRingHom R) q (β.universalJimboReduced 2) =
      β.normalizedBurauAlexander q := by
  let ev : LaurentPolynomial ℤ →+* R := eval₂ (Int.castRingHom R) q
  have hq2 : (q : R) ^ 2 = -1 := by
    linear_combination (q : R) * hq - Units.mul_inv q
  have hqinv2 : (↑q⁻¹ : R) ^ 2 = -1 := by
    linear_combination (↑q⁻¹ : R) * hq - Units.inv_mul q
  have hD2 : (∑ a : Fin 2, jimboWeight q a) = 0 := by
    rw [Fin.sum_univ_two]
    simpa [jimboWeight_def] using hq
  refine congrFun (eq_of_skein 1 ((↑q⁻¹ : R) - (q : R)) 0
    (F := fun γ ↦ ev (γ.universalJimboReduced 2))
    (G := fun γ ↦ γ.normalizedBurauAlexander q)
    (fun _ _ h ↦ congrArg ev (h.universalJimboReduced_eq 2))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq q)
    (fun n c i ↦ ?_)
    (fun n c i ↦ by simpa using normalizedBurauAlexander_skein 1 c i q)
    (fun n b ↦ by
      simp only [universalJimboReduced_strandIncl, map_mul, map_sum, zero_smul]
      simp only [ev, eval₂_jimboWeight_genericUnit, hD2, zero_mul])
    (fun n b ↦ by simp)
    (by simp [ev])) β
  have h := congrArg ev (universalJimboReduced_skein 2 (1 : BraidGroup (n + 1)) c i)
  simp only [ev, map_sub, map_mul, genericUnit_val, genericUnit_inv,
    Units.val_pow_eq_pow_val, map_pow, eval₂_T, zpow_one, zpow_neg_one, one_mul, hq2,
    hqinv2] at h
  simp only [inv_one, Units.val_one, smul_eq_mul]
  linear_combination -h

end MarkovBraid

end TauCeti
