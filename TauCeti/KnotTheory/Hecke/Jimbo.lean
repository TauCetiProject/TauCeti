/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke
public import TauCeti.KnotTheory.Homfly.Reduced
import Mathlib.Tactic.LinearCombination

/-!
# Comparison of the normalized Hecke braid trace with the Jimbo and HOMFLY invariants

This file connects the algebraic braid-closure invariant `MarkovBraid.heckeTrace` built from the
Ocneanu trace on `InfiniteTypeAHeckeAlgebra` with two invariants constructed from Jimbo's tensor
representations:

1. **Finite-colour Turaev–Jimbo comparison.** Over any commutative ring `R`, when `c` is an
   inverse to the `N`-colour quantum dimension `δ = ∑ a : Fin N, jimboWeight q a`, normalizing
   `ocneanuTrace R q (c * q ^ N)` with strand-number factor `C = δ` and writhe unit `l = (q ^ N)⁻¹`
   recovers `c * β.jimboTrace (N := N) q` on every braid `β`
   (`TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace`). Over a field with `δ ≠ 0`,
   this equals `β.jimboReducedTrace (N := N) q`
   (`TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`).

2. **HOMFLY comparison.** When `R` receives a ring homomorphism `φ : K →+* R` from a field `K`,
   whenever `τ` is a Markov trace with parameter `z` normalized by `C * l * z = 1` and
   `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, and `u : Rˣ` satisfies `u = q - q⁻¹`, evaluating
   `β.reducedHomfly K` along `φ` at inner variable `u` and outer variable `l⁻¹` recovers
   `β.heckeTrace τ C l` (`TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`), while evaluating
   the unreduced `β.homfly K` gives `C * β.heckeTrace τ C l`
   (`TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`).

The intrinsic regular extension of the generic normalized Ocneanu braid trace across the
zero-factor specializations `l = ±1` over an arbitrary commutative ring (without assuming a map
from a field) is constructed in `TauCeti.KnotTheory.Hecke.Regular`.

## Main results

* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace` and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`: finite-colour comparison with
  the writhe-normalized and reduced Jimbo traces.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace` and
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`: comparison with the two-variable HOMFLY
  polynomials along a ring homomorphism from a field.
* `TauCeti.MarkovBraid.homflySpecialization_reducedHomfly_eq_heckeTrace` and
  `TauCeti.MarkovBraid.reducedHomfly_eq_of_homflySpecialization_eq_heckeTrace`: determination of
  `reducedHomfly` by the positive-rank Ocneanu braid traces.

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett, A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
* M. Jimbo, *A q-analogue of U(gl(N + 1)), Hecke algebra, and the Yang-Baxter equation*,
  Lett. Math. Phys. 11 (1986), 247–252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public noncomputable section

namespace TauCeti

open LaurentPolynomial
open InfiniteTypeAHeckeAlgebra (IsMarkovTrace ocneanuTrace isMarkovTrace_ocneanuTrace)
open scoped BigOperators

section FiniteColour

variable {R : Type*} [CommRing R] {N : ℕ}

namespace KnotTheory

/-- When `c` inverts the `N`-colour quantum dimension,
`(∑ a, jimboWeight q a) * (q ^ N)⁻¹ * (c * q ^ N) = 1`. -/
theorem sum_jimboWeight_mul_inv_pow_mul_eq_one (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑(q ^ N)⁻¹ : R) * (c * ↑(q ^ N)) = 1 := by
  have hq : (↑(q ^ N)⁻¹ : R) * ↑(q ^ N) = 1 := Units.inv_mul (q ^ N)
  linear_combination (∑ a : Fin N, jimboWeight q a) * c * hq + hc

/-- When `c` inverts the `N`-colour quantum dimension,
`(∑ a, jimboWeight q a) * ((q ^ N)⁻¹)⁻¹ * (c * q ^ N - (q - q⁻¹)) = 1`. -/
theorem sum_jimboWeight_mul_inv_inv_pow_mul_sub_eq_one (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑((q ^ N)⁻¹)⁻¹ : R) *
        (c * ↑(q ^ N) - ((q : R) - ↑q⁻¹)) = 1 := by
  rw [inv_inv]
  have hs := jimboWeight_sum (N := N) q
  have hq : (↑(q ^ N) : R) * ↑((q⁻¹) ^ N) = 1 := by
    rw [inv_pow]
    exact Units.mul_inv (q ^ N)
  linear_combination (↑(q ^ N) : R) ^ 2 * hc - (↑(q ^ N) : R) * hs + hq

end KnotTheory

namespace MarkovBraid

open KnotTheory BraidGroup

/-- **Finite-colour comparison between the normalized Ocneanu braid trace and the writhe-normalized
Jimbo trace.** When `c` inverts the `N`-colour quantum dimension, `MarkovBraid.heckeTrace` of
`ocneanuTrace R q (c * q ^ N)` equals `c` times `MarkovBraid.jimboTrace`. -/
theorem heckeTrace_ocneanuTrace_eq_mul_jimboTrace (β : MarkovBraid) (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      c * β.jimboTrace (N := N) q := by
  rw [heckeTrace_def, jimboTrace_def, ← TypeAHeckeAlgebra.toInfinite_braidHom,
    ← TypeAHeckeAlgebra.pow_mul_jimboWeightedTrace_eq_ocneanuTrace hc,
    TypeAHeckeAlgebra.jimboWeightedTrace_braidHom, inv_zpow', zpow_neg]
  have hcancel :
      (∑ a : Fin N, jimboWeight q a) ^ β.predStrands * c ^ (β.predStrands + 1) = c := by
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_comm (∑ a : Fin N, jimboWeight q a) c, hc,
      one_pow, one_mul]
  linear_combination
    ↑(((q ^ N) ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))⁻¹) *
      jimboWeightedTrace (N := N) q β.braid * hcancel

/-- Multiplying the normalized Ocneanu braid trace at `z = c * q ^ N` by the quantum dimension
recovers the unreduced writhe-normalized Jimbo trace `MarkovBraid.jimboTrace`. -/
theorem sum_jimboWeight_mul_heckeTrace_ocneanuTrace_eq_jimboTrace (β : MarkovBraid) (q : Rˣ)
    {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      β.jimboTrace (N := N) q := by
  rw [heckeTrace_ocneanuTrace_eq_mul_jimboTrace β q hc, ← mul_assoc, mul_comm _ c, hc, one_mul]

end MarkovBraid

/-- On `Quot MarkovEquiv`, `heckeBraidInvariant` of the Ocneanu trace at `c * q ^ N` agrees with
`c * β.jimboTrace q`. -/
theorem heckeBraidInvariant_ocneanuTrace_mk_eq_mul_jimboTrace (β : MarkovBraid) (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) :
    heckeBraidInvariant (isMarkovTrace_ocneanuTrace (q := q) (c * ↑(q ^ N)))
        (∑ a : Fin N, KnotTheory.jimboWeight q a) (q ^ N)⁻¹
        (KnotTheory.sum_jimboWeight_mul_inv_pow_mul_eq_one q hc)
        (KnotTheory.sum_jimboWeight_mul_inv_inv_pow_mul_sub_eq_one q hc)
        (Quot.mk MarkovEquiv β) =
      c * β.jimboTrace (N := N) q :=
  (heckeBraidInvariant_mk _ _ _ _ _ β).trans
    (β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace q hc)

namespace MarkovBraid

open KnotTheory

/-- Over a field where the `N`-colour quantum dimension is nonzero, the normalized Ocneanu braid
trace at `q ^ N / [N]_q` equals the reduced Jimbo trace `MarkovBraid.jimboReducedTrace`. -/
theorem heckeTrace_ocneanuTrace_eq_jimboReducedTrace {K : Type*} [Field K] (β : MarkovBraid)
    (q : Kˣ) (hδ : ∑ a : Fin N, jimboWeight q a ≠ 0) :
    β.heckeTrace (ocneanuTrace K q (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      β.jimboReducedTrace (N := N) q := by
  have hc : (∑ a : Fin N, jimboWeight q a)⁻¹ * ∑ a : Fin N, jimboWeight q a = 1 :=
    inv_mul_cancel₀ hδ
  simpa only [div_eq_inv_mul, jimboReducedTrace_def] using
    β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace q hc

end MarkovBraid

end FiniteColour

section HomflyComparison

variable {K R : Type*} [Field K] [CommRing R]

namespace KnotTheory

/-- Given a ring homomorphism `φ : K →+* R` from a field `K`, under the normalization equations
`C * l * z = 1` and `C * l⁻¹ * (z - u) = 1`, evaluating `homflyUnknot K` along `φ` at inner
variable `u` and outer variable `l⁻¹` produces the strand-number factor `C`. -/
theorem eval₂_homflyUnknot_eq_of_hecke_normalization (φ : K →+* R) {u l : Rˣ} {z C : R}
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - (u : R)) = 1) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  simp only [homflyUnknot_def, map_mul, map_sub, eval₂_C, eval₂_T, zpow_one, zpow_neg_one, inv_inv]
  have hCz : C * z = ↑l⁻¹ := by
    linear_combination (↑l⁻¹ : R) * hpos - C * z * l.mul_inv
  have hCsub : C * (z - (u : R)) = (l : R) := by
    linear_combination (l : R) * hneg - C * (z - (u : R)) * l.inv_mul
  rw [← hCz, ← hCsub]
  linear_combination C * u.mul_inv

end KnotTheory

namespace MarkovBraid

open KnotTheory BraidGroup

/-- **HOMFLY comparison for normalized Hecke braid traces.** When `R` receives a ring homomorphism
`φ : K →+* R` from a field `K` and `τ` is a Markov trace with parameter `z` normalized by `C` and
`l`, evaluating `β.reducedHomfly K` along `φ` at inner variable `u = q - q⁻¹` and outer variable
`l⁻¹` gives `β.heckeTrace τ C l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (φ : K →+* R) {q u l : Rˣ} {z C : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) = β.heckeTrace τ C l := by
  refine congrFun (eq_heckeTrace_of_skein hτ hpos hneg
    (F := fun γ ↦ eval₂ (eval₂ φ u) l⁻¹ (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg _ (h.reducedHomfly_eq K))
    (fun n c i ↦ ?_) (fun n b ↦ ?_) (by simp)) β
  · have hs := congrArg (eval₂ (eval₂ φ u) l⁻¹) (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
    simpa only [map_sub, map_mul, eval₂_T, eval₂_C, zpow_one, zpow_neg_one, inv_inv, one_mul,
      hu] using hs
  · rw [reducedHomfly_strandIncl, map_mul,
      eval₂_homflyUnknot_eq_of_hecke_normalization φ hpos (by rwa [← hu] at hneg)]

/-- Unreduced HOMFLY comparison: when `R` receives a ring homomorphism `φ : K →+* R` from a field
`K`, evaluating `β.homfly K` along `φ` at inner variable `u = q - q⁻¹` and outer variable `l⁻¹`
gives `C * β.heckeTrace τ C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace (φ : K →+* R) {q u l : Rˣ} {z C : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) = C * β.heckeTrace τ C l := by
  rw [← homflyUnknot_mul_reducedHomfly, map_mul,
    eval₂_homflyUnknot_eq_of_hecke_normalization φ hpos (by rwa [← hu] at hneg),
    eval₂_reducedHomfly_eq_heckeTrace φ hτ hpos hneg hu]

/-- Every positive-rank `homflySpecialization` of `β.reducedHomfly K` equals the normalized Ocneanu
braid trace in `RatFunc K` at `q = X`, `z = X ^ (N + 1) / [N + 1]_X`, `C = [N + 1]_X`, and
`l = (X ^ (N + 1))⁻¹`. -/
theorem homflySpecialization_reducedHomfly_eq_heckeTrace (β : MarkovBraid) (N : ℕ) :
    let q : (RatFunc K)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
    homflySpecialization K (N + 1) (β.reducedHomfly K) =
      β.heckeTrace
        (ocneanuTrace (RatFunc K) q (↑(q ^ (N + 1)) / ∑ a : Fin (N + 1), jimboWeight q a))
        (∑ a : Fin (N + 1), jimboWeight q a) (q ^ (N + 1))⁻¹ := by
  intro q
  rw [homflySpecialization_reducedHomfly,
    ← heckeTrace_ocneanuTrace_eq_jimboReducedTrace β q (jimboWeight_sum_X_ne_zero N)]

/-- The positive-rank normalized Ocneanu braid traces uniquely determine `β.reducedHomfly K`. -/
theorem reducedHomfly_eq_of_homflySpecialization_eq_heckeTrace {β : MarkovBraid}
    {P : LaurentPolynomial (LaurentPolynomial K)}
    (h : ∀ N,
      let q : (RatFunc K)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
      homflySpecialization K (N + 1) P =
        β.heckeTrace
          (ocneanuTrace (RatFunc K) q (↑(q ^ (N + 1)) / ∑ a : Fin (N + 1), jimboWeight q a))
          (∑ a : Fin (N + 1), jimboWeight q a) (q ^ (N + 1))⁻¹) :
    β.reducedHomfly K = P := by
  refine reducedHomfly_eq_of_homflySpecialization_eq K fun N ↦ ?_
  rw [h N, heckeTrace_ocneanuTrace_eq_jimboReducedTrace β _ (jimboWeight_sum_X_ne_zero N)]

end MarkovBraid

end HomflyComparison

end TauCeti
