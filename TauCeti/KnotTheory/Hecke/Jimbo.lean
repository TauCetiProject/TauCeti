/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke
public import TauCeti.KnotTheory.Homfly.Alexander
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Laurent.Regular

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
   (`TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`). The two-strand unlink and
   both single-crossing two-strand closures are verified explicitly.

2. **Universal HOMFLY comparison.** Whenever `τ` is a Markov trace with parameter `z` normalized by
   `C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, and `u : Rˣ` satisfies `u = q - q⁻¹`,
   evaluating `β.reducedHomfly K` at inner variable `u` and outer variable `l⁻¹` recovers
   `β.heckeTrace τ C l` (`TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`), while evaluating
   the unreduced `β.homfly K` gives `C * β.heckeTrace τ C l`.

3. **Regularity across zero-factor specializations (`C = 0`).** At `l = ±1`, the strand factor
   `C = (l⁻¹ - l) * u⁻¹` vanishes and the Ocneanu parameter `z = u / (l * (l⁻¹ - l))` has a pole.
   Over every commutative ring `R`, `LaurentPolynomial R` embeds injectively into
   `Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`, and an induction on the finite stages
   of `InfiniteTypeAHeckeAlgebra` shows that the generic normalized Ocneanu trace
   `MarkovBraid.heckeUniversalTrace` equals the image of a unique Laurent polynomial
   `MarkovBraid.heckeRegularExtension` in `R[l, l⁻¹]`. After establishing this regular extension,
   we evaluate it at both zero-factor points `l = 1` (yielding the Conway/Burau Alexander
   specialization) and `l = -1` (yielding the signed Conway specialization).

## Main definitions

* `TauCeti.MarkovBraid.heckeUniversalTrace`: the normalized Ocneanu braid trace at the generic
  writhe parameter in `Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`.
* `TauCeti.MarkovBraid.heckeRegularExtension`: the unique regular Laurent polynomial in
  `LaurentPolynomial R` extending `heckeUniversalTrace` across `T (-1) - T 1 = 0`.

## Main results

* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace` and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`: finite-colour comparison with
  the writhe-normalized and reduced Jimbo traces.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace` and
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`: comparison with the two-variable HOMFLY
  polynomials.
* `TauCeti.MarkovBraid.existsUnique_algebraMap_eq_heckeUniversalTrace`: existence and uniqueness of
  the regular Laurent polynomial extension across `l = ±1` over any commutative ring.
* `TauCeti.MarkovBraid.eval₂_one_heckeRegularExtension_eq_normalizedBurauAlexander` and
  `TauCeti.MarkovBraid.eval₂_neg_one_heckeRegularExtension_skein`: evaluations at the two
  zero-factor specializations `l = 1` and `l = -1`.

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

/-- When `c` inverts the `N`-colour quantum dimension, `C = ∑ a, jimboWeight q a`,
`l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy the positive Markov stabilization identity
`C * l * z = 1`. -/
theorem jimboWeight_sum_hecke_pos (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑(q ^ N)⁻¹ : R) * (c * ↑(q ^ N)) = 1 := by
  have hq : (↑(q ^ N)⁻¹ : R) * ↑(q ^ N) = 1 := Units.inv_mul (q ^ N)
  linear_combination (∑ a : Fin N, jimboWeight q a) * c * hq + hc

/-- When `c` inverts the `N`-colour quantum dimension, `C = ∑ a, jimboWeight q a`,
`l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy the negative Markov stabilization identity
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`. -/
theorem jimboWeight_sum_hecke_neg (q : Rˣ) {c : R}
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
    ← TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace hc,
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

/-- Explicit value of the finite-colour normalized Ocneanu braid trace on the two-strand unlink. -/
theorem heckeTrace_ocneanuTrace_two_strand_one (q : Rˣ) (c : R) :
    heckeTrace ⟨1, 1⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ =
      ∑ a : Fin N, jimboWeight q a :=
  heckeTrace_two_strand_one (isMarkovTrace_ocneanuTrace _).map_one _ _

/-- Explicit value of `c * jimboTrace` on the two-strand unlink, matching
`heckeTrace_ocneanuTrace_two_strand_one`. -/
theorem mul_jimboTrace_two_strand_one (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    c * jimboTrace (N := N) ⟨1, 1⟩ q = ∑ a : Fin N, jimboWeight q a := by
  rw [jimboTrace_one, sq, ← mul_assoc, hc, one_mul]

/-- Explicit value of the finite-colour normalized Ocneanu braid trace on the positive
single-crossing two-strand closure. -/
theorem heckeTrace_ocneanuTrace_sigma_two (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, sigma (n := 2) 0⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ = 1 :=
  heckeTrace_sigma_two_eq_one (isMarkovTrace_ocneanuTrace _) _ _
    (jimboWeight_sum_hecke_pos q hc)

/-- Explicit value of `c * jimboTrace` on the positive single-crossing two-strand closure, matching
`heckeTrace_ocneanuTrace_sigma_two`. -/
theorem mul_jimboTrace_sigma_two (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    c * jimboTrace (N := N) ⟨1, sigma (n := 2) 0⟩ q = 1 :=
  (heckeTrace_ocneanuTrace_eq_mul_jimboTrace ⟨1, sigma (n := 2) 0⟩ q hc).symm.trans
    (heckeTrace_ocneanuTrace_sigma_two q hc)

/-- Explicit value of the finite-colour normalized Ocneanu braid trace on the negative
single-crossing two-strand closure. -/
theorem heckeTrace_ocneanuTrace_sigma_two_inv (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) (q ^ N)⁻¹ = 1 :=
  heckeTrace_sigma_two_inv_eq_one (isMarkovTrace_ocneanuTrace _) _ _
    (jimboWeight_sum_hecke_neg q hc)

/-- Explicit value of `c * jimboTrace` on the negative single-crossing two-strand closure, matching
`heckeTrace_ocneanuTrace_sigma_two_inv`. -/
theorem mul_jimboTrace_sigma_two_inv (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    c * jimboTrace (N := N) ⟨1, (sigma (n := 2) 0)⁻¹⟩ q = 1 :=
  (heckeTrace_ocneanuTrace_eq_mul_jimboTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ q hc).symm.trans
    (heckeTrace_ocneanuTrace_sigma_two_inv q hc)

end MarkovBraid

/-- On `Quot MarkovEquiv`, `heckeBraidInvariant` of the Ocneanu trace at `c * q ^ N` agrees with
`c * β.jimboTrace q`. -/
theorem heckeBraidInvariant_ocneanuTrace_mk_eq_mul_jimboTrace (β : MarkovBraid) (q : Rˣ) {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) :
    heckeBraidInvariant (isMarkovTrace_ocneanuTrace (q := q) (c * ↑(q ^ N)))
        (∑ a : Fin N, KnotTheory.jimboWeight q a) (q ^ N)⁻¹
        (KnotTheory.jimboWeight_sum_hecke_pos q hc)
        (KnotTheory.jimboWeight_sum_hecke_neg q hc)
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

/-- Under the Hecke normalization equations `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`, evaluating `homflyUnknot K` at inner variable `u = q - q⁻¹` and
outer variable `l⁻¹` produces the strand-number factor `C`. -/
theorem eval₂_homflyUnknot_eq_of_hecke_normalization (φ : K →+* R) {q u l : Rˣ} {z C : R}
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  simp only [homflyUnknot_def, map_mul, map_sub, eval₂_C, eval₂_T, zpow_one, zpow_neg_one, inv_inv]
  rw [← hu] at hneg
  have hCz : C * z = ↑l⁻¹ := by
    linear_combination (↑l⁻¹ : R) * hpos - C * z * l.mul_inv
  have hCsub : C * (z - (u : R)) = (l : R) := by
    linear_combination (l : R) * hneg - C * (z - (u : R)) * l.inv_mul
  rw [← hCz, ← hCsub]
  linear_combination C * u.mul_inv

end KnotTheory

namespace MarkovBraid

open KnotTheory BraidGroup

/-- **Universal HOMFLY comparison for normalized Hecke braid traces.** Whenever `τ` is a Markov
trace with parameter `z` normalized by `C` and `l`, evaluating `β.reducedHomfly K` at inner
variable `u = q - q⁻¹` and outer variable `l⁻¹` gives `β.heckeTrace τ C l`. -/
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
      eval₂_homflyUnknot_eq_of_hecke_normalization φ hpos hneg hu]

/-- Unreduced HOMFLY comparison: evaluating `β.homfly K` at inner variable `u = q - q⁻¹` and outer
variable `l⁻¹` gives `C * β.heckeTrace τ C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace (φ : K →+* R) {q u l : Rˣ} {z C : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) = C * β.heckeTrace τ C l := by
  rw [← homflyUnknot_mul_reducedHomfly, map_mul,
    eval₂_homflyUnknot_eq_of_hecke_normalization φ hpos hneg hu,
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

section ZeroFactorRegularity

variable {R : Type*} [CommRing R]

/-- Over every commutative ring `R`, `LaurentPolynomial R` injects into the localization away from
`T (-1) - T 1`. -/
theorem algebraMap_localizationAway_T_neg_one_sub_T_one_injective :
    Function.Injective
      (algebraMap (LaurentPolynomial R)
        (Localization.Away (T (-1) - T 1 : LaurentPolynomial R))) := by
  refine IsLocalization.injective _
    (M := Submonoid.powers (T (-1) - T 1 : LaurentPolynomial R)) (Submonoid.powers_le.mpr ?_)
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_
  exact (isRegular_T_sub_T (by decide : (-1 : ℤ) ≠ 1)).right (hx.trans (zero_mul _).symm)

namespace MarkovBraid

open KnotTheory BraidGroup

/-- The normalized Ocneanu braid trace at the generic writhe unit `l = T 1` inside
`Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`, where the strand factor
`C = (T (-1) - T 1) * u⁻¹` is invertible and the Ocneanu parameter is
`z = u * ((T (-1) - T 1) * T 1)⁻¹`. -/
def heckeUniversalTrace (β : MarkovBraid) (q u : Rˣ) :
    Localization.Away (T (-1) - T 1 : LaurentPolynomial R) :=
  let s : LaurentPolynomial R := T (-1) - T 1
  let S := Localization.Away s
  let ι : LaurentPolynomial R →+* S := algebraMap (LaurentPolynomial R) S
  let qS : Sˣ := Units.map ((ι.comp C) : R →* S) q
  let uS : Sˣ := Units.map ((ι.comp C) : R →* S) u
  let lS : Sˣ := Units.map (ι : LaurentPolynomial R →* S) (genericUnit R)
  let vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
  β.heckeTrace (ocneanuTrace S qS ↑(uS * (vS * lS)⁻¹)) ↑(vS * uS⁻¹) lS

private theorem heckeUniversal_pos_neg {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    let s : LaurentPolynomial R := T (-1) - T 1
    let S := Localization.Away s
    let ι : LaurentPolynomial R →+* S := algebraMap (LaurentPolynomial R) S
    let qS : Sˣ := Units.map ((ι.comp C) : R →* S) q
    let uS : Sˣ := Units.map ((ι.comp C) : R →* S) u
    let lS : Sˣ := Units.map (ι : LaurentPolynomial R →* S) (genericUnit R)
    let vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
    (↑(vS * uS⁻¹) : S) * (lS : S) * ↑(uS * (vS * lS)⁻¹) = 1 ∧
      (↑(vS * uS⁻¹) : S) * (↑lS⁻¹ : S) *
        (↑(uS * (vS * lS)⁻¹) - ((qS : S) - ↑qS⁻¹)) = 1 := by
  intro s S ι qS uS lS
  set vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
  have hvS : (vS : S) = (↑lS⁻¹ : S) - (lS : S) := by
    simp [vS, s, lS, ι]
  have huS : (uS : S) = (qS : S) - ↑qS⁻¹ := by
    have hqinv : (↑qS⁻¹ : S) = ι (C ↑q⁻¹) := by simp [qS]
    calc
      (uS : S) = ι (C (u : R)) := rfl
      _ = ι (C ((q : R) - ↑q⁻¹)) := by rw [hu]
      _ = (qS : S) - ↑qS⁻¹ := by simp [qS, hqinv, map_sub]
  refine ⟨?_, ?_⟩
  · have hmul (a b c : Sˣ) : a * b⁻¹ * c * (b * (a * c)⁻¹) = 1 := by
      rw [mul_right_comm a b⁻¹ c, mul_assoc (a * c), ← mul_assoc b⁻¹, inv_mul_cancel, one_mul,
        mul_inv_cancel]
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_one]
    exact congrArg Units.val (hmul vS uS lS)
  · rw [← huS]
    have hsub : (↑(uS * (vS * lS)⁻¹) : S) - (uS : S) = ↑(uS * vS⁻¹ * lS) := by
      have hv : (↑vS⁻¹ : S) * ((↑lS⁻¹ : S) - lS) = 1 := by
        rw [← hvS]
        exact vS.inv_mul
      simp only [mul_inv_rev, Units.val_mul]
      linear_combination (uS : S) * hv
    have hmul (a b c : Sˣ) : a * b⁻¹ * c⁻¹ * (b * a⁻¹ * c) = 1 := by
      rw [mul_comm (b * a⁻¹) c, ← mul_assoc (a * b⁻¹ * c⁻¹) c, mul_assoc (a * b⁻¹) c⁻¹ c,
        inv_mul_cancel, mul_one, ← mul_assoc (a * b⁻¹) b a⁻¹, mul_assoc a b⁻¹ b, inv_mul_cancel,
        mul_one, mul_inv_cancel]
    rw [hsub, ← Units.val_mul, ← Units.val_mul, ← Units.val_one]
    exact congrArg Units.val (hmul vS uS lS)

/-- Over every commutative ring `R`, `β.heckeUniversalTrace q u` lies in the image of
`LaurentPolynomial R` inside `Localization.Away (T (-1) - T 1)`. -/
theorem exists_algebraMap_eq_heckeUniversalTrace (β : MarkovBraid) (q u : Rˣ) :
    ∃ P : LaurentPolynomial R,
      algebraMap (LaurentPolynomial R)
          (Localization.Away (T (-1) - T 1 : LaurentPolynomial R)) P =
        β.heckeUniversalTrace q u := by
  let s : LaurentPolynomial R := T (-1) - T 1
  let S := Localization.Away s
  let ι : LaurentPolynomial R →+* S := algebraMap (LaurentPolynomial R) S
  let qS : Sˣ := Units.map ((ι.comp C) : R →* S) q
  let uS : Sˣ := Units.map ((ι.comp C) : R →* S) u
  let lS : Sˣ := Units.map (ι : LaurentPolynomial R →* S) (genericUnit R)
  set vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
  have hqS : algebraMap R S (q : R) = (qS : S) :=
    IsScalarTower.algebraMap_apply R (LaurentPolynomial R) S (q : R)
  have hC : ι ((T (-1) - T 1) * C (↑u⁻¹ : R)) = ↑(vS * uS⁻¹) := by
    have hu_inv : (↑uS⁻¹ : S) = ι (C (↑u⁻¹ : R)) := by simp [uS]
    simp [vS, s, ι, hu_inv, map_mul]
  have hCz : (↑(vS * uS⁻¹) : S) * ↑(uS * (vS * lS)⁻¹) = ι (T (-1)) := by
    have hmul (a b c : Sˣ) : a * b⁻¹ * (b * (a * c)⁻¹) = c⁻¹ := by
      rw [mul_assoc a b⁻¹, ← mul_assoc b⁻¹, inv_mul_cancel, one_mul, mul_inv_rev,
        mul_comm c⁻¹ a⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    have hl_inv : (↑lS⁻¹ : S) = ι (T (-1)) := by simp [lS]
    rw [← Units.val_mul, hmul vS uS lS, hl_inv]
  let zS : S := ↑(uS * (vS * lS)⁻¹)
  let L (n : ℕ) : InfiniteTypeAHeckeAlgebra R q →ₗ[R] S :=
    ((LinearMap.mulLeft S ((↑(vS * uS⁻¹) : S) ^ n)).comp (ocneanuTrace S qS zS)).restrictScalars R
      ∘ₗ (InfiniteTypeAHeckeAlgebra.map hqS).toLinearMap
  let M : Submodule R S :=
    (LinearMap.range (Algebra.linearMap (LaurentPolynomial R) S)).restrictScalars R
  have hstage (n : ℕ) :
      Subalgebra.toSubmodule (InfiniteTypeAHeckeAlgebra.stage R q (n + 1)) ≤ M.comap (L n) := by
    induction n with
    | zero =>
      intro x hx
      rw [Subalgebra.mem_toSubmodule,
        InfiniteTypeAHeckeAlgebra.stage_eq_bot_of_le_one le_rfl, Algebra.mem_bot] at hx
      obtain ⟨r, rfl⟩ := hx
      refine ⟨C r, ?_⟩
      simp [L, AlgHom.commutes,
        IsScalarTower.algebraMap_apply R S (InfiniteTypeAHeckeAlgebra S qS),
        (isMarkovTrace_ocneanuTrace zS).map_algebraMap,
        IsScalarTower.algebraMap_apply R (LaurentPolynomial R) S]
    | succ n ih =>
      refine InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two_le_iff.2
        ⟨fun y hy ↦ ?_, fun a ha b hb ↦ ?_⟩
      · obtain ⟨P, hP⟩ := ih hy
        refine ⟨(T (-1) - T 1) * C (↑u⁻¹ : R) * P, ?_⟩
        simp only [L, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
          Algebra.linearMap_apply, LinearMap.mulLeft_apply, pow_succ'] at hP ⊢
        rw [map_mul, hC, hP, mul_assoc]
      · obtain ⟨P, hP⟩ := ih ((Subalgebra.mem_toSubmodule _).2 (mul_mem hb ha))
        refine ⟨T (-1) * P, ?_⟩
        have hτS := isMarkovTrace_ocneanuTrace (R := S) (q := qS) zS
        simp only [L, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
          Algebra.linearMap_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply, map_mul,
          InfiniteTypeAHeckeAlgebra.map_T, pow_succ'] at hP ⊢
        rw [hτS.map_mul_T_mul (InfiniteTypeAHeckeAlgebra.map_mem_stage hqS ha)
            (InfiniteTypeAHeckeAlgebra.map_mem_stage hqS hb),
          ← mul_assoc ((↑(vS * uS⁻¹) : S) * _), mul_right_comm (↑(vS * uS⁻¹) : S) _ zS,
          hCz, mul_assoc (ι (T (-1))), ← hP]
  obtain ⟨P, hP⟩ := hstage β.predStrands
    ((Subalgebra.mem_toSubmodule _).2
      (InfiniteTypeAHeckeAlgebra.braidHom_mem_stage β.braid))
  simp only [L, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    Algebra.linearMap_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    InfiniteTypeAHeckeAlgebra.map_braidHom] at hP
  let w : ℤ := Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)
  have hlw : (↑(lS ^ w) : S) = ι (T w) := by
    rw [← _root_.map_zpow (Units.map (ι : LaurentPolynomial R →* S)) (genericUnit R) w,
      Units.coe_map, genericUnit_zpow_val]
    rfl
  refine ⟨T w * P, ?_⟩
  rw [map_mul, hP, ← hlw, heckeUniversalTrace, heckeTrace_def]
  dsimp only [zS]
  ring

/-- The unique regular Laurent polynomial in `LaurentPolynomial R` extending
`MarkovBraid.heckeUniversalTrace` across the zero-factor locus `T (-1) - T 1 = 0`. -/
def heckeRegularExtension (β : MarkovBraid) (q u : Rˣ) : LaurentPolynomial R :=
  (exists_algebraMap_eq_heckeUniversalTrace β q u).choose

/-- **Regularity of the generic normalized Ocneanu trace across `l = ±1`.** Inside
`Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`, `β.heckeUniversalTrace q u` equals the
image of `β.heckeRegularExtension q u` over every commutative ring `R`. -/
@[simp]
theorem algebraMap_heckeRegularExtension (β : MarkovBraid) (q u : Rˣ) :
    algebraMap (LaurentPolynomial R)
        (Localization.Away (T (-1) - T 1 : LaurentPolynomial R))
        (β.heckeRegularExtension q u) =
      β.heckeUniversalTrace q u :=
  (exists_algebraMap_eq_heckeUniversalTrace β q u).choose_spec

/-- Any Laurent polynomial in `LaurentPolynomial R` whose image in
`Localization.Away (T (-1) - T 1)` agrees with `β.heckeUniversalTrace q u` equals
`β.heckeRegularExtension q u`. -/
theorem eq_heckeRegularExtension_of_algebraMap_eq {β : MarkovBraid} {q u : Rˣ}
    {P : LaurentPolynomial R}
    (hP : algebraMap (LaurentPolynomial R)
        (Localization.Away (T (-1) - T 1 : LaurentPolynomial R)) P =
      β.heckeUniversalTrace q u) :
    P = β.heckeRegularExtension q u :=
  algebraMap_localizationAway_T_neg_one_sub_T_one_injective
    (hP.trans (β.algebraMap_heckeRegularExtension q u).symm)

/-- **Existence and uniqueness of the regular Laurent polynomial extension** of the generic
normalized Ocneanu braid trace across `T (-1) - T 1 = 0`, over every commutative ring `R`. -/
theorem existsUnique_algebraMap_eq_heckeUniversalTrace (β : MarkovBraid) (q u : Rˣ) :
    ∃! P : LaurentPolynomial R,
      algebraMap (LaurentPolynomial R)
          (Localization.Away (T (-1) - T 1 : LaurentPolynomial R)) P =
        β.heckeUniversalTrace q u :=
  ⟨β.heckeRegularExtension q u, β.algebraMap_heckeRegularExtension q u,
    fun _ hP ↦ eq_heckeRegularExtension_of_algebraMap_eq hP⟩

/-- On a one-strand braid, `heckeRegularExtension` is `1`. -/
@[simp]
theorem heckeRegularExtension_one_strand (q u : Rˣ) (b : BraidGroup 1) :
    heckeRegularExtension ⟨0, b⟩ q u = 1 := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  rw [map_one, heckeUniversalTrace]
  exact (heckeTrace_one_strand (isMarkovTrace_ocneanuTrace _).map_one _ _ b).symm

/-- Adding an uncrossed strand multiplies `heckeRegularExtension` by `(T (-1) - T 1) * C ↑u⁻¹`. -/
theorem heckeRegularExtension_strandIncl (q u : Rˣ) {n : ℕ} (b : BraidGroup (n + 1)) :
    heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u =
      (T (-1) - T 1) * C (↑u⁻¹ : R) * heckeRegularExtension ⟨n, b⟩ q u := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  let s : LaurentPolynomial R := T (-1) - T 1
  let S := Localization.Away s
  let ι : LaurentPolynomial R →+* S := algebraMap (LaurentPolynomial R) S
  let uS : Sˣ := Units.map ((ι.comp C) : R →* S) u
  let vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
  have hC : ι ((T (-1) - T 1) * C (↑u⁻¹ : R)) = ↑(vS * uS⁻¹) := by
    have hu_inv : (↑uS⁻¹ : S) = ι (C (↑u⁻¹ : R)) := by simp [uS]
    simp [vS, s, ι, hu_inv, map_mul]
  rw [map_mul, algebraMap_heckeRegularExtension, hC, heckeUniversalTrace, heckeUniversalTrace]
  exact ((ocneanuTrace S _ _).heckeTrace_strandIncl _ _ b).symm

/-- Skein relation of `heckeRegularExtension` in `LaurentPolynomial R`. -/
theorem heckeRegularExtension_skein (q u : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    T (-1) * heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u -
        T 1 * heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u =
      C ((q : R) - ↑q⁻¹) * heckeRegularExtension ⟨n, b * c⟩ q u := by
  apply algebraMap_localizationAway_T_neg_one_sub_T_one_injective
  let s : LaurentPolynomial R := T (-1) - T 1
  let S := Localization.Away s
  let ι : LaurentPolynomial R →+* S := algebraMap (LaurentPolynomial R) S
  let qS : Sˣ := Units.map ((ι.comp C) : R →* S) q
  let lS : Sˣ := Units.map (ι : LaurentPolynomial R →* S) (genericUnit R)
  have hl_inv : ι (T (-1)) = (↑lS⁻¹ : S) := by simp [lS]
  have hl : ι (T 1) = (lS : S) := by simp [lS]
  have hq : ι (C ((q : R) - ↑q⁻¹)) = (qS : S) - ↑qS⁻¹ := by
    have hqinv : (↑qS⁻¹ : S) = ι (C ↑q⁻¹) := by simp [qS]
    simp [qS, hqinv, map_sub]
  rw [map_sub, map_mul, map_mul, map_mul, algebraMap_heckeRegularExtension,
    algebraMap_heckeRegularExtension, algebraMap_heckeRegularExtension,
    hl_inv, hl, hq, heckeUniversalTrace, heckeUniversalTrace, heckeUniversalTrace]
  exact heckeTrace_skein _ lS b c i

end MarkovBraid

/-- Markov-equivalent braids have equal `heckeUniversalTrace` when `u = q - q⁻¹`. -/
theorem MarkovEquiv.heckeUniversalTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    β.heckeUniversalTrace q u = γ.heckeUniversalTrace q u := by
  obtain ⟨hpos, hneg⟩ := MarkovBraid.heckeUniversal_pos_neg hu
  exact h.heckeTrace_eq (isMarkovTrace_ocneanuTrace _) _ _ hpos hneg

/-- Markov-equivalent braids have equal `heckeRegularExtension` over any commutative ring when
`u = q - q⁻¹`. -/
theorem MarkovEquiv.heckeRegularExtension_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    β.heckeRegularExtension q u = γ.heckeRegularExtension q u :=
  MarkovBraid.eq_heckeRegularExtension_of_algebraMap_eq
    ((β.algebraMap_heckeRegularExtension q u).trans (h.heckeUniversalTrace_eq hu))

namespace MarkovBraid

open KnotTheory BraidGroup

/-- When `R` receives a ring homomorphism `φ` from a field `K` and `u = q - q⁻¹`, the intrinsic
regular extension `β.heckeRegularExtension q u` agrees with evaluating `β.reducedHomfly K` at inner
variable `u` and outer variable `(genericUnit R)⁻¹`. -/
theorem heckeRegularExtension_eq_eval₂_reducedHomfly {K : Type*} [Field K] (φ : K →+* R)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    β.heckeRegularExtension q u =
      eval₂ (C.comp (eval₂ φ u)) (genericUnit R)⁻¹ (β.reducedHomfly K) := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  let s : LaurentPolynomial R := T (-1) - T 1
  let S := Localization.Away s
  let ι : LaurentPolynomial R →+* S := algebraMap (LaurentPolynomial R) S
  let qS : Sˣ := Units.map ((ι.comp C) : R →* S) q
  let uS : Sˣ := Units.map ((ι.comp C) : R →* S) u
  let lS : Sˣ := Units.map (ι : LaurentPolynomial R →* S) (genericUnit R)
  obtain ⟨hpos, hneg⟩ := heckeUniversal_pos_neg hu
  have huS : (uS : S) = (qS : S) - ↑qS⁻¹ := by
    have hqinv : (↑qS⁻¹ : S) = ι (C ↑q⁻¹) := by simp [qS]
    calc
      (uS : S) = ι (C (u : R)) := rfl
      _ = ι (C ((q : R) - ↑q⁻¹)) := by rw [hu]
      _ = (qS : S) - ↑qS⁻¹ := by simp [qS, hqinv, map_sub]
  have hcomp : ι.comp (C.comp (eval₂ φ u)) = eval₂ (ι.comp (C.comp φ)) uS :=
    RingHom.ext fun p ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, hom_eval₂, hom_eval₂]
      rfl
  have hl_inv : Units.map (ι : LaurentPolynomial R →* S) (genericUnit R)⁻¹ = lS⁻¹ :=
    _root_.map_inv _ _
  rw [hom_eval₂, hcomp, hl_inv]
  exact eval₂_reducedHomfly_eq_heckeTrace (ι.comp (C.comp φ))
    (isMarkovTrace_ocneanuTrace _) hpos hneg huS β

/-- Evaluating `β.heckeRegularExtension q u` at any writhe unit `l₀ : Rˣ` agrees with
`eval₂ (eval₂ φ u) l₀⁻¹ (β.reducedHomfly K)` whenever `φ : K →+* R` is a ring homomorphism from a
field `K`. -/
theorem eval₂_heckeRegularExtension_eq_eval₂_reducedHomfly {K : Type*} [Field K] (φ : K →+* R)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) (l₀ : Rˣ) (β : MarkovBraid) :
    eval₂ (RingHom.id R) l₀ (β.heckeRegularExtension q u) =
      eval₂ (eval₂ φ u) l₀⁻¹ (β.reducedHomfly K) := by
  rw [heckeRegularExtension_eq_eval₂_reducedHomfly φ hu]
  have hcomp : (eval₂ (RingHom.id R) l₀).comp (C.comp (eval₂ φ u)) = eval₂ φ u :=
    RingHom.ext fun p ↦ by simp
  have hl : Units.map (eval₂ (RingHom.id R) l₀ : LaurentPolynomial R →* R) (genericUnit R)⁻¹ =
      l₀⁻¹ := by
    ext
    simp
  rw [hom_eval₂, hcomp, hl]

/-- At the `l = 1` zero-factor specialization, the one-strand unknot has value `1`. -/
theorem eval₂_one_heckeRegularExtension_one_strand (q u : Rˣ) (b : BraidGroup 1) :
    eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨0, b⟩ q u) = 1 := by
  simp

/-- At the `l = 1` zero-factor specialization (`C = 0`), adding an uncrossed strand kills the
invariant over every commutative ring `R`. -/
@[simp]
theorem eval₂_one_heckeRegularExtension_strandIncl (q u : Rˣ) {n : ℕ} (b : BraidGroup (n + 1)) :
    eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u) = 0 := by
  rw [heckeRegularExtension_strandIncl, map_mul, map_mul, map_sub]
  simp

/-- At the `l = 1` zero-factor specialization, `heckeRegularExtension` satisfies the Conway skein
relation `F(L₊) - F(L₋) = (q - q⁻¹) * F(L₀)` over every commutative ring `R`. -/
theorem eval₂_one_heckeRegularExtension_skein (q u : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1))
    (i : Fin n) :
    eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u) -
        eval₂ (RingHom.id R) 1
          (heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u) =
      ((q : R) - ↑q⁻¹) * eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨n, b * c⟩ q u) := by
  simpa only [map_sub, map_mul, eval₂_T, eval₂_C, one_zpow, zpow_one, Units.val_one, one_mul,
    RingHom.id_apply] using
    congrArg (eval₂ (RingHom.id R) 1) (heckeRegularExtension_skein q u b c i)

/-- **Comparison with the normalized Burau Alexander invariant at `l = 1`.** Over every commutative
ring `R`, when `u = q - q⁻¹` and `s⁻¹ - s = q - q⁻¹` (for instance `s = q⁻¹`), evaluating the
regular extension at `l = 1` recovers `β.normalizedBurauAlexander s`. -/
theorem eval₂_one_heckeRegularExtension_eq_normalizedBurauAlexander {q u s : Rˣ}
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hs : ((s⁻¹ : Rˣ) : R) - (s : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (RingHom.id R) 1 (β.heckeRegularExtension q u) =
      β.normalizedBurauAlexander s := by
  refine congrFun (eq_of_skein (R := R) (M := R) 1 ((q : R) - ↑q⁻¹) 0
    (F := fun γ ↦ eval₂ (RingHom.id R) 1 (γ.heckeRegularExtension q u))
    (G := fun γ ↦ γ.normalizedBurauAlexander s)
    (fun _ _ h ↦ congrArg _ (h.heckeRegularExtension_eq hu))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun n c i ↦ ?_) (fun n c i ↦ ?_) (fun n b ↦ ?_) (fun n b ↦ ?_) (by simp)) β
  · simpa using eval₂_one_heckeRegularExtension_skein q u (1 : BraidGroup (n + 1)) c i
  · simpa [hs] using normalizedBurauAlexander_skein (1 : BraidGroup (n + 1)) c i s
  · simp
  · simp

/-- At the `l = -1` zero-factor specialization, the one-strand unknot has value `1`. -/
theorem eval₂_neg_one_heckeRegularExtension_one_strand (q u : Rˣ) (b : BraidGroup 1) :
    eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨0, b⟩ q u) = 1 := by
  simp

/-- At the `l = -1` zero-factor specialization (`C = 0`), adding an uncrossed strand kills the
invariant over every commutative ring `R`. -/
@[simp]
theorem eval₂_neg_one_heckeRegularExtension_strandIncl (q u : Rˣ) {n : ℕ}
    (b : BraidGroup (n + 1)) :
    eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u) = 0 := by
  rw [heckeRegularExtension_strandIncl, map_mul, map_mul, map_sub]
  simp

/-- At the `l = -1` zero-factor specialization, `heckeRegularExtension` satisfies the signed Conway
skein relation `-F(L₊) + F(L₋) = (q - q⁻¹) * F(L₀)` over every commutative ring `R`. -/
theorem eval₂_neg_one_heckeRegularExtension_skein (q u : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1))
    (i : Fin n) :
    -eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u) +
        eval₂ (RingHom.id R) (-1)
          (heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u) =
      ((q : R) - ↑q⁻¹) * eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨n, b * c⟩ q u) := by
  have hs := congrArg (eval₂ (RingHom.id R) (-1)) (heckeRegularExtension_skein q u b c i)
  simp only [map_sub, map_mul, eval₂_T, eval₂_C, zpow_one, zpow_neg_one, Units.val_neg,
    Units.val_one, inv_neg, inv_one, neg_one_mul, sub_neg_eq_add, RingHom.id_apply] at hs
  exact hs

end MarkovBraid

/-- Markov invariance of the `l = 1` zero-factor evaluation of `heckeRegularExtension`. -/
theorem MarkovEquiv.eval₂_one_heckeRegularExtension_eq {β γ : MarkovBraid}
    (h : MarkovEquiv β γ) {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (RingHom.id R) 1 (β.heckeRegularExtension q u) =
      eval₂ (RingHom.id R) 1 (γ.heckeRegularExtension q u) :=
  congrArg _ (h.heckeRegularExtension_eq hu)

/-- Markov invariance of the `l = -1` zero-factor evaluation of `heckeRegularExtension`. -/
theorem MarkovEquiv.eval₂_neg_one_heckeRegularExtension_eq {β γ : MarkovBraid}
    (h : MarkovEquiv β γ) {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (RingHom.id R) (-1) (β.heckeRegularExtension q u) =
      eval₂ (RingHom.id R) (-1) (γ.heckeRegularExtension q u) :=
  congrArg _ (h.heckeRegularExtension_eq hu)

end ZeroFactorRegularity

end TauCeti
