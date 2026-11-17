/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke.RegularTrace
public import TauCeti.KnotTheory.Homfly.Reduced

/-!
# Comparison of Ocneanu braid invariants with Jimbo and HOMFLY invariants

This module compares the regularized and normalized Ocneanu braid-closure invariants
`TauCeti.MarkovBraid.regularHeckeTrace` (`TauCeti.KnotTheory.Hecke.RegularTrace`) and
`TauCeti.MarkovBraid.heckeTrace` (`TauCeti.KnotTheory.Hecke.Trace`) with the library's native Jimbo
and HOMFLY braid invariants:

* **Jimbo weighted and reduced traces:** over every commutative ring `R`, for all `N : ℕ` and
  `q : Rˣ`, `β.jimboTrace q` equals `δ_N * β.regularHeckeTrace q δ_N ((q ^ N)⁻¹)` with no
  invertibility hypotheses (`jimboTrace_eq_mul_regularHeckeTrace`), and over a field with
  `δ_N ≠ 0`, `β.jimboReducedTrace q` equals both `regularHeckeTrace` and the Ocneanu `heckeTrace`
  at `z = q ^ N / δ_N` (`jimboReducedTrace_eq_heckeTrace`).
* **Two-variable HOMFLY polynomial:** for any homomorphism `f : K →+* R` from a field `K` to a
  commutative ring `R` and any units `q u l : Rˣ` with `u = q - q⁻¹`, evaluating `β.reducedHomfly K`
  at `z = u` and `a = l⁻¹` gives `β.regularHeckeTrace q ((l⁻¹ - l) * u⁻¹) l`—including across the
  zero-factor locus `l = ±1` (`eval₂_reducedHomfly_eq_regularHeckeTrace`)—and coincides with the
  Ocneanu `heckeTrace` whenever `(l⁻¹ - l) * u⁻¹ * z = l⁻¹` (`eval₂_reducedHomfly_eq_heckeTrace`).

## Main results

* `TauCeti.MarkovBraid.jimboTrace_eq_mul_regularHeckeTrace` and
  `TauCeti.MarkovBraid.jimboReducedTrace_eq_heckeTrace`: comparison with the `N`-colour Jimbo braid
  invariants.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_regularHeckeTrace`,
  `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`, and
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`: comparison with `reducedHomfly` and
  `homfly`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public section

open LaurentPolynomial
open scoped BigOperators

namespace TauCeti

open BraidGroup InfiniteTypeAHeckeAlgebra KnotTheory

section JimboComparison

namespace MarkovBraid

/-- **Unconditional comparison of `jimboTrace` with `regularHeckeTrace`.** Over every commutative
ring `R`, for every number of colours `N`, unit `q : Rˣ`, and braid `β`, the writhe-normalized
`N`-colour Jimbo trace equals the quantum dimension `δ_N` times `regularHeckeTrace` at
`C = δ_N` and `l = (q ^ N)⁻¹`. No division by `δ_N` or `q - q⁻¹` is required. -/
theorem jimboTrace_eq_mul_regularHeckeTrace {R : Type*} [CommRing R] (N : ℕ) (β : MarkovBraid)
    (q : Rˣ) :
    β.jimboTrace (N := N) q =
      (∑ a : Fin N, jimboWeight q a) *
        β.regularHeckeTrace q (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rcases β with ⟨n, b⟩
  rw [jimboTrace_def, regularHeckeTrace_def, ← TypeAHeckeAlgebra.jimboWeightedTrace_braidHom,
    TypeAHeckeAlgebra.jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace,
    TypeAHeckeAlgebra.toInfinite_braidHom, inv_inv, inv_zpow', zpow_neg]
  ring

/-- When `c * δ_N = 1`, `jimboTrace` equals `δ_N` times the normalized Ocneanu `heckeTrace` at
Markov parameter `c * q ^ N`. -/
theorem jimboTrace_eq_mul_heckeTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    β.jimboTrace (N := N) q =
      (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  have hz : (∑ a : Fin N, jimboWeight q a) * (c * ↑(q ^ N)) = ↑((q ^ N)⁻¹)⁻¹ := by
    rw [inv_inv, ← mul_assoc, mul_comm _ c, hc, one_mul]
  rw [jimboTrace_eq_mul_regularHeckeTrace, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- Rescaled form of `jimboTrace_eq_mul_heckeTrace`: when `c * δ_N = 1`, multiplying `jimboTrace` by
`c` recovers the normalized Ocneanu `heckeTrace` directly. -/
theorem mul_jimboTrace_eq_heckeTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    c * β.jimboTrace (N := N) q =
      β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rw [jimboTrace_eq_mul_heckeTrace hc, ← mul_assoc, hc, one_mul]

/-- Over a field where the `N`-colour quantum dimension `δ_N` is nonzero, `jimboReducedTrace`
coincides with `regularHeckeTrace` at `C = δ_N` and `l = (q ^ N)⁻¹`. -/
theorem jimboReducedTrace_eq_regularHeckeTrace {K : Type*} [Field K] {N : ℕ} (β : MarkovBraid)
    {q : Kˣ} (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q =
      β.regularHeckeTrace q (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rw [jimboReducedTrace_def, jimboTrace_eq_mul_regularHeckeTrace, mul_div_cancel_left₀ _ hδ]

/-- **Comparison of `jimboReducedTrace` with the Ocneanu `heckeTrace`.** Over a field where the
`N`-colour quantum dimension `δ_N` is nonzero, `jimboReducedTrace` equals the normalized Ocneanu
braid invariant at `z = q ^ N / δ_N`, `C = δ_N`, and `l = (q ^ N)⁻¹`. -/
theorem jimboReducedTrace_eq_heckeTrace {K : Type*} [Field K] {N : ℕ} (β : MarkovBraid)
    {q : Kˣ} (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q =
      β.heckeTrace (ocneanuTrace K q (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  have hz : (∑ a : Fin N, jimboWeight q a) * (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a) =
      ↑((q ^ N)⁻¹)⁻¹ := by
    rw [inv_inv, mul_div_cancel₀ _ hδ]
  rw [jimboReducedTrace_eq_regularHeckeTrace β hδ, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

end MarkovBraid

end JimboComparison

section HomflyComparison

variable {K R : Type*} [Field K] [CommRing R]

/-- Evaluating the HOMFLY unknot polynomial `(a - a⁻¹) z⁻¹` at `z = u` and `a` gives
`(a - a⁻¹) * u⁻¹`. -/
@[simp]
theorem KnotTheory.eval₂_homflyUnknot (f : K →+* R) (u a : Rˣ) :
    eval₂ (eval₂ f u) a (homflyUnknot K) = ((a : R) - ↑a⁻¹) * ↑u⁻¹ := by
  simp [homflyUnknot_def]

namespace MarkovBraid

/-- **Comparison of `reducedHomfly` with `regularHeckeTrace`.** For any ring homomorphism
`f : K →+* R` from a field `K` to a commutative ring `R` and any units `q u l : Rˣ` with
`u = q - q⁻¹`, evaluating `β.reducedHomfly K` at `z = u` and `a = l⁻¹` yields
`β.regularHeckeTrace q ((l⁻¹ - l) * u⁻¹) l`. Because `regularHeckeTrace` requires no inverse of
`C = (l⁻¹ - l) * u⁻¹`, this holds across zero-factor specializations such as `l = ±1`. -/
theorem eval₂_reducedHomfly_eq_regularHeckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.reducedHomfly K) =
      β.regularHeckeTrace q (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ f u) l⁻¹
  have heT1 : e (LaurentPolynomial.T 1) = (↑l⁻¹ : R) := by simp [e]
  have heTneg1 : e (LaurentPolynomial.T (-1)) = (l : R) := by simp [e]
  have hez : e (C (LaurentPolynomial.T 1)) = (u : R) := by simp [e]
  have heU : e (homflyUnknot K) = ((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹ := by
    simp [e]
  have hstab : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R) := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  have h := eq_regularHeckeTrace_of_skein hstab
    (F := fun γ ↦ e (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun n c i ↦ ?_)
    (fun n b ↦ ?_)
    (by simp [e])
  · exact congrFun h β
  · simpa only [one_mul, map_sub, map_mul, heT1, heTneg1, hez, hu] using
      congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
  · rw [reducedHomfly_strandIncl, map_mul, heU]

/-- **Comparison of `reducedHomfly` with the Ocneanu `heckeTrace`.** Whenever `z : R` satisfies
`((l⁻¹ - l) * u⁻¹) * z = l⁻¹` (in particular whenever `((l⁻¹ - l) * u⁻¹) * l * z = 1`), evaluating
`β.reducedHomfly K` at `z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹` gives the normalized Ocneanu trace
`β.heckeTrace (ocneanuTrace R q z) ((l⁻¹ - l) * u⁻¹) l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) {z : R}
    (hz : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * z = ↑l⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace (ocneanuTrace R q z) (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [eval₂_reducedHomfly_eq_regularHeckeTrace β f q u l hu,
    regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- Field form of `eval₂_reducedHomfly_eq_heckeTrace`: over a field `L` with `q - q⁻¹ ≠ 0` and
`l⁻¹ - l ≠ 0`, `reducedHomfly` specializes to Jones's Ocneanu braid invariant with Markov parameter
`z = l⁻¹ * (q - q⁻¹) / (l⁻¹ - l)` and unlink factor `C = (l⁻¹ - l) / (q - q⁻¹)`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_div {L : Type*} [Field L] (β : MarkovBraid)
    (f : K →+* L) {q l : Lˣ} (hq : (q : L) - ↑q⁻¹ ≠ 0) (hl : (↑l⁻¹ : L) - (l : L) ≠ 0) :
    eval₂ (eval₂ f (Units.mk0 ((q : L) - ↑q⁻¹) hq)) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace
        (ocneanuTrace L q (((↑l⁻¹ : L) * ((q : L) - ↑q⁻¹)) / ((↑l⁻¹ : L) - (l : L))))
        (((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹)) l := by
  have hC : (((↑l⁻¹ : L) - (l : L)) * ↑(Units.mk0 ((q : L) - ↑q⁻¹) hq)⁻¹) =
      ((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹) := by
    simp [div_eq_mul_inv]
  have hz : (((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹)) *
      (((↑l⁻¹ : L) * ((q : L) - ↑q⁻¹)) / ((↑l⁻¹ : L) - (l : L))) = ↑l⁻¹ := by
    field_simp
  rw [eval₂_reducedHomfly_eq_regularHeckeTrace β f q (Units.mk0 ((q : L) - ↑q⁻¹) hq) l rfl,
    hC, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- **Comparison of unreduced `homfly` with `regularHeckeTrace`.** Evaluating `β.homfly K` at
`z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹` gives `((l⁻¹ - l) * u⁻¹)` times `regularHeckeTrace`,
valid across all `l : Rˣ` including `l = ±1`. -/
theorem eval₂_homfly_eq_mul_regularHeckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.homfly K) =
      (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) *
        β.regularHeckeTrace q (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [← homflyUnknot_mul_reducedHomfly, _root_.map_mul, eval₂_homflyUnknot, inv_inv,
    eval₂_reducedHomfly_eq_regularHeckeTrace β f q u l hu]

/-- **Comparison of unreduced `homfly` with the Ocneanu `heckeTrace`.** When
`((l⁻¹ - l) * u⁻¹) * z = l⁻¹`, evaluating `β.homfly K` at `z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹`
gives `((l⁻¹ - l) * u⁻¹)` times the normalized Ocneanu trace. -/
theorem eval₂_homfly_eq_mul_heckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) {z : R}
    (hz : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * z = ↑l⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.homfly K) =
      (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) *
        β.heckeTrace (ocneanuTrace R q z) (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [eval₂_homfly_eq_mul_regularHeckeTrace β f q u l hu,
    regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

end MarkovBraid

end HomflyComparison

end TauCeti
