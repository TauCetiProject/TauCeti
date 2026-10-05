/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Padic

/-!
# A finite obstruction invisible over `ℝ`

The ternary form `q = ⟨1, 1, -3⟩` over `ℚ`, that is `x² + y² - 3z²`, is indefinite: it is
isotropic over `ℝ`, where `(√3, 0, 1)` is a zero. It is anisotropic over `ℚ_3`, because
`3` is not a sum of two squares in `ℚ_3`: the Hilbert symbol `(-1, 3)_3` is `-1`, the residue
`-1` being a nonsquare modulo `3`. Since an isotropic vector over `ℚ` would remain isotropic over
`ℚ_3`, the form is anisotropic over `ℚ`.

At every real place `q` is isometric to `⟨1, 1, -1⟩`, which is isotropic over `ℚ`. So the two
forms have the same rank and the same signature at every real place but are not isometric over
`ℚ`: real signatures alone do not classify forms over a number field, and isotropy at the real
places does not imply global isotropy. The obstruction is visible at the finite place `3`.

## Main results

All in the namespace `TauCeti.NumberField.QuadraticForm`:

* `not_anisotropic_sumTwoSquaresSubThreeSq_atRealPlace`: `⟨1, 1, -3⟩` is isotropic at every real
  place of `ℚ`.
* `anisotropic_sumTwoSquaresSubThreeSq_atFinitePlace`: `⟨1, 1, -3⟩` is anisotropic at the finite
  place `3`.
* `anisotropic_sumTwoSquaresSubThreeSq`: `⟨1, 1, -3⟩` is anisotropic over `ℚ`.
* `equivalent_sumTwoSquaresSubThreeSq_sumTwoSquaresSubSq_atRealPlace`,
  `not_equivalent_sumTwoSquaresSubThreeSq_sumTwoSquaresSubSq`: `⟨1, 1, -3⟩` and `⟨1, 1, -1⟩` are
  isometric at every real place but not over `ℚ`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1 and Chapter IV, §3.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §66.
-/

public section
noncomputable section

open IsDedekindDomain NumberField QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

/-- The ternary form `⟨1, 1, -3⟩` over `ℚ`, isotropic over `ℝ` and anisotropic over `ℚ_3`. -/
def sumTwoSquaresSubThreeSq : _root_.QuadraticForm ℚ (Fin 3 → ℚ) :=
  weightedSumSquares ℚ ![1, 1, -3]

/-- The value of `⟨1, 1, -3⟩` at `(x, y, z)` is `x² + y² - 3z²`. -/
@[simp]
theorem sumTwoSquaresSubThreeSq_apply (x : Fin 3 → ℚ) :
    sumTwoSquaresSubThreeSq x = x 0 ^ 2 + x 1 ^ 2 - 3 * x 2 ^ 2 := by
  simp [sumTwoSquaresSubThreeSq, weightedSumSquares_apply, Fin.sum_univ_three, pow_two]
  ring

/-- The ternary form `⟨1, 1, -1⟩` over `ℚ`, isotropic over `ℚ` and isometric to `⟨1, 1, -3⟩` at
every real place. -/
def sumTwoSquaresSubSq : _root_.QuadraticForm ℚ (Fin 3 → ℚ) :=
  weightedSumSquares ℚ ![1, 1, -1]

/-- The value of `⟨1, 1, -1⟩` at `(x, y, z)` is `x² + y² - z²`. -/
@[simp]
theorem sumTwoSquaresSubSq_apply (x : Fin 3 → ℚ) :
    sumTwoSquaresSubSq x = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 := by
  simp [sumTwoSquaresSubSq, weightedSumSquares_apply, Fin.sum_univ_three, pow_two]
  ring

/-- The form `⟨1, 1, -3⟩` is isotropic at every real place of `ℚ`: `(√3, 0, 1)` is a zero. -/
theorem not_anisotropic_sumTwoSquaresSubThreeSq_atRealPlace
    (w : {w : InfinitePlace ℚ // w.IsReal}) :
    let : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
    ¬ (sumTwoSquaresSubThreeSq.atRealPlace w).Anisotropic := by
  intro _
  have he : (sumTwoSquaresSubThreeSq.atRealPlace w).IsometryEquiv
      (weightedSumSquares ℝ fun i =>
        InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1, -3] i)) :=
    _root_.QuadraticForm.atRealPlaceWeightedSumSquares w ![(1 : ℚ), 1, -3]
  have hcoeff : (fun i : Fin 3 =>
      InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1, -3] i)) = ![(1 : ℝ), 1, -3] := by
    funext i
    fin_cases i <;> simp
  rw [(QuadraticMap.Equivalent.anisotropic_iff ⟨he⟩), hcoeff]
  intro h
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 := h ![Real.sqrt 3, 0, 1] (by
    simp [weightedSumSquares_apply, Fin.sum_univ_three, ← pow_two, h3])
  simpa using congrFun h0 2

/-- The form `⟨1, 1, -3⟩` is anisotropic at the finite place of `ℚ` above `3`. -/
theorem anisotropic_sumTwoSquaresSubThreeSq_atFinitePlace (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v).1 = 3) :
    (sumTwoSquaresSubThreeSq.atFinitePlace v).Anisotropic := by
  have h2 : (2 : v.adicCompletion ℚ) ≠ 0 :=
    have := algebraRat.charZero (v.adicCompletion ℚ)
    two_ne_zero
  have h3 : (3 : v.adicCompletion ℚ) ≠ 0 :=
    have := algebraRat.charZero (v.adicCompletion ℚ)
    three_ne_zero
  let : Invertible (2 : v.adicCompletion ℚ) := invertibleOfNonzero h2
  have he : (sumTwoSquaresSubThreeSq.atFinitePlace v).IsometryEquiv
      (weightedSumSquares (v.adicCompletion ℚ) fun i =>
        algebraMap ℚ (v.adicCompletion ℚ) (![(1 : ℚ), 1, -3] i)) :=
    _root_.QuadraticForm.atFinitePlaceWeightedSumSquares v ![(1 : ℚ), 1, -3]
  have hcoeff : (fun i : Fin 3 =>
      algebraMap ℚ (v.adicCompletion ℚ) (![(1 : ℚ), 1, -3] i)) =
      ![1, -(((-1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ),
        -((Units.mk0 (3 : v.adicCompletion ℚ) h3 : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ)] := by
    funext i
    fin_cases i <;> simp
  rw [(QuadraticMap.Equivalent.anisotropic_iff ⟨he⟩), hcoeff]
  by_contra h
  rw [← hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares,
    hilbertSymbol_eq_one_iff] at h
  obtain ⟨x, y, hxy⟩ := h
  -- Transport `3 = x² + y²` to `ℚ_3`, where `(-1, 3)_3 = -1` forbids it.
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have hp : Fact p.1.Prime := ⟨p.2⟩
  have hsymb := Padic.hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three p.1
    (by simp [p, hv])
  rw [hilbertSymbol_eq_neg_one_iff] at hsymb
  let e := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv
  have h := congrArg e hxy
  exact hsymb ⟨e x, e y, by simpa [p, hv, map_ofNat e 3] using h⟩

/-- The form `⟨1, 1, -3⟩` is anisotropic over `ℚ`: an isotropic vector would remain isotropic in
the completion at `3`. -/
theorem anisotropic_sumTwoSquaresSubThreeSq : sumTwoSquaresSubThreeSq.Anisotropic := by
  by_contra h
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨3, Nat.prime_three⟩
  have hv : Rat.HeightOneSpectrum.primesEquiv v = (⟨3, Nat.prime_three⟩ : Nat.Primes) :=
    Equiv.apply_symm_apply _ _
  exact ((_root_.QuadraticForm.isLocallyIsotropic_iff _).mp
    (_root_.QuadraticForm.isLocallyIsotropic_of_not_anisotropic _ h)).1 v
    (anisotropic_sumTwoSquaresSubThreeSq_atFinitePlace v (by rw [hv]))

/-- At every real place, `⟨1, 1, -3⟩` is isometric to `⟨1, 1, -1⟩`. -/
theorem equivalent_sumTwoSquaresSubThreeSq_sumTwoSquaresSubSq_atRealPlace
    (w : {w : InfinitePlace ℚ // w.IsReal}) :
    let : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
    (sumTwoSquaresSubThreeSq.atRealPlace w).Equivalent (sumTwoSquaresSubSq.atRealPlace w) := by
  intro _
  have he₁ : (sumTwoSquaresSubThreeSq.atRealPlace w).IsometryEquiv
      (weightedSumSquares ℝ fun i =>
        InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1, -3] i)) :=
    _root_.QuadraticForm.atRealPlaceWeightedSumSquares w ![(1 : ℚ), 1, -3]
  have he₂ := _root_.QuadraticForm.atRealPlaceWeightedSumSquares w ![(1 : ℚ), 1, -1]
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hcoeff₁ : (fun i : Fin 3 =>
      InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1, -3] i)) =
      fun i => ((![1, 1, -Units.mk0 3 h3] : Fin 3 → ℝˣ) i : ℝ) := by
    funext i
    fin_cases i <;> simp
  have hcoeff₂ : (fun i : Fin 3 =>
      InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1, -1] i)) =
      fun i => ((![1, 1, -1] : Fin 3 → ℝˣ) i : ℝ) := by
    funext i
    fin_cases i <;> simp
  rw [hcoeff₁] at he₁
  rw [hcoeff₂] at he₂
  refine (Equivalent.trans ⟨he₁⟩ ?_).trans ⟨he₂.symm⟩
  rw [← weightedSumSquares_units, ← weightedSumSquares_units]
  refine equivalent_weightedSumSquares_of_isSquare_div fun i => ?_
  fin_cases i
  · simp
  · simp
  · refine ⟨Units.mk0 (Real.sqrt 3) (by positivity), Units.ext ?_⟩
    simp [← pow_two, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- `⟨1, 1, -3⟩` and `⟨1, 1, -1⟩` are not isometric over `ℚ`, although they are isometric at every
real place: the second is isotropic and the first is not. -/
theorem not_equivalent_sumTwoSquaresSubThreeSq_sumTwoSquaresSubSq :
    ¬ sumTwoSquaresSubThreeSq.Equivalent sumTwoSquaresSubSq := by
  intro h
  have hani := h.anisotropic_iff.mp anisotropic_sumTwoSquaresSubThreeSq
  have h0 := hani ![1, 0, 1] (by simp)
  simpa using congrFun h0 0

end TauCeti.NumberField.QuadraticForm
