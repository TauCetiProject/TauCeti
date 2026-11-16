/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.QuadraticForm.Binary
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Quadratic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
import TauCeti.NumberTheory.QuadraticForm.Global.Squares

/-!
# The quadratic Hasse norm theorem for binary norm forms

This file bridges the coordinate quadratic Hasse norm theorem
(`TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion`) to quadratic-form language
for the binary norm form `⟨1, -d⟩ = QuadraticMap.weightedSumSquares K ![1, -d]` over a number
field `K`.

The bridge drops three technical hypotheses at once:
* **Complex places are automatic**: the completion at a complex place is isomorphic to `ℂ`, where
  every element is already a square `x² = x² - d · 0²`, so `LocallyRepresentsScalar` (which ranges
  over finite and real places only) suffices.
* **Square discriminants `d = r²`**: if `d = 0`, representing `a` by `⟨1, 0⟩` is squareness of `a`
  and follows from the global square theorem; if `d = r²` with `r ≠ 0`, then `⟨1, -d⟩` represents
  every scalar explicitly via `a = ((a + 1) / 2)² - d * ((a - 1) / (2 * r))²`.
* **Zero scalar `a = 0`**: every quadratic form represents `0`.

Consequently, `⟨1, -d⟩` represents `a` over `K` if and only if it locally represents `a` at every
finite and real place of `K`, for arbitrary `d a : K`.

## Main results

* `QuadraticForm.represents_atFinitePlace_weightedSumSquares_one_neg_iff`: at a finite place,
  scalar representation by `⟨1, -d⟩` is solvability of `a = x² - d * y²` in the adic completion.
* `QuadraticForm.represents_atRealPlace_weightedSumSquares_one_neg_iff`: at a real place, scalar
  representation by `⟨1, -d⟩` is solvability of `a = x² - d * y²` in `ℝ`.
* `QuadraticForm.locallyRepresentsScalar_weightedSumSquares_one_neg_iff`: `LocallyRepresentsScalar`
  for `⟨1, -d⟩` unpacked into finite- and real-place norm equations.
* `QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar`: the binary
  norm form `⟨1, -d⟩` represents `a` over a number field if and only if it locally represents `a`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 65:20 and 66:1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, §3 (Theorem 3.1).
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

universe u

namespace QuadraticForm

section Field

variable {K : Type u} [Field K]

/-- At a real place, the binary norm form `⟨1, -d⟩` represents the embedded scalar `a` if and only
if `a = x² - d * y²` has a solution in `ℝ`. -/
theorem represents_atRealPlace_weightedSumSquares_one_neg_iff
    (w : {w : InfinitePlace K // w.IsReal}) (d a : K) :
    QuadraticMap.Represents (atRealPlace (QuadraticMap.weightedSumSquares K ![1, -d]) w)
        (embedding_of_isReal w.2 a) ↔
      ∃ x y : ℝ, embedding_of_isReal w.2 a = x ^ 2 - embedding_of_isReal w.2 d * y ^ 2 := by
  rw [(atRealPlaceWeightedSumSquares w ![1, -d]).represents_iff]
  have hfun : (fun i : Fin 2 ↦ embedding_of_isReal w.2 (![1, -d] i)) =
      ![1, -embedding_of_isReal w.2 d] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]
  exact TauCeti.represents_weightedSumSquares_one_neg_iff _ _

/-- Every real or complex infinite completion of `K` solves `a = x² - d * y²` whenever every real
embedding of `K` does. -/
private theorem forall_infinitePlaceCompletion_exists_sq_sub_mul_sq_of_real {d a : K}
    (hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, ∃ x y : ℝ,
      embedding_of_isReal w.2 a = x ^ 2 - embedding_of_isReal w.2 d * y ^ 2)
    (w : InfinitePlace K) :
    ∃ x y : w.Completion,
      algebraMap K w.Completion a = x ^ 2 - algebraMap K w.Completion d * y ^ 2 := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := Completion.ringEquivRealOfIsReal hw
    rw [← e.exists_eq_sq_sub_mul_sq_map_iff]
    simpa [e, Completion.algebraMap_apply_eq_coe] using hreal ⟨w, hw⟩
  · let e := Completion.ringEquivComplexOfIsComplex hw
    rw [← e.exists_eq_sq_sub_mul_sq_map_iff]
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap K w.Completion a))
      (by norm_num : 0 < 2)
    exact ⟨x, 0, by simp [hx]⟩

end Field

section NumberField

variable {K : Type u} [Field K] [NumberField K]

/-- At a finite place, the binary norm form `⟨1, -d⟩` represents the localized scalar `a` if and
only if `a = x² - d * y²` has a solution in the adic completion. -/
theorem represents_atFinitePlace_weightedSumSquares_one_neg_iff
    (v : HeightOneSpectrum (𝓞 K)) (d a : K) :
    QuadraticMap.Represents (atFinitePlace (QuadraticMap.weightedSumSquares K ![1, -d]) v)
        (algebraMap K (v.adicCompletion K) a) ↔
      ∃ x y : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) a =
          x ^ 2 - algebraMap K (v.adicCompletion K) d * y ^ 2 := by
  rw [(atFinitePlaceWeightedSumSquares v ![1, -d]).represents_iff]
  have hfun : (fun i : Fin 2 ↦ algebraMap K (v.adicCompletion K) (![1, -d] i)) =
      ![1, -algebraMap K (v.adicCompletion K) d] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]
  exact TauCeti.represents_weightedSumSquares_one_neg_iff _ _

/-- Local scalar representation by the binary norm form `⟨1, -d⟩` is solvability of
`a = x² - d * y²` in every finite completion and at every real embedding of `K`. -/
theorem locallyRepresentsScalar_weightedSumSquares_one_neg_iff (d a : K) :
    LocallyRepresentsScalar (QuadraticMap.weightedSumSquares K ![1, -d]) a ↔
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) a =
          x ^ 2 - algebraMap K (v.adicCompletion K) d * y ^ 2) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, ∃ x y : ℝ,
        embedding_of_isReal w.2 a = x ^ 2 - embedding_of_isReal w.2 d * y ^ 2 := by
  simp only [locallyRepresentsScalar_iff,
    represents_atFinitePlace_weightedSumSquares_one_neg_iff,
    represents_atRealPlace_weightedSumSquares_one_neg_iff]

/-- **The Hasse norm theorem for binary norm forms.** Over a number field `K`, the binary diagonal
form `⟨1, -d⟩` represents `a` if and only if it locally represents `a` at every finite and real
place of `K`. -/
theorem represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar (d a : K) :
    QuadraticMap.Represents (QuadraticMap.weightedSumSquares K ![1, -d]) a ↔
      LocallyRepresentsScalar (QuadraticMap.weightedSumSquares K ![1, -d]) a := by
  refine ⟨LocallyRepresentsScalar.of_represents, fun h ↦ ?_⟩
  by_cases ha : a = 0
  · subst ha
    exact QuadraticMap.represents_zero _
  rw [locallyRepresentsScalar_weightedSumSquares_one_neg_iff] at h
  rw [TauCeti.represents_weightedSumSquares_one_neg_iff]
  by_cases hd : IsSquare d
  · obtain ⟨r, rfl⟩ := hd
    by_cases hr : r = 0
    · subst hr
      have hsq : IsSquare a :=
        (TauCeti.isSquare_iff_forall_isSquare_algebraMap_adicCompletion a).mpr fun v ↦ by
          obtain ⟨x, _, hx⟩ := h.1 v
          exact ⟨x, by simpa [pow_two] using hx⟩
      obtain ⟨x, rfl⟩ := hsq
      exact ⟨x, 0, by ring⟩
    · refine ⟨(a + 1) / 2, (a - 1) / (2 * r), ?_⟩
      field_simp
      ring
  · exact (TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion hd
      (Units.mk0 a ha)).mpr ⟨h.1, forall_infinitePlaceCompletion_exists_sq_sub_mul_sq_of_real h.2⟩

end NumberField

end QuadraticForm
