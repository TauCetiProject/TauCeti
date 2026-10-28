/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass

/-!
# The rank-one boundary of diagonal descent

In rank at least two, invariance under coefficient permutations and binary replacements suffices
to descend a function on diagonal presentations to isometry classes. This fails in rank one:
there is no binary replacement, while isometric one-dimensional forms can have distinct
coefficients in the same square class.

This file makes the obstruction explicit. The function
`TauCeti.RegularFormPresentation.rankOneCoefficient` reads the lone coefficient in rank one and
returns `1` in every other rank. It is invariant under every permutation and binary step, but
separates the isometric rational forms `⟨1⟩` and `⟨4⟩`. Consequently it cannot be obtained from a
function on `TauCeti.RegularFormClass ℚ`. This shows why the rank-one hypothesis in
`TauCeti.RegularFormClass.liftDiagonal` is necessary.

## Main results

* `TauCeti.PermutationStep.rankOneCoefficient_eq`: the rank-one coefficient is invariant under
  permutation steps.
* `TauCeti.BinaryStep.rankOneCoefficient_eq`: the rank-one coefficient is invariant under binary
  steps.
* `TauCeti.exists_rankOne_equivalent_not_diagonalChain`: the forms `⟨1⟩` and `⟨4⟩` are
  isometric, but no diagonal chain connects their coefficient families, and the rank-one
  coefficient separates them.
* `TauCeti.not_exists_rankOneCoefficient_descend`: invariance under elementary steps alone does
  not suffice to define a function on isometry classes.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2.
-/

public section

open QuadraticMap

namespace TauCeti

universe u

variable {K : Type u} [Field K]

namespace RegularFormPresentation

/-- The lone coefficient of a rank-one diagonal presentation, and `1` in every other rank. -/
def rankOneCoefficient (p : RegularFormPresentation K) : Kˣ :=
  if h : p.1 = 1 then p.2 (Fin.cast h.symm 0) else 1

/-- On a rank-one presentation, `rankOneCoefficient` returns its unique coefficient. -/
@[simp]
theorem rankOneCoefficient_one (w : Fin 1 → Kˣ) :
    rankOneCoefficient (K := K) ⟨1, w⟩ = w 0 := by
  simp [rankOneCoefficient]

/-- Away from rank one, `rankOneCoefficient` returns `1`. -/
@[simp]
theorem rankOneCoefficient_of_ne_one {n : ℕ} (hn : n ≠ 1) (w : Fin n → Kˣ) :
    rankOneCoefficient (K := K) ⟨n, w⟩ = 1 := by
  simp [rankOneCoefficient, hn]

end RegularFormPresentation

namespace PermutationStep

/-- Permuting coefficients does not change the rank-one coefficient. -/
theorem rankOneCoefficient_eq {n : ℕ} {w w' : Fin n → Kˣ} (h : PermutationStep w w') :
    RegularFormPresentation.rankOneCoefficient (K := K) ⟨n, w⟩ =
      RegularFormPresentation.rankOneCoefficient (K := K) ⟨n, w'⟩ := by
  by_cases hn : n = 1
  · subst n
    obtain ⟨σ, hσ⟩ := h.exists_perm
    rw [RegularFormPresentation.rankOneCoefficient_one,
      RegularFormPresentation.rankOneCoefficient_one, hσ]
    exact congrArg w (Subsingleton.elim _ _)
  · simp [hn]

end PermutationStep

namespace BinaryStep

/-- A binary replacement does not change the rank-one coefficient. In rank one no such step
exists, since it would require two distinct indices. -/
theorem rankOneCoefficient_eq {n : ℕ} {w w' : Fin n → Kˣ} (h : BinaryStep w w') :
    RegularFormPresentation.rankOneCoefficient (K := K) ⟨n, w⟩ =
      RegularFormPresentation.rankOneCoefficient (K := K) ⟨n, w'⟩ := by
  by_cases hn : n = 1
  · subst n
    obtain ⟨i, j, hij, _⟩ := h.exists_pair
    exact (hij (Subsingleton.elim i j)).elim
  · simp [hn]

end BinaryStep

/-- Over `ℚ`, the coefficient families of `⟨1⟩` and `⟨4⟩` present isometric forms, but they
are not connected by a diagonal chain and `rankOneCoefficient` distinguishes them. -/
theorem exists_rankOne_equivalent_not_diagonalChain :
    ∃ w v : Fin 1 → ℚˣ,
      (w 0 : ℚ) = 1 ∧ (v 0 : ℚ) = 4 ∧
        (presentedForm ⟨1, w⟩).Equivalent (presentedForm ⟨1, v⟩) ∧
        ¬DiagonalChain w v ∧
        RegularFormPresentation.rankOneCoefficient ⟨1, w⟩ ≠
          RegularFormPresentation.rankOneCoefficient ⟨1, v⟩ := by
  let w : Fin 1 → ℚˣ := fun _ => 1
  let v : Fin 1 → ℚˣ := fun _ => Units.mk0 4 (by norm_num)
  refine ⟨w, v, by simp [w], by simp [v], ?_, ?_, ?_⟩
  · rw [presentedForm_eq_weightedSumSquares, presentedForm_eq_weightedSumSquares]
    apply equivalent_weightedSumSquares_of_isSquare_div
    intro i
    refine ⟨Units.mk0 (1 / 2 : ℚ) (by norm_num), ?_⟩
    apply Units.ext
    norm_num [w, v]
  · rw [diagonalChain_fin_one_iff_eq]
    intro hwv
    have := congrArg (fun u : Fin 1 → ℚˣ => (u 0 : ℚ)) hwv
    norm_num [w, v] at this
  · intro h
    have := congrArg Units.val h
    norm_num [w, v] at this

/-- No function on rational regular-form classes agrees with `rankOneCoefficient` on every
presentation. Thus the permutation and binary-step hypotheses alone do not suffice for descent. -/
theorem not_exists_rankOneCoefficient_descend :
    ¬∃ g : RegularFormClass ℚ → ℚˣ, ∀ p,
      g (Quotient.mk _ p) = RegularFormPresentation.rankOneCoefficient p := by
  rintro ⟨g, hg⟩
  obtain ⟨w, v, _, _, hequiv, _, hcoeff⟩ := exists_rankOne_equivalent_not_diagonalChain
  apply hcoeff
  rw [← hg ⟨1, w⟩, ← hg ⟨1, v⟩]
  congr 1
  exact (RegularFormClass.mk_eq_mk_iff).mpr hequiv

end TauCeti
